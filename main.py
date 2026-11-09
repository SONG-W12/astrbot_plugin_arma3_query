"""Arma3 服务器查询插件（AstrBot 版）。

发送服务器名即可查询在线状态、玩家列表与服务器资源。
"""

import asyncio
import copy
import json
import math
import os
import re
import shutil
import tempfile
import time

import a2s
import psutil
import requests

from astrbot.api import logger
from astrbot.api.event import filter, AstrMessageEvent, MessageChain
from astrbot.api.event.filter import EventMessageType
from astrbot.api.message_components import At, Plain
from astrbot.api.platform import MessageType
from astrbot.api.star import Context, Star, StarTools

PLUGIN_NAMESPACE = "astrbot_plugin_arma3_query"

# A2S 单次查询超时（秒）。info 与 players 并发，所以总耗时约等于这一个值。
QUERY_TIMEOUT = 3.0
# 「服务器列表」探查每台服务器用的超时（秒），比单台查询更短，避免列表等太久。
PROBE_TIMEOUT = 2.0
# 同一人两次查询的最小间隔（秒），0 表示不限制。可在 WebUI 配置里改。
DEFAULT_COOLDOWN = 5
# 主人 QQ 一律由面板配置 owner_qq 提供。留空表示「还没配置主人」，
# 此时主人专属指令（白名单授权等）不生效，不会误把任何人当成主人。
DEFAULT_OWNER_QQ = ""
# 巡检默认间隔（秒）
DEFAULT_WATCHDOG_INTERVAL = 180

# 没在面板里设置、也没在群里单独设置时使用的欢迎语。
# 因为发送时会自动 @ 新人（对方已经被点名一次了），默认文案里不再重复写 {昵称}。
# 可用变量：{昵称} {群名片} {QQ} {群号} {群名} {人数} {时间}
DEFAULT_WELCOME_TEMPLATE = (
    "欢迎加入本群！\n"
    "本群是 Arma3 服务器交流群，发送「服务器列表」可以查看当前在架的服务器。\n"
    "有问题随时 @管理员 ~"
)


class Arma3Query(Star):
    def __init__(self, context: Context, config: dict = None):
        super().__init__(context)
        # 注意：AstrBot 传入的是 AstrBotConfig（dict 子类，带 save_config）。
        # 不能用 `config or {}`——空配置时会把配置对象降级成普通 dict，
        # 导致 save_config 丢失、白名单只能写进内存。
        self.config = config if config is not None else {}

        # servers.json 缓存（内容 + 文件修改时间），避免每条群消息都读盘。
        # 必须在下面两个迁移动作之前初始化，迁移里会调用 _load_servers()。
        self._servers_cache: dict | None = None
        self._servers_mtime = 0.0

        self._plugin_dir = os.path.dirname(os.path.abspath(__file__))
        self._data_dir = self._resolve_data_dir()
        # servers.json 是运行期可变数据，放到插件数据目录，
        # 避免插件更新/重装覆盖插件目录时把服务器清单一起冲掉。
        # 1.4.0 起结构为 {"群号": {"服务器名": {"ip": ..., "port": ...}}}，按群隔离。
        self.server_file = os.path.join(self._data_dir, "servers.json")
        self._migrate_legacy_servers()
        self._migrate_servers_to_per_group()

        # 每个群单独的欢迎语设置（覆盖面板默认值）
        self.welcome_file = os.path.join(self._data_dir, "welcome.json")
        # 查询冷却：发送者 QQ → 上次查询的单调时间
        self._cooldowns: dict[str, float] = {}

        # 掉线巡检状态
        self._watchdog_task = None
        self._watchdog_stop = False
        self._watchdog_state: dict[str, bool] = {}
        # 最近一次收到消息的群会话，作为巡检推送地址的兜底
        self._last_umo: dict[str, str] = {}

        if not self._owner_qq():
            logger.info(
                "[Arma3查询] 还没有配置「主人 QQ」（插件配置里的 owner_qq）。"
                "在填好之前，「添加白名单」等主人专属指令不会生效。"
            )

        # 公网 IP 缓存
        self._cached_public_ip = None
        self._last_update_time = 0.0
        self._last_fail_time = 0.0
        self._CACHE_DURATION = 300
        # 取不到公网 IP 时先冷静一会儿，别让每次查询都卡在网络请求上
        self._FAIL_BACKOFF = 60
        # 实测顺序：ipify 常被重置、ifconfig.me / ip.sb 会返回 IPv6，
        # 所以把真正返回 IPv4 的两个放前面。
        self._IP_API_LIST = [
            "https://ipv4.icanhazip.com",
            "https://checkip.amazonaws.com",
            "https://api.ipify.org",
            "https://v4.ifconfig.me/ip",
        ]

    # ---------- 数据目录 ----------
    def _resolve_data_dir(self) -> str:
        try:
            return str(StarTools.get_data_dir(PLUGIN_NAMESPACE))
        except Exception as e:
            logger.warning(f"[Arma3查询] 无法创建插件数据目录，回退到插件目录: {e}")
            return self._plugin_dir

    def _migrate_legacy_servers(self):
        """把旧版放在插件目录里的 servers.json 一次性复制到数据目录。"""
        legacy = os.path.join(self._plugin_dir, "servers.json")
        if os.path.abspath(legacy) == os.path.abspath(self.server_file):
            return
        if os.path.exists(self.server_file) or not os.path.exists(legacy):
            return
        try:
            shutil.copy2(legacy, self.server_file)
            logger.info(f"[Arma3查询] servers.json 已迁移到 {self.server_file}")
        except Exception as e:
            logger.error(f"[Arma3查询] servers.json 迁移失败: {e}")

    @staticmethod
    def _is_legacy_servers(data: dict) -> bool:
        """老格式：顶层 key 就是服务器名、value 直接是 {ip, port}。"""
        for value in data.values():
            if isinstance(value, dict) and "ip" in value and "port" in value:
                return True
        return False

    def _migrate_servers_to_per_group(self):
        """把 1.3.x 的全局清单拆成按群隔离的清单。

        老格式：{"逃离": {"ip": .., "port": ..}}
        新格式：{"群号": {"逃离": {"ip": .., "port": ..}}}

        策略：原有服务器给每个白名单群各复制一份（两个群都还能查到），
        老文件另存为 servers.json.legacy 备查。
        """
        data = self._load_servers()
        if not data or not self._is_legacy_servers(data):
            return
        groups = self._allowed_groups()
        if not groups:
            logger.warning(
                "[Arma3查询] 服务器清单还是旧格式，但当前没有白名单群，"
                "暂不迁移（避免数据丢失）；配置好白名单群后重启即可自动迁移"
            )
            return
        backup = self.server_file + ".legacy"
        try:
            if not os.path.exists(backup):
                shutil.copy2(self.server_file, backup)
        except Exception as e:
            logger.warning(f"[Arma3查询] 旧清单备份失败（不影响迁移）: {e}")
        migrated = {gid: copy.deepcopy(data) for gid in groups}
        if self._save_servers(migrated):
            logger.info(
                f"[Arma3查询] 服务器清单已改为按群隔离：原有 {len(data)} 台已复制到 "
                f"{len(groups)} 个群 {groups}，旧文件备份为 {os.path.basename(backup)}"
            )

    # ---------- 配置 ----------
    def _whitelist_enabled(self) -> bool:
        return bool(self.config.get("enable_group_whitelist", True))

    def _allowed_groups(self) -> list:
        groups = self.config.get("allowed_groups", []) or []
        return [str(g) for g in groups]

    def _save_whitelist(self, groups: list):
        """保存白名单到 WebUI 插件配置（唯一持久化入口，无旧版 API 回退）。

        注意：这里不再强制把 enable_group_whitelist 改成 True。
        管理员在面板里关掉总开关后，执行「添加白名单」不应该把这个决定又翻回去。
        """
        groups = [str(g) for g in groups]
        self.config["allowed_groups"] = groups

        save_config = getattr(self.config, "save_config", None)
        if not callable(save_config):
            logger.error("[Arma3查询] 配置对象不支持 save_config，白名单仅保存在内存中")
            return
        try:
            save_config()
            logger.info(f"[Arma3查询] 白名单已保存: {groups}")
        except Exception as e:
            logger.error(f"[Arma3查询] 白名单保存失败: {e}")

    # ---------- 入群欢迎 ----------
    def _load_welcome(self) -> dict:
        try:
            with open(self.welcome_file, "r", encoding="utf-8") as f:
                data = json.load(f)
        except FileNotFoundError:
            return {}
        except Exception as e:
            logger.error(f"[Arma3查询] 读取 {self.welcome_file} 失败: {e}")
            return {}
        return data if isinstance(data, dict) else {}

    def _save_welcome(self, data: dict) -> bool:
        """先写临时文件再原子替换，避免写到一半崩溃把配置弄坏。"""
        tmp_path = None
        try:
            fd, tmp_path = tempfile.mkstemp(
                prefix=".welcome-", suffix=".json", dir=self._data_dir
            )
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            os.replace(tmp_path, self.welcome_file)
            tmp_path = None
            return True
        except Exception as e:
            logger.error(f"[Arma3查询] 欢迎语保存失败: {e}")
            return False
        finally:
            if tmp_path and os.path.exists(tmp_path):
                try:
                    os.remove(tmp_path)
                except OSError:
                    pass

    def _welcome_global_enabled(self) -> bool:
        return bool(self.config.get("welcome_enabled", True))

    def _welcome_at_enabled(self) -> bool:
        """欢迎语前面是否 @ 新人（面板可关）。"""
        return bool(self.config.get("welcome_at_newcomer", True))

    def _default_welcome_template(self) -> str:
        template = self.config.get("welcome_template", "")
        if isinstance(template, str) and template.strip():
            return template
        return DEFAULT_WELCOME_TEMPLATE

    def _welcome_setting(self, group_id: str) -> dict:
        """返回该群生效的欢迎设置：群内单独设置 > 面板默认。"""
        setting = self._load_welcome().get(str(group_id))
        if not isinstance(setting, dict):
            setting = {}
        enabled = setting.get("enabled")
        if not isinstance(enabled, bool):
            enabled = self._welcome_global_enabled()
        template = setting.get("template")
        if not isinstance(template, str) or not template.strip():
            template = self._default_welcome_template()
        return {
            "enabled": enabled,
            "template": template,
            "custom": isinstance(setting.get("template"), str)
            and bool(setting.get("template").strip()),
        }

    def _update_welcome_setting(self, group_id: str, **changes) -> bool:
        data = self._load_welcome()
        setting = data.get(str(group_id))
        if not isinstance(setting, dict):
            setting = {}
        for key in ("enabled", "template"):
            if key in changes:
                if changes[key] is None:
                    setting.pop(key, None)
                else:
                    setting[key] = changes[key]
        if setting:
            data[str(group_id)] = setting
        else:
            data.pop(str(group_id), None)
        return self._save_welcome(data)

    # ---------- 工具函数 ----------
    def _load_servers(self) -> dict:
        """读取服务器清单。

        按文件修改时间缓存，群消息频繁时不必每条消息都读盘。
        返回的是一份拷贝，调用方随便改都不会污染缓存。
        """
        try:
            mtime = os.path.getmtime(self.server_file)
        except OSError:
            self._servers_cache = None
            self._servers_mtime = 0.0
            return {}
        if self._servers_cache is not None and mtime == self._servers_mtime:
            return copy.deepcopy(self._servers_cache)
        try:
            with open(self.server_file, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            logger.error(f"[Arma3查询] 读取 {self.server_file} 失败: {e}")
            return {}
        data = data if isinstance(data, dict) else {}
        self._servers_cache = data
        self._servers_mtime = mtime
        return copy.deepcopy(data)

    def _save_servers(self, servers: dict) -> bool:
        """先写临时文件再原子替换。写到一半崩溃也不会留下半截文件。"""
        tmp_path = None
        try:
            fd, tmp_path = tempfile.mkstemp(
                prefix=".servers-", suffix=".json", dir=self._data_dir
            )
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                json.dump(servers, f, ensure_ascii=False, indent=2)
            os.replace(tmp_path, self.server_file)
            tmp_path = None
            self._servers_cache = copy.deepcopy(servers)
            try:
                self._servers_mtime = os.path.getmtime(self.server_file)
            except OSError:
                self._servers_cache = None
                self._servers_mtime = 0.0
            return True
        except Exception as e:
            logger.error(f"[Arma3查询] 保存失败: {e}")
            return False
        finally:
            if tmp_path and os.path.exists(tmp_path):
                try:
                    os.remove(tmp_path)
                except OSError:
                    pass

    # ---------- 按群隔离的清单访问 ----------
    @staticmethod
    def _group_servers(all_servers: dict, group_id: str) -> dict:
        """取出某个群的服务器清单。结构不对的一律过滤掉，避免脏数据混进查询。"""
        entry = all_servers.get(str(group_id))
        if not isinstance(entry, dict):
            return {}
        return {
            name: srv
            for name, srv in entry.items()
            if isinstance(srv, dict) and "ip" in srv and "port" in srv
        }

    @classmethod
    def _merged_servers(cls, all_servers: dict) -> dict:
        """私聊用：把所有群的服务器合并成一份视图（只读）。"""
        merged = {}
        for group_id in all_servers:
            merged.update(cls._group_servers(all_servers, group_id))
        return merged

    @classmethod
    def _conflicted_names(cls, all_servers: dict) -> set:
        """同名但不同群指向不同地址的那些名字（私聊查询时不能瞎猜）。"""
        seen = {}
        conflicts = set()
        for group_id in all_servers:
            for name, srv in cls._group_servers(all_servers, group_id).items():
                key = (str(srv.get("ip", "")), str(srv.get("port", "")))
                if name in seen and seen[name] != key:
                    conflicts.add(name)
                else:
                    seen[name] = key
        return conflicts

    @classmethod
    def _groups_with_servers(cls, all_servers: dict) -> list:
        return [gid for gid in all_servers if cls._group_servers(all_servers, gid)]

    _IPV4_RE = re.compile(r"^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$")

    @classmethod
    def _is_ipv4(cls, text: str) -> bool:
        match = cls._IPV4_RE.match((text or "").strip())
        if not match:
            return False
        return all(0 <= int(part) <= 255 for part in match.groups())

    def _get_public_ipv4(self):
        """返回本机公网 IPv4；取不到时返回 None（由调用方决定怎么显示）。"""
        now = time.time()
        if self._cached_public_ip and (now - self._last_update_time) < self._CACHE_DURATION:
            return self._cached_public_ip
        if self._last_fail_time and (now - self._last_fail_time) < self._FAIL_BACKOFF:
            return None
        for api in self._IP_API_LIST:
            try:
                resp = requests.get(api, timeout=2)
                if resp.status_code != 200:
                    continue
                ip_text = resp.text.strip()
                if self._is_ipv4(ip_text):
                    self._cached_public_ip = ip_text
                    self._last_update_time = now
                    self._last_fail_time = 0.0
                    return ip_text
            except Exception:
                continue
        self._last_fail_time = now
        logger.warning("[Arma3查询] 获取公网 IPv4 失败，本次显示填写地址")
        return None

    @staticmethod
    def _format_duration(seconds: int) -> str:
        return f"{int(seconds // 3600):02d}:{int((seconds % 3600) // 60):02d}:{int(seconds % 60):02d}"

    # ---------- 查询 ----------
    async def _query_server(self, ip: str, port: str) -> str:
        """查询一台服务器。

        info 与 players 同时发起（都是阻塞 UDP，各自丢线程池），
        所以总耗时约等于一个 QUERY_TIMEOUT，而不是以前的两倍。
        """
        try:
            addr = (ip, int(port))
        except (TypeError, ValueError):
            return "❌ 端口填写不正确，应该是 1–65535 之间的数字"

        info_res, players_res = await asyncio.gather(
            asyncio.to_thread(a2s.info, addr, timeout=QUERY_TIMEOUT),
            asyncio.to_thread(a2s.players, addr, timeout=QUERY_TIMEOUT),
            return_exceptions=True,
        )

        if isinstance(info_res, BaseException):
            logger.error(f"[Arma3查询] {ip}:{port} 查询失败: {info_res!r}")
            return f"❌ {self._friendly_error(info_res)}"

        players_failed = isinstance(players_res, BaseException)
        if players_failed:
            # 玩家列表拿不到不算致命，至少还能显示概况与在线人数
            logger.warning(
                f"[Arma3查询] {ip}:{port} 玩家列表获取失败: {players_res!r}"
            )
            players: list = []
        else:
            players = list(players_res)

        host = await asyncio.to_thread(self._collect_host_stats)
        return self._render_report(ip, port, info_res, players, players_failed, host)

    def _collect_host_stats(self) -> dict:
        """采集「运行 AstrBot 这台主机」的资源占用。

        A2S 协议不提供服务器自身的 CPU / 内存，这里采到的是本机数据，
        输出时统一标注成「机器人主机」，避免被误读成服务器的负载。
        """
        public_ip = self._get_public_ipv4()
        try:
            mem = psutil.virtual_memory()
            return {
                "cpu": psutil.cpu_percent(interval=0.1),
                "mem_used": round(mem.used / 1024 / 1024 / 1024, 1),
                "mem_total": round(mem.total / 1024 / 1024 / 1024, 1),
                "mem_percent": mem.percent,
                "public_ip": public_ip,
            }
        except Exception as e:
            logger.warning(f"[Arma3查询] 主机资源采集失败: {e}")
            return {
                "cpu": "?",
                "mem_used": "?",
                "mem_total": "?",
                "mem_percent": "?",
                "public_ip": public_ip,
            }

    @staticmethod
    def _friendly_error(exc: BaseException) -> str:
        """把底层异常翻译成用户看得懂的话，原始细节只进日志。"""
        name = type(exc).__name__
        if isinstance(exc, TimeoutError) or "timeout" in name.lower():
            return "服务器没有响应。可能是服没开、端口填错了，或被防火墙拦了。"
        if isinstance(exc, ConnectionRefusedError):
            return "服务器拒绝连接，这个端口可能不是查询端口。"
        if isinstance(exc, ConnectionResetError):
            return "连接被重置，服务器可能刚关闭，或者端口填错了。"
        if name in ("BrokenMessageError", "BufferExhaustedError"):
            return "返回的数据不是 Arma3 的查询格式，请确认查询端口是否正确。"
        if isinstance(exc, OSError):
            return "网络连接失败，请检查服务器地址与网络。"
        return "查询失败，请稍后再试。"

    def _render_report(
        self,
        ip: str,
        port: str,
        info,
        players: list,
        players_failed: bool,
        host: dict,
    ) -> str:
        server_name = (getattr(info, "server_name", "") or "").strip()
        game_name = (getattr(info, "game", "") or "").strip()
        game_version = (getattr(info, "version", "") or "").strip()
        map_name = (getattr(info, "map_name", "") or "").strip()
        has_pwd = bool(getattr(info, "password_protected", False))
        is_encrypted = "有密码" if has_pwd else "没有密码"

        try:
            connect_port = int(port) - 1  # 进服连接端口 = 查询端口 - 1
        except (TypeError, ValueError):
            connect_port = port

        public_ip = host.get("public_ip")
        addr_ip = public_ip or ip
        addr_hint = "" if public_ip else "（未取到公网 IP，显示的是填写的地址）"

        ranking = []
        for p in sorted(
            players, key=lambda x: getattr(x, "duration", 0) or 0, reverse=True
        ):
            duration = self._format_duration(getattr(p, "duration", 0) or 0)
            score = getattr(p, "score", 0)
            name = (getattr(p, "name", "") or "").strip() or "无名"
            ranking.append(f"时长：{duration}  |得分：{score}   |{name}")

        if ranking:
            ranking_str = "\n".join(ranking)
        elif players_failed:
            ranking_str = "（玩家列表获取失败，只显示在线人数）"
        else:
            ranking_str = "暂无玩家数据"

        return (
            f"服务器名：{server_name}\n"
            f"游戏名称：{game_name}\n"
            f"游戏地图：{map_name}\n"
            f"游戏版本：{game_version}\n"
            f"是否加密：{is_encrypted}\n"
            f"服务器地址：{addr_ip}:{connect_port}{addr_hint}\n"
            f"-------------------------------------------\n"
            f"{ranking_str}\n"
            f"-------------------------------------------\n"
            f"当前玩家：{getattr(info, 'player_count', '?')}    最大玩家：{getattr(info, 'max_players', '?')}\n"
            f"机器人主机 CPU：{host.get('cpu')}%\n"
            f"机器人主机内存：{host.get('mem_used')}G/{host.get('mem_total')}G ({host.get('mem_percent')}%)"
        )

    # ---------- 权限/白名单 ----------
    def _owner_qq(self) -> str:
        """主人 QQ：只来自面板配置 owner_qq。

        没有兜底常量——没配置就返回空字符串，表示「还没设定主人」，
        这样不会把任何陌生人误当主人。换号只需改面板，不必改代码。
        """
        value = self.config.get("owner_qq") if isinstance(self.config, dict) else ""
        text = str(value or "").strip()
        return text if text.isdigit() else ""

    def _is_owner(self, event: AstrMessageEvent) -> bool:
        """是否机器人主人（唯一授权人）。未配置主人时恒为 False。"""
        owner = self._owner_qq()
        if not owner:
            return False
        user_id = str(getattr(event.message_obj.sender, "user_id", ""))
        return user_id == owner

    def _get_group_id(self, event: AstrMessageEvent) -> str:
        try:
            return str(event.get_group_id() or event.message_obj.group_id or "")
        except Exception:
            return ""

    def _is_group_allowed(self, event: AstrMessageEvent) -> bool:
        """群白名单判断：启用白名单时，仅白名单内群可使用查询插件"""
        if not self._whitelist_enabled():
            return True
        return self._get_group_id(event) in self._allowed_groups()

    @staticmethod
    def _get_sender_role(event: AstrMessageEvent) -> str:
        """从原始事件中解析 QQ 群角色（owner/admin/member）。

        注：aiocqhttp 的 Event 是 dict 子类，因此 dict 分支对 QQ 有效；
        其他适配器的 raw_message 结构不同，本插件已在 metadata.yaml 中
        声明 support_platforms: [aiocqhttp]。
        """
        raw = getattr(event.message_obj, "raw_message", None)
        try:
            if isinstance(raw, dict):
                return str(raw.get("sender", {}).get("role", "") or "")
            if isinstance(raw, str):
                data = json.loads(raw)
                return str(data.get("sender", {}).get("role", "") or "")
        except Exception:
            pass
        return ""

    def _is_admin(self, event: AstrMessageEvent) -> bool:
        """私聊：仅主人；群聊：群主(owner)/群管理员(admin)"""
        msg_type = event.get_message_type()
        if msg_type == MessageType.FRIEND_MESSAGE:
            owner = self._owner_qq()
            if not owner:
                return False
            user_id = str(getattr(event.message_obj.sender, "user_id", ""))
            return user_id == owner
        return self._get_sender_role(event) in ("owner", "admin")

    # ---------- 白名单授权指令 ----------
    async def _handle_whitelist_cmd(self, event: AstrMessageEvent, msg: str):
        """处理 添加白名单/删除白名单/白名单。返回 (是否已处理, 回复文本列表)。"""
        if msg not in ("添加白名单", "删除白名单", "白名单"):
            return False, []

        # 仅主人可操作
        if not self._is_owner(event):
            event.stop_event()
            return True, ["❌权限不足！仅机器人主人可以授权白名单"]

        # 私聊中发送：无群可授权
        if event.get_message_type() != MessageType.GROUP_MESSAGE:
            if msg == "白名单":
                groups = self._allowed_groups()
                txt = "📋 当前白名单群：" + ("\n".join(groups) if groups else "（空）")
            else:
                txt = "❌请在你想要授权/取消授权的**群内**发送该指令"
            event.stop_event()
            return True, [txt]

        gid = self._get_group_id(event)
        groups = self._allowed_groups()

        if msg == "添加白名单":
            if gid in groups:
                txt = f"✅ 该群（{gid}）已在白名单中"
            else:
                groups.append(gid)
                self._save_whitelist(groups)
                txt = f"✅ 已授权本群（{gid}）使用查询插件！"
        elif msg == "删除白名单":
            if gid in groups:
                groups.remove(gid)
                self._save_whitelist(groups)
                txt = f"🗑️ 已取消本群（{gid}）的查询权限"
            else:
                txt = f"该群（{gid}）不在白名单中"
        else:  # 白名单
            txt = "📋 当前白名单群：\n" + ("\n".join(groups) if groups else "（空）")

        event.stop_event()
        return True, [txt]

    # ---------- 入群欢迎 ----------
    async def _handle_group_notice(self, event: AstrMessageEvent) -> bool:
        """处理 QQ 入群通知。返回 True 表示这条事件已被本插件消费。

        AstrBot 会把 OneBot 的 notice 事件转成一条「正文为空」的群消息，
        所以必须在读取 message_str 之前先拦下来。
        """
        raw = getattr(event.message_obj, "raw_message", None)
        if not hasattr(raw, "get"):
            return False
        try:
            if raw.get("post_type") != "notice":
                return False
            if raw.get("notice_type") != "group_increase":
                return False
        except Exception:
            return False

        # 入群事件不是用户指令，无论发不发欢迎语都必须截断，
        # 否则这条空消息会继续流到 AI 那边。
        event.stop_event()

        if event.get_message_type() != MessageType.GROUP_MESSAGE:
            return True
        group_id = self._get_group_id(event)
        if not group_id:
            return True
        if not self._is_group_allowed(event):
            return True

        setting = self._welcome_setting(group_id)
        if not setting["enabled"]:
            return True

        user_id = str(raw.get("user_id", "") or "")
        text = await self._render_welcome(
            event, group_id, user_id, setting["template"]
        )
        if not text:
            return True

        # 在欢迎语前面 @ 一下新人，QQ 会给他推送提醒，不然他大概率看不到
        chain = []
        if self._welcome_at_enabled() and user_id.isdigit():
            chain.append(At(qq=user_id))
        chain.append(Plain(text))

        try:
            await event.send(event.chain_result(chain))
            logger.info(
                f"[Arma3查询] 已发送入群欢迎: 群 {group_id} 新人 {user_id}"
                f"（@提醒: {'开' if len(chain) > 1 else '关'}）"
            )
        except Exception as e:
            logger.error(f"[Arma3查询] 入群欢迎发送失败: {e}")
        return True

    async def _render_welcome(
        self,
        event: AstrMessageEvent,
        group_id: str,
        user_id: str,
        template: str,
    ) -> str:
        member, group = await asyncio.gather(
            self._fetch_member_info(event, group_id, user_id),
            self._fetch_group_info(event, group_id),
            return_exceptions=True,
        )
        if isinstance(member, BaseException) or not isinstance(member, dict):
            member = {}
        if isinstance(group, BaseException) or not isinstance(group, dict):
            group = {}

        nickname = (
            str(member.get("nickname") or "").strip()
            or str(member.get("card") or "").strip()
            or user_id
        )
        card = str(member.get("card") or "").strip() or nickname
        values = {
            "{昵称}": nickname,
            "{群名片}": card,
            "{QQ}": user_id,
            "{群号}": group_id,
            "{群名}": str(group.get("group_name") or "").strip(),
            "{人数}": str(group.get("member_count") or "").strip(),
            "{时间}": time.strftime("%H:%M"),
        }
        text = template or DEFAULT_WELCOME_TEMPLATE
        for key, value in values.items():
            text = text.replace(key, value)
        return text.strip()

    @staticmethod
    async def _fetch_member_info(
        event: AstrMessageEvent, group_id: str, user_id: str
    ) -> dict:
        bot = getattr(event, "bot", None)
        if bot is None:
            return {}
        try:
            info = await bot.call_action(
                "get_group_member_info",
                group_id=int(group_id),
                user_id=int(user_id),
                no_cache=True,
                self_id=int(event.get_self_id()),
            )
        except Exception as e:
            logger.warning(f"[Arma3查询] 获取群成员信息失败: {e}")
            return {}
        return info if isinstance(info, dict) else {}

    @staticmethod
    async def _fetch_group_info(event: AstrMessageEvent, group_id: str) -> dict:
        bot = getattr(event, "bot", None)
        if bot is None:
            return {}
        try:
            info = await bot.call_action(
                "get_group_info",
                group_id=int(group_id),
                no_cache=True,
                self_id=int(event.get_self_id()),
            )
        except Exception as e:
            logger.warning(f"[Arma3查询] 获取群信息失败: {e}")
            return {}
        return info if isinstance(info, dict) else {}

    def _at_hint(self) -> str:
        return "@新人 " if self._welcome_at_enabled() else ""

    @staticmethod
    def _preview_welcome(template: str) -> str:
        """把变量替换成示例值，方便设置时先看一眼效果。"""
        sample = {
            "{昵称}": "示例昵称",
            "{群名片}": "示例名片",
            "{QQ}": "123456789",
            "{群号}": "123456789",
            "{群名}": "示例群",
            "{人数}": "128",
            "{时间}": time.strftime("%H:%M"),
        }
        text = template or DEFAULT_WELCOME_TEMPLATE
        for key, value in sample.items():
            text = text.replace(key, value)
        return text.strip()

    WELCOME_SWITCH_WORDS = ("开", "开启", "on", "关", "关闭", "off")

    @classmethod
    def _is_welcome_cmd(cls, msg: str) -> bool:
        """判断是不是欢迎语相关指令。

        只认「欢迎」「欢迎 开/关」「设置欢迎语 ...」「清除欢迎语」这几种，
        避免把名字里带「欢迎」的服务器吃掉。
        """
        if msg in ("欢迎", "清除欢迎语"):
            return True
        if msg.startswith("设置欢迎语"):
            return True
        if msg.startswith("欢迎"):
            arg = msg[len("欢迎"):].strip().lower()
            return arg in cls.WELCOME_SWITCH_WORDS
        return False

    def _handle_welcome_cmd(self, event: AstrMessageEvent, msg: str):
        """处理 欢迎 / 欢迎 开 / 欢迎 关 / 设置欢迎语 / 清除欢迎语。"""
        if event.get_message_type() != MessageType.GROUP_MESSAGE:
            return False, ""
        group_id = self._get_group_id(event)
        if not group_id:
            return False, ""
        if not self._is_admin(event):
            return True, "❌权限不足！仅群主/群管理员可以修改本群欢迎语"

        if msg.startswith("设置欢迎语"):
            content = msg[len("设置欢迎语"):].strip()
            if not content:
                return True, (
                    "❌指令后面要写上欢迎语内容。\n"
                    "例：设置欢迎语 欢迎 {昵称} 加入！本群是 Arma3 交流群。\n"
                    "可用变量：{昵称} {群名片} {QQ} {群号} {群名} {人数} {时间}"
                )
            if len(content) > 500:
                return True, "❌欢迎语太长了，请控制在 500 字以内。"
            if not self._update_welcome_setting(
                group_id, template=content, enabled=True
            ):
                return True, "❌保存失败，请检查插件数据目录的写入权限。"
            return True, (
                "✅ 本群欢迎语已更新，实际发送效果如下：\n"
                "————\n"
                f"{self._at_hint()}{self._preview_welcome(content)}\n"
                "————\n"
                "（{昵称} {群名片} {QQ} {群号} {群名} {人数} {时间} 这些变量会自动替换）"
            )

        if msg == "清除欢迎语":
            if not self._update_welcome_setting(group_id, template=None):
                return True, "❌保存失败，请检查插件数据目录的写入权限。"
            return True, "🗑️ 已清除本群单独设置的欢迎语，恢复使用面板里的默认欢迎语。"

        # msg == "欢迎"
        arg = msg[len("欢迎"):].strip()
        if arg in ("开", "开启", "on"):
            ok = self._update_welcome_setting(group_id, enabled=True)
            return True, "✅ 本群入群欢迎已开启" if ok else "❌保存失败"
        if arg in ("关", "关闭", "off"):
            ok = self._update_welcome_setting(group_id, enabled=False)
            return True, "✅ 本群入群欢迎已关闭" if ok else "❌保存失败"
        if arg:
            return True, "❌用法：欢迎 / 欢迎 开 / 欢迎 关"

        setting = self._welcome_setting(group_id)
        state = "开" if setting["enabled"] else "关"
        source = "本群单独设置" if setting["custom"] else "面板默认"
        at_state = "开" if self._welcome_at_enabled() else "关"
        return True, (
            f"📢 本群入群欢迎：{state}（{source}）\n"
            f"@新人提醒：{at_state}\n"
            "————\n"
            f"{self._at_hint()}{setting['template']}\n"
            "————\n"
            "可用变量：{昵称} {群名片} {QQ} {群号} {群名} {人数} {时间}\n"
            "修改：设置欢迎语 <内容>｜关闭：欢迎 关｜还原：清除欢迎语"
        )

    # ---------- 服务器清单输入校验 ----------
    _HOSTNAME_RE = re.compile(r"^[A-Za-z0-9]([A-Za-z0-9.\-]{0,251}[A-Za-z0-9])?$")

    @classmethod
    def _parse_server_input(cls, raw: str):
        """解析并校验「IP>查询端口>名称」。

        以前这里只做 split，端口填错、名字重名都会静默写进去，
        查询的时候才炸。现在一律提前拦下来，直接告诉用户哪里错了。
        """
        parts = [p.strip() for p in (raw or "").split(">")]
        if len(parts) != 3:
            raise ValueError("格式不对。正确格式：添加服务器 IP>查询端口>名称")
        ip, port_text, name = parts

        if not ip:
            raise ValueError("IP 或域名不能为空")
        if not (cls._is_ipv4(ip) or cls._HOSTNAME_RE.match(ip)):
            raise ValueError(f"「{ip}」不是有效的 IP 或域名")
        if not port_text.isdigit():
            raise ValueError(f"查询端口「{port_text}」必须是数字")
        port = int(port_text)
        if not 1 <= port <= 65535:
            raise ValueError(f"查询端口 {port} 超出范围，应在 1–65535 之间")
        if not name:
            raise ValueError("名称不能为空")
        if len(name) > 20:
            raise ValueError(f"名称「{name}」太长，请控制在 20 字以内")
        return ip, str(port), name

    # ---------- 服务器状态探查 ----------
    async def _probe_one(self, ip: str, port: str, timeout: float = PROBE_TIMEOUT):
        """探一下服务器是否在线。返回 (是否在线, 当前人数, 最大人数)。"""
        try:
            addr = (ip, int(port))
        except (TypeError, ValueError):
            return False, 0, 0
        try:
            info = await asyncio.to_thread(a2s.info, addr, timeout=timeout)
        except Exception:
            return False, 0, 0
        return (
            True,
            int(getattr(info, "player_count", 0) or 0),
            int(getattr(info, "max_players", 0) or 0),
        )

    async def _render_server_list(self, servers: dict, title: str = "服务器列表") -> str:
        """一次把清单里的服务器查一遍，列表直接带在线状态。"""
        names = list(servers)
        results = await asyncio.gather(
            *(
                self._probe_one(s.get("ip", ""), s.get("port", ""))
                for s in servers.values()
            ),
            return_exceptions=True,
        )
        lines = [f"📂 {title}："]
        online_count = 0
        for name, res in zip(names, results):
            if isinstance(res, BaseException) or not res[0]:
                lines.append(f"- {name}　❌ 离线")
                continue
            online_count += 1
            lines.append(f"- {name}　✅ 在线 {res[1]}/{res[2]}")
        lines.append(f"（共 {len(names)} 台，在线 {online_count} 台）")
        return "\n".join(lines)

    async def _render_all_groups(self, all_servers: dict) -> str:
        """私聊用：按群分组列出全部服务器。"""
        blocks = []
        for group_id in self._groups_with_servers(all_servers):
            blocks.append(
                await self._render_server_list(
                    self._group_servers(all_servers, group_id),
                    title=f"群 {group_id} 的服务器",
                )
            )
        return "\n\n".join(blocks) if blocks else "📂 所有群都还没有录入服务器"

    # ---------- 掉线巡检 ----------
    def _watchdog_enabled(self) -> bool:
        return bool(self.config.get("watchdog_enabled", True))

    def _watchdog_interval(self) -> int:
        try:
            value = int(
                self.config.get("watchdog_interval", DEFAULT_WATCHDOG_INTERVAL)
            )
        except (TypeError, ValueError):
            return DEFAULT_WATCHDOG_INTERVAL
        return max(60, min(value, 3600))

    def _group_umo(self, group_id: str):
        """拼出「平台实例:GroupMessage:群号」会话标识，用于主动推送。

        平台实例 id 是用户在面板里起的名字（例如「洛小汐」），不能写死，
        所以运行时枚举平台，失败再用最近一次收到消息的会话兜底。
        """
        try:
            for inst in self.context.platform_manager.get_insts():
                meta = inst.meta()
                if getattr(meta, "name", "") == "aiocqhttp":
                    return f"{meta.id}:{MessageType.GROUP_MESSAGE.value}:{group_id}"
        except Exception as e:
            logger.warning(f"[Arma3查询] 枚举平台适配器失败: {e}")
        return self._last_umo.get(str(group_id))

    async def _send_to_group(self, group_id: str, text: str) -> bool:
        umo = self._group_umo(str(group_id))
        if not umo:
            logger.warning(f"[Arma3查询] 找不到群 {group_id} 的会话，跳过播报")
            return False
        try:
            ok = await StarTools.send_message(umo, MessageChain([Plain(text)]))
        except Exception as e:
            logger.error(f"[Arma3查询] 播报到群 {group_id} 失败: {e}")
            return False
        if not ok:
            logger.warning(f"[Arma3查询] 群 {group_id} 没有匹配到平台，播报未发出")
        return bool(ok)

    async def _watchdog_tick(self, announce: bool = True):
        """按群巡检本群的服务器，掉线/恢复时只播报到这个群。"""
        if not self._watchdog_enabled():
            return
        all_servers = self._load_servers()
        watched = set(self._allowed_groups())
        for group_id in self._groups_with_servers(all_servers):
            if watched and group_id not in watched:
                continue  # 已经不在白名单里的群不再播报
            for name, srv in self._group_servers(all_servers, group_id).items():
                online, count, max_players = await self._probe_one(
                    srv.get("ip", ""), srv.get("port", ""), timeout=PROBE_TIMEOUT
                )
                key = f"{group_id}/{name}"
                previous = self._watchdog_state.get(key)
                self._watchdog_state[key] = online
                if previous is None or previous == online or not announce:
                    # 首次探测只记录状态，避免每次重启 AstrBot 就刷一条播报
                    continue
                stamp = time.strftime("%H:%M")
                if online:
                    text = (
                        f"✅ 服务器「{name}」已恢复在线"
                        f"（{count}/{max_players}）　{stamp}"
                    )
                else:
                    text = (
                        f"⚠️ 服务器「{name}」掉线了　{stamp}\n"
                        f"发「{name}」可以再确认一次"
                    )
                await self._send_to_group(group_id, text)

    async def _watchdog_loop(self):
        interval = self._watchdog_interval()
        logger.info(f"[Arma3查询] 掉线巡检已启动，每 {interval} 秒检查一次")
        while not self._watchdog_stop:
            try:
                await asyncio.sleep(interval)
            except asyncio.CancelledError:
                break
            if self._watchdog_stop:
                break
            try:
                await self._watchdog_tick()
            except Exception as e:
                logger.error(f"[Arma3查询] 巡检出错: {repr(e)}")

    @filter.on_astrbot_loaded()
    async def _start_watchdog(self):
        """AstrBot 加载完成后启动后台巡检（这里才有可用的事件循环）。"""
        if self._watchdog_task is not None and not self._watchdog_task.done():
            return
        if not self._watchdog_enabled():
            logger.info("[Arma3查询] 掉线巡检在面板里是关闭的，跳过启动")
            return
        self._watchdog_stop = False
        self._watchdog_task = asyncio.create_task(self._watchdog_loop())

    def __del__(self):
        # 只置标志位，让巡检任务自己退出；跨线程 cancel 不安全
        try:
            self._watchdog_stop = True
        except Exception:
            pass

    # ---------- 查询冷却 ----------
    def _cooldown_seconds(self) -> int:
        try:
            value = int(self.config.get("query_cooldown", DEFAULT_COOLDOWN))
        except (TypeError, ValueError):
            return DEFAULT_COOLDOWN
        return max(0, min(value, 3600))

    def _cooldown_remaining(self, event) -> int:
        """查询冷却。返回还要等几秒，0 表示放行（放行时会记录本次时间）。

        主人不受冷却限制——他自己经常要连着查好几台服。
        """
        cooldown = self._cooldown_seconds()
        try:
            user_id = str(event.get_sender_id() or "")
        except Exception:
            user_id = ""
        if cooldown <= 0 or not user_id:
            return 0
        if self._is_owner(event):
            return 0
        now = time.monotonic()
        if len(self._cooldowns) > 2000:
            # 简单清理，避免长期运行后字典无限增长
            self._cooldowns = {
                k: v for k, v in self._cooldowns.items() if now - v < cooldown
            }
        remain = cooldown - (now - self._cooldowns.get(user_id, 0.0))
        if remain > 0:
            return max(1, math.ceil(remain))
        self._cooldowns[user_id] = now
        return 0

    # ---------- 消息处理 ----------
    @filter.event_message_type(EventMessageType.GROUP_MESSAGE | EventMessageType.PRIVATE_MESSAGE)
    async def on_message(self, event: AstrMessageEvent):
        # 0. 入群通知：正文为空，必须在取 message_str 之前处理
        if await self._handle_group_notice(event):
            return

        try:
            msg = (event.message_str or "").strip()
        except Exception:
            return
        if not msg:
            return

        # 记下这个群的会话标识，巡检主动推送时如果枚举不到平台可以兜底
        try:
            gid = event.get_group_id()
            if gid:
                self._last_umo[str(gid)] = event.unified_msg_origin
        except Exception:
            pass

        # 1. 白名单授权指令（仅主人可用，不受白名单限制，避免"先有鸡还是先有蛋"）
        handled, replies = await self._handle_whitelist_cmd(event, msg)
        if handled:
            for r in replies:
                yield event.plain_result(r)
            return

        # 2. 群白名单过滤：非白名单群，插件完全静默
        if event.get_message_type() == MessageType.GROUP_MESSAGE:
            if not self._is_group_allowed(event):
                return

        # 3. 入群欢迎语设置（群内仅群主/群管理员）
        if self._is_welcome_cmd(msg):
            accepted, txt = self._handle_welcome_cmd(event, msg)
            if accepted:
                yield event.plain_result(txt)
                event.stop_event()
                return

        # 按群隔离：群里只看本群清单；私聊是全部群的只读合并视图
        all_servers = self._load_servers()
        is_group_chat = event.get_message_type() == MessageType.GROUP_MESSAGE
        current_group = self._get_group_id(event) if is_group_chat else ""
        servers = (
            self._group_servers(all_servers, current_group)
            if is_group_chat
            else self._merged_servers(all_servers)
        )

        # 帮助
        if msg in ("help", "帮助"):
            help_text = (
                "【Arma3服务器查询机器人 帮助】\n"
                "🔹普通成员/私聊好友可用指令：\n"
                "help / 帮助    查看指令说明\n"
                "服务器名称     查询本群（私聊为全部群）的服务器状态\n"
                "服务器列表     查看服务器，附带在线状态\n\n"
                "🔹仅机器人主人（你）可用：\n"
                "添加白名单     在当前群授权查询功能\n"
                "删除白名单     取消当前群的查询权限\n"
                "白名单         查看已授权群列表\n\n"
                "🔹群内仅群主/群管理员可用：\n"
                "添加服务器 IP>查询端口>名称\n"
                "覆盖服务器 IP>查询端口>名称\n"
                "删除服务器 名称\n"
                "欢迎                查看本群入群欢迎语\n"
                "欢迎 开 / 欢迎 关   打开或关闭本群入群欢迎\n"
                "设置欢迎语 <内容>   设置本群欢迎语\n"
                "清除欢迎语          恢复使用面板里的默认欢迎语\n\n"
                "🔹欢迎语可用变量：\n"
                "{昵称} {群名片} {QQ} {群号} {群名} {人数} {时间}\n\n"
                "🔹每个群的服务器清单互相独立，只能看到、改到本群的\n"
                "🔹私聊只能查询，增删服务器请到对应的群里操作\n"
                "📌使用示例：\n"
                "添加服务器 123.123.123.123>2303>arma1\n"
                "覆盖服务器 123.123.123.123>2303>arma1\n"
                "删除服务器 arma1\n"
                "设置欢迎语 欢迎加入本群！有问题 @管理员\n"
                "arma1\n"
                "服务器列表（会显示每台在线状态）\n"
                "注：进服连接端口自动为填写的查询端口减1"
            )
            yield event.plain_result(help_text)
            event.stop_event()
            return

        # 管理员指令：添加 / 覆盖 / 删除服务器（只能在群里做）
        if (
            msg.startswith("添加服务器")
            or msg.startswith("覆盖服务器")
            or msg.startswith("删除服务器")
        ):
            if not is_group_chat:
                yield event.plain_result(
                    "❌ 私聊只能查询，增删服务器请到对应的群里发送指令"
                )
                event.stop_event()
                return
            if not self._is_admin(event):
                yield event.plain_result("❌权限不足！仅群主/群管理员可执行该操作")
                event.stop_event()
                return

            # 本群清单的引用，改完整个 all_servers 一起落盘
            group_store = all_servers.setdefault(current_group, {})

            # 删除
            if msg.startswith("删除服务器"):
                cmd_name = msg[len("删除服务器"):].strip()
                if cmd_name in servers:
                    group_store.pop(cmd_name, None)
                    if self._save_servers(all_servers):
                        yield event.plain_result(
                            f"🗑️ 已从本群删除服务器：{cmd_name}"
                        )
                    else:
                        yield event.plain_result("❌ 保存失败，请检查插件数据目录的写入权限")
                else:
                    yield event.plain_result(f"❌ 本群没有服务器「{cmd_name}」")
                event.stop_event()
                return

            # 添加 / 覆盖
            overwrite = msg.startswith("覆盖服务器")
            prefix = "覆盖服务器" if overwrite else "添加服务器"
            try:
                ip, port, cmd_name = self._parse_server_input(msg[len(prefix):].strip())
            except ValueError as e:
                yield event.plain_result(f"❌ {e}")
                event.stop_event()
                return

            exists = servers.get(cmd_name)
            if isinstance(exists, dict) and not overwrite:
                old_ip = str(exists.get("ip", ""))
                old_port = str(exists.get("port", ""))
                if old_ip == ip and old_port == port:
                    yield event.plain_result(
                        f"ℹ️「{cmd_name}」已经是 {ip}:{port} 了，不用重复添加"
                    )
                else:
                    yield event.plain_result(
                        f"⚠️ 名称「{cmd_name}」已被占用，当前指向 {old_ip}:{old_port}\n"
                        f"如果确定要改成 {ip}:{port}，请发送：\n"
                        f"覆盖服务器 {ip}>{port}>{cmd_name}"
                    )
                event.stop_event()
                return

            group_store[cmd_name] = {"ip": ip, "port": port}
            if self._save_servers(all_servers):
                try:
                    game_port = f"{int(port) - 1}"
                except (TypeError, ValueError):
                    game_port = "查询端口-1"
                yield event.plain_result(
                    f"✅ {'覆盖' if exists else '添加'}成功！本群指令：{cmd_name}\n"
                    f"查询端口 {port}　进服地址 {ip}:{game_port}\n"
                    f"（只在本群生效，其他群看不到）"
                )
            else:
                yield event.plain_result("❌ 保存失败，请检查插件数据目录的写入权限")
            event.stop_event()
            return

        # 服务器列表（带在线状态；群里只列本群，私聊按群分组列全部）
        if msg == "服务器列表":
            if not servers:
                yield event.plain_result(
                    "📂 本群还没有录入服务器" if is_group_chat else "📂 所有群都还没有录入服务器"
                )
                event.stop_event()
                return
            wait = self._cooldown_remaining(event)
            if wait > 0:
                yield event.plain_result(f"⏳ 刚查过，请 {wait} 秒后再试")
                event.stop_event()
                return
            if is_group_chat:
                yield event.plain_result(await self._render_server_list(servers))
            else:
                yield event.plain_result(await self._render_all_groups(all_servers))
            event.stop_event()
            return

        # 查询服务器（阻塞操作已通过 asyncio.to_thread 移出事件循环）
        if msg in servers:
            # 私聊是把所有群合并出来的视图，同名不同地址时不能瞎猜
            if not is_group_chat and msg in self._conflicted_names(all_servers):
                detail = []
                for gid in self._groups_with_servers(all_servers):
                    entry = self._group_servers(all_servers, gid).get(msg)
                    if entry:
                        detail.append(f"群 {gid}：{entry.get('ip')}:{entry.get('port')}")
                yield event.plain_result(
                    f"⚠️「{msg}」在多个群里指向不同地址，请到对应群里查询：\n"
                    + "\n".join(detail)
                )
                event.stop_event()
                return
            wait = self._cooldown_remaining(event)
            if wait > 0:
                yield event.plain_result(f"⏳ 查询太频繁了，请 {wait} 秒后再试")
                event.stop_event()
                return
            srv = servers[msg]
            res = await self._query_server(srv.get("ip", ""), srv.get("port", ""))
            yield event.plain_result(res)
            event.stop_event()
            return

        # 未命中任何指令：不拦截，交给 AI 正常对话
