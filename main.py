#!/usr/bin/env python3
# ============================================================================
# DEVIL JARVIS — TELEGRAM JARVIS NATURAL LANGUAGE CONTROL  (single file)
#
#   Telegram message -> /AI detection -> NLU (intent + params + conditions)
#   -> structured plan -> permission/safety validation -> confirmation (if
#   sensitive) -> predefined TOOL REGISTRY execution -> real Telegram result
#   -> JARVIS reply.
#
#   AI NEVER executes arbitrary Python/shell/Telegram methods. It can only
#   select tools from the allowlisted registry below. Unsupported requests
#   are honestly reported — JARVIS never fakes success.
#
#   Render ready:  python main.py  ->  0.0.0.0:$PORT   (health: /health)
#   Clock: Asia/Kathmandu (NPT). Single running instance by design.
# ============================================================================

import asyncio
import hmac
import json
import logging
import os
import re
import struct
import time
import uuid
from collections import deque
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from functools import wraps
from pathlib import Path

from quart import Quart, jsonify, request, send_file

try:
    from telethon import TelegramClient, events, functions
    from telethon.sessions import StringSession
    from telethon.errors import (
        ChatAdminRequiredError, FloodWaitError, PasswordHashInvalidError,
        PhoneCodeExpiredError, PhoneCodeInvalidError, PhoneNumberInvalidError,
        RPCError, SessionPasswordNeededError, UserNotParticipantError,
    )
    TELETHON_OK = True
except Exception:  # telethon missing -> web layer still boots cleanly
    TelegramClient = None
    TELETHON_OK = False

try:
    import httpx
except Exception:  # optional cloud AI providers
    httpx = None

# ---- Asia/Kathmandu (explicit) ------------------------------------------------
try:
    from zoneinfo import ZoneInfo
    KTM = ZoneInfo("Asia/Kathmandu")
except Exception:
    KTM = timezone(timedelta(hours=5, minutes=45), "NPT")

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)-5s [%(name)s] %(message)s")
log = logging.getLogger("jarvis")

BASE = Path(__file__).resolve().parent
DATA = BASE / "data"
DATA.mkdir(exist_ok=True)

SECRET_MARKERS = ("api_hash", "session", "password", "token", "otp", "secret", "api_key", "phone_code_hash")

def scrub(obj):
    if isinstance(obj, dict):
        return {k: ("***" if any(m in str(k).lower() for m in SECRET_MARKERS) else scrub(v)) for k, v in obj.items()}
    if isinstance(obj, list):
        return [scrub(v) for v in obj]
    return obj

LOG_RING = deque(maxlen=150)

def safe_log(level, source, msg):
    LOG_RING.appendleft({"ts": int(time.time()), "level": level, "source": source, "msg": str(msg)[:400]})

# ----------------------------------------------------------------------------
# JSON persistence — atomic writes, corruption recovery
# ----------------------------------------------------------------------------
class JSONStore:
    def __init__(self, path, default):
        self.path = path
        self.default = default
        self.lock = asyncio.Lock()

    def load(self):
        try:
            if self.path.exists():
                return json.loads(self.path.read_text(encoding="utf-8"))
        except Exception as e:
            log.warning("STORAGE %s corrupted (%s) -> safe defaults", self.path.name, type(e).__name__)
            safe_log("WARN", "STORAGE", f"{self.path.name} corrupted — recovered to safe defaults")
        return json.loads(json.dumps(self.default))

    async def save(self, value):
        async with self.lock:
            try:
                tmp = self.path.with_suffix(self.path.suffix + ".tmp")
                tmp.write_text(json.dumps(value, indent=1, ensure_ascii=False), encoding="utf-8")
                tmp.replace(self.path)
            except Exception as e:
                log.error("STORAGE write failed for %s: %s", self.path.name, type(e).__name__)

    def save_bg(self, value):
        try:
            asyncio.get_running_loop().create_task(self.save(value))
        except RuntimeError:
            pass

DEFAULT_STATE = {
    "engine": {"status": "stopped", "queue": [], "deferred": [], "processed": 0,
               "failed": 0, "flood_wait_until": 0, "last_event": "engine idle — /AI cross start"},
    "monitor": {"active": False, "task_id": None, "source": None, "destination": None,
                "keywords": ["toss", "result", "winner", "score", "update", "line"],
                "last_message_id": 0, "processed": 0, "last_event": "monitor idle"},
    "account": None,               # SAFE metadata only — never a session
    "last_command": None,
    "last_error": None,
}
state_store   = JSONStore(DATA / "jarvis_state.json", DEFAULT_STATE)
history_store = JSONStore(DATA / "ai_history.json", [])
jobs_store    = JSONStore(DATA / "scheduled_jobs.json", [])
STATE   = state_store.load()
HISTORY = history_store.load()
STATE.setdefault("monitor", json.loads(json.dumps(DEFAULT_STATE["monitor"])))

# ----------------------------------------------------------------------------
# Auth (fail closed)
# ----------------------------------------------------------------------------
def server_token():
    return os.getenv("JARVIS_ACCESS_TOKEN", "").strip()

def require_token(fn):
    @wraps(fn)
    async def wrapper(*args, **kwargs):
        token = server_token()
        if not token:
            return jsonify({"ok": False, "error": "JARVIS_ACCESS_TOKEN not configured on server"}), 503
        supplied = request.headers.get("Authorization", "").removeprefix("Bearer ").strip() \
            or request.headers.get("X-Jarvis-Token", "")
        if not supplied or not hmac.compare_digest(supplied, token):
            safe_log("WARN", "AUTH", "Rejected protected API call — invalid token (fail closed)")
            return jsonify({"ok": False, "error": "UNAUTHORIZED — fail closed"}), 401
        return await fn(*args, **kwargs)
    return wrapper

def authorized_admin_ids(account):
    raw = os.getenv("AUTHORIZED_ADMINS", "").strip()
    ids = {int(x) for x in re.split(r"[,\s]+", raw) if x.strip().isdigit()}
    if not ids and account:
        ids = {int(account["user_id"])}
    return ids

def caller_origin():
    sid = request.headers.get("X-Session-Id", "").strip() if request else ""
    return f"web:{sid}" if sid else "web"

# ----------------------------------------------------------------------------
# Time — Asia/Kathmandu
# ----------------------------------------------------------------------------
def ktm_now():
    return datetime.now(KTM)

def fmt_kt(ts):
    return datetime.fromtimestamp(ts, KTM).strftime("%d %b %I:%M %p NPT")

def parse_rel_time(text):
    t = text.lower()
    now = time.time()
    m = re.search(r"(\d+)\s*(second|sec|sek)\s*(baad|bad|mein|me)", t)
    if m: return now + int(m[1]), f"{m[1]} second baad"
    m = re.search(r"(\d+)\s*(minute|min|mint)\s*(baad|bad|mein|me)", t)
    if m: return now + int(m[1]) * 60, f"{m[1]} minute baad"
    m = re.search(r"(\d+)\s*(hour|hr|ghante|ghanta)\s*(baad|bad|mein|me)", t)
    if m: return now + int(m[1]) * 3600, f"{m[1]} ghante baad"
    m = re.search(r"(\d{1,2})(?::(\d{2}))?\s*(am|pm)?", t)
    if m and re.search(r"(baje|par|pe|kal|aaj|raat|subah|shaam)", t):
        h, minute, ap = int(m[1]), int(m[2] or 0), m[3]
        if ap == "pm" and h < 12: h += 12
        if ap == "am" and h == 12: h = 0
        if not ap and re.search(r"(raat|shaam)", t) and h < 12: h += 12
        d = ktm_now().replace(hour=h % 24, minute=minute % 60, second=0, microsecond=0)
        label = d.strftime("%I:%M %p") + (" kal" if "kal" in t else "")
        if "kal" in t: d += timedelta(days=1)
        elif d.timestamp() <= now: d += timedelta(days=1)
        return d.timestamp(), label
    return None, None

# ----------------------------------------------------------------------------
# Session CONTEXT — short-lived memory per origin (expires, never permanent)
# ----------------------------------------------------------------------------
CTX_TTL = 600  # 10 minutes
CONTEXT = {}   # origin -> {last_channel, last_user, last_task, at}

def ctx_get(origin):
    c = CONTEXT.get(origin)
    if not c:
        return {}
    if time.time() - c.get("at", 0) > CTX_TTL:
        CONTEXT.pop(origin, None)
        return {}
    return c

def ctx_set(origin, **kw):
    c = ctx_get(origin)
    c.update({k: v for k, v in kw.items() if v})
    c["at"] = time.time()
    CONTEXT[origin] = c

# ----------------------------------------------------------------------------
# TOOL REGISTRY — the ONLY things JARVIS can ever do.
# Every tool: name, description, params, validation, permission, confirmation,
# execution, formatter. AI can select; it can never invent.
# ----------------------------------------------------------------------------
@dataclass
class ToolParam:
    name: str
    kind: str            # "chat" | "user" | "text" | "number" | "list" | "time"
    required: bool = False
    desc: str = ""

@dataclass
class Tool:
    name: str
    desc: str
    category: str
    fn: object
    params: list = field(default_factory=list)
    needs_telegram: bool = True
    confirm: bool = False        # destructive / sensitive -> explicit YES
    sensitive: bool = False      # admin-grade action

class ToolRegistry:
    def __init__(self):
        self.tools = {}

    def register(self, name, desc, category, fn, params=None, needs_telegram=True, confirm=False, sensitive=False):
        self.tools[name] = Tool(name, desc, category, fn, params or [], needs_telegram, confirm, sensitive)

    def summary_for_ai(self):
        out = []
        for t in self.tools.values():
            ps = ", ".join(f"{p.name}{'*' if p.required else ''}" for p in t.params) or "none"
            out.append(f"- {t.name} ({t.category}): {t.desc} | params: {ps}")
        return "\n".join(out)

    async def run(self, name, params, origin):
        t = self.tools.get(name)
        if not t:
            return {"ok": False, "lines": [f"TOOL NOT REGISTERED ▸ {name}"]}
        connected, _ = TG.status()
        if t.needs_telegram and not connected:
            return {"ok": False, "lines": ["TELEGRAM DISCONNECTED ▸ pehle Telegram connect karo (web dashboard se ya env session)"]}
        # validation phase
        for p in t.params:
            if p.required and not str(params.get(p.name, "")).strip():
                hint = {"chat": "channel ka @username batao", "user": "user ka @username batao",
                        "time": "time batao — jaise '10 minute baad' / '7:30 PM par'"} .get(p.kind, f"{p.name} chahiye")
                return {"ok": False, "lines": [f"PARAM MISSING ▸ {t.name} ke liye '{p.name}' zaroori hai — {hint}"]}
        try:
            result = await t.fn(params, origin)
            result.setdefault("ok", True)
            return result
        except FloodWaitError as fw:
            log.warning("FloodWait %ss in %s — waiting exact delay", fw.seconds, name)
            safe_log("WARN", "TOOL", f"FloodWait {fw.seconds}s in {name} — exact delay honoured")
            await asyncio.sleep(fw.seconds)
            return {"ok": False, "lines": [f"FloodWait {fw.seconds}s honour kar liya — dobara try karo"]}
        except ChatAdminRequiredError:
            return {"ok": False, "lines": ["PERMISSION ERROR ▸ is channel me admin rights nahi hain — Telegram ne mana kar diya"]}
        except UserNotParticipantError:
            return {"ok": False, "lines": ["ACCESS ERROR ▸ account is channel/group ka member nahi hai"]}
        except RPCError as e:
            name_e = type(e).__name__
            return {"ok": False, "lines": [f"TELEGRAM ERROR ▸ {name_e}: {str(e)[:140]}"]}
        except Exception as e:
            log.error("Tool %s failed: %s", name, type(e).__name__)
            STATE["last_error"] = f"{name}: {type(e).__name__}"
            safe_log("ERROR", "TOOL", f"{name} failed ({type(e).__name__}) — server alive")
            return {"ok": False, "lines": [f"{name} FAILED ▸ {type(e).__name__} — real error, koi fake success nahi"]}

REG = ToolRegistry()
bar = "────────────────────────────"

async def resolve_chat(ref):
    ref = str(ref).strip()
    return await TG.client.get_entity(int(ref) if ref.lstrip("-").isdigit() else ref)

# ============================================================================
# TASK MANAGER — every long-running operation carries a task ID
# ============================================================================
class TaskManager:
    def __init__(self):
        self.tasks = {}   # id -> {id, kind, label, status, started_at, stop, reset, stats}

    def register(self, kind, label, stop_fn, reset_fn=None, stats_fn=None, fixed_id=None):
        tid = fixed_id or f"{kind}-{uuid.uuid4().hex[:4].upper()}"
        self.tasks[tid] = {"id": tid, "kind": kind, "label": label, "status": "RUNNING",
                           "started_at": time.time(), "stop": stop_fn, "reset": reset_fn, "stats": stats_fn}
        return self.tasks[tid]

    def set_status(self, tid, status):
        if tid in self.tasks:
            self.tasks[tid]["status"] = status

    def remove(self, tid):
        self.tasks.pop(tid, None)

    def running(self):
        return [t for t in self.tasks.values() if t["status"] in ("RUNNING", "PAUSED")]

    async def stop(self, tid):
        t = self.tasks.get(tid)
        if not t:
            return None
        if t["stop"]:
            await t["stop"]()
        return t

TASKS = TaskManager()

# ============================================================================
# CROSS-PROMOTION ENGINE — authorized scope, pause/resume, FloodWait-safe
# ============================================================================
class CrossEngine:
    MAX_ATTEMPTS = 3
    CYCLE_DELAY = 8

    def __init__(self):
        self.eng = STATE["engine"]
        if self.eng.get("flood_wait_until", 0) < time.time():
            self.eng["flood_wait_until"] = 0
        self.task = None
        self.tid = None

    def status(self):
        return self.eng["status"]

    def source_configured(self):
        cid = os.getenv("SOURCE_CHAT_ID", "").strip()
        ids = [x for x in re.split(r"[,\s]+", os.getenv("SOURCE_MESSAGE_IDS", "")) if x.strip().isdigit()]
        return (cid if cid.lstrip("-").isdigit() else None), [int(x) for x in ids]

    def _task_sync(self):
        st = self.eng["status"]
        if st == "running" and not self.tid:
            t = TASKS.register("CROSS", "Cross-Promotion Engine",
                               stop_fn=self._task_stop, reset_fn=self.reset,
                               stats_fn=lambda: f"{self.eng['processed']} done", fixed_id="CROSS-0001")
            self.tid = t["id"]
        if self.tid:
            TASKS.set_status(self.tid, {"running": "RUNNING", "paused": "PAUSED"}.get(st, "STOPPED"))

    async def _task_stop(self):
        self.stop()

    async def start(self, params=None, origin="system"):
        if self.eng["status"] == "paused":
            return await self.resume(params, origin)
        if self.eng["status"] == "running":
            return {"lines": [f"ENGINE ALREADY RUNNING ▸ queue {len(self.eng['queue'])} ▸ task {self.tid or '-'}"]}
        connected, _ = TG.status()
        if not connected:
            return {"ok": False, "lines": ["SOURCE NOT AVAILABLE ▸ Telegram not connected"]}
        cid, ids = self.source_configured()
        if not cid or not ids:
            self.eng["last_event"] = "SOURCE NOT AVAILABLE — set SOURCE_CHAT_ID / SOURCE_MESSAGE_IDS"
            state_store.save_bg(STATE)
            return {"ok": False, "lines": ["SOURCE NOT AVAILABLE ▸ SOURCE_CHAT_ID aur SOURCE_MESSAGE_IDS env vars configure karo — engine start nahi hui"]}
        if not self.eng["queue"]:
            msg = await self.rebuild_queue()
            if msg:
                return {"ok": False, "lines": ["SOURCE NOT AVAILABLE ▸ " + msg]}
        self.eng["status"] = "running"
        self.eng["last_event"] = "engine started — sources validated"
        self.ensure_task()
        self._task_sync()
        state_store.save_bg(STATE)
        safe_log("CMD", "ENGINE", f"Started ▸ {len(self.eng['queue'])} targets queued")
        return {"lines": [f"CROSS ENGINE STARTED ▸ {len(self.eng['queue'])} authorized targets queued",
                          f"Task ID: {self.tid}",
                          "Status: RUNNING ✅ paused flood-safe".replace(" ✅", "")]}

    def stop(self):
        self.eng["status"] = "stopped"
        self.eng["last_event"] = "stopped by operator"
        self._task_sync()
        state_store.save_bg(STATE)
        safe_log("CMD", "ENGINE", "Stopped by operator")
        return {"lines": [f"CROSS ENGINE STOPPED ▸ {self.eng['processed']} processed ▸ {len(self.eng['deferred'])} deferred",
                          f"Task {self.tid or '-'}: STOPPED"]}

    async def pause(self, params=None, origin="system"):
        if self.eng["status"] != "running":
            return {"lines": ["Engine running nahi hai — pause ka koi matlab nahi"]}
        self.eng["status"] = "paused"
        self.eng["last_event"] = "paused by operator (manual hold)"
        self._task_sync()
        state_store.save_bg(STATE)
        safe_log("CMD", "ENGINE", "Paused (manual)")
        return {"lines": [f"CROSS ENGINE PAUSED ▸ task {self.tid}: PAUSED", "/AI cross resume karne par wapas chalegi"]}

    async def resume(self, params=None, origin="system"):
        if self.eng["status"] != "paused":
            return {"lines": ["Engine paused nahi hai — resume ka koi matlab nahi"]}
        self.eng["status"] = "running"
        self.eng["last_event"] = "resumed by operator"
        self.ensure_task()
        self._task_sync()
        state_store.save_bg(STATE)
        safe_log("CMD", "ENGINE", "Resumed")
        return {"lines": [f"CROSS ENGINE RESUMED ▸ task {self.tid}: RUNNING"]}

    async def reset(self, params=None, origin="system"):
        self.eng.update({"status": "stopped", "processed": 0, "failed": 0,
                         "deferred": [], "flood_wait_until": 0})
        self.tid = None
        msg = None
        connected, _ = TG.status()
        if connected:
            msg = await self.rebuild_queue()
        self._task_sync()
        state_store.save_bg(STATE)
        safe_log("CMD", "ENGINE", "Reset ▸ queue rebuilt ▸ counters cleared")
        if msg:
            return {"lines": ["ENGINE RESET ▸ counters cleared, par queue empty: " + msg]}
        return {"lines": [f"ENGINE RESET ▸ queue rebuilt ({len(self.eng['queue'])}) ▸ counters cleared"]}

    def config_lines(self):
        cid, ids = self.source_configured()
        return ["CROSS ENGINE CONFIG", bar,
                f"Status       ▸ {self.eng['status'].upper()}{f' ▸ task {self.tid}' if self.tid else ''}",
                f"Cycle delay  ▸ {self.CYCLE_DELAY}s per send (conservative pacing — limit-safe)",
                f"Max attempts ▸ {self.MAX_ATTEMPTS} per target (phir deferred — infinite retry nahi)",
                f"Source       ▸ {f'chat {cid} • messages {ids[:4]}' if cid and ids else 'NOT CONFIGURED — SOURCE_CHAT_ID / SOURCE_MESSAGE_IDS env vars set karo'}",
                f"Queue        ▸ {len(self.eng['queue'])} pending ▸ {len(self.eng['deferred'])} deferred",
                "Conditional pause ▸ manual via '/AI cross pause' / '/AI cross resume'"]

    async def rebuild_queue(self):
        folders = await scan_folders()
        queue = []
        for f in folders:
            for ch in f["channels"]:
                queue.append({"channel": ch["name"], "username": ch.get("username"),
                              "chat_id": ch["id"], "attempts": 0})
        self.eng["queue"] = queue[:60]
        state_store.save_bg(STATE)
        if not queue:
            return "dialog folders me koi channel visible nahi"
        return None

    def ensure_task(self):
        if not self.task or self.task.done():
            self.task = asyncio.get_running_loop().create_task(self._loop())

    async def _loop(self):
        while True:
            await asyncio.sleep(self.CYCLE_DELAY)
            if self.eng["status"] != "running":   # paused/stopped -> idle wait
                continue
            now = time.time()
            hold = self.eng.get("flood_wait_until") or 0
            if hold and now < hold:
                continue
            connected, _ = TG.status()
            if not connected:
                self.eng["last_event"] = "Telegram disconnected — engine paused-safe"
                continue
            cid, ids = self.source_configured()
            if not cid or not ids:
                self.eng["status"] = "stopped"
                self.eng["last_event"] = "SOURCE NOT AVAILABLE — configure source ids"
                self._task_sync()
                state_store.save_bg(STATE)
                continue
            if not self.eng["queue"]:
                self.eng["last_event"] = "queue drained — cycle complete"
                continue
            item = self.eng["queue"].pop(0)
            try:
                probe = await TG.client.get_messages(int(cid), ids=ids[:1])
                if not probe or probe[0] is None:
                    self.eng["status"] = "stopped"
                    self.eng["last_event"] = "SOURCE NOT AVAILABLE — source message deleted/missing"
                    self._task_sync()
                    state_store.save_bg(STATE)
                    safe_log("ERROR", "ENGINE", "Source message missing — engine stopped safely")
                    continue
                await TG.client.forward_messages(int(item["chat_id"]), ids[0], from_peer=int(cid))
                self.eng["processed"] += 1
                self.eng["last_event"] = f"posted ▸ {item['channel']}"
            except FloodWaitError as fw:
                self.eng["flood_wait_until"] = time.time() + fw.seconds
                self.eng["queue"].insert(0, item)
                self.eng["last_event"] = f"FloodWait {fw.seconds}s — holding"
                log.warning("FloodWaitError: waiting exact %ss (Telegram-mandated)", fw.seconds)
                safe_log("WARN", "ENGINE", f"FloodWait {fw.seconds}s — exact delay honoured")
            except Exception as e:
                item["attempts"] += 1
                if item["attempts"] >= self.MAX_ATTEMPTS:
                    self.eng["deferred"].append(item)
                    self.eng["failed"] += 1
                    safe_log("WARN", "ENGINE", f"{item['channel']} -> deferred after 3 attempts ({type(e).__name__})")
                else:
                    self.eng["queue"].append(item)
            state_store.save_bg(STATE)

ENGINE = CrossEngine()

# ============================================================================
# SOURCE MONITOR — real-time, event-based (fast mode), dedupe, persistent
# ============================================================================
DEFAULT_KEYWORDS = ["toss", "result", "winner", "score", "update", "line"]

class SourceMonitor:
    def __init__(self):
        self.m = STATE["monitor"]
        self.queue = asyncio.Queue()
        self.worker = None
        self.attached_client = None

    def configured(self):
        src = self.m.get("source") or os.getenv("MONITOR_SOURCE", "").strip() or None
        dst = self.m.get("destination") or os.getenv("MONITOR_DESTINATION", "").strip() or None
        return src, dst

    async def start(self, params, origin):
        connected, _ = TG.status()
        if not connected:
            return {"ok": False, "lines": ["TELEGRAM DISCONNECTED ▸ pehle connect karo"]}
        src = params.get("source") or self.m.get("source") or os.getenv("MONITOR_SOURCE", "").strip()
        dst = params.get("destination") or self.m.get("destination") or os.getenv("MONITOR_DESTINATION", "").strip()
        if not src or not dst:
            return {"ok": False, "lines": [
                "SOURCE NOT CONFIGURED ▸ monitoring ke liye source aur destination chahiye:",
                "  env: MONITOR_SOURCE=@source_channel  MONITOR_DESTINATION=@output_channel",
                "  ya command me: '/AI @source ko monitor karo, @output par bhejo'"]}
        try:
            src_ent = await resolve_chat(src)
            dst_ent = await resolve_chat(dst)
        except Exception as e:
            return {"ok": False, "lines": [f"ENTITY ERROR ▸ source/destination resolve nahi hua ({type(e).__name__}) — @username check karo"]}
        kws = params.get("keywords")
        if kws:
            self.m["keywords"] = kws
        self.m.update({"active": True, "source": src, "destination": dst})
        if not self.m.get("last_message_id"):  # baseline: don't repost old messages
            latest = await TG.client.get_messages(src_ent, limit=1)
            self.m["last_message_id"] = latest[0].id if latest and latest[0] else 0
        await self.attach(TG.client)
        self.ensure_worker()
        if not self.m.get("task_id") or self.m["task_id"] not in TASKS.tasks:
            self.m["task_id"] = TASKS.register("MON", f"Source monitor {src} -> {dst}",
                                               stop_fn=self._task_stop, reset_fn=self.reset)["id"]
        state_store.save_bg(STATE)
        safe_log("CMD", "MONITOR", f"Started ▸ {src} -> {dst} ▸ event-based listener")
        return {"lines": [
            f"SOURCE MONITORING STARTED (event-based — fastest mode)",
            f"Task ID: {self.m['task_id']}",
            f"Source      ▸ {src}",
            f"Destination ▸ {dst}",
            f"Keywords    ▸ {', '.join(self.m['keywords'])}",
            f"Baseline    ▸ last message id {self.m['last_message_id']} (purane messages repost nahi honge)",
            "Har naya matching message ka exact source text formatted hokar destination par jayega."]}

    async def _task_stop(self):
        await self.stop({}, "task")

    async def stop(self, params, origin):
        if not self.m.get("active"):
            return {"lines": ["Monitor already stopped"]}
        self.m["active"] = False
        tid = self.m.get("task_id")
        if tid:
            TASKS.set_status(tid, "STOPPED")
        self.m["last_event"] = "stopped by operator"
        state_store.save_bg(STATE)
        safe_log("CMD", "MONITOR", "Stopped cleanly")
        return {"lines": [f"MONITOR STOPPED ▸ task {tid or '-'}: STOPPED", "State persistent hai — 'monitor start' se wapas resume hoga"]}

    async def reset(self, params=None, origin="task"):
        self.m["last_message_id"] = 0
        self.m["processed"] = 0
        if self.m.get("active") and TG.client:
            src, _ = self.configured()
            if src:
                try:
                    latest = await TG.client.get_messages(await resolve_chat(src), limit=1)
                    self.m["last_message_id"] = latest[0].id if latest and latest[0] else 0
                except Exception:
                    pass
        state_store.save_bg(STATE)
        safe_log("CMD", "MONITOR", f"Reset ▸ baseline {self.m['last_message_id']}")
        return {"lines": [f"MONITOR RESET ▸ baseline message id {self.m['last_message_id']} ▸ counters zero"]}

    def status_lines(self):
        src, dst = self.configured()
        tid = self.m.get("task_id")
        state = "RUNNING (event-based)" if self.m.get("active") else "STOPPED"
        if tid:
            state += f" ▸ task {tid}"
        return ["SOURCE MONITOR", bar,
                f"Status      ▸ {state}",
                f"Source      ▸ {src or 'NOT CONFIGURED'}",
                f"Destination ▸ {dst or 'NOT CONFIGURED'}",
                f"Keywords    ▸ {', '.join(self.m['keywords'])}",
                f"Processed   ▸ {self.m.get('processed', 0)} updates ▸ last id {self.m.get('last_message_id', 0)}",
                f"Last event  ▸ {self.m.get('last_event', '—')}"]

    def ensure_worker(self):
        if not self.worker or self.worker.done():
            self.worker = asyncio.get_running_loop().create_task(self._work())

    async def attach(self, client):
        """Register NewMessage listener on the (single) client; re-attach after reconnect."""
        if not TELETHON_OK or self.attached_client is client:
            return
        self.attached_client = client
        mon = self

        @client.on(events.NewMessage())
        async def _on_source_msg(event):
            try:
                if not mon.m.get("active"):
                    return
                src, _dst = mon.configured()
                if not src:
                    return
                chat_id = event.chat_id
                if str(chat_id) != str(src).lstrip("@") and f"@{chat_id}" != str(src):
                    ent = event.chat
                    uname = getattr(ent, "username", None)
                    eid = getattr(ent, "id", None)
                    if str(eid) != str(src).lstrip("-100").lstrip("-") and uname != str(src).lstrip("@"):
                        return
                msg = event.message
                if not msg or not getattr(msg, "text", None):
                    return
                if msg.id <= (mon.m.get("last_message_id") or 0):
                    return  # duplicate guard
                await mon.queue.put(msg)
                mon.ensure_worker()
            except Exception as e:
                log.error("monitor event error: %s", type(e).__name__)

    async def _work(self):
        while not self.queue.empty():
            msg = await self.queue.get()
            try:
                await self._process(msg)
            except FloodWaitError as fw:
                log.warning("FloodWait %ss in monitor — waiting exact delay", fw.seconds)
                safe_log("WARN", "MONITOR", f"FloodWait {fw.seconds}s — exact delay honoured")
                await asyncio.sleep(fw.seconds)
                await self._process(msg)  # retry once after exact wait
            except Exception as e:
                log.error("monitor process error: %s", type(e).__name__)
                safe_log("ERROR", "MONITOR", f"process error ({type(e).__name__}) — continuing")

    async def _process(self, msg):
        self.m["last_message_id"] = max(self.m.get("last_message_id") or 0, msg.id)
        src, dst = self.configured()
        parsed = parse_source_text(msg.text or "", self.m["keywords"])
        body = format_update_text(parsed["body"])
        await TG.client.send_message(await resolve_chat(dst), body)
        self.m["processed"] = self.m.get("processed", 0) + 1
        self.m["last_event"] = f"update sent ▸ id {msg.id} {'(keyword match)' if parsed['matched'] else '(full text)'}"
        state_store.save_bg(STATE)
        safe_log("OK", "MONITOR", f"Update id {msg.id} -> {dst} {'(keywords)' if parsed['matched'] else '(full)'}")

MONITOR = SourceMonitor()

# ----------------------------------------------------------------------------
# Source message helpers — no fabrication: only real Telegram-provided text
# ----------------------------------------------------------------------------
def parse_source_text(text, keywords):
    lines = [ln.strip() for ln in (text or "").split("\n") if ln.strip()]
    kws = [k.lower() for k in (keywords or DEFAULT_KEYWORDS)]
    matched = [ln for ln in lines if any(k in ln.lower() for k in kws)]
    return {"matched": bool(matched), "body": "\n".join(matched) if matched else (text or "").strip(),
            "total_lines": len(lines), "matched_lines": len(matched)}

def format_update_text(body):
    tpl = os.getenv("MONITOR_TEMPLATE", "").strip()
    ts = ktm_now().strftime("%d %b %I:%M %p NPT")
    body = (body or "")[:1800]
    if tpl:
        return tpl.replace("{body}", body).replace("{time}", ts)[:3800]
    return f"UPDATE ▸\n{body}\n— via JARVIS · {ts}"

# ============================================================================
# NLU — intent classification + parameter extraction + condition handling.
# NOT phrase tables: lexicon scoring over clause segments, multi-step aware.
# ============================================================================
@dataclass
class Step:
    tool: str
    params: dict = field(default_factory=dict)
    note: str = ""

@dataclass
class Plan:
    steps: list = field(default_factory=list)
    unsupported: list = field(default_factory=list)
    notes: list = field(default_factory=list)
    provider: str = "LOCAL"
    needs: list = field(default_factory=list)   # missing-param prompts

V_START  = ("start", "shuru", "chalu", "chalao", "chala", "on", "lagao", "begin", "shuruaat", "kr do", "kar do")
V_STOP   = ("stop", "band", "bandh", "rok", "ruko", "off", "band kar", "band kar do", "rok do")
V_PAUSE  = ("pause", "hold", "wait kar", "ruk jao", "thahro", "temporary ruk")
V_RESUME = ("resume", "continue", "wapas chalu", "phir chalu", "phir se chalu", "unpause")
V_RESET  = ("reset", "clear", "saaf", "zero", "fresh")
V_STATUS = ("status", "stithi", "batao", "kaisa", "kya haal", "report", "dikhao", "dikha")
V_CHECK  = ("check", "dekho", "inspect", "jaanch", "batao", "details", "karo", "dikhao", "dikha")
V_CANCEL = ("cancel", "hatao", "abort")
V_CONFIG = ("config", "setting", "setup dikhao", "configuration")
V_MON    = ("monitor", "watch", "nazar", "track", "follow", "toss line", "result line", "source line",
            "fastest update", "fast update", "jaldi update", "instant update", "live update")
V_SEND   = ("bhejo", "bhej", "send", "forward", "copy paste", "copy karke", "daal do", "post")
V_FETCH  = ("latest", "last message", "naya message", "recent message", "fetch", "lao", "nikalo")

CROSS_T  = ("cross", "engine", "promotion", "promo")
SCHED_T  = ("scheduler", "schedule", "job")
MON_T    = ("monitor", "monitoring", "source watch", "watcher")
TASK_T   = ("task", "jo chal raha", "jo task", "running task", "ye wala", "usko")

def has(t, words):
    return any(w in t for w in words)

def target_of(t):
    if has(t, CROSS_T): return "cross"
    if has(t, MON_T): return "monitor"
    if has(t, SCHED_T): return "scheduler"
    if has(t, TASK_T): return "task"
    return None

def extract(t, origin):
    p = {}
    u = re.search(r"@([a-zA-Z0-9_]{3,32})", t)
    if u:
        p["ref"] = u.group(1)
    m = re.search(r"(-?\d{6,15})", t)
    if m:
        p.setdefault("id", m.group(1))
    km = re.search(r"(?:keywords?|shabd)\s*[:=]?\s*([a-zA-Z, ]+)$", t)
    if km:
        p["keywords"] = [k.strip() for k in km.group(1).split(",") if k.strip()][:8]
    # two-chat pattern:  "@a ko monitor karo @b par bhejo"
    um = re.findall(r"@([a-zA-Z0-9_]{3,32})", t)
    if len(um) >= 2 and has(t, V_MON):
        p["source"], p["destination"] = "@" + um[0], "@" + um[1]
    elif len(um) == 1 and has(t, V_MON):
        if has(t, V_SEND):
            p["destination"] = "@" + um[0]
        else:
            p["source"] = "@" + um[0]
    ts, label = parse_rel_time(t)
    if ts:
        p["run_at"], p["label"] = ts, label
    return p

def is_condition_clause(t):
    return has(t, ("toss", "lekin", "but", "mat karna", "mat kar", "wait karna", "dhyaan")) and not has(t, ("start", "stop", "band", "chalu", "monitor", "status"))

def classify(raw, origin):
    """Structured execution plan from mixed Hindi/Hinglish/English text."""
    t = re.sub(r"^\s*\/?(ai|jarvis|devil)\b[\s,:.-]*", "", raw.strip().lower())
    t = re.sub(r"\s+", " ", t)
    plan = Plan()
    if not t:
        plan.steps.append(Step("jarvis_help")); return plan

    ctx = ctx_get(origin)

    # ---------- legacy /AI UPPERCASE fast-path (console compatibility) ----------
    legacy = {
        "STATUS": ("jarvis_status", {}), "ACCOUNT": ("telegram_account", {}),
        "FOLDERS CHANNELS": ("telegram_folders", {"include_channels": True}),
        "FOLDERS": ("telegram_folders", {}), "CHANNEL LIST": ("telegram_folders", {"include_channels": True}),
        "DEAD CHANNELS": ("telegram_dead_channel_scan", {}), "CHANNEL INFO": ("telegram_channel_info", {}),
        "RECENT ACTIVITY": ("telegram_recent_messages", {}), "SAVED MESSAGES": ("telegram_saved_messages", {}),
        "DIAGNOSTICS": ("jarvis_diagnostics", {}), "SAVE STATE": ("jarvis_save_state", {}),
        "SCHEDULE LIST": ("scheduler_list", {}), "HELP": ("jarvis_help", {}),
    }
    up = t.upper()
    if up in legacy:
        tool, prm = legacy[up]
        if tool == "telegram_channel_info" and ctx.get("last_channel"):
            prm = dict(prm); prm["channel"] = ctx["last_channel"]
        plan.steps.append(Step(tool, prm)); return plan
    if up.startswith("SEARCH "):
        plan.steps.append(Step("telegram_message_search", {"query": t[7:].strip()})); return plan
    m_can = re.match(r"^cancel job\s*([a-z0-9]+)?$", t)
    if m_can:
        plan.steps.append(Step("scheduler_cancel", {"id": m_can.group(1) or ""})); return plan

    # ---------- split into clauses (multi-step) ----------
    clauses = [c.strip() for c in re.split(
        r"[,;.!?]|(?:\baur\b)|(?:\bbut\b)|(?:\blekin\b)|(?:\band then\b)|(?:\bthen\b)|(?:\bphir\b)|(?:\bfir\b)", t) if c.strip()]
    if not clauses:
        clauses = [t]

    pending_conditions = []
    for c in clauses:
        # pure condition clause -> attach to previous step (or note globally)
        if is_condition_clause(c) and plan.steps:
            if "toss" in c:
                plan.unsupported.append(
                    "Toss-time auto-pause abhi supported nahi hai — toss ka koi official live source configured nahi. "
                    "Manual control supported hai: '/AI cross pause' aur '/AI cross resume'.")
            elif has(c, ("wait karna", "mat karna", "mat kar")):
                plan.unsupported.append(
                    "Conditional wait/trigger abhi supported nahi hai — manual pause/stop commands available hain.")
            continue

        # "@output par bhejo" right after a monitor step -> attach destination
        if plan.steps and plan.steps[-1].tool == "monitor_source" and has(c, V_SEND) and re.search(r"@", c):
            mm = re.search(r"@([a-zA-Z0-9_]{3,32})", c)
            plan.steps[-1].params["destination"] = "@" + mm.group(1)
            continue

        tgt = target_of(c)
        p = extract(c, origin)

        # time-boxed engine control -> scheduler
        if p.get("run_at") and has(c, V_START) and not has(c, V_STOP):
            plan.steps.append(Step("scheduler_start", {"run_at": p["run_at"], "label": p["label"]}))
            continue
        if p.get("run_at") and has(c, V_STOP):
            plan.steps.append(Step("scheduler_stop", {"run_at": p["run_at"], "label": p["label"]}))
            continue

        # ----- monitoring / update workflow -----
        if has(c, V_MON) and (has(c, V_START) or has(c, ("karna", "karo", "kr", "shuru", "chalu", "lgao", "lagao"))):
            plan.steps.append(Step("monitor_source", {k: v for k, v in p.items() if k in ("source", "destination", "keywords")}))
            if has(c, ("fastest", "jaldi", "instant", "fast")):
                plan.notes.append("Fast mode: event-based Telegram listener use hoga (polling nahi) — ye supported hai.")
            continue
        if has(c, V_MON) and has(c, V_STOP):
            plan.steps.append(Step("task_stop", {"kind": "MON"}))
            continue
        if ("toss line" in c or "result line" in c or "source line" in c or "fastest update" in c or "fast update" in c) and not plan.steps:
            if has(c, ("copy", "bhejo", "bhej", "send")):
                plan.steps.append(Step("copy_source_text", p.get("ref") and {"source": "@" + p["ref"]} or {}))
            else:
                plan.steps.append(Step("monitor_source", {k: v for k, v in p.items() if k in ("source", "destination", "keywords")}))
                if has(c, ("fastest", "jaldi", "instant", "fast")):
                    plan.notes.append("Fast mode: event-based Telegram listener (polling nahi) — supported.")
            continue
        if has(c, ("latest message", "last message", "naya message")) or (has(c, V_FETCH) and tgt in ("monitor", None) and has(c, ("message", "update", "line", "source"))):
            if has(c, V_SEND):
                plan.steps.append(Step("copy_source_text", p.get("ref") and {"source": "@" + p["ref"]} or {}))
            else:
                plan.steps.append(Step("fetch_latest_source_message", p.get("ref") and {"source": "@" + p["ref"]} or {}))
            continue
        if has(c, ("ka update", "update bhejo", "format karke", "template")) and has(c, V_FETCH + V_SEND):
            plan.steps.append(Step("format_update", {}))
            continue

        # ----- cross engine -----
        if tgt == "cross" or (tgt is None and has(c, CROSS_T)):
            if has(c, V_PAUSE):
                plan.steps.append(Step("cross_pause", {})); continue
            if has(c, V_RESUME):
                plan.steps.append(Step("cross_resume", {})); continue
            if has(c, V_RESET):
                plan.steps.append(Step("cross_reset", {})); continue
            if has(c, V_CONFIG):
                plan.steps.append(Step("cross_config", {})); continue
            if has(c, V_STOP):
                plan.steps.append(Step("cross_stop", {})); continue
            if has(c, V_START):
                plan.steps.append(Step("cross_start", {})); continue
            if has(c, V_STATUS + ("ka ",)):
                plan.steps.append(Step("cross_status", {})); continue

        # ----- scheduler / tasks -----
        if tgt == "scheduler" and has(c, V_STATUS + V_CHECK):
            plan.steps.append(Step("scheduler_status", {})); continue
        if has(c, V_CANCEL) and ("job" in c or p.get("id")) and tgt != "cross":
            plan.steps.append(Step("scheduler_cancel", {"id": p.get("id", "")})); continue
        if tgt == "task" and has(c, V_STOP + V_CANCEL):
            plan.steps.append(Step("task_stop", {"id": p.get("id", "")})); continue
        if tgt == "task" and (has(c, V_RESET)):
            plan.steps.append(Step("task_reset", {"id": p.get("id", "")})); continue
        if tgt == "task" and has(c, V_STATUS):
            plan.steps.append(Step("task_status", {})); continue
        if has(c, ("task status", "tasks dikhao", "kya chal raha", "kya kya chal raha")):
            plan.steps.append(Step("task_status", {})); continue

        # ----- channels / dialogs -----
        if "folder" in c:
            plan.steps.append(Step("telegram_folders", {"include_channels": has(c, ("channel", "channels", "list", "andar", "jitne", "saare", "dikhao"))})); continue
        if has(c, ("dialog", "chats list", "conversations")):
            plan.steps.append(Step("telegram_dialogs", {})); continue
        if "channels" in c and has(c, ("dikhao", "dikha", "list", "batao", "saare", "jitne")):
            plan.steps.append(Step("telegram_folders", {"include_channels": True})); continue
        if ("dead" in c or "inactive" in c) and "channel" in c:
            plan.steps.append(Step("telegram_dead_channel_scan", {})); continue
        if "age" in c or "old" in c or "purana" in c or "kab bana" in c or "kitna time" in c:
            pr = p.get("ref") or ctx.get("last_channel")
            step = Step("telegram_channel_age_estimate", {"channel": pr or ""})
            if not pr:
                plan.needs.append("channel")
            plan.steps.append(step); continue
        if has(c, ("activ", "activity")) or "active hai" in c:
            pr = p.get("ref") or ctx.get("last_channel")
            step = Step("telegram_channel_activity", {"channel": pr or ""})
            if not pr:
                plan.needs.append("channel")
            plan.steps.append(step); continue
        if "channel" in c and has(c, V_CHECK + ("info",)):
            pr = p.get("ref") or ctx.get("last_channel")
            step = Step("telegram_channel_info", {"channel": pr or ""})
            if not pr:
                plan.needs.append("channel")
            plan.steps.append(step); continue
        if has(c, ("recent message", "messages padho", "messages dikhao", "messages check")):
            plan.steps.append(Step("telegram_recent_messages", {"channel": p.get("ref") or ctx.get("last_channel") or ""})); continue
        if has(c, ("search", "dhundo", "dhundho", "khojo")):
            q = re.sub(r"(search|dhundo|dhundho|khojo|karo|message|messages)", "", c).strip() or "promo"
            plan.steps.append(Step("telegram_message_search", {"query": q[:60]})); continue
        if "saved message" in c:
            plan.steps.append(Step("telegram_saved_messages", {})); continue

        # ----- users / admin -----
        if "admin" in c and has(c, ("permissions", "adikar", "rights", "kar sakta", "check")):
            plan.steps.append(Step("admin_check_permissions", {"channel": p.get("ref") or ctx.get("last_channel") or ""})); continue
        if "admin" in c and has(c, ("de do", "bana", "dena", "banana", "promote", "do"))and "de-admin" not in c:
            um = re.findall(r"@([a-zA-Z0-9_]{3,32})", c)
            pr = {"user": um[-1] if um else "", "channel": ctx.get("last_channel", "")}
            if um and not pr["channel"]:
                pr["channel"] = um[0] if len(um) > 1 else ""
            plan.steps.append(Step("admin_promote", pr))
            if not pr["user"]:
                plan.needs.append("user")
            continue
        if "admin" in c and has(c, ("hatao", "remove", "demote", "nikalo")):
            um = re.findall(r"@([a-zA-Z0-9_]{3,32})", c)
            plan.steps.append(Step("admin_demote", {"user": um[-1] if um else "", "channel": ctx.get("last_channel", "")})); continue
        if ("user" in c) and has(c, V_CHECK + ("info", "whois", "kaun")):
            plan.steps.append(Step("telegram_user_info", {"user": p.get("ref") or ctx.get("last_user") or ""})); continue
        if has(c, ("permissions", "adhikar", "rights")) and "channel" in c:
            plan.steps.append(Step("telegram_permissions", {"channel": p.get("ref") or ctx.get("last_channel") or ""})); continue

        # ----- jarvis system -----
        if has(c, ("diagnostic",)):
            plan.steps.append(Step("jarvis_diagnostics", {})); continue
        if has(c, ("save state", "state save")):
            plan.steps.append(Step("jarvis_save_state", {})); continue
        if has(c, ("help", "madad", "commands", "kya kya kar", "kya kar sakte")):
            plan.steps.append(Step("jarvis_help", {})); continue
        if has(c, ("status", "stithi")) and tgt is None and not plan.steps:
            plan.steps.append(Step("jarvis_status", {})); continue
        if "account" in c or "mera telegram" in c:
            plan.steps.append(Step("telegram_account", {})); continue

        # monitor status alias
        if tgt == "monitor" and has(c, V_STATUS):
            plan.steps.append(Step("fetch_latest_source_message", {})) if False else plan.steps.append(Step("task_status", {}))
            continue

        pending_conditions.append(c)

    # leftover unmatched clauses -> note them; AI escalation happens upstream if zero steps
    if pending_conditions and plan.steps:
        for c in pending_conditions:
            plan.notes.append(f"Is part ko map nahi kar paya: '{c[:60]}' — supported actions ke liye /AI HELP")

    # dedupe: same tool from split clauses -> merge params (include_channels etc.)
    merged = []
    for s in plan.steps:
        prev = next((x for x in merged if x.tool == s.tool), None)
        if prev:
            prev.params.update({k: v for k, v in s.params.items() if v not in ("", None, False)})
        else:
            merged.append(s)
    plan.steps = merged

    if not plan.steps:
        return plan  # caller may escalate to AI providers
    return plan

# ----------------------------------------------------------------------------
# AI provider chain — NLU escalation only (validated plan output, no execution)
# ----------------------------------------------------------------------------
class AIManager:
    PROVIDERS = [
        ("GROQ",        "GROQ_API_KEY",        "GROQ_MODEL",        "llama-3.3-70b-versatile"),
        ("GEMINI",      "GEMINI_API_KEY",      "GEMINI_MODEL",      "gemini-2.0-flash"),
        ("OPENROUTER",  "OPENROUTER_API_KEY",  "OPENROUTER_MODEL",  "openrouter/auto"),
        ("ANTHROPIC",   "ANTHROPIC_API_KEY",   "ANTHROPIC_MODEL",   "claude-sonnet-4-20250514"),
        ("HUGGINGFACE", "HF_TOKEN",            "HF_MODEL",          "mistralai/Mistral-7B-Instruct-v0.3"),
        ("OPENAI",      "OPENAI_API_KEY",      "OPENAI_MODEL",      "gpt-4o-mini"),
    ]

    def __init__(self):
        self.total = 0
        self.last_provider = "LOCAL"

    def configured(self):
        return [n for n, k, *_ in self.PROVIDERS if os.getenv(k)] if httpx else []

    def prompt(self, text):
        return (
            "You are the NLU layer of JARVIS, a Telegram control assistant. Convert the user "
            "instruction (English/Hindi/Hinglish, possibly multi-step) into ONE raw JSON object:\n"
            '{"steps":[{"tool":"<tool name>","params":{...}}],'
            '"unsupported":["<requested behavior with no tool>"],'
            '"reply":"<one short line for the user>"}\n'
            "You may ONLY use tools from this registry (never invent tools or params):\n"
            + REG.summary_for_ai() +
            "\nRules: raw JSON only. If nothing maps safely, use \"steps\":[] and explain in reply. "
            "Never emit code, shell commands, or API calls.\nUSER: " + text)

    async def _call(self, name, key, model, text):
        async with httpx.AsyncClient(timeout=10.0) as c:
            msg = self.prompt(text)
            if name in ("GROQ", "OPENAI", "OPENROUTER"):
                url = {"GROQ": "https://api.groq.com/openai/v1/chat/completions",
                       "OPENAI": "https://api.openai.com/v1/chat/completions",
                       "OPENROUTER": "https://openrouter.ai/api/v1/chat/completions"}[name]
                r = await c.post(url, headers={"Authorization": f"Bearer {key}"},
                                 json={"model": model, "messages": [{"role": "user", "content": msg}], "temperature": 0.1})
                r.raise_for_status()
                return r.json()["choices"][0]["message"]["content"]
            if name == "GEMINI":
                url = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?key={key}"
                r = await c.post(url, json={"contents": [{"parts": [{"text": msg}]}]})
                r.raise_for_status()
                return r.json()["candidates"][0]["content"]["parts"][0]["text"]
            if name == "ANTHROPIC":
                r = await c.post("https://api.anthropic.com/v1/messages",
                                 headers={"x-api-key": key, "anthropic-version": "2023-06-01"},
                                 json={"model": model, "max_tokens": 600, "messages": [{"role": "user", "content": msg}]})
                r.raise_for_status()
                return r.json()["content"][0]["text"]
            r = await c.post(f"https://api-inference.huggingface.co/models/{model}",
                             headers={"Authorization": f"Bearer {key}"}, json={"inputs": msg})
            r.raise_for_status()
            out = r.json()
            return out[0]["generated_text"] if isinstance(out, list) else str(out)

    async def plan(self, text):
        """Return validated Plan or None. Never raises."""
        for name, key_env, model_env, default_model in self.PROVIDERS:
            key = os.getenv(key_env)
            if not key or not httpx:
                continue
            try:
                blob = await self._call(name, key, os.getenv(model_env, default_model), text)
                m = re.search(r"\{.*\}", blob, re.S)
                if not m:
                    raise ValueError("no JSON")
                obj = json.loads(m.group(0))
                plan = Plan(provider=name)
                for s in obj.get("steps") or []:
                    tool = str(s.get("tool", "")).strip()
                    prm = s.get("params") if isinstance(s.get("params"), dict) else {}
                    if tool not in REG.tools:
                        plan.unsupported.append(f"AI ne unknown tool manga '{tool}' — registry me nahi hai, skip kiya")
                        continue
                    allowed = {p.name for p in REG.tools[tool].params}
                    prm = {k: v for k, v in prm.items() if not allowed or k in allowed}
                    plan.steps.append(Step(tool, prm))
                plan.unsupported += [str(u)[:200] for u in (obj.get("unsupported") or [])]
                if obj.get("reply"):
                    plan.notes.append(str(obj["reply"])[:300])
                self.total += 1
                self.last_provider = name
                return plan
            except Exception as e:
                log.warning("AI provider %s failed (%s) — trying next", name, type(e).__name__)
                safe_log("WARN", "AI", f"Provider {name} failed ({type(e).__name__}) — failover")
        return None

AI = AIManager()

# ----------------------------------------------------------------------------
# Telegram manager — single client, session / phone+OTP / 2FA, Saved Messages
# ----------------------------------------------------------------------------
LOGIN_TTL = 300
CONFIRM_TTL = 90

class TelegramManager:
    def __init__(self):
        self.client = None
        self.account = STATE.get("account")
        self.authorized = False
        self.lock = asyncio.Lock()
        self.pending = {}

    async def _finalize(self, client):
        me = await client.get_me()
        self.client = client
        self.authorized = True
        self.account = {
            "name": f"{me.first_name or ''} {me.last_name or ''}".strip() or "Telegram User",
            "username": getattr(me, "username", None) or "unknown",
            "user_id": me.id,
            "phone": ("+•••••" + str(me.phone)[-4:]) if getattr(me, "phone", None) else None,
            "connected_at": int(time.time()),
        }
        STATE["account"] = self.account
        state_store.save_bg(STATE)
        self._attach_listener(client)
        await MONITOR.attach(client)
        if STATE["monitor"].get("active"):
            MONITOR.ensure_worker()
        log.info("TELEGRAM authorized as @%s (%s)", self.account["username"], me.id)
        safe_log("OK", "TELEGRAM", f"Authorized as @{self.account['username']} (ID {me.id})")
        return client.session.save()

    async def _replace_client(self, client):
        if self.client and self.client is not client:
            try:
                await self.client.disconnect()
                safe_log("WARN", "TELEGRAM", "Previous client disconnected — single session enforced")
            except Exception:
                pass

    async def connect_session(self, api_id, api_hash, session_string):
        if not TELETHON_OK:
            return False, "telethon not installed — pip install -r requirements.txt"
        async with self.lock:
            client = TelegramClient(StringSession(session_string.strip()), api_id, api_hash.strip())
            try:
                await client.connect()
                if not await client.is_user_authorized():
                    await client.disconnect()
                    return False, "SESSION INVALID — expired ya revoked; fresh StringSession generate karo"
                await self._replace_client(client)
                await self._finalize(client)
                return True, {"account": self.account}
            except SessionPasswordNeededError:
                await client.disconnect()
                return False, "Session ke saath 2FA password mang raha hai — Phone/OTP login use karo"
            except (ValueError, EOFError, struct.error):
                await client.disconnect()
                return False, "SESSION STRING CORRUPT — fresh Telethon StringSession export karo"
            except RPCError as e:
                await client.disconnect()
                return False, f"Telegram RPC error ({type(e).__name__}) — API ID / HASH verify karo"
            except Exception as e:
                try:
                    await client.disconnect()
                except Exception:
                    pass
                log.error("TELEGRAM connect failure: %s", type(e).__name__)
                return False, "Connection failed — network ya credentials issue"

    async def send_code(self, api_id, api_hash, phone):
        if not TELETHON_OK:
            return False, "telethon not installed — pip install -r requirements.txt"
        for old in list(self.pending.values()):
            try:
                await old["client"].disconnect()
            except Exception:
                pass
        self.pending.clear()
        client = TelegramClient(StringSession(), api_id, api_hash.strip())
        try:
            await client.connect()
            sent = await client.send_code_request(phone.strip())
            login_id = uuid.uuid4().hex[:12]
            self.pending[login_id] = {"client": client, "phone": phone.strip(),
                                      "phone_code_hash": sent.phone_code_hash,
                                      "expires": time.time() + LOGIN_TTL}
            safe_log("INFO", "TELEGRAM", "OTP requested — code sent by Telegram (never logged)")
            return True, {"login_id": login_id, "message": "OTP sent to your Telegram app. 5 minute me expire hoga."}
        except PhoneNumberInvalidError:
            await client.disconnect()
            return False, "INVALID PHONE — international format use karo, e.g. +97798XXXXXXXX"
        except FloodWaitError as fw:
            await client.disconnect()
            return False, f"FloodWait — Telegram keh raha hai {fw.seconds}s wait karo (exact delay, no bypass)"
        except RPCError as e:
            await client.disconnect()
            return False, f"Telegram RPC error ({type(e).__name__}) — API ID / HASH verify karo"
        except Exception as e:
            await client.disconnect()
            log.error("send_code failure: %s", type(e).__name__)
            return False, "OTP bhejna fail hua — network ya credentials issue"

    def _pending_login(self, login_id):
        p = self.pending.get(login_id)
        if not p:
            return None, "LOGIN EXPIRED — phone step se dobara shuru karo"
        if time.time() > p["expires"]:
            self.pending.pop(login_id, None)
            return None, "OTP window expired (5 min) — naya code mangwao"
        return p, None

    async def verify_code(self, login_id, code):
        async with self.lock:
            p, err = self._pending_login(login_id)
            if err:
                return False, err
            try:
                await p["client"].sign_in(phone=p["phone"], code=code.strip().replace(" ", ""),
                                          phone_code_hash=p["phone_code_hash"])
                await self._replace_client(p["client"])
                session = await self._finalize(p["client"])
                self.pending.pop(login_id, None)
                return True, {"account": self.account, "session_string": session,
                              "message": "Authorized — SESSION STRING abhi copy karo, sirf ek baar dikhaya jayega."}
            except SessionPasswordNeededError:
                p["expires"] = time.time() + LOGIN_TTL
                safe_log("INFO", "TELEGRAM", "OTP accepted — 2FA password step required")
                return True, {"needs_2fa": True, "message": "OTP accepted. Account me 2FA hai — cloud password daalo."}
            except PhoneCodeInvalidError:
                return False, "INVALID OTP — Telegram app ka code check karke retry karo"
            except PhoneCodeExpiredError:
                self.pending.pop(login_id, None)
                return False, "OTP EXPIRED — naya code request karo"
            except FloodWaitError as fw:
                return False, f"FloodWait — {fw.seconds}s baad retry karo (exact delay honoured)"
            except RPCError as e:
                return False, f"Telegram RPC error ({type(e).__name__})"
            except Exception as e:
                log.error("verify_code failure: %s", type(e).__name__)
                return False, "OTP verification fail — dobara try karo"

    async def verify_2fa(self, login_id, password):
        async with self.lock:
            p, err = self._pending_login(login_id)
            if err:
                return False, err
            try:
                await p["client"].sign_in(password=password)
                await self._replace_client(p["client"])
                session = await self._finalize(p["client"])
                self.pending.pop(login_id, None)
                return True, {"account": self.account, "session_string": session,
                              "message": "2FA accepted — authorized. SESSION STRING abhi copy karo (ek baar hi dikhaya jayega)."}
            except PasswordHashInvalidError:
                return False, "INVALID 2FA PASSWORD — dobara try karo"
            except FloodWaitError as fw:
                return False, f"FloodWait — {fw.seconds}s baad retry karo (exact delay honoured)"
            except Exception as e:
                log.error("verify_2fa failure: %s", type(e).__name__)
                return False, "2FA verification fail — dobara try karo"

    async def disconnect(self, clear=True):
        async with self.lock:
            if self.client:
                try:
                    await self.client.disconnect()
                except Exception:
                    pass
            self.client = None
            self.authorized = False
            MONITOR.attached_client = None
            if clear:
                self.account = None
                STATE["account"] = None
                state_store.save_bg(STATE)
            safe_log("WARN", "TELEGRAM", "Client disconnected" + (" — metadata cleared" if clear else ""))

    def status(self):
        connected = bool(self.client and self.client.is_connected())
        return connected, bool(connected and self.authorized)

    def _attach_listener(self, client):
        mgr = self

        @client.on(events.NewMessage(chats="me"))
        async def _on_saved(event):
            try:
                sender = int(event.sender_id or 0)
                admins = authorized_admin_ids(mgr.account)
                if sender not in admins:
                    log.warning("Ignoring command from non-admin id %s (fail closed)", sender)
                    safe_log("WARN", "AUTH", f"Ignored message from non-admin {sender} (fail closed)")
                    return
                text = (event.raw_text or "").strip()
                prefixed = re.match(r"^\s*\/?(ai|jarvis|cross|task|monitor)\b", text, re.I)
                confirm_pending = f"tg:{sender}" in PENDING_CONFIRM
                if not prefixed and not confirm_pending:
                    return
                result = await handle_command(text, origin=f"tg:{sender}")
                reply = "\n".join(result.get("lines") or ["Koi output nahi."])[:3800]
                await event.reply(reply)
                safe_log("CMD", "TELEGRAM", f"/AI from admin {sender} -> plan executed")
            except FloodWaitError as fw:
                log.warning("FloodWait %ss sending reply — waiting exact duration", fw.seconds)
                safe_log("WARN", "TELEGRAM", f"FloodWait {fw.seconds}s on reply — exact delay honoured")
                await asyncio.sleep(fw.seconds)
            except Exception as e:
                log.error("Saved-messages handler error: %s", type(e).__name__)

TG = TelegramManager()
PENDING_CONFIRM = {}   # origin -> {plan, lines(summary), expires}

# ----------------------------------------------------------------------------
# Folder scanning + channel activity (bounded, FloodWait-safe)
# ----------------------------------------------------------------------------
async def scan_folders():
    connected, _ = TG.status()
    if not connected:
        return []
    out = []
    async with TG.lock:
        try:
            filters = await TG.client(functions.messages.GetDialogFiltersRequest())
        except Exception as e:
            log.warning("Dialog filters unavailable (%s)", type(e).__name__)
            filters = []
        dialogs = [d async for d in TG.client.iter_dialogs(limit=300)]
    channels = [d for d in dialogs if getattr(d, "is_channel", False)]
    peer_map = {getattr(d.entity, "id", None): d for d in channels}
    for f in filters:
        title = getattr(getattr(f, "title", None), "text", None) or getattr(f, "title", None)
        include = getattr(f, "include_peers", None)
        if not title or not isinstance(title, str) or include is None:
            continue
        chans = []
        for p in include:
            d = peer_map.get(getattr(p, "channel_id", None))
            if d:
                chans.append({"id": d.entity.id, "name": getattr(d.entity, "title", "Channel"),
                              "username": getattr(d.entity, "username", None)})
        out.append({"name": title.upper(), "channels": chans})
    if not out and channels:
        out.append({"name": "ALL CHANNELS", "channels": [
            {"id": d.entity.id, "name": getattr(d.entity, "title", "Channel"),
             "username": getattr(d.entity, "username", None)} for d in channels]})
    return out

async def analyze_channel(cid):
    threshold = int(os.getenv("DEAD_THRESHOLD_DAYS", "30"))
    try:
        msgs = await TG.client.get_messages(int(cid), limit=1)
        if not msgs or msgs[0] is None:
            return "INACTIVE", "Empty history — koi post nahi mila", None
        last = msgs[0].date
        age = datetime.now(last.tzinfo) - last
        iso = last.isoformat()
        if age.days > threshold:
            return "INACTIVE", f"{age.days} din se koi post nahi (threshold {threshold})", iso
        return "ACTIVE", f"Last post {age.days}d pehle", iso
    except FloodWaitError as fw:
        log.warning("FloodWait %ss during scan — honouring exact delay", fw.seconds)
        await asyncio.sleep(fw.seconds)
        return "UNKNOWN", "Scan FloodWait se ruka — baad me retry", None
    except RPCError as e:
        name = type(e).__name__
        if "Private" in name or "Forbidden" in name:
            return "INACCESSIBLE", f"Messages read nahi kar sakte ({name})", None
        return "RESTRICTED", f"Restricted access ({name})", None
    except Exception as e:
        return "UNKNOWN", f"Unclassified ({type(e).__name__})", None

# ============================================================================
# TELEGRAM TOOLS (registry entries)
# ============================================================================

async def t_telegram_status(p, o):
    connected, authed = TG.status()
    return {"lines": ["TELEGRAM STATUS", bar,
                      f"Connection ▸ {'LIVE' if connected else 'DISCONNECTED'}",
                      f"Authorized ▸ {'YES' if authed else 'NO'}",
                      f"Account    ▸ {('@' + TG.account['username']) if (authed and TG.account) else '—'}",
                      f"2FA        ▸ session active — OTP phir se nahi mangta" if authed else ""]}

async def t_telegram_account(p, o):
    if not TG.account:
        return {"ok": False, "lines": ["TELEGRAM DISCONNECTED ▸ connect first"]}
    a = TG.account
    ctx_set(o, last_user=a["username"])
    return {"lines": ["AUTHENTICATED ACCOUNT", bar, f"Name     ▸ {a['name']}",
                      f"Username ▸ @{a['username']}", f"User ID  ▸ {a['user_id']}",
                      f"Phone    ▸ {a.get('phone') or 'hidden'}", "Auth     ▸ VALID session"],
            "data": {"user": a["username"]}}

async def t_telegram_dialogs(p, o):
    lines, n = ["RECENT DIALOGS", bar], 0
    async for d in TG.client.iter_dialogs(limit=int(p.get("limit") or 15)):
        n += 1
        kind = "channel" if getattr(d, "is_channel", False) else "group" if getattr(d, "is_group", False) else "user"
        unread = f" ▸ {d.unread_count} unread" if getattr(d, "unread_count", 0) else ""
        lines.append(f"{n}. {d.name} ({kind}){unread}")
    return {"lines": lines + [f"Total shown: {n}"]}

async def t_telegram_folders(p, o):
    folders = await scan_folders()
    if not folders:
        return {"ok": False, "lines": ["TELEGRAM DISCONNECTED ▸ ya koi folder visible nahi"]}
    include = p.get("include_channels")
    lines, total = ["TELEGRAM FOLDERS", bar], 0
    for i, f in enumerate(folders, 1):
        lines += [f"{i}. Folder: {f['name']}", f"   Channels: {len(f['channels'])}"]
        total += len(f["channels"])
        if include:
            for j, c in enumerate(f["channels"][:10], 1):
                lines.append(f"   {j}) {c['name']} {'@' + c['username'] if c.get('username') else '(private)'} ▸ ID {c['id']}")
            if len(f["channels"]) > 10:
                lines.append(f"   … +{len(f['channels']) - 10} more in {f['name']}")
    lines += [bar, f"Total folders: {len(folders)} ▸ Total channels: {total}"]
    return {"lines": lines}

async def t_dead_scan(p, o):
    folders = await scan_folders()
    if not folders:
        return {"ok": False, "lines": ["TELEGRAM DISCONNECTED ▸ ya koi folder visible nahi"]}
    buckets = {k: [] for k in ("ACTIVE", "INACTIVE", "RESTRICTED", "INACCESSIBLE", "UNKNOWN")}
    checked = 0
    for f in folders:
        for c in f["channels"][:25]:
            checked += 1
            status, reason, _ = await analyze_channel(c["id"])
            buckets[status].append((c, reason))
    lines = ["CHANNEL ACTIVITY SCAN COMPLETE", bar,
             f"Checked: {checked} ▸ Active: {len(buckets['ACTIVE'])} ▸ Inactive: {len(buckets['INACTIVE'])} "
             f"▸ Restricted: {len(buckets['RESTRICTED'])} ▸ Inaccessible: {len(buckets['INACCESSIBLE'])} ▸ Unknown: {len(buckets['UNKNOWN'])}",
             bar, "INACTIVE / POSSIBLY DEAD CHANNELS"]
    i = 0
    for st in ("INACTIVE", "RESTRICTED", "INACCESSIBLE"):
        for c, reason in buckets[st]:
            i += 1
            if i <= 12:
                lines += [f"{i}. {c['name']} {'@' + c['username'] if c.get('username') else '(private)'}",
                          f"   Status: {st}", f"   Reason: {reason}"]
    if i == 0:
        lines.append("None — sab channels healthy hain.")
    if i > 12:
        lines.append(f"+{i - 12} more")
    lines.append("Note: ek failed request se kisi channel ko permanently dead declare nahi kiya jata.")
    return {"lines": lines}

async def _chan_target(p, o):
    chan = str(p.get("channel", "")).strip()
    if not chan:
        chan = ctx_get(o).get("last_channel", "")
    return chan

async def t_channel_info(p, o):
    chan = await _chan_target(p, o)
    if not chan:
        return {"ok": False, "lines": ["Kaunsa channel? @username batao — e.g. '/AI @mynews channel inspect karo'"]}
    try:
        e = await resolve_chat(chan)
    except Exception as ex:
        return {"ok": False, "lines": [f"ENTITY ERROR ▸ '{chan}' resolve nahi hua ({type(ex).__name__}) — private/inaccessible ho sakta hai"]}
    ctx_set(o, last_channel=getattr(e, "username", None) or str(e.id))
    members = getattr(e, "participants_count", None)
    latest_txt, latest_dt = None, None
    try:
        msgs = await TG.client.get_messages(e, limit=1)
        if msgs and msgs[0]:
            latest_dt = msgs[0].date
            latest_txt = (msgs[0].text or "")[:100]
    except Exception:
        pass
    return {"lines": ["CHANNEL REPORT", bar,
                      f"Title     ▸ {getattr(e, 'title', chan)}",
                      f"Username  ▸ @{getattr(e, 'username', None) or '(private)'}",
                      f"Chat ID   ▸ {e.id}",
                      f"Type      ▸ {'broadcast channel' if getattr(e, 'broadcast', False) else 'megagroup/channel'}",
                      f"Members   ▸ {members if members is not None else 'account ko visible nahi'}",
                      f"Verified  ▸ {'YES' if getattr(e, 'verified', False) else 'no'}",
                      f"Latest    ▸ {latest_dt.strftime('%d %b %I:%M %p') if latest_dt else 'history readable nahi'}",
                      f"Preview   ▸ {latest_txt or '—'}"],
            "data": {"channel": getattr(e, "username", None) or str(e.id)}}

async def t_channel_activity(p, o):
    chan = await _chan_target(p, o)
    if not chan:
        return {"ok": False, "lines": ["Kaunsa channel? @username batao"]}
    try:
        e = await resolve_chat(chan)
    except Exception as ex:
        return {"ok": False, "lines": [f"ENTITY ERROR ▸ '{chan}' resolve nahi hua ({type(ex).__name__})"]}
    ctx_set(o, last_channel=getattr(e, "username", None) or str(e.id))
    dates = []
    try:
        async for m in TG.client.iter_messages(e, limit=20):
            if m and m.date:
                dates.append(m.date)
    except RPCError as ex:
        return {"ok": False, "lines": [f"READ ERROR ▸ history access nahi ({type(ex).__name__})"]}
    if not dates:
        return {"lines": [f"{getattr(e, 'title', chan)} ▸ koi message visible nahi — INACTIVE lag raha hai (history empty/read-only)"]}
    latest, oldest = dates[0], dates[-1]
    span = max(1, (latest - oldest).days or 1)
    per_day = round(len(dates) / span, 1)
    age_h = (datetime.now(latest.tzinfo) - latest).total_seconds() / 3600
    status = "ACTIVE" if age_h < 72 else "INACTIVE (72h+ se koi post nahi)"
    return {"lines": ["CHANNEL ACTIVITY", bar,
                      f"Channel   ▸ {getattr(e, 'title', chan)}",
                      f"Status    ▸ {status}",
                      f"Latest    ▸ {latest.strftime('%d %b %I:%M %p')} ({int(age_h)}h pehle)",
                      f"Window    ▸ pichle {len(dates)} messages {oldest.strftime('%d %b')} se {latest.strftime('%d %b')} tak",
                      f"Frequency ▸ ~{per_day} posts/day (visible sample se)"],
            "data": {"channel": getattr(e, "username", None) or str(e.id)}}

async def t_channel_age(p, o):
    chan = await _chan_target(p, o)
    if not chan:
        return {"ok": False, "lines": ["Kaunsa channel? @username batao"]}
    try:
        e = await resolve_chat(chan)
    except Exception as ex:
        return {"ok": False, "lines": [f"ENTITY ERROR ▸ '{chan}' resolve nahi hua ({type(ex).__name__})"]}
    ctx_set(o, last_channel=getattr(e, "username", None) or str(e.id))
    try:
        earliest = await TG.client.get_messages(e, limit=1, reverse=True)
    except Exception as ex:
        return {"ok": False, "lines": [f"READ ERROR ▸ earliest message fetch nahi hua ({type(ex).__name__})"]}
    if not earliest or not earliest[0] or not earliest[0].date:
        return {"lines": [f"{getattr(e, 'title', chan)} ▸ history accessible nahi — age estimate possible nahi"]}
    d = earliest[0].date
    days = (datetime.now(d.tzinfo) - d).days
    return {"lines": ["CHANNEL AGE ESTIMATE", bar,
                      f"Channel ▸ {getattr(e, 'title', chan)}",
                      "Estimated age based on earliest accessible message:",
                      f"Earliest ▸ {d.strftime('%d %b %Y %I:%M %p')} (~{days} din / ~{round(days / 30, 1)} months purana)",
                      "Note: exact creation date Telegram provide nahi karta — ye sirf history-based estimate hai."],
            "data": {"channel": getattr(e, "username", None) or str(e.id)}}

async def t_recent_messages(p, o):
    chan = str(p.get("channel", "")).strip() or ctx_get(o).get("last_channel", "")
    lines = ["RECENT MESSAGES", bar]
    if chan:
        try:
            e = await resolve_chat(chan)
            ctx_set(o, last_channel=getattr(e, "username", None) or str(e.id))
            n = 0
            async for m in TG.client.iter_messages(e, limit=6):
                if m and (m.text or ""):
                    n += 1
                    lines.append(f"{n}. {m.date.strftime('%d %b %H:%M')} ▸ {(m.text or '')[:80]}")
            if n == 0:
                lines.append("Koi readable message nahi mila.")
            return {"lines": lines}
        except Exception as ex:
            return {"ok": False, "lines": [f"READ ERROR ▸ ({type(ex).__name__})"]}
    n = 0
    async for d in TG.client.iter_dialogs(limit=10):
        if getattr(d, "is_channel", False) and d.message and (d.message.text or ""):
            n += 1
            lines.append(f"{n}. [{d.name}] {d.message.date.strftime('%d %b %H:%M')} ▸ {(d.message.text or '')[:70]}")
    return {"lines": lines + [f"Checked {n} channels"]}

async def t_message_search(p, o):
    q = str(p.get("query", ""))[:60]
    if not q:
        return {"ok": False, "lines": ["Usage: /AI <text> search karo"]}
    hits = []
    async for m in TG.client.iter_messages("me", search=q, limit=5):
        if m.text:
            hits.append(f"▸ {m.date.strftime('%d %b %H:%M')} — {m.text[:90]}")
    return {"lines": [f"MESSAGE SEARCH — \"{q}\"", bar] + (hits or ["Readable dialogs me koi match nahi"])}

async def t_saved_messages(p, o):
    lines = ["SAVED MESSAGES — LAST ENTRIES", bar]
    async for m in TG.client.iter_messages("me", limit=5):
        if m.text:
            lines.append(f"▸ {m.date.strftime('%d %b %H:%M')} — {m.text[:80]}")
    lines += [bar, "JARVIS is chat me /AI commands monitor karta hai (sirf authorized admins — fail closed)."]
    return {"lines": lines}

async def t_user_info(p, o):
    ref = str(p.get("user", "")).strip() or ctx_get(o).get("last_user", "")
    if not ref:
        return {"ok": False, "lines": ["Kaunsa user? @username batao"]}
    try:
        u = await resolve_chat(ref)
    except Exception as ex:
        return {"ok": False, "lines": [f"USER ERROR ▸ '{ref}' resolve nahi hua ({type(ex).__name__}) — deleted/private ho sakta hai"]}
    ctx_set(o, last_user=getattr(u, "username", None) or str(u.id))
    return {"lines": ["USER REPORT", bar,
                      f"Name     ▸ {getattr(u, 'first_name', '') or ''} {getattr(u, 'last_name', '') or ''}".strip(),
                      f"Username ▸ @{getattr(u, 'username', None) or '(none)'}",
                      f"User ID  ▸ {u.id}",
                      f"Bot      ▸ {'YES' if getattr(u, 'bot', False) else 'no'}"],
            "data": {"user": getattr(u, "username", None) or str(u.id)}}

async def t_permissions(p, o):
    chan = await _chan_target(p, o)
    if not chan:
        return {"ok": False, "lines": ["Kaunsa channel? @username batao"]}
    try:
        e = await resolve_chat(chan)
        perms = await TG.client.get_permissions(e, "me")
    except Exception as ex:
        return {"ok": False, "lines": [f"PERMISSION ERROR ▸ ({type(ex).__name__})"]}
    ctx_set(o, last_channel=getattr(e, "username", None) or str(e.id))
    if not perms.is_admin and not perms.is_creator:
        return {"lines": [f"{getattr(e, 'title', chan)} ▸ account ADMIN nahi hai — read-only access"]}
    rights = [k for k in ("post_messages", "edit_messages", "delete_messages", "ban_users",
                          "invite_users", "add_admins", "manage_call", "pin_messages")
              if getattr(perms, k, False)]
    return {"lines": ["CHANNEL PERMISSIONS", bar,
                      f"Channel ▸ {getattr(e, 'title', chan)}",
                      f"Role    ▸ {'CREATOR' if perms.is_creator else 'ADMIN'}",
                      f"Rights  ▸ {', '.join(rights) if rights else 'custom/limited'}"]}

# ---------------- monitor workflow tools ----------------

async def _monitor_src(p):
    return (p.get("source") or STATE["monitor"].get("source")
            or os.getenv("MONITOR_SOURCE", "").strip() or None)

async def t_monitor_source(p, o):
    return await MONITOR.start(p, o)

async def t_fetch_latest(p, o):
    src = await _monitor_src(p)
    if not src:
        return {"ok": False, "lines": ["SOURCE NOT CONFIGURED ▸ MONITOR_SOURCE env set karo ya '/AI @channel ko monitor karo'"]}
    try:
        e = await resolve_chat(src)
        msgs = await TG.client.get_messages(e, limit=1)
    except Exception as ex:
        return {"ok": False, "lines": [f"SOURCE ERROR ▸ latest message fetch nahi hua ({type(ex).__name__})"]}
    if not msgs or not msgs[0]:
        return {"lines": ["Source me abhi koi message nahi mila — Telegram ne kuch provide nahi kiya (fabricate nahi karunga)."]}
    ctx_set(o, last_channel=getattr(e, "username", None) or str(e.id))
    m = msgs[0]
    txt = (m.text or "(non-text message / media)")[:600]
    return {"lines": ["LATEST SOURCE MESSAGE", bar,
                      f"Source ▸ {src} ▸ message id {m.id}",
                      f"Date   ▸ {m.date.strftime('%d %b %Y %I:%M %p') if m.date else '—'}",
                      bar, txt]}

async def t_parse_source(p, o):
    src = await _monitor_src(p)
    if not src:
        return {"ok": False, "lines": ["SOURCE NOT CONFIGURED ▸ MONITOR_SOURCE env set karo"]}
    try:
        e = await resolve_chat(src)
        msgs = await TG.client.get_messages(e, limit=1)
    except Exception as ex:
        return {"ok": False, "lines": [f"SOURCE ERROR ▸ ({type(ex).__name__})"]}
    if not msgs or not msgs[0] or not (msgs[0].text or ""):
        return {"lines": ["Parse karne layak text nahi mila — latest message empty ya non-text hai."]}
    kws = STATE["monitor"].get("keywords") or DEFAULT_KEYWORDS
    parsed = parse_source_text(msgs[0].text, kws)
    return {"lines": ["SOURCE PARSE RESULT", bar,
                      f"Keywords ▸ {', '.join(kws)}",
                      f"Match    ▸ {'YES — ' + str(parsed['matched_lines']) + ' line(s)' if parsed['matched'] else 'NO — full text use hoga'}",
                      bar, parsed["body"][:800]]}

async def t_copy_source(p, o):
    src = await _monitor_src(p)
    _, dst = MONITOR.configured()
    if not src or not dst:
        return {"ok": False, "lines": ["SOURCE/DESTINATION NOT CONFIGURED ▸ MONITOR_SOURCE aur MONITOR_DESTINATION set karo"]}
    try:
        e = await resolve_chat(src)
        msgs = await TG.client.get_messages(e, limit=1)
    except Exception as ex:
        return {"ok": False, "lines": [f"SOURCE ERROR ▸ ({type(ex).__name__})"]}
    if not msgs or not msgs[0] or not (msgs[0].text or ""):
        return {"ok": False, "lines": ["Copy karne layak source text nahi mila — latest message empty/non-text (fabricate nahi karunga)."]}
    parsed = parse_source_text(msgs[0].text, STATE["monitor"].get("keywords"))
    body = format_update_text(parsed["body"])
    try:
        sent = await TG.client.send_message(await resolve_chat(dst), body)
    except FloodWaitError as fw:
        await asyncio.sleep(fw.seconds)
        sent = await TG.client.send_message(await resolve_chat(dst), body)
    STATE["monitor"]["last_event"] = f"manual copy sent ▸ msg {sent.id}"
    state_store.save_bg(STATE)
    return {"lines": ["SOURCE TEXT COPIED → DESTINATION", bar,
                      f"Source ▸ {src} (id {msgs[0].id})",
                      f"Sent   ▸ {dst} (id {sent.id})",
                      f"Mode   ▸ {'keyword-filtered' if parsed['matched'] else 'verbatim full text'}", bar,
                      parsed["body"][:500]]}

async def t_format_update(p, o):
    src = await _monitor_src(p)
    if not src:
        return {"ok": False, "lines": ["SOURCE NOT CONFIGURED ▸ MONITOR_SOURCE env set karo"]}
    try:
        e = await resolve_chat(src)
        msgs = await TG.client.get_messages(e, limit=1)
    except Exception as ex:
        return {"ok": False, "lines": [f"SOURCE ERROR ▸ ({type(ex).__name__})"]}
    if not msgs or not msgs[0] or not (msgs[0].text or ""):
        return {"ok": False, "lines": ["Format karne layak text nahi mila."]}
    parsed = parse_source_text(msgs[0].text, STATE["monitor"].get("keywords"))
    return {"lines": ["UPDATE PREVIEW (abhi send nahi hua)", bar,
                      format_update_text(parsed["body"])[:700],
                      bar, "Bhejne ke liye: '/AI latest result bhejo' ya '/AI source copy karke destination par bhejo'"]}

async def t_send_update(p, o):
    return await t_copy_source(p, o)

# ---------------- cross engine tools ----------------

async def t_cross_start(p, o):    return await ENGINE.start(p, o)
async def t_cross_stop(p, o):     return ENGINE.stop()
async def t_cross_pause(p, o):    return await ENGINE.pause(p, o)
async def t_cross_resume(p, o):   return await ENGINE.resume(p, o)
async def t_cross_reset(p, o):    return await ENGINE.reset(p, o)

async def t_cross_status(p, o):
    e = STATE["engine"]
    hold = max(0, int((e.get("flood_wait_until") or 0) - time.time()))
    return {"lines": ENGINE.config_lines() + [
        f"Processed    ▸ {e['processed']} ▸ Failed: {e['failed']}",
        (f"FloodWait    ▸ {hold}s remaining — exact delay honoured" if hold else "FloodWait    ▸ none"),
        f"Last event   ▸ {e['last_event']}"]}

async def t_cross_config(p, o):
    return {"lines": ENGINE.config_lines()}

# ---------------- scheduler / task tools ----------------

async def t_scheduler_status(p, o):
    active = [j for j in SCHED.jobs if not j.get("done")]
    return {"lines": [f"SCHEDULER STATUS — clock Asia/Kathmandu ({ktm_now().strftime('%I:%M %p NPT')})", bar,
                      f"Active jobs ▸ {len(active)} ▸ History: {len(SCHED.jobs)}",
                      f"Next        ▸ {fmt_kt(min(j['run_at'] for j in active)) if active else '—'}",
                      "Persistence ▸ scheduled_jobs.json ▸ restart recovery on ▸ no double-fire"]}

async def t_scheduler_list(p, o):
    lines = [f"SCHEDULED JOBS — ({ktm_now().strftime('%I:%M %p NPT')})", bar]
    if not SCHED.jobs:
        lines.append('Koi job nahi. Try: "10 minute baad cross start karo" / "7:30 PM par stop karo".')
    for j in SCHED.jobs[-8:]:
        lines.append(f"[{j['id']}] {j['action']} — {j['label']} ▸ {fmt_kt(j['run_at'])} ▸ {'DONE' if j.get('done') else 'PENDING'}")
    return {"lines": lines}

async def t_scheduler_start(p, o):
    if not p.get("run_at"):
        return {"ok": False, "lines": ["Time samajh nahi aaya — e.g. '10 minute baad start' / '7:30 PM par start'"]}
    j = SCHED.add("START", float(p["run_at"]), str(p.get("label", "scheduled")))
    return {"lines": [f"JOB SCHEDULED ▸ ENGINE START at {j['label']} ({fmt_kt(j['run_at'])}) ▸ id [{j['id']}]"]}

async def t_scheduler_stop(p, o):
    if not p.get("run_at"):
        return {"ok": False, "lines": ["Time samajh nahi aaya — e.g. '10 minute baad stop' / '7:30 PM par stop'"]}
    j = SCHED.add("STOP", float(p["run_at"]), str(p.get("label", "scheduled")))
    return {"lines": [f"JOB SCHEDULED ▸ ENGINE STOP at {j['label']} ({fmt_kt(j['run_at'])}) ▸ id [{j['id']}]"]}

async def t_scheduler_cancel(p, o):
    jid = str(p.get("id", ""))
    if not jid:
        pend = [j for j in SCHED.jobs if not j.get("done")]
        if len(pend) == 1:
            jid = pend[0]["id"]
        else:
            return {"ok": False, "lines": ["Job id batao — '/AI schedule list' se id dekho, phir '/AI cancel job <id>'"]}
    return {"lines": [f"CANCELLED ▸ [{jid}]"] if SCHED.cancel(jid) else ["JOB NOT FOUND ▸ " + jid]}

async def t_task_status(p, o):
    running = TASKS.running()
    lines = ["TASK MANAGER", bar]
    if not running and not TASKS.tasks:
        lines.append("Koi tracked task nahi — cross ya monitor start karo.")
    for t in TASKS.tasks.values():
        stats = t["stats"]() if t.get("stats") else ""
        lines.append(f"[{t['id']}] {t['label']} ▸ {t['status']} ▸ since {fmt_kt(t['started_at'])} {('▸ ' + stats) if stats else ''}")
    lines.append(MONITOR.status_lines()[2])
    return {"lines": lines}

async def t_task_stop(p, o):
    tid = str(p.get("id", "")).upper()
    kind = str(p.get("kind", "")).upper()
    target = None
    if tid:
        target = TASKS.tasks.get(tid) or next((t for t in TASKS.tasks.values() if t["id"].upper() == tid), None)
    elif kind:
        target = next((t for t in TASKS.tasks.values() if t["kind"] == kind and t["status"] in ("RUNNING", "PAUSED")), None)
    if not target:
        cand = TASKS.running()
        if len(cand) == 1:
            target = cand[0]
        elif len(cand) > 1:
            return {"ok": False, "lines": ["Multiple tasks chal rahe hain — id specify karo:"] +
                                           [f"▸ [{t['id']}] {t['label']} ({t['status']})" for t in cand]}
    if not target:
        return {"lines": ["Koi running task nahi mila jo stop kiya ja sake."]}
    await TASKS.stop(target["id"])
    return {"lines": [f"TASK STOPPED ▸ [{target['id']}] {target['label']}", "Actual engine/monitor ko safely stop kiya gaya."]}

async def t_task_reset(p, o):
    tid = str(p.get("id", "")).upper()
    target = TASKS.tasks.get(tid) if tid else (TASKS.running()[0] if len(TASKS.running()) == 1 else None)
    if not target:
        return {"ok": False, "lines": ["Reset ke liye task id batao — '/AI task status'"]}
    if target.get("reset"):
        res = await target["reset"]()
        return res if isinstance(res, dict) else {"lines": [str(res)]}
    return {"ok": False, "lines": ["Is task me reset supported nahi hai."]}

# ---------------- admin tools ----------------

async def _admin_resolve(p, o):
    chan = str(p.get("channel", "")).strip() or ctx_get(o).get("last_channel", "")
    user = str(p.get("user", "")).strip() or ctx_get(o).get("last_user", "")
    return chan, user

async def t_admin_check(p, o):
    chan = await _chan_target(p, o)
    if not chan:
        return {"ok": False, "lines": ["Kaunsa channel? @username batao"]}
    return await t_permissions({"channel": chan}, o)

ADMIN_RIGHTS = dict(post_messages=True, edit_messages=True, delete_messages=True,
                    invite_users=True, ban_users=False, add_admins=False, pin_messages=True)

async def t_admin_promote(p, o):
    chan, user = await _admin_resolve(p, o)
    if not chan or not user:
        return {"ok": False, "lines": [
            "ADMIN PROMOTE ke liye channel aur user dono chahiye:",
            "'/AI @channel me @user ko admin de do' — exact action confirm ke baad hi hoga"]}
    try:
        chan_e = await resolve_chat(chan)
        user_e = await resolve_chat(user)
        perms = await TG.client.get_permissions(chan_e, "me")
    except Exception as ex:
        return {"ok": False, "lines": [f"RESOLVE ERROR ▸ ({type(ex).__name__}) — channel/user accessible nahi"]}
    if not perms.is_admin and not perms.is_creator:
        return {"ok": False, "lines": ["PERMISSION DENIED ▸ aap is channel ke admin nahi — promote karne ka right nahi hai (bypass nahi hoga)"]}
    if not (perms.is_creator or getattr(perms, "add_admins", False)):
        return {"ok": False, "lines": ["PERMISSION DENIED ▸ aapke paas 'add admins' right nahi hai is channel me"]}
    await TG.client.edit_admin(chan_e, user_e, is_admin=True, title="Admin", **ADMIN_RIGHTS)
    ctx_set(o, last_channel=getattr(chan_e, "username", None), last_user=getattr(user_e, "username", None))
    safe_log("CMD", "ADMIN", f"Promoted @{getattr(user_e,'username',user)} in {getattr(chan_e,'title',chan)} (confirmed)")
    return {"lines": ["ADMIN PROMOTED (real Telegram result)", bar,
                      f"User    ▸ @{getattr(user_e, 'username', None) or user_e.id}",
                      f"Channel ▸ {getattr(chan_e, 'title', chan)}",
                      "Rights  ▸ " + ", ".join(k for k, v in ADMIN_RIGHTS.items() if v)]}

async def t_admin_demote(p, o):
    chan, user = await _admin_resolve(p, o)
    if not chan or not user:
        return {"ok": False, "lines": ["DEMOTE ke liye channel aur user dono chahiye — '/AI @channel se @user ka admin hatao'"]}
    try:
        chan_e = await resolve_chat(chan)
        user_e = await resolve_chat(user)
        perms = await TG.client.get_permissions(chan_e, "me")
    except Exception as ex:
        return {"ok": False, "lines": [f"RESOLVE ERROR ▸ ({type(ex).__name__})"]}
    if not perms.is_admin and not perms.is_creator:
        return {"ok": False, "lines": ["PERMISSION DENIED ▸ aap admin nahi — demote karne ka right nahi (bypass nahi hoga)"]}
    await TG.client.edit_admin(chan_e, user_e, is_admin=False)
    safe_log("CMD", "ADMIN", f"Demoted @{getattr(user_e,'username',user)} in {getattr(chan_e,'title',chan)} (confirmed)")
    return {"lines": ["ADMIN DEMOTED (real Telegram result)", bar,
                      f"User    ▸ @{getattr(user_e, 'username', None) or user_e.id}",
                      f"Channel ▸ {getattr(chan_e, 'title', chan)}",
                      "Rights  ▸ sab admin rights revok kar di gayi"]}

# ---------------- jarvis system tools ----------------

async def t_jarvis_status(p, o):
    eng = STATE["engine"]
    connected, authed = TG.status()
    hold = max(0, int((eng.get("flood_wait_until") or 0) - time.time()))
    return {"lines": ["JARVIS SYSTEM STATUS", bar, "JARVIS     ▸ ONLINE (NLU active)",
                      f"TELEGRAM   ▸ {'CONNECTED @' + TG.account['username'] if authed and TG.account else 'DISCONNECTED'}",
                      "AUTH       ▸ AUTHORIZED (fail-closed)",
                      f"TASKS      ▸ {len(TASKS.running())} running ({', '.join(t['id'] for t in TASKS.running()) or 'none'})",
                      f"ENGINE     ▸ {eng['status'].upper()}" + (f" — FloodWait {hold}s" if hold else ""),
                      f"MONITOR    ▸ {'RUNNING (event-based)' if STATE['monitor'].get('active') else 'STOPPED'}",
                      f"AI         ▸ {AI.last_provider} ({AI.total} calls ▸ providers: {', '.join(AI.configured()) or 'local-only'})",
                      f"SCHEDULER  ▸ {len([j for j in SCHED.jobs if not j.get('done')])} active jobs (NPT)",
                      f"TOOLS      ▸ {len(REG.tools)} registered (whitelist)",
                      f"LAST ERROR ▸ {STATE.get('last_error') or 'none'}"]}

async def t_jarvis_help(p, o):
    cats = {}
    for t in REG.tools.values():
        cats.setdefault(t.category, []).append(t)
    lines = [f"JARVIS TOOL REGISTRY — {len(REG.tools)} tools (whitelist only)", bar,
             "Natural language full support: English · Hindi · Hinglish · multi-step",
             "Examples are endless — kuch bhi naturally likho, JARVIS intent samjhega.", bar]
    labels = {"TELEGRAM": "TELEGRAM", "JARVIS": "JARVIS", "SCHEDULER": "SCHEDULER",
              "CROSS": "CROSS ENGINE", "MONITOR": "SOURCE MONITOR", "TASK": "TASKS", "ADMIN": "ADMIN"}
    for cat in ("TELEGRAM", "JARVIS", "SCHEDULER", "CROSS", "MONITOR", "TASK", "ADMIN"):
        tools = cats.get(cat, [])
        if not tools:
            continue
        lines.append(labels.get(cat, cat) + ":")
        for t in tools:
            need = " (confirm)" if t.confirm else ""
            lines.append(f"  ▸ {t.desc}{need}")
    lines += [bar, "Jo cheez supported nahi hai, JARVIS clearly bolega — fake success kabhi nahi."]
    return {"lines": lines}

async def t_jarvis_diagnostics(p, o):
    d = diagnostics()
    return {"lines": [f"JARVIS DIAGNOSTICS — SCORE {d['score']}%", bar] +
                     [f"[{c['status']}] {c['name']} — {c['detail']}" for c in d["checks"]]}

async def t_jarvis_save_state(p, o):
    await state_store.save(STATE)
    await history_store.save(HISTORY[-50:])
    await jobs_store.save(SCHED.jobs[-40:])
    return {"lines": ["STATE SAVED ▸ jarvis_state.json ▸ ai_history.json ▸ scheduled_jobs.json (atomic, no secrets)"]}

# ============================================================================
# REGISTER ALL TOOLS (single source of truth for the whitelist)
# ============================================================================
REG.register("telegram_status", "Telegram connection/authorization status", "TELEGRAM", t_telegram_status)
REG.register("telegram_account", "Authenticated account details", "TELEGRAM", t_telegram_account)
REG.register("telegram_dialogs", "Recent dialogs list", "TELEGRAM", t_telegram_dialogs,
             params=[ToolParam("limit", "number")])
REG.register("telegram_folders", "Dialog folders scan (channels optional)", "TELEGRAM", t_telegram_folders)
REG.register("telegram_channel_info", "Channel inspect — title/id/members/latest", "TELEGRAM", t_channel_info,
             params=[ToolParam("channel", "chat", False)])
REG.register("telegram_channel_activity", "Channel recent activity + active/inactive", "TELEGRAM", t_channel_activity,
             params=[ToolParam("channel", "chat", False)])
REG.register("telegram_channel_age_estimate", "Channel age from earliest visible message", "TELEGRAM", t_channel_age,
             params=[ToolParam("channel", "chat", False)])
REG.register("telegram_recent_messages", "Recent messages (channel ya globally)", "TELEGRAM", t_recent_messages,
             params=[ToolParam("channel", "chat", False)])
REG.register("telegram_message_search", "Search readable messages", "TELEGRAM", t_message_search,
             params=[ToolParam("query", "text", True)])
REG.register("telegram_saved_messages", "Saved Messages inbox", "TELEGRAM", t_saved_messages)
REG.register("telegram_user_info", "User resolve + basic info", "TELEGRAM", t_user_info,
             params=[ToolParam("user", "user", False)])
REG.register("telegram_permissions", "Own permissions in a channel", "TELEGRAM", t_permissions,
             params=[ToolParam("channel", "chat", False)])
REG.register("telegram_dead_channel_scan", "Folders me inactive/restricted scan", "TELEGRAM", t_dead_scan)

REG.register("monitor_source", "Source monitoring start (event-based, fast)", "MONITOR", t_monitor_source,
             params=[ToolParam("source", "chat"), ToolParam("destination", "chat"), ToolParam("keywords", "list")])
REG.register("fetch_latest_source_message", "Latest source message fetch", "MONITOR", t_fetch_latest,
             params=[ToolParam("source", "chat")])
REG.register("parse_source_message", "Latest source message parse (keywords)", "MONITOR", t_parse_source)
REG.register("copy_source_text", "Exact source text copy → destination", "MONITOR", t_copy_source, confirm=True)
REG.register("format_update", "Update preview from template (no send)", "MONITOR", t_format_update)
REG.register("send_update", "Update destination par bhejo", "MONITOR", t_send_update, confirm=True)

REG.register("cross_status", "Cross engine status", "CROSS", t_cross_status, needs_telegram=False)
REG.register("cross_start", "Cross engine start", "CROSS", t_cross_start)
REG.register("cross_stop", "Cross engine stop", "CROSS", t_cross_stop, needs_telegram=False)
REG.register("cross_pause", "Cross engine pause (manual hold)", "CROSS", t_cross_pause, needs_telegram=False)
REG.register("cross_resume", "Cross engine resume", "CROSS", t_cross_resume, needs_telegram=False)
REG.register("cross_reset", "Cross engine reset (queue+counters)", "CROSS", t_cross_reset, needs_telegram=False, confirm=True)
REG.register("cross_config", "Cross engine configuration", "CROSS", t_cross_config, needs_telegram=False)

REG.register("scheduler_status", "Scheduler status", "SCHEDULER", t_scheduler_status, needs_telegram=False)
REG.register("scheduler_list", "Scheduled jobs list", "SCHEDULER", t_scheduler_list, needs_telegram=False)
REG.register("scheduler_start", "Deferred engine start", "SCHEDULER", t_scheduler_start, needs_telegram=False,
             params=[ToolParam("run_at", "time", True)])
REG.register("scheduler_stop", "Deferred engine stop", "SCHEDULER", t_scheduler_stop, needs_telegram=False,
             params=[ToolParam("run_at", "time", True)])
REG.register("scheduler_cancel", "Job cancel by id", "SCHEDULER", t_scheduler_cancel, needs_telegram=False)

REG.register("task_status", "All running tasks", "TASK", t_task_status, needs_telegram=False)
REG.register("task_stop", "Task stop by id / active task stop", "TASK", t_task_stop, needs_telegram=False)
REG.register("task_reset", "Task reset by id", "TASK", t_task_reset, needs_telegram=False)

REG.register("admin_check_permissions", "Admin rights check in channel", "ADMIN", t_admin_check,
             params=[ToolParam("channel", "chat", False)])
REG.register("admin_promote", "User ko channel admin banao", "ADMIN", t_admin_promote, confirm=True, sensitive=True,
             params=[ToolParam("channel", "chat"), ToolParam("user", "user")])
REG.register("admin_demote", "User se admin rights hatao", "ADMIN", t_admin_demote, confirm=True, sensitive=True,
             params=[ToolParam("channel", "chat"), ToolParam("user", "user")])

REG.register("jarvis_help", "Commands/tools help", "JARVIS", t_jarvis_help, needs_telegram=False)
REG.register("jarvis_status", "Full system status", "JARVIS", t_jarvis_status, needs_telegram=False)
REG.register("jarvis_diagnostics", "Diagnostics sweep", "JARVIS", t_jarvis_diagnostics, needs_telegram=False)
REG.register("jarvis_save_state", "JSON state persist", "JARVIS", t_jarvis_save_state, needs_telegram=False)

log.info("Registry armed: %d tools", len(REG.tools))

# ============================================================================
# COMMAND PIPELINE — /AI detection -> NLU -> plan -> validate -> confirm -> run
# ============================================================================
def plan_summary_lines(plan):
    lines = []
    if len(plan.steps) > 1 or plan.unsupported or plan.notes:
        lines.append("EXECUTION PLAN ▸")
        for i, s in enumerate(plan.steps, 1):
            note = f" — {s.note}" if s.note else ""
            lines.append(f"  {i}. {s.tool}{note}")
        for u in plan.unsupported:
            lines.append(f"  [UNSUPPORTED] {u}")
        for n in plan.notes:
            lines.append(f"  [NOTE] {n}")
        lines.append(bar)
    return lines

async def execute_plan(plan, origin):
    lines = plan_summary_lines(plan)
    ok_all = True
    for step in plan.steps:
        res = await REG.run(step.tool, step.params, origin)
        ok_all = ok_all and res.get("ok", True)
        lines += res.get("lines", [])
        data = res.get("data") or {}
        if data.get("channel"):
            ctx_set(origin, last_channel=data["channel"])
        if data.get("user"):
            ctx_set(origin, last_user=data["user"])
    for u in plan.unsupported:
        lines.append(f"[UNSUPPORTED] {u}")
    for n in plan.notes:
        lines.append(f"[NOTE] {n}")
    return {"ok": ok_all, "lines": lines or ["Koi output nahi."], "provider": plan.provider}

async def build_plan(raw, origin):
    """NLU entry. Local classifier first (always available), AI chain as escalation."""
    stripped = re.sub(r"^\s*\/?(ai|jarvis|devil)\b[\s,:.-]*", "", raw.strip(), flags=re.I).strip()
    m = re.match(r"^\/cross\s+(start|stop|reset|status|pause|resume|config)\b", raw.strip(), re.I)
    if m:
        return Plan(steps=[Step("cross_" + m.group(1).lower())], provider="CMD")
    m = re.match(r"^\/(task|monitor)\s+(status|stop|reset)\b", raw.strip(), re.I)
    if m:
        sub = m.group(2).lower()
        if m.group(1).lower() == "monitor" and sub == "stop":
            return Plan(steps=[Step("task_stop", {"kind": "MON"})], provider="CMD")
        return Plan(steps=[Step(f"task_{sub}")], provider="CMD")
    plan = classify(stripped, origin)
    if plan.steps:
        return plan
    ai_plan = await AI.plan(stripped)
    if ai_plan and ai_plan.steps:
        return ai_plan
    plan = Plan(provider=(ai_plan.provider if ai_plan else "LOCAL"))
    if ai_plan:
        plan.unsupported = ai_plan.unsupported
        plan.notes = ai_plan.notes
    return plan

async def handle_command(raw, origin):
    raw = (raw or "").strip()
    if not raw:
        return {"ok": False, "action": "EMPTY", "lines": ["Empty command"]}
    STATE["last_command"] = raw[:120]
    safe_log("CMD", "CMD", f"[{origin}] {raw[:80]}")

    # 1) pending confirmation — origin-bound + expiring
    pend = PENDING_CONFIRM.get(origin)
    if pend:
        if time.time() > pend["expires"]:
            PENDING_CONFIRM.pop(origin, None)
            return {"ok": False, "action": "CONFIRM_EXPIRED",
                    "lines": ["CONFIRMATION EXPIRED ▸ command dobara issue karo"]}
        if re.match(r"^(yes|y|haan|ha|confirm|ok|haan kar do)$", raw, re.I):
            PENDING_CONFIRM.pop(origin, None)
            safe_log("CMD", "CONFIRM", f"{origin} confirmed — executing plan")
            res = await execute_plan(pend["plan"], origin)
            _record(raw, "CONFIRMED", res, origin)
            return res
        PENDING_CONFIRM.pop(origin, None)
        safe_log("WARN", "CONFIRM", f"{origin} declined — aborted")
        return {"ok": True, "action": "ABORTED", "lines": ["ABORTED ▸ koi change nahi hua"]}
    if re.match(r"^(yes|y|no|n|haan|nahi)$", raw, re.I):
        return {"ok": False, "action": "NO_PENDING_CONFIRM",
                "lines": ["Aapki session me koi confirmation pending nahi hai — pehle command do"]}

    # 2) NLU -> plan
    plan = await build_plan(raw, origin)

    if not plan.steps:
        lines = ["I couldn't map this request to an available Telegram/JARVIS action.",
                 "Ye instruction abhi registry ke kisi tool se match nahi hua.",
                 "Available actions ke liye: /AI HELP"]
        for u in plan.unsupported:
            lines.append(f"[UNSUPPORTED] {u}")
        _record(raw, "UNMAPPED", {"ok": False, "lines": lines}, origin, plan.provider)
        return {"ok": False, "action": "UNMAPPED", "provider": plan.provider, "lines": lines}

    # 3) sensitive steps -> one confirmation for the whole plan
    confirm_steps = [s for s in plan.steps if REG.tools.get(s.tool) and REG.tools[s.tool].confirm]
    if confirm_steps:
        summary = plan_summary_lines(plan) + [
            "SENSITIVE ACTION(S):", bar,
            *[f"  ▸ {s.tool}" for s in confirm_steps],
            bar, f"CONFIRM REQUIRED ▸ {CONFIRM_TTL}s me YES reply karo, warna abort."]
        PENDING_CONFIRM[origin] = {"plan": plan, "expires": time.time() + CONFIRM_TTL}
        return {"ok": True, "action": "CONFIRM", "requires_confirmation": True,
                "confirm_expires_in": CONFIRM_TTL, "provider": plan.provider, "lines": summary}

    # 4) execute
    result = await execute_plan(plan, origin)
    _record(raw, "PLAN", result, origin, plan.provider)
    return result

def _record(raw, action, result, origin, provider=None):
    HISTORY.insert(0, {"ts": int(time.time()), "user": raw[:120], "action": action,
                       "ok": bool(result.get("ok")), "provider": provider or result.get("provider", "LOCAL"),
                       "latency_ms": 0, "summary": (result["lines"][0] if result.get("lines") else "")[:120]})
    history_store.save_bg(HISTORY[-50:])
    if not result.get("ok"):
        STATE["last_error"] = (result["lines"][0] if result.get("lines") else "unknown")[:120]
    elif STATE.get("last_error"):
        STATE["last_error"] = None
    state_store.save_bg(STATE)

HISTORY = history_store.load()

# ----------------------------------------------------------------------------
# Diagnostics
# ----------------------------------------------------------------------------
def diagnostics():
    checks = []
    connected, authed = TG.status()
    eng = STATE["engine"]
    cid, ids = ENGINE.source_configured()

    def add(name, status, detail):
        checks.append({"name": name, "status": status, "detail": detail})

    add("Web Server", "PASS", "Quart on 0.0.0.0:$PORT — /health OK")
    add("Telegram Connection", "PASS" if connected else "FAIL",
        f"Live as @{TG.account['username']}" if connected and TG.account else "No client connected")
    add("Session Validity", "PASS" if authed else ("FAIL" if connected else "WARN"),
        "Session authorized — OTP nahi mangta" if authed else "Not authorized" if connected else "No session")
    add("JARVIS Authorization", "PASS" if server_token() else "FAIL",
        "JARVIS_ACCESS_TOKEN configured" if server_token() else "JARVIS_ACCESS_TOKEN missing — fail closed")
    add("Source Configuration", "PASS" if (cid and ids) or STATE["monitor"].get("source") else "WARN",
        f"cross chat {cid} • monitor {STATE['monitor'].get('source') or 'env'}"
        if (cid and ids) or STATE["monitor"].get("source") else "SOURCE NOT AVAILABLE — SOURCE_CHAT_ID / MONITOR_SOURCE unset")
    try:
        probe = DATA / ".probe"
        probe.write_text("ok"); probe.unlink()
        add("JSON Storage", "PASS", "data/ writable — no database")
    except Exception:
        add("JSON Storage", "FAIL", "data/ not writable")
    conf = AI.configured()
    add("AI Providers", "PASS" if conf else "WARN",
        f"NLU chain: {', '.join(conf)}" if conf else "No cloud keys — deterministic local NLU active (full offline)")
    add("Scheduler", "PASS", f"{len([j for j in SCHED.jobs if not j.get('done')])} active jobs ▸ Asia/Kathmandu ▸ recovery on")
    add("Cross Engine", "PASS" if ENGINE.status() == "running" else "WARN",
        f"{ENGINE.status().upper()} ▸ task {ENGINE.tid or '-'}")
    add("Monitor", "PASS" if STATE["monitor"].get("active") else "WARN",
        "Event-based listener live" if STATE["monitor"].get("active") else "Stopped — /AI source monitor start")
    missing = [k for k in ("API_ID", "API_HASH", "SESSION_STRING") if not os.getenv(k)]
    add("Environment", "PASS" if not missing else "WARN",
        "Core env vars present" if not missing else f"Optional env unset (web form works too): {', '.join(missing)}")
    score = round(sum(1 if c["status"] == "PASS" else 0.5 if c["status"] == "WARN" else 0
                      for c in checks) / len(checks) * 100)
    safe_log("OK" if score >= 85 else "WARN", "DIAG", f"Diagnostics score {score}%")
    return {"ok": True, "score": score, "checks": checks, "ran_at": int(time.time())}

# ----------------------------------------------------------------------------
# Scheduler (KTM) — persisted, recovered, no double-fire
# ----------------------------------------------------------------------------
class Scheduler:
    def __init__(self):
        self.jobs = jobs_store.load()
        self.fired = set(j["id"] for j in self.jobs if j.get("done"))

    def add(self, action, run_at, label):
        job = {"id": uuid.uuid4().hex[:6], "action": action, "run_at": float(run_at),
               "label": str(label), "created_at": time.time(), "done": False}
        self.jobs.append(job)
        jobs_store.save_bg(self.jobs[-40:])
        safe_log("CMD", "SCHEDULER", f"Job [{job['id']}] ▸ {action} at {fmt_kt(run_at)}")
        return job

    def cancel(self, job_id):
        for j in self.jobs:
            if j["id"] == job_id and not j.get("done"):
                j["done"] = True
                jobs_store.save_bg(self.jobs[-40:])
                safe_log("CMD", "SCHEDULER", f"Job [{job_id}] cancelled")
                return True
        return False

    async def fire(self, job):
        if job["id"] in self.fired:
            return
        self.fired.add(job["id"])
        job["done"] = True
        jobs_store.save_bg(self.jobs[-40:])
        safe_log("CMD", "SCHEDULER", f"Firing [{job['id']}] ▸ {job['action']}")
        if job["action"] == "START":
            await ENGINE.start()
        elif job["action"] == "STOP":
            ENGINE.stop()

    async def recover(self):
        now = time.time()
        for j in self.jobs:
            if not j.get("done") and j["run_at"] <= now:
                safe_log("WARN", "SCHEDULER", f"Recovering overdue job [{j['id']}]")
                await self.fire(j)

    async def loop(self):
        while True:
            await asyncio.sleep(2)
            now = time.time()
            for j in list(self.jobs):
                if not j.get("done") and j["run_at"] <= now:
                    await self.fire(j)

SCHED = Scheduler()

# ----------------------------------------------------------------------------
# Web API (unchanged contract for index.html)
# ----------------------------------------------------------------------------
app = Quart(__name__)

@app.route("/")
async def home():
    return await send_file(BASE / "index.html")

@app.route("/health")
async def health():
    return jsonify({"status": "ok"}), 200

@app.route("/api/status")
async def api_status():
    eng = STATE["engine"]
    connected, authed = TG.status()
    return jsonify({
        "ok": True, "backend": True, "jarvis": "ONLINE",
        "now_kt": ktm_now().strftime("%d %b %Y %I:%M:%S %p NPT"),
        "auth_configured": bool(server_token()),
        "telegram": {"connected": connected, "authorized": authed,
                     "account": scrub(TG.account) if TG.account else None},
        "engine": {"status": eng["status"], "queue": len(eng["queue"]),
                   "deferred": len(eng["deferred"]), "processed": eng["processed"],
                   "failed": eng["failed"],
                   "flood_wait_in": max(0, int((eng.get("flood_wait_until") or 0) - time.time())),
                   "last_event": eng.get("last_event"),
                   "source_configured": bool(ENGINE.source_configured()[0] and ENGINE.source_configured()[1])},
        "ai": {"provider": AI.last_provider, "calls": AI.total, "configured": AI.configured()},
        "scheduler": {"active": len([j for j in SCHED.jobs if not j.get("done")]),
                      "jobs": [{"id": j["id"], "action": j["action"], "label": j["label"],
                                "run_at": j["run_at"], "done": bool(j.get("done"))} for j in SCHED.jobs[-10:]]},
        "last_command": STATE.get("last_command"),
        "last_error": STATE.get("last_error"),
    })

@app.route("/api/diagnostics")
async def api_diag():
    return jsonify(diagnostics())

@app.route("/api/telegram/connect", methods=["POST"])
async def api_connect():
    body = await request.get_json(silent=True) or {}
    try:
        api_id = int(str(body.get("api_id", "")).strip() or os.getenv("API_ID", "0"))
    except ValueError:
        return jsonify({"ok": False, "error": "Invalid API ID — numeric, from my.telegram.org"}), 400
    api_hash = str(body.get("api_hash", "")).strip() or os.getenv("API_HASH", "")
    session_string = str(body.get("session_string", "")).strip() or os.getenv("SESSION_STRING", "")
    if not api_id or not api_hash or not session_string:
        return jsonify({"ok": False, "error": "API_ID, API_HASH and SESSION_STRING are required"}), 400
    ok, payload = await TG.connect_session(api_id, api_hash, session_string)
    if not ok:
        safe_log("ERROR", "TELEGRAM", f"Session login rejected: {payload}")
        return jsonify({"ok": False, "error": payload}), 401
    return jsonify({"ok": True, "account": scrub(TG.account)})

@app.route("/api/telegram/send_code", methods=["POST"])
async def api_send_code():
    body = await request.get_json(silent=True) or {}
    try:
        api_id = int(str(body.get("api_id", "")).strip() or os.getenv("API_ID", "0"))
    except ValueError:
        return jsonify({"ok": False, "error": "Invalid API ID — numeric, from my.telegram.org"}), 400
    api_hash = str(body.get("api_hash", "")).strip() or os.getenv("API_HASH", "")
    phone = str(body.get("phone", "")).strip()
    if not api_id or not api_hash:
        return jsonify({"ok": False, "error": "API_ID and API_HASH are required"}), 400
    if not re.match(r"^\+\d{8,15}$", phone):
        return jsonify({"ok": False, "error": "Phone must be international format, e.g. +97798XXXXXXXX"}), 400
    ok, payload = await TG.send_code(api_id, api_hash, phone)
    if not ok:
        return jsonify({"ok": False, "error": payload}), 400
    return jsonify({"ok": True, **payload})

@app.route("/api/telegram/verify_code", methods=["POST"])
async def api_verify_code():
    body = await request.get_json(silent=True) or {}
    login_id, code = str(body.get("login_id", "")), str(body.get("code", "")).strip()
    if not login_id or not code:
        return jsonify({"ok": False, "error": "login_id and OTP code are required"}), 400
    ok, payload = await TG.verify_code(login_id, code)
    if not ok:
        return jsonify({"ok": False, "error": payload}), 400
    return jsonify({"ok": True, **payload})

@app.route("/api/telegram/verify_2fa", methods=["POST"])
async def api_verify_2fa():
    body = await request.get_json(silent=True) or {}
    login_id, password = str(body.get("login_id", "")), str(body.get("password", ""))
    if not login_id or not password:
        return jsonify({"ok": False, "error": "login_id and 2FA password are required"}), 400
    ok, payload = await TG.verify_2fa(login_id, password)
    if not ok:
        return jsonify({"ok": False, "error": payload}), 400
    return jsonify({"ok": True, **payload})

@app.route("/api/telegram/disconnect", methods=["POST"])
@require_token
async def api_disconnect():
    await TG.disconnect(clear=True)
    return jsonify({"ok": True})

@app.route("/api/jarvis/auth", methods=["POST"])
async def api_auth():
    token = server_token()
    if not token:
        return jsonify({"ok": False, "error": "JARVIS_ACCESS_TOKEN not configured on server"}), 503
    body = await request.get_json(silent=True) or {}
    if hmac.compare_digest(str(body.get("token", "")), token):
        return jsonify({"ok": True, "access": "ENABLED"})
    safe_log("WARN", "AUTH", "Rejected web unlock — invalid token")
    return jsonify({"ok": False, "error": "ACCESS DENIED — invalid token (fail closed)"}), 401

@app.route("/api/jarvis/command", methods=["POST"])
@require_token
async def api_command():
    body = await request.get_json(silent=True) or {}
    cmd = str(body.get("command", "")).strip()
    if not cmd:
        return jsonify({"ok": False, "error": "Empty command"}), 400
    result = await handle_command(cmd, origin=caller_origin())
    if "action" not in result:
        result["action"] = "PLAN"
    return jsonify(scrub(result))

@app.route("/api/start", methods=["POST"])
@require_token
async def api_start():
    r = await ENGINE.start()
    return jsonify({"ok": r.get("ok", True), "lines": r.get("lines", [])})

@app.route("/api/stop", methods=["POST"])
@require_token
async def api_stop():
    return jsonify({"ok": True, "lines": ENGINE.stop().get("lines", [])})

@app.route("/api/reset", methods=["POST"])
@require_token
async def api_reset():
    body = await request.get_json(silent=True) or {}
    origin = caller_origin()
    if str(body.get("confirm", "")).lower() != "yes":
        return jsonify({"ok": True, "requires_confirmation": True, "confirm_expires_in": CONFIRM_TTL,
                        "lines": [f"CONFIRM REQUIRED ▸ reset clears queue/counters ({CONFIRM_TTL}s). Send {{'confirm':'yes'}}."]})
    PENDING_CONFIRM.pop(origin, None)
    r = await ENGINE.reset()
    return jsonify({"ok": True, "lines": r.get("lines", [])})

@app.route("/api/scheduler/cancel", methods=["POST"])
@require_token
async def api_sched_cancel():
    body = await request.get_json(silent=True) or {}
    jid = str(body.get("id", ""))
    if SCHED.cancel(jid):
        return jsonify({"ok": True, "message": f"CANCELLED ▸ [{jid}]"})
    return jsonify({"ok": False, "error": f"JOB NOT FOUND ▸ {jid}"}), 404

@app.route("/api/logs", methods=["GET"])
@require_token
async def api_logs():
    return jsonify({"ok": True, "logs": list(LOG_RING)[:120]})

@app.route("/api/history", methods=["GET"])
@require_token
async def api_history():
    return jsonify({"ok": True, "history": HISTORY[:40]})

@app.errorhandler(404)
async def not_found(_e):
    return jsonify({"ok": False, "error": "Not found"}), 404

@app.errorhandler(Exception)
async def on_error(e):
    log.error("HTTP error: %s", type(e).__name__)
    safe_log("ERROR", "HTTP", f"Request error ({type(e).__name__}) — server alive")
    return jsonify({"ok": False, "error": "Internal error — server is alive, secrets are safe"}), 500

# ----------------------------------------------------------------------------
# Lifecycle
# ----------------------------------------------------------------------------
@app.before_serving
async def boot():
    log.info("BOOT DEVIL JARVIS ▸ %d tools (NLU whitelist) ▸ clock Asia/Kathmandu", len(REG.tools))
    safe_log("INFO", "BOOT", f"JARVIS online — {len(REG.tools)} tools, NLU armed (local + provider chain)")
    loop = asyncio.get_running_loop()
    loop.create_task(SCHED.loop())
    ENGINE.ensure_task()
    await SCHED.recover()
    if all(os.getenv(k) for k in ("API_ID", "API_HASH", "SESSION_STRING")):
        ok, payload = await TG.connect_session(int(os.environ["API_ID"]),
                                               os.environ["API_HASH"], os.environ["SESSION_STRING"])
        log.info("BOOT env auto-connect: %s", "OK" if ok else payload)
        safe_log("INFO" if ok else "WARN", "TELEGRAM", f"Env auto-connect: {'OK' if ok else payload}")
    if not server_token():
        log.warning("BOOT JARVIS_ACCESS_TOKEN not set — protected endpoints refuse (fail closed)")
        safe_log("WARN", "BOOT", "JARVIS_ACCESS_TOKEN missing — fail-closed mode")
    log.info("BOOT ONLINE ▸ /health ready")

@app.after_serving
async def shutdown():
    log.info("SHUTDOWN — engine stop + Telegram disconnect")
    try:
        ENGINE.eng["status"] = "stopped"
        state_store.save_bg(STATE)
        await TG.disconnect(clear=False)
    except Exception:
        pass

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.getenv("PORT", "5000")))
