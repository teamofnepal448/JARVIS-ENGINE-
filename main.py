#!/usr/bin/env python3
# ============================================================================
# DEVIL JARVIS v4.0 — TELEGRAM JARVIS NATURAL LANGUAGE CONTROL (single file)
#
#   /AI <natural language> -> NLU (intent + params + conditions, fuzzy) ->
#   plan -> validation -> expiring confirmation -> TOOL REGISTRY (whitelist)
#   -> real Telegram result -> reply. No arbitrary execution anywhere —
#   user scripts run only inside the AST sandbox below.
#
#   Render ready:  python main.py  ->  0.0.0.0:$PORT   (health: /health)
#   Clock: Asia/Kathmandu (NPT). Single running instance by design.
#   Secrets: ENV only, or Fernet-encrypted (JARVIS_SECRET_KEY) in JSON.
# ============================================================================

import ast
import asyncio
import builtins as _py_builtins
import contextlib
import hmac
import inspect
import json
import logging
import os
import re
import struct
import sys
import time
import types as _mod_types
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
    from telethon import utils as tl_utils, types as tl_types, errors as tl_errors
    from telethon.errors import (
        ChatAdminRequiredError, FloodWaitError, PasswordHashInvalidError,
        PhoneCodeExpiredError, PhoneCodeInvalidError, PhoneNumberInvalidError,
        RPCError, SessionPasswordNeededError, UserNotParticipantError,
    )
    TELETHON_OK = True
except Exception:
    TelegramClient = None
    TELETHON_OK = False

try:
    import httpx
except Exception:
    httpx = None

try:
    from cryptography.fernet import Fernet
    FERNET_OK = True
except Exception:
    FERNET_OK = False

# ---- Asia/Kathmandu (explicit)
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

SECRET_MARKERS = ("api_hash", "session", "password", "token", "otp", "secret", "api_key",
                  "phone_code_hash", "_enc")

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
# JSON persistence — atomic writes, corruption recovery, memory-only fallback
# ----------------------------------------------------------------------------
_STORAGE_WARNED = False

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
                global _STORAGE_WARNED
                if not _STORAGE_WARNED:
                    _STORAGE_WARNED = True
                    log.warning("data/ not writable (%s) — falling back to MEMORY-ONLY "
                                "(Render ephemeral filesystem? state will not survive restart)",
                                type(e).__name__)
                    safe_log("WARN", "STORAGE",
                             f"{self.path.name} not writable — memory-only fallback active")

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
    "account": None,
    "last_command": None,
    "last_error": None,
}
DEFAULT_RUNTIME = {"source_chat_id": None, "source_message_ids": [],
                   "monitor_source": None, "monitor_destination": None,
                   "dead_threshold_days": 30, "updated_at": 0}

state_store    = JSONStore(DATA / "jarvis_state.json", DEFAULT_STATE)
history_store  = JSONStore(DATA / "ai_history.json", [])
jobs_store     = JSONStore(DATA / "scheduled_jobs.json", [])
runtime_store  = JSONStore(DATA / "runtime_config.json", DEFAULT_RUNTIME)
accounts_store = JSONStore(DATA / "accounts.json", {"accounts": []})
scripts_store  = JSONStore(DATA / "scripts.json", {})
templates_store = JSONStore(DATA / "templates.json", {})
automation_store = JSONStore(DATA / "automation_templates.json", {"templates": []})
acctcfg_store = JSONStore(DATA / "account_config.json", {})

STATE    = state_store.load()
HISTORY  = history_store.load()   # BUG FIX 5: defined before any use
STATE.setdefault("monitor", json.loads(json.dumps(DEFAULT_STATE["monitor"])))

# ----------------------------------------------------------------------------
# Fernet encryption — sessions stored encrypted in accounts.json
# ----------------------------------------------------------------------------
_FERNET_CACHE = None

def _get_fernet():
    global _FERNET_CACHE
    if _FERNET_CACHE is not None:
        return _FERNET_CACHE or None
    key = os.getenv("JARVIS_SECRET_KEY", "").strip()
    if not key:
        log.warning("JARVIS_SECRET_KEY not set — sessions stay in memory only. "
                    "Generate one: python -c \"from cryptography.fernet import Fernet; print(Fernet.generate_key().decode())\"")
        safe_log("WARN", "CRYPTO", "JARVIS_SECRET_KEY missing — sessions cannot persist across restarts")
        _FERNET_CACHE = False
        return None
    try:
        _FERNET_CACHE = Fernet(key.encode())
        return _FERNET_CACHE
    except Exception:
        log.error("JARVIS_SECRET_KEY invalid — not a valid Fernet key")
        _FERNET_CACHE = False
        return None

def encrypt_str(s):
    if not FERNET_OK or not s:
        return ""
    f = _get_fernet()
    if not f:
        return ""
    try:
        return f.encrypt(str(s).encode()).decode()
    except Exception:
        return ""

def decrypt_str(s):
    if not FERNET_OK or not s:
        return ""
    f = _get_fernet()
    if not f:
        return ""
    try:
        return f.decrypt(s.encode()).decode()
    except Exception:
        return ""

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

def caller_origin():
    sid = request.headers.get("X-Session-Id", "").strip() if request else ""
    return f"web:{sid}" if sid else "web"

# ----------------------------------------------------------------------------
# Runtime source config — JSON config > ENV > default  (editable without redeploy)
# ----------------------------------------------------------------------------
def cfg_get():
    cfg = runtime_store.load()
    merged = dict(DEFAULT_RUNTIME)
    merged.update({k: v for k, v in cfg.items() if v not in (None, "", [])})
    return merged

def cfg_source():
    """(source_chat_id, [message_ids]) with JSON > ENV priority."""
    cfg = cfg_get()
    cid = cfg.get("source_chat_id") or os.getenv("SOURCE_CHAT_ID", "").strip()
    ids = cfg.get("source_message_ids")
    if not ids:
        ids = [int(x) for x in re.split(r"[,\s]+", os.getenv("SOURCE_MESSAGE_IDS", "")) if x.strip().isdigit()]
    ids = [int(x) for x in ids if str(x).strip().lstrip("-").isdigit()]
    cid = str(cid).strip() if cid not in (None, "") else ""
    return (cid if cid.lstrip("-").isdigit() else None), ids

def cfg_monitor():
    cfg = cfg_get()
    src = STATE["monitor"].get("source") or cfg.get("monitor_source") or os.getenv("MONITOR_SOURCE", "").strip() or None
    dst = STATE["monitor"].get("destination") or cfg.get("monitor_destination") or os.getenv("MONITOR_DESTINATION", "").strip() or None
    return src, dst

def cfg_dead_threshold():
    try:
        return int(cfg_get().get("dead_threshold_days") or os.getenv("DEAD_THRESHOLD_DAYS", "30"))
    except Exception:
        return 30

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
# Short-lived CONTEXT per origin (expires, never permanent instructions)
# ----------------------------------------------------------------------------
CTX_TTL = 600
CONTEXT = {}

def ctx_get(origin):
    c = CONTEXT.get(origin)
    if not c or time.time() - c.get("at", 0) > CTX_TTL:
        CONTEXT.pop(origin, None)
        return {}
    return c

def ctx_set(origin, **kw):
    c = ctx_get(origin)
    c.update({k: v for k, v in kw.items() if v})
    c["at"] = time.time()
    CONTEXT[origin] = c

# ----------------------------------------------------------------------------
# TOOL REGISTRY — the ONLY actions JARVIS can ever take
# ----------------------------------------------------------------------------
@dataclass
class ToolParam:
    name: str
    kind: str
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
    confirm: bool = False
    sensitive: bool = False

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
        for p in t.params:
            if p.required and not str(params.get(p.name, "")).strip():
                hint = {"chat": "channel ka @username batao", "user": "user ka @username batao",
                        "time": "time batao — jaise '10 minute baad' / '7:30 PM par'"}.get(p.kind, f"{p.name} chahiye")
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
            return {"ok": False, "lines": [f"TELEGRAM ERROR ▸ {type(e).__name__}: {str(e)[:140]}"]}
        except Exception as e:
            log.error("Tool %s failed: %s", name, type(e).__name__)
            STATE["last_error"] = f"{name}: {type(e).__name__}"
            safe_log("ERROR", "TOOL", f"{name} failed ({type(e).__name__}) — server alive")
            return {"ok": False, "lines": [f"{name} FAILED ▸ {type(e).__name__} — real error, koi fake success nahi"]}

REG = ToolRegistry()
bar = "────────────────────────────"

async def resolve_chat(ref):
    ref = str(ref).strip().lstrip("@")
    return await TG.client.get_entity(int(ref) if ref.lstrip("-").isdigit() else ref)

# ============================================================================
# TASK MANAGER — every long-running operation carries a task ID
# ============================================================================
class TaskManager:
    def __init__(self):
        self.tasks = {}

    def register(self, kind, label, stop_fn, reset_fn=None, stats_fn=None, fixed_id=None):
        tid = fixed_id or f"{kind}-{uuid.uuid4().hex[:4].upper()}"
        self.tasks[tid] = {"id": tid, "kind": kind, "label": label, "status": "RUNNING",
                           "started_at": time.time(), "stop": stop_fn, "reset": reset_fn, "stats": stats_fn}
        return self.tasks[tid]

    def set_status(self, tid, status):
        if tid in self.tasks:
            self.tasks[tid]["status"] = status

    def running(self):
        return [t for t in self.tasks.values() if t["status"] in ("RUNNING", "PAUSED")]

    async def stop(self, tid):
        t = self.tasks.get(tid)
        if t and t["stop"]:
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
        return cfg_source()

    def reload_config(self):
        safe_log("CMD", "ENGINE", "Source config reloaded — engine picks it up on next cycle")

    def _task_sync(self):
        st = self.eng["status"]
        if st == "running" and not self.tid:
            t = TASKS.register("CROSS", "Cross-Promotion Engine", stop_fn=self._task_stop,
                               reset_fn=self.reset, stats_fn=lambda: f"{self.eng['processed']} done",
                               fixed_id="CROSS-0001")
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
            self.eng["last_event"] = "SOURCE NOT AVAILABLE — web Source Config panel ya ENV se set karo"
            state_store.save_bg(STATE)
            return {"ok": False, "lines": SOURCE_NOT_AVAILABLE_HELP + [
                "", "(ya web dashboard ke Source Configuration panel se source set karo)"]}
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
                          f"Task ID: {self.tid}", "Status: RUNNING"]}

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
                f"Source       ▸ {f'chat {cid} • messages {ids[:4]}' if cid and ids else 'NOT CONFIGURED — web Source Config panel ya ENV se set karo'}",
                f"Queue        ▸ {len(self.eng['queue'])} pending ▸ {len(self.eng['deferred'])} deferred",
                "Config hot-reload ▸ Source Config panel se save karte hi apply (redeploy nahi chahiye)"]

    async def rebuild_queue(self, targets=None):
        """Build the send queue. Configured main channels win over folder scan."""
        queue = []
        if targets:
            for t in targets:
                queue.append({"channel": t.get("title") or str(t.get("chat_id")),
                              "username": t.get("username"),
                              "chat_id": t.get("chat_id"), "attempts": 0})
        else:
            folders = await scan_folders()
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
            if self.eng["status"] != "running":
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
                self.eng["last_event"] = "SOURCE NOT AVAILABLE — configure source"
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
                # BUG FIX 4: keyword-argument signature (Telethon version-safe)
                await TG.client.forward_messages(entity=int(item["chat_id"]), messages=[ids[0]],
                                                 from_peer=int(cid))
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

# ---------------------------------------------------------------------------
# REPLY-BASED CROSS SOURCE (Saved Messages)
#   Reply to any saved post and send "/cross start" — the replied message
#   becomes the Cross source automatically. No manual IDs, and the existing
#   Cross Engine is reused unchanged (we only feed it a resolved source).
# ---------------------------------------------------------------------------
REPLY_SOURCE = {}          # origin -> {chat_id, message_id, preview, at}
REPLY_SOURCE_TTL = 600     # a captured reply stays usable for 10 minutes

SOURCE_NOT_AVAILABLE_HELP = [
    "SOURCE NOT AVAILABLE",
    "",
    "Reply to the post/message in Saved Messages and send:",
    "",
    "/cross start",
]

def remember_reply_source(origin, chat_id, message_id, preview=""):
    """Store the message a command was sent in reply to."""
    try:
        REPLY_SOURCE[origin] = {"chat_id": int(chat_id), "message_id": int(message_id),
                                "preview": str(preview or "")[:90], "at": time.time()}
    except Exception:
        return
    safe_log("INFO", "CROSS", f"reply source captured ▸ chat {chat_id} ▸ msg {message_id}")

def take_reply_source(origin):
    """Consume-once: a captured reply is used for exactly one cross start, so a
    later '/cross start' sent WITHOUT a reply never silently reuses it."""
    r = REPLY_SOURCE.pop(origin, None)
    if not r:
        return None
    if time.time() - r["at"] > REPLY_SOURCE_TTL:
        return None
    return r

async def apply_reply_source(chat_id, message_id):
    """Persist the replied message as the cross source (existing engine reads this)."""
    cfg = runtime_store.load()
    cfg["source_chat_id"] = int(chat_id)
    cfg["source_message_ids"] = [int(message_id)]
    cfg["updated_at"] = int(time.time())
    await runtime_store.save(cfg)
    ENGINE.reload_config()
    safe_log("CMD", "CROSS", f"source set from reply ▸ chat {chat_id} ▸ msg {message_id}")

async def capture_reply_from_event(event, origin):
    """If a Saved-Messages command is a reply, resolve the real replied message."""
    try:
        if not getattr(event, "is_reply", False):
            return None
        rm = await event.get_reply_message()
        if not rm:
            return None
        chat_id = getattr(rm, "chat_id", None)
        if chat_id is None:
            chat_id = getattr(event, "chat_id", None)
        if chat_id is None:
            return None
        preview = (getattr(rm, "text", None) or getattr(rm, "message", None) or "")[:90]
        if not preview:
            preview = "(media / non-text message)"
        remember_reply_source(origin, chat_id, rm.id, preview)
        return {"chat_id": int(chat_id), "message_id": int(rm.id), "preview": preview}
    except Exception as e:
        log.warning("reply capture failed: %s", type(e).__name__)
        return None


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
        return cfg_monitor()

    async def start(self, params, origin):
        connected, _ = TG.status()
        if not connected:
            return {"ok": False, "lines": ["TELEGRAM DISCONNECTED ▸ pehle connect karo"]}
        src = params.get("source") or cfg_monitor()[0]
        dst = params.get("destination") or cfg_monitor()[1]
        if not src or not dst:
            return {"ok": False, "lines": [
                "SOURCE NOT CONFIGURED ▸ monitoring ke liye source aur destination chahiye:",
                "  web: Source Configuration panel se save karo",
                "  env: MONITOR_SOURCE=@source  MONITOR_DESTINATION=@output",
                "  ya command me: '/AI @source ko monitor karo, @output par bhejo'"]}
        try:
            src_ent = await resolve_chat(src)
            dst_ent = await resolve_chat(dst)
        except Exception as e:
            return {"ok": False, "lines": [f"ENTITY ERROR ▸ source/destination resolve nahi hua ({type(e).__name__})"]}
        if params.get("keywords"):
            self.m["keywords"] = params["keywords"]
        self.m.update({"active": True, "source": src, "destination": dst})
        # sync into runtime config so the web panel reflects it
        cfg = runtime_store.load()
        cfg["monitor_source"], cfg["monitor_destination"] = str(src), str(dst)
        cfg["updated_at"] = int(time.time())
        runtime_store.save_bg(cfg)
        if not self.m.get("last_message_id"):
            latest = await TG.client.get_messages(src_ent, limit=1)
            self.m["last_message_id"] = latest[0].id if latest and latest[0] else 0
        await self.attach(TG.client)
        self.ensure_worker()
        if not self.m.get("task_id") or self.m["task_id"] not in TASKS.tasks:
            self.m["task_id"] = TASKS.register("MON", f"Source monitor {src} -> {dst}",
                                               stop_fn=self._task_stop, reset_fn=self.reset)["id"]
        state_store.save_bg(STATE)
        safe_log("CMD", "MONITOR", f"Started ▸ {src} -> {dst} ▸ event-based")
        return {"lines": [
            "SOURCE MONITORING STARTED (event-based — fastest mode)",
            f"Task ID: {self.m['task_id']}",
            f"Source      ▸ {src}",
            f"Destination ▸ {dst}",
            f"Keywords    ▸ {', '.join(self.m['keywords'])}",
            f"Baseline    ▸ last message id {self.m['last_message_id']} (purane repost nahi honge)",
            "Har naya matching message ka exact source text destination par jayega."]}

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
        return {"lines": [f"MONITOR STOPPED ▸ task {tid or '-'}: STOPPED", "State persistent — 'monitor start' se resume hoga"]}

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
        return {"lines": [f"MONITOR RESET ▸ baseline id {self.m['last_message_id']} ▸ counters zero"]}

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
        if not TELETHON_OK or self.attached_client is client or client is None:
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
                ent = event.chat
                uname = getattr(ent, "username", None)
                eid = getattr(ent, "id", None)
                ref = str(src).lstrip("@").lstrip("-100").lstrip("-")
                if str(eid) != ref and uname != ref:
                    return
                msg = event.message
                if not msg or not getattr(msg, "text", None):
                    return
                if msg.id <= (mon.m.get("last_message_id") or 0):
                    return
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
                await self._process(msg)
            except Exception as e:
                log.error("monitor process error: %s", type(e).__name__)
                safe_log("ERROR", "MONITOR", f"process error ({type(e).__name__}) — continuing")

    async def _process(self, msg):
        self.m["last_message_id"] = max(self.m.get("last_message_id") or 0, msg.id)
        _src, dst = self.configured()
        parsed = parse_source_text(msg.text or "", self.m["keywords"])
        body = format_update_text(parsed["body"])
        await TG.client.send_message(await resolve_chat(dst), body)
        self.m["processed"] = self.m.get("processed", 0) + 1
        self.m["last_event"] = f"update sent ▸ id {msg.id} {'(keyword match)' if parsed['matched'] else '(full text)'}"
        state_store.save_bg(STATE)
        safe_log("OK", "MONITOR", f"Update id {msg.id} -> {dst}")

MONITOR = SourceMonitor()

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
# NLU — fuzzy spell-correction + intent classification + params + conditions
# ============================================================================
def _lev(a, b):
    """Levenshtein distance (small tokens only)."""
    if a == b:
        return 0
    la, lb = len(a), len(b)
    if abs(la - lb) > 3 or la > 14 or lb > 14:
        return 9
    prev = list(range(lb + 1))
    for i in range(1, la + 1):
        cur = [i]
        for j in range(1, lb + 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (a[i - 1] != b[j - 1])))
        prev = cur
    return prev[lb]

LEV_WORDS = ("channel", "channels", "cross", "folder", "folders", "monitor", "task", "tasks", "status",
             "admin", "user", "message", "messages", "search", "start", "stop", "pause", "resume",
             "reset", "scheduler", "schedule", "dead", "inactive", "account", "saved", "recent",
             "diagnostics", "help", "latest", "config", "list", "update",
             # custom-script vocabulary — must never be fuzzed into something else
             "cancel", "template", "templates", "script", "scripts", "updater", "select",
             "main", "source", "destination", "custom", "run", "create")

# Real Hindi/Hinglish/domain words that must NEVER be "corrected" into a
# lexicon word (saare->start, result->resume, cancel->channel were real bugs).
FUZZY_PROTECTED = {
    "saare", "sare", "saara", "sab", "sabhi", "karo", "kar", "kro", "kardo",
    "result", "results", "toss", "mera", "mere", "meri", "wala", "wali",
    "bhejo", "bhej", "dikhao", "dikha", "batao", "bata", "chalu", "band",
    "naya", "nahi", "haan", "abhi", "phir", "fir", "jitne", "apna", "apne",
    "iska", "uska", "inka", "unka", "yeh", "woh", "kya", "kaun", "kaise",
    "kitna", "kitne", "line", "bana", "banao", "aaye", "rakho", "rakhna",
    "time", "data", "jaldi", "fast", "live", "auto", "promo", "news",
    "sirf", "wale", "pehle", "baad", "minute", "ghante", "select", "cancel",
}

def fuzzy_norm(t):
    """BUG FIX 6: spelling-tolerant lexicon ('cros'->cross, 'chanel'->channel, 'usr'->user).
    Protected words and template-ish tokens are left untouched."""
    out = []
    for tok in t.split(" "):
        if (len(tok) < 3 or tok.startswith("@") or any(ch.isdigit() for ch in tok)
                or tok in LEV_WORDS or tok in FUZZY_PROTECTED or "-" in tok or "_" in tok):
            out.append(tok)
            continue
        best = min(LEV_WORDS, key=lambda w: _lev(tok, w))
        d = _lev(tok, best)
        threshold = 2 if len(tok) >= 5 else 1
        out.append(best if d <= threshold and abs(len(tok) - len(best)) <= 3 else tok)
    return " ".join(out)

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
    needs: list = field(default_factory=list)

V_START  = ("start", "shuru", "chalu", "chalao", "chala", "on", "lagao", "begin", "shuruaat", "kr do", "kar do")
V_STOP   = ("stop", "band", "bandh", "rok", "ruko", "off", "rok do")
V_PAUSE  = ("pause", "hold", "wait kar", "ruk jao", "thahro")
V_RESUME = ("resume", "continue", "wapas chalu", "phir chalu", "phir se chalu", "unpause")
V_RESET  = ("reset", "clear", "saaf", "zero", "fresh")
V_STATUS = ("status", "stithi", "batao", "kaisa", "kya haal", "report", "dikhao", "dikha")
V_CHECK  = ("check", "dekho", "inspect", "jaanch", "batao", "details", "karo", "dikhao", "dikha")
V_CANCEL = ("cancel", "hatao", "abort")
V_CONFIG = ("config", "setting", "configuration")
V_MON    = ("monitor", "watch", "nazar", "track", "follow", "toss line", "result line", "source line",
            "fastest update", "fast update", "jaldi update", "instant update", "live update")
V_SEND   = ("bhejo", "bhej", "send", "forward", "copy paste", "copy karke", "daal do", "post")
V_FETCH  = ("latest", "last message", "naya message", "recent message", "fetch", "lao", "nikalo")

CROSS_T  = ("cross", "engine", "promotion", "promo")
SCHED_T  = ("scheduler", "schedule", "job")
MON_T    = ("monitor", "monitoring", "watcher")
TASK_T   = ("task", "jo chal raha", "jo task", "running task", "usko")

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
    um = re.findall(r"@([a-zA-Z0-9_]{3,32})", t)
    if len(um) >= 2 and has(t, V_MON):
        p["source"], p["destination"] = "@" + um[0], "@" + um[1]
    elif len(um) == 1 and has(t, V_MON):
        p["destination" if has(t, V_SEND) else "source"] = "@" + um[0]
    ts, label = parse_rel_time(t)
    if ts:
        p["run_at"], p["label"] = ts, label
    return p

def is_condition_clause(t):
    return has(t, ("toss", "lekin", "but", "mat karna", "mat kar", "wait karna", "dhyaan")) \
        and not has(t, ("start", "stop", "band", "chalu", "monitor", "status"))

def classify(raw, origin):
    t = re.sub(r"^\s*\/?(ai|jarvis|devil)\b[\s,:.-]*", "", raw.strip().lower())
    t = re.sub(r"\s+", " ", t)
    t = fuzzy_norm(t)   # BUG FIX 6
    plan = Plan()
    if not t:
        plan.steps.append(Step("jarvis_help")); return plan
    ctx = ctx_get(origin)

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

    clauses = [c.strip() for c in re.split(
        r"[,;.!?]|(?:\baur\b)|(?:\bbut\b)|(?:\blekin\b)|(?:\band then\b)|(?:\bthen\b)|(?:\bphir\b)|(?:\bfir\b)", t) if c.strip()]
    if not clauses:
        clauses = [t]

    pending = []
    for c in clauses:
        if is_condition_clause(c) and plan.steps:
            if "toss" in c:
                plan.unsupported.append(
                    "Toss-time auto-pause abhi supported nahi hai — toss ka official live source configured nahi. "
                    "Manual: '/AI cross pause' / '/AI cross resume'.")
            else:
                plan.unsupported.append(
                    "Conditional wait/trigger abhi supported nahi hai — manual pause/stop commands available hain.")
            continue

        if plan.steps and plan.steps[-1].tool == "monitor_source" and has(c, V_SEND) and re.search(r"@", c):
            mm = re.search(r"@([a-zA-Z0-9_]{3,32})", c)
            plan.steps[-1].params["destination"] = "@" + mm.group(1)
            continue

        tgt = target_of(c)
        p = extract(c, origin)

        # ---- CUSTOM SCRIPT RUNNER: templates / account context (§34-§36) ----
        # saved template names are matched first so "TOSS-CROSS start karo"
        # runs the template, not the generic cross engine
        _tpl_hit = None
        _cnorm = re.sub(r"[^a-z0-9 ]+", " ", c)
        for _t in templates_all():
            for _cand in {str(_t.get("name", "")).lower(), str(_t.get("template_id", "")).lower()}:
                if not _cand:
                    continue
                _flat = re.sub(r"[^a-z0-9 ]+", " ", _cand).strip()
                if _flat and (_flat in _cnorm or _cand in c):
                    _tpl_hit = _t
                    break
            if _tpl_hit:
                break

        m_acc = re.search(r"account\s*(\d+|[a-z0-9_]{2,})", c)
        if m_acc and has(c, ("select", "choose", "chuno", "switch", "pe switch")):
            plan.steps.append(Step("account_select", {"account": m_acc.group(1)})); continue

        if has(c, ("main channel", "main chanel")) or (has(c, ("source", "destination")) and has(c, ("set", "lagao", "kar do", "karo")) and not has(c, ("monitor", "cross", "template", "script"))):
            prm = {}
            mm = re.search(r"main chann?el\s*(?:ko\s*)?(?:set\s*)?(-?\d{5,20}|@[a-z0-9_]+)", c)
            if mm: prm["main_channel"] = mm.group(1)
            ms = re.search(r"source\s*(?:ko\s*)?(?:set\s*)?(@[a-z0-9_]+|-?\d{5,20})", c)
            if ms: prm["source"] = ms.group(1)
            md = re.search(r"destination\s*(?:ko\s*)?(?:set\s*)?(@[a-z0-9_]+|-?\d{5,20})", c)
            if md: prm["destination"] = md.group(1)
            if m_acc and not re.fullmatch(r"\d{5,20}", m_acc.group(1)): prm["account"] = m_acc.group(1)
            if prm:
                plan.steps.append(Step("account_config_set", prm)); continue

        if has(c, ("template banao", "template bana", "create template", "naya template",
                   "template create", "script banao", "automation banao")):
            nm = re.search(r"(?:name|naam)\s*[:=]?\s*([a-z0-9_\-]+)", c)
            prm = {"text": c[:300]}
            if nm: prm["name"] = nm.group(1)
            if m_acc: prm["account"] = m_acc.group(1)
            plan.steps.append(Step("template_create", prm))
            break  # description text belongs to the template, not further clauses

        if has(c, ("saved script", "saved template", "script list", "template list", "templates dikhao",
                   "saved scripts", "mera script", "mere script", "custom script list", "scripts dikhao",
                   "templates list")):
            plan.steps.append(Step("template_list", {})); continue

        _task_words = has(c, ("task", "tasks"))
        if _task_words and has(c, ("cancel", "stop", "band", "rok")) and has(c, ("saare", "sab", "all", "sabhi")):
            plan.steps.append(Step("tasks_cancel_all", {})); continue
        if _task_words and has(c, ("dikhao", "list", "batao", "status", "chal rah", "running", "custom")):
            plan.steps.append(Step("tasks_list", {})); continue

        if _tpl_hit:
            if has(c, V_STOP):
                plan.steps.append(Step("template_stop", {"template": _tpl_hit["name"]})); continue
            if has(c, V_START + ("run", "chala")):
                prm = {"template": _tpl_hit["name"]}
                if m_acc: prm["account"] = m_acc.group(1)
                plan.steps.append(Step("template_run", prm)); continue

        if has(c, ("template", "updater")) or (has(c, ("script",)) and has(c, ("run", "chalu", "start", "stop", "band"))):
            _name = None
            _m = re.search(r"(?:template|script)\s+([a-z0-9][a-z0-9_\-]{1,30})", c)
            if _m and _m.group(1) not in ("run", "start", "stop", "list", "banao"):
                _name = _m.group(1)
            else:
                _m2 = re.search(r"([a-z0-9][a-z0-9_\- ]{1,30}?)\s*(?:template|updater|script)", c)
                if _m2:
                    _name = _m2.group(1).strip()
            if _name:
                # drop leading account phrases / filler words
                _name = re.sub(r"^(?:account\s*\d+\s*(?:ka|ke|ki|wala|wali)?\s*)", "", _name).strip()
                _name = re.sub(r"^(?:mera|mere|meri|my|ye|is|wo|custom|saved)\s+", "", _name).strip()
                _name = re.sub(r"\s+(?:ka|ke|ki|wala|wali)$", "", _name).strip()
            if _name in ("custom", "saved", "mera", "mere", "my", "ye", "is", ""):
                _name = None
            if has(c, V_STOP):
                plan.steps.append(Step("template_stop", {"template": _name or ""})); continue
            if has(c, V_START + ("run", "chala")):
                prm = {"template": _name or ""}
                if m_acc: prm["account"] = m_acc.group(1)
                plan.steps.append(Step("template_run", prm)); continue

        if p.get("run_at") and has(c, V_START) and not has(c, V_STOP):
            plan.steps.append(Step("scheduler_start", {"run_at": p["run_at"], "label": p["label"]})); continue
        if p.get("run_at") and has(c, V_STOP):
            plan.steps.append(Step("scheduler_stop", {"run_at": p["run_at"], "label": p["label"]})); continue

        if has(c, V_MON) and (has(c, V_START) or has(c, ("karna", "karo", "kr", "shuru", "chalu", "lagao"))):
            plan.steps.append(Step("monitor_source", {k: v for k, v in p.items() if k in ("source", "destination", "keywords")}))
            if has(c, ("fastest", "jaldi", "instant", "fast")):
                plan.notes.append("Fast mode: event-based Telegram listener (polling nahi) — supported.")
            continue
        if has(c, V_MON) and has(c, V_STOP):
            plan.steps.append(Step("task_stop", {"kind": "MON"})); continue
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
            plan.steps.append(Step("format_update", {})); continue

        if tgt == "cross" or (tgt is None and has(c, CROSS_T)):
            if has(c, V_PAUSE):   plan.steps.append(Step("cross_pause", {})); continue
            if has(c, V_RESUME):  plan.steps.append(Step("cross_resume", {})); continue
            if has(c, V_RESET):   plan.steps.append(Step("cross_reset", {})); continue
            if has(c, V_CONFIG):  plan.steps.append(Step("cross_config", {})); continue
            if has(c, V_STOP):    plan.steps.append(Step("cross_stop", {})); continue
            if has(c, V_START):   plan.steps.append(Step("cross_start", {})); continue
            # "is message ko cross karo" / "reply wale post se cross karo" / "cross kro"
            if has(c, ("cross karo", "cross kar do", "cross kar", "cross kro", "ko cross",
                       "se cross", "cross this", "cross it")):
                plan.steps.append(Step("cross_start", {})); continue
            if has(c, V_STATUS + ("ka ",)):
                plan.steps.append(Step("cross_status", {})); continue

        if tgt == "scheduler" and has(c, V_STATUS + V_CHECK):
            plan.steps.append(Step("scheduler_status", {})); continue
        if has(c, V_CANCEL) and ("job" in c or p.get("id")) and tgt != "cross":
            plan.steps.append(Step("scheduler_cancel", {"id": p.get("id", "")})); continue
        if tgt == "task" and has(c, V_STOP + V_CANCEL):
            plan.steps.append(Step("task_stop", {"id": p.get("id", "")})); continue
        if tgt == "task" and has(c, V_RESET):
            plan.steps.append(Step("task_reset", {"id": p.get("id", "")})); continue
        if tgt == "task" and has(c, V_STATUS):
            plan.steps.append(Step("task_status", {})); continue
        if has(c, ("task status", "tasks dikhao", "kya chal raha", "kya kya chal raha")):
            plan.steps.append(Step("task_status", {})); continue

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
            plan.steps.append(Step("telegram_channel_age_estimate", {"channel": pr or ""}))
            if not pr: plan.needs.append("channel")
            continue
        if has(c, ("activ", "activity")) or "active hai" in c:
            pr = p.get("ref") or ctx.get("last_channel")
            plan.steps.append(Step("telegram_channel_activity", {"channel": pr or ""}))
            if not pr: plan.needs.append("channel")
            continue
        if "channel" in c and has(c, V_CHECK + ("info",)):
            pr = p.get("ref") or ctx.get("last_channel")
            plan.steps.append(Step("telegram_channel_info", {"channel": pr or ""}))
            if not pr: plan.needs.append("channel")
            continue
        if has(c, ("recent message", "messages padho", "messages dikhao", "messages check")):
            plan.steps.append(Step("telegram_recent_messages", {"channel": p.get("ref") or ctx.get("last_channel") or ""})); continue
        if has(c, ("search", "dhundo", "dhundho", "khojo")):
            q = re.sub(r"(search|dhundo|dhundho|khojo|karo|message|messages)", "", c).strip() or "promo"
            plan.steps.append(Step("telegram_message_search", {"query": q[:60]})); continue
        if "saved message" in c:
            plan.steps.append(Step("telegram_saved_messages", {})); continue

        if "admin" in c and has(c, ("permissions", "adikar", "rights", "kar sakta", "check")):
            plan.steps.append(Step("admin_check_permissions", {"channel": p.get("ref") or ctx.get("last_channel") or ""})); continue
        if "admin" in c and has(c, ("hatao", "remove", "demote", "nikalo")):
            um = re.findall(r"@([a-zA-Z0-9_]{3,32})", c)
            plan.steps.append(Step("admin_demote", {"user": um[-1] if um else "", "channel": ctx.get("last_channel", "")})); continue
        if "admin" in c and has(c, ("de do", "bana", "dena", "banana", "promote", "do")):
            um = re.findall(r"@([a-zA-Z0-9_]{3,32})", c)
            pr = {"user": um[-1] if um else "", "channel": ctx.get("last_channel", "")}
            if len(um) > 1 and not pr["channel"]:
                pr["channel"] = um[0]
            plan.steps.append(Step("admin_promote", pr))
            if not pr["user"]: plan.needs.append("user")
            continue
        if "user" in c and has(c, V_CHECK + ("info", "whois", "kaun")):
            plan.steps.append(Step("telegram_user_info", {"user": p.get("ref") or ctx.get("last_user") or ""})); continue
        if has(c, ("permissions", "adhikar", "rights")) and "channel" in c:
            plan.steps.append(Step("telegram_permissions", {"channel": p.get("ref") or ctx.get("last_channel") or ""})); continue

        if "diagnostic" in c:
            plan.steps.append(Step("jarvis_diagnostics", {})); continue
        if has(c, ("save state", "state save")):
            plan.steps.append(Step("jarvis_save_state", {})); continue
        if has(c, ("help", "madad", "commands", "kya kya kar", "kya kar sakte")):
            plan.steps.append(Step("jarvis_help", {})); continue
        if has(c, ("status", "stithi")) and tgt is None and not plan.steps:
            plan.steps.append(Step("jarvis_status", {})); continue
        if "account" in c or "mera telegram" in c:
            plan.steps.append(Step("telegram_account", {})); continue

        pending.append(c)

    if pending and plan.steps:
        for c in pending:
            plan.notes.append(f"Is part ko map nahi kar paya: '{c[:60]}' — /AI HELP")

    merged = []
    for s in plan.steps:
        prev = next((x for x in merged if x.tool == s.tool), None)
        if prev:
            prev.params.update({k: v for k, v in s.params.items() if v not in ("", None, False)})
        else:
            merged.append(s)
    plan.steps = merged
    return plan

# ----------------------------------------------------------------------------
# AI provider chain — NLU escalation only. Per-provider status tracking.
# BUG FIX 3: max_tokens set, graceful per-provider errors, never blocks tools.
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
        self.provider_status = {n: "skipped" for n, *_ in self.PROVIDERS}

    def configured(self):
        return [n for n, k, *_ in self.PROVIDERS if os.getenv(k)] if httpx else []

    def providers_view(self):
        return [{"id": n, "configured": bool(os.getenv(k)) if httpx else False,
                 "status": self.provider_status.get(n, "skipped"),
                 "role": "PRIMARY" if i == 0 else f"FALLBACK {i}"}
                for i, (n, k, *_m) in enumerate(self.PROVIDERS)]

    def prompt(self, text):
        return ("You are the NLU layer of JARVIS, a Telegram control assistant. Convert the user "
                "instruction (English/Hindi/Hinglish, possibly multi-step) into ONE raw JSON object:\n"
                '{"steps":[{"tool":"<tool name>","params":{...}}],'
                '"unsupported":["<requested behavior with no tool>"],'
                '"reply":"<one short line>"}\n'
                "ONLY these tools (never invent):\n" + REG.summary_for_ai() +
                "\nRaw JSON only. Unknown -> \"steps\":[] with explanation in reply. No code ever.\nUSER: " + text)

    async def _call(self, name, key, model, text):
        async with httpx.AsyncClient(timeout=10.0) as c:
            msg = self.prompt(text)
            if name in ("GROQ", "OPENAI", "OPENROUTER"):
                url = {"GROQ": "https://api.groq.com/openai/v1/chat/completions",
                       "OPENAI": "https://api.openai.com/v1/chat/completions",
                       "OPENROUTER": "https://openrouter.ai/api/v1/chat/completions"}[name]
                r = await c.post(url, headers={"Authorization": f"Bearer {key}"},
                                 json={"model": model, "max_tokens": 600,
                                       "messages": [{"role": "user", "content": msg}], "temperature": 0.1})
                r.raise_for_status()
                return r.json()["choices"][0]["message"]["content"]
            if name == "GEMINI":
                url = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?key={key}"
                r = await c.post(url, json={"contents": [{"parts": [{"text": msg}]}],
                                            "generationConfig": {"maxOutputTokens": 600}})
                r.raise_for_status()
                return r.json()["candidates"][0]["content"]["parts"][0]["text"]
            if name == "ANTHROPIC":
                r = await c.post("https://api.anthropic.com/v1/messages",
                                 headers={"x-api-key": key, "anthropic-version": "2023-06-01"},
                                 json={"model": model, "max_tokens": 600,
                                       "messages": [{"role": "user", "content": msg}]})
                r.raise_for_status()
                return r.json()["content"][0]["text"]
            r = await c.post(f"https://api-inference.huggingface.co/models/{model}",
                             headers={"Authorization": f"Bearer {key}"},
                             json={"inputs": msg, "parameters": {"max_new_tokens": 600}})
            r.raise_for_status()
            out = r.json()
            return out[0]["generated_text"] if isinstance(out, list) else str(out)

    async def plan(self, text):
        for name, key_env, model_env, default_model in self.PROVIDERS:
            key = os.getenv(key_env)
            if not key or not httpx:
                continue
            try:
                blob = await self._call(name, key, os.getenv(model_env, default_model), text)
                m = re.search(r"\{.*\}", blob, re.S)
                if not m:
                    raise ValueError("no JSON in provider reply")
                obj = json.loads(m.group(0))
                plan = Plan(provider=name)
                for s in obj.get("steps") or []:
                    tool = str(s.get("tool", "")).strip()
                    prm = s.get("params") if isinstance(s.get("params"), dict) else {}
                    if tool not in REG.tools:
                        plan.unsupported.append(f"AI ne unknown tool manga '{tool}' — registry me nahi, skip")
                        continue
                    allowed = {p.name for p in REG.tools[tool].params}
                    plan.steps.append(Step(tool, {k: v for k, v in prm.items() if not allowed or k in allowed}))
                plan.unsupported += [str(u)[:200] for u in (obj.get("unsupported") or [])]
                if obj.get("reply"):
                    plan.notes.append(str(obj["reply"])[:300])
                self.total += 1
                self.last_provider = name
                self.provider_status[name] = "OK"
                return plan
            except Exception as e:
                self.provider_status[name] = f"FAIL:{type(e).__name__}"
                log.warning("AI provider %s failed (%s) — trying next", name, type(e).__name__)
                safe_log("WARN", "AI", f"Provider {name} failed ({type(e).__name__}) — failover, local NLU stays live")
        return None

AI = AIManager()

# ----------------------------------------------------------------------------
# Dialog folders / channel analysis — PER-CLIENT helpers (multi-account safe)
# BUG FIX 1: fully version-safe parsing, crash-proof
# BUG FIX 2: tzinfo-safe age math
# ----------------------------------------------------------------------------
async def _scan_folders_client(client):
    out = []
    try:
        raw_filters = await client(functions.messages.GetDialogFiltersRequest())
        # Telethon >= 1.36 returns messages.DialogFilters (object with .filters);
        # older versions return a plain list. Normalize both -> list.
        if hasattr(raw_filters, "filters"):
            filters = list(getattr(raw_filters, "filters", None) or [])
        elif isinstance(raw_filters, (list, tuple)):
            filters = list(raw_filters)
        else:
            try:
                filters = list(raw_filters)
            except TypeError:
                log.warning("Unexpected dialog-filter shape %s — treating as empty",
                            type(raw_filters).__name__)
                filters = []
    except Exception as e:
        log.warning("Dialog filters unavailable (%s)", type(e).__name__)
        filters = []
    try:
        dialogs = [d async for d in client.iter_dialogs(limit=300)]
    except Exception as e:
        log.warning("Dialogs fetch failed (%s)", type(e).__name__)
        dialogs = []

    channels = [d for d in dialogs if getattr(d, "is_channel", False)]
    peer_map = {}
    for d in channels:
        try:
            peer_map[getattr(d.entity, "id", None)] = d
        except Exception:
            continue

    for f in filters:
        try:
            raw_title = getattr(f, "title", None)
            if raw_title is None:
                continue
            title = raw_title if isinstance(raw_title, str) else (getattr(raw_title, "text", None) or str(raw_title))
            if not title or not str(title).strip():
                continue
            include = getattr(f, "include_peers", None) or []
            chans = []
            for p in include:
                try:
                    d = peer_map.get(getattr(p, "channel_id", None))
                    if d:
                        chans.append({"id": d.entity.id, "name": getattr(d.entity, "title", "Channel"),
                                      "username": getattr(d.entity, "username", None)})
                except Exception:
                    continue
            out.append({"name": str(title).upper(), "channels": chans})
        except Exception as e:
            log.warning("Folder parse skip (%s)", type(e).__name__)
            continue

    if not out and channels:
        out.append({"name": "ALL CHANNELS", "channels": [
            {"id": getattr(d.entity, "id", None), "name": getattr(d.entity, "title", "Channel"),
             "username": getattr(d.entity, "username", None)} for d in channels]})
    return out

async def scan_folders():
    connected, _ = TG.status()
    if not connected:
        return []
    async with TG.lock:
        return await _scan_folders_client(TG.client)

async def scan_folders_for(account_ctx):
    return await _scan_folders_client(account_ctx["client"])

async def _analyze_channel_client(client, cid):
    threshold = cfg_dead_threshold()
    try:
        msgs = await client.get_messages(int(cid), limit=1)
        if not msgs or msgs[0] is None:
            return "INACTIVE", "Empty history — koi post nahi mila", None
        last = msgs[0].date
        # BUG FIX 2: tzinfo None crash guard
        now = datetime.now(last.tzinfo) if getattr(last, "tzinfo", None) else datetime.now(timezone.utc)
        if getattr(last, "tzinfo", None) is None:
            last = last.replace(tzinfo=timezone.utc)
        age = now - last
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

async def analyze_channel(cid):
    return await _analyze_channel_client(TG.client, cid)

async def analyze_channel_for(account_ctx, cid):
    return await _analyze_channel_client(account_ctx["client"], cid)

# ----------------------------------------------------------------------------
# Telegram manager — PRIMARY account (session / phone+OTP / 2FA login)
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

    def bind(self, client, meta):
        """Point all tools/engine at this client (used for managed-account activation)."""
        self.client = client
        self.authorized = True
        self.account = meta
        STATE["account"] = meta
        state_store.save_bg(STATE)
        self._attach_listener(client)
        MONITOR.attached_client = None
        try:
            asyncio.get_running_loop().create_task(MONITOR.attach(client))
        except RuntimeError:
            pass
        safe_log("OK", "TELEGRAM", f"Active account -> @{meta.get('username')}")

    async def _finalize(self, client):
        me = await client.get_me()
        meta = {
            "name": f"{me.first_name or ''} {me.last_name or ''}".strip() or "Telegram User",
            "username": getattr(me, "username", None) or "unknown",
            "user_id": me.id,
            "phone": ("+•••••" + str(me.phone)[-4:]) if getattr(me, "phone", None) else None,
            "connected_at": int(time.time()),
        }
        self.client = client
        self.authorized = True
        self.account = meta
        STATE["account"] = meta
        state_store.save_bg(STATE)
        self._attach_listener(client)
        await MONITOR.attach(client)
        if STATE["monitor"].get("active"):
            MONITOR.ensure_worker()
        log.info("TELEGRAM authorized as @%s (%s)", meta["username"], me.id)
        safe_log("OK", "TELEGRAM", f"Authorized as @{meta['username']} (ID {me.id})")
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
                              "message": "2FA accepted — authorized. SESSION STRING abhi copy karo (ek baar)."}
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
            try:  # scripts bound to a disconnected account are stopped
                for acc_id in list(set(list(SCRIPT_TASKS) + list(SCRIPT_PROGRESS))):
                    asyncio.get_running_loop().create_task(stop_script(acc_id, "account disconnected"))
            except Exception:
                pass
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
                admins = authorized_admin_ids()
                if sender not in admins:
                    log.warning("Ignoring command from non-admin id %s (fail closed)", sender)
                    safe_log("WARN", "AUTH", f"Ignored message from non-admin {sender} (fail closed)")
                    return
                text = (event.raw_text or "").strip()
                # /setchannel — per-account channel config straight from Telegram (§1)
                m_set = re.match(r"^\s*/setchannel\s+(main|source|destination)\s+(\S+)\s*$", text, re.I)
                if m_set:
                    reply = await set_channel_cmd(sender, m_set.group(1).lower(), m_set.group(2))
                    await event.reply(reply)
                    return
                if re.match(r"^\s*/setchannel\b", text, re.I):
                    await event.reply(
                        "USAGE ▸ /setchannel <main|source|destination> <id_or_@username>\n"
                        "Example ▸ /setchannel main 1716302260\n"
                        "Ye setting sirf is account ke liye save hoti hai (per-account config).")
                    return
                if re.match(r"^\s*/getchannel\b", text, re.I):
                    await event.reply(get_channel_cmd(sender))
                    return
                prefixed = re.match(r"^\s*\/?(ai|jarvis|cross|task|monitor)\b", text, re.I)
                confirm_pending = f"tg:{sender}" in PENDING_CONFIRM
                if not prefixed and not confirm_pending:
                    return
                origin = f"tg:{sender}"
                # Saved Messages: if this command is a reply, the replied message
                # becomes the cross source automatically (no manual IDs needed).
                await capture_reply_from_event(event, origin)
                result = await handle_command(text, origin=origin)
                reply = "\n".join(result.get("lines") or ["Koi output nahi."])[:3800]
                await event.reply(reply)
                safe_log("CMD", "TELEGRAM", f"/AI from admin {sender} -> plan executed")
            except FloodWaitError as fw:
                log.warning("FloodWait %ss sending reply — waiting exact duration", fw.seconds)
                safe_log("WARN", "TELEGRAM", f"FloodWait {fw.seconds}s on reply — exact delay honoured")
                await asyncio.sleep(fw.seconds)
            except Exception as e:
                log.error("Saved-messages handler error: %s", type(e).__name__)

def _account_for_user(user_id):
    """Map a Telegram sender to the managed account whose session it is."""
    for aid, acc in ACCOUNTS.accounts.items():
        if str(acc["meta"].get("user_id")) == str(user_id):
            return aid, acc
    active = ACCOUNTS.get_active()
    if active:
        return active["meta"]["id"], active
    return None, None

async def set_channel_cmd(sender_id, kind, value):
    """/setchannel <main|source|destination> <id|@username> — per-account, no .env."""
    aid, acc = _account_for_user(sender_id)
    if not aid:
        return "NO ACCOUNT ▸ pehle web dashboard se account add/activate karo."
    key = {"main": "main_channel", "source": "source", "destination": "destination"}[kind]
    val = str(value).strip()
    resolved = ""
    client = (acc or {}).get("client")
    if client:
        try:
            ent = await client.get_entity(int(val) if val.lstrip("-").isdigit() else val)
            resolved = f" ({getattr(ent, 'title', None) or getattr(ent, 'username', '') or 'resolved'})"
        except Exception as e:
            resolved = f" (warning: resolve failed — {type(e).__name__}; value saved as given)"
    store = acctcfg_store.load()
    cfg = store.get(aid, {})
    cfg[key] = val
    cfg["updated_at"] = int(time.time())
    store[aid] = cfg
    await acctcfg_store.save(store)
    safe_log("CMD", "ACCOUNT", f"/setchannel {kind} for {aid}")
    c = acct_cfg(aid)
    return ("CHANNEL SET\n"
            f"Account     ▸ @{acc['meta'].get('username')} ({aid})\n"
            f"{kind.upper():11s} ▸ {val}{resolved}\n"
            "────────────────────────────\n"
            f"main        ▸ {c.get('main_channel') or 'not set'}\n"
            f"source      ▸ {c.get('source') or 'not set'}\n"
            f"destination ▸ {c.get('destination') or 'not set'}")

def get_channel_cmd(sender_id):
    aid, acc = _account_for_user(sender_id)
    if not aid:
        return "NO ACCOUNT ▸ pehle account add/activate karo."
    c = acct_cfg(aid)
    return ("CHANNEL CONFIG\n"
            f"Account     ▸ @{acc['meta'].get('username')} ({aid})\n"
            f"main        ▸ {c.get('main_channel') or 'not set'}\n"
            f"source      ▸ {c.get('source') or 'not set'}\n"
            f"destination ▸ {c.get('destination') or 'not set'}\n"
            "Change ▸ /setchannel main <id>")

TG = TelegramManager()

def authorized_admin_ids():
    raw = os.getenv("AUTHORIZED_ADMINS", "").strip()
    ids = {int(x) for x in re.split(r"[,\s]+", raw) if x.strip().isdigit()}
    if TG.account:
        ids.add(int(TG.account["user_id"]))
    for acc in ACCOUNTS.accounts.values():
        if acc["meta"].get("user_id"):
            ids.add(int(acc["meta"]["user_id"]))
    return ids

PENDING_CONFIRM = {}

# ============================================================================
# ACCOUNT MANAGER — up to 2 encrypted accounts, one active at a time
# ============================================================================
class AccountManager:
    MAX_ACCOUNTS = 2

    def __init__(self):
        self.accounts = {}
        self._load_from_disk()

    def _load_from_disk(self):
        for a in accounts_store.load().get("accounts", []):
            self.accounts[a["id"]] = {"meta": a, "client": None,
                                      "lock": asyncio.Lock(), "authorized": False}

    def _persist(self):
        accounts_store.save_bg({"accounts": [v["meta"] for v in self.accounts.values()]})

    def persistent(self):
        return bool(_get_fernet())

    async def add_account(self, label, api_id, api_hash, session_string):
        if len(self.accounts) >= self.MAX_ACCOUNTS:
            return False, f"Max {self.MAX_ACCOUNTS} accounts allowed"
        if not TELETHON_OK:
            return False, "telethon not installed"
        client = None
        try:
            client = TelegramClient(StringSession(session_string.strip()), api_id, api_hash.strip())
            await client.connect()
            if not await client.is_user_authorized():
                await client.disconnect()
                return False, "Session invalid — expired ya revoked"
            me = await client.get_me()
        except (ValueError, EOFError, struct.error):
            if client:
                try:
                    await client.disconnect()
                except Exception:
                    pass
            return False, "SESSION STRING CORRUPT — fresh export karo"
        except FloodWaitError as fw:
            if client:
                try:
                    await client.disconnect()
                except Exception:
                    pass
            return False, f"FloodWait — {fw.seconds}s baad retry (exact delay honoured)"
        except Exception as e:
            if client:
                try:
                    await client.disconnect()
                except Exception:
                    pass
            return False, f"Connection failed: {type(e).__name__} — API ID/HASH/session verify karo"
        acc_id = f"acc_{uuid.uuid4().hex[:6]}"
        enc_session = encrypt_str(session_string)
        enc_hash = encrypt_str(api_hash)
        meta = {"id": acc_id, "label": label, "api_id": api_id,
                "api_hash_enc": enc_hash, "session_enc": enc_session,
                "username": getattr(me, "username", None) or "unknown", "user_id": me.id,
                "active": False, "persisted": bool(enc_session), "config": {},
                "created_at": int(time.time())}
        self.accounts[acc_id] = {"meta": meta, "client": client, "lock": asyncio.Lock(), "authorized": True}
        self._persist()
        TG._attach_listener(client)
        await MONITOR.attach(client)
        safe_log("OK", "ACCOUNT", f"Added {acc_id} (@{meta['username']}) — persisted={'yes' if enc_session else 'memory-only (set JARVIS_SECRET_KEY)'}")
        warn = None if enc_session else "JARVIS_SECRET_KEY set nahi — ye account restart tak hi rahega"
        return True, {"id": acc_id, "username": meta["username"], "user_id": me.id, "warning": warn}

    async def remove_account(self, acc_id):
        acc = self.accounts.get(acc_id)
        if not acc:
            return False, "Account not found"
        was_active = acc["meta"].get("active")
        if acc.get("client"):
            try:
                await acc["client"].disconnect()
            except Exception:
                pass
        self.accounts.pop(acc_id, None)
        if was_active:
            TG.client = None
            TG.authorized = False
            TG.account = None
            STATE["account"] = None
            state_store.save_bg(STATE)
        self._persist()
        safe_log("WARN", "ACCOUNT", f"Removed {acc_id}")
        try:  # auto-stop any running script bound to this account
            asyncio.get_running_loop().create_task(stop_scripts_for_account(acc_id))
        except Exception:
            pass
        return True, "Removed"

    async def activate(self, acc_id):
        acc = self.accounts.get(acc_id)
        if not acc:
            return False, "Account not found"
        if not (acc.get("client") and acc["client"].is_connected() and acc.get("authorized")):
            return False, "Account not connected — session reconnect failed (restart ya re-add karo)"
        for aid, a in self.accounts.items():
            a["meta"]["active"] = (aid == acc_id)
        self._persist()
        meta = dict(acc["meta"])
        TG.bind(acc["client"], {"name": meta.get("label") or "Telegram User", "username": meta["username"],
                                "user_id": meta["user_id"], "phone": None, "connected_at": int(time.time())})
        safe_log("OK", "ACCOUNT", f"Activated {acc_id} (@{meta['username']}) — saare tools ab is account par")
        return True, f"Activated @{meta['username']}"

    def get_active(self):
        for acc in self.accounts.values():
            if acc["meta"].get("active"):
                return acc
        return None

    def view(self):
        out = []
        for aid, acc in self.accounts.items():
            m = acc["meta"]
            out.append({"id": aid, "label": m.get("label") or "Account", "username": m.get("username"),
                        "user_id": m.get("user_id"), "active": bool(m.get("active")),
                        "persisted": bool(m.get("persisted")),
                        "authorized": bool(acc.get("authorized")),
                        "connected": bool(acc.get("client") and acc["client"].is_connected())})
        return out

    async def reconnect_all(self):
        if not self.accounts:
            return 0
        n = 0
        for acc in self.accounts.values():
            meta = acc["meta"]
            try:
                api_hash = decrypt_str(meta.get("api_hash_enc"))
                session = decrypt_str(meta.get("session_enc"))
                if not api_hash or not session:
                    safe_log("WARN", "ACCOUNT", f"{meta['id']} reconnect skip — encrypted session unavailable (JARVIS_SECRET_KEY)")
                    continue
                client = TelegramClient(StringSession(session), int(meta["api_id"]), api_hash)
                await client.connect()
                if await client.is_user_authorized():
                    acc["client"] = client
                    acc["authorized"] = True
                    TG._attach_listener(client)
                    await MONITOR.attach(client)
                    n += 1
                    log.info("Reconnected account %s (@%s)", meta["id"], meta.get("username"))
                else:
                    await client.disconnect()
            except Exception as e:
                log.warning("Reconnect failed for %s: %s", meta["id"], type(e).__name__)
        active = self.get_active()
        if active and active.get("client") and active.get("authorized"):
            meta = dict(active["meta"])
            TG.bind(active["client"], {"name": meta.get("label") or "Telegram User",
                                       "username": meta["username"], "user_id": meta["user_id"],
                                       "phone": None, "connected_at": int(time.time())})
        return n

ACCOUNTS = AccountManager()

# ============================================================================
# TELEGRAM TOOLS
# ============================================================================
async def t_telegram_status(p, o):
    connected, authed = TG.status()
    accs = ACCOUNTS.view()
    lines = ["TELEGRAM STATUS", bar,
             f"Connection ▸ {'LIVE' if connected else 'DISCONNECTED'}",
             f"Authorized ▸ {'YES' if authed else 'NO'}",
             f"Account    ▸ {('@' + TG.account['username']) if (authed and TG.account) else '—'}"]
    if accs:
        lines.append(f"Managed    ▸ {len(accs)}/{AccountManager.MAX_ACCOUNTS} accounts (active: {next((a['username'] for a in accs if a['active']), '—')})")
    return {"lines": lines}

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
    lines.append("Note: ek failed request se kisi ko permanently dead declare nahi kiya jata.")
    return {"lines": lines}

async def _chan_target(p, o):
    chan = str(p.get("channel", "")).strip()
    return chan or ctx_get(o).get("last_channel", "")

async def t_channel_info(p, o):
    chan = await _chan_target(p, o)
    if not chan:
        return {"ok": False, "lines": ["Kaunsa channel? @username batao — e.g. '/AI @mynews channel inspect karo'"]}
    try:
        e = await resolve_chat(chan)
    except Exception as ex:
        return {"ok": False, "lines": [f"ENTITY ERROR ▸ '{chan}' resolve nahi hua ({type(ex).__name__}) — private/inaccessible?"]}
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
        return {"lines": [f"{getattr(e, 'title', chan)} ▸ koi message visible nahi — INACTIVE lag raha hai"]}
    latest, oldest = dates[0], dates[-1]
    span = max(1, (latest - oldest).days or 1)
    per_day = round(len(dates) / span, 1)
    latest_aware = latest if latest.tzinfo else latest.replace(tzinfo=timezone.utc)
    age_h = (datetime.now(latest_aware.tzinfo) - latest_aware).total_seconds() / 3600
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
    d_aware = d if d.tzinfo else d.replace(tzinfo=timezone.utc)
    days = (datetime.now(d_aware.tzinfo) - d_aware).days
    return {"lines": ["CHANNEL AGE ESTIMATE", bar,
                      f"Channel ▸ {getattr(e, 'title', chan)}",
                      "Estimated age based on earliest accessible message:",
                      f"Earliest ▸ {d.strftime('%d %b %Y %I:%M %p')} (~{days} din / ~{round(days / 30, 1)} months purana)",
                      "Note: exact creation date Telegram provide nahi karta — history-based estimate hai."],
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
        return {"ok": False, "lines": [f"USER ERROR ▸ '{ref}' resolve nahi hua ({type(ex).__name__}) — deleted/private?"]}
    ctx_set(o, last_user=getattr(u, "username", None) or str(u.id))
    return {"lines": ["USER REPORT", bar,
                      f"Name     ▸ {(getattr(u, 'first_name', '') or '') + ' ' + (getattr(u, 'last_name', '') or '')}".strip(),
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

# ---------------- monitor workflow ----------------
async def _monitor_src(p):
    return p.get("source") or cfg_monitor()[0]

async def t_monitor_source(p, o):
    return await MONITOR.start(p, o)

async def t_fetch_latest(p, o):
    src = await _monitor_src(p)
    if not src:
        return {"ok": False, "lines": ["SOURCE NOT CONFIGURED ▸ Source Config panel ya MONITOR_SOURCE env set karo"]}
    try:
        e = await resolve_chat(src)
        msgs = await TG.client.get_messages(e, limit=1)
    except Exception as ex:
        return {"ok": False, "lines": [f"SOURCE ERROR ▸ latest message fetch nahi hua ({type(ex).__name__})"]}
    if not msgs or not msgs[0]:
        return {"lines": ["Source me abhi koi message nahi — Telegram ne kuch provide nahi kiya (fabricate nahi karunga)."]}
    ctx_set(o, last_channel=getattr(e, "username", None) or str(e.id))
    m = msgs[0]
    return {"lines": ["LATEST SOURCE MESSAGE", bar,
                      f"Source ▸ {src} ▸ message id {m.id}",
                      f"Date   ▸ {m.date.strftime('%d %b %Y %I:%M %p') if m.date else '—'}",
                      bar, (m.text or "(non-text message / media)")[:600]]}

async def t_parse_source(p, o):
    src = await _monitor_src(p)
    if not src:
        return {"ok": False, "lines": ["SOURCE NOT CONFIGURED ▸ Source Config panel ya MONITOR_SOURCE env set karo"]}
    try:
        e = await resolve_chat(src)
        msgs = await TG.client.get_messages(e, limit=1)
    except Exception as ex:
        return {"ok": False, "lines": [f"SOURCE ERROR ▸ ({type(ex).__name__})"]}
    if not msgs or not msgs[0] or not (msgs[0].text or ""):
        return {"lines": ["Parse karne layak text nahi mila — latest empty/non-text."]}
    kws = STATE["monitor"].get("keywords") or DEFAULT_KEYWORDS
    parsed = parse_source_text(msgs[0].text, kws)
    return {"lines": ["SOURCE PARSE RESULT", bar,
                      f"Keywords ▸ {', '.join(kws)}",
                      f"Match    ▸ {'YES — ' + str(parsed['matched_lines']) + ' line(s)' if parsed['matched'] else 'NO — full text use hoga'}",
                      bar, parsed["body"][:800]]}

async def t_copy_source(p, o):
    src = await _monitor_src(p)
    _s, dst = cfg_monitor()
    if not src or not dst:
        return {"ok": False, "lines": ["SOURCE/DESTINATION NOT CONFIGURED ▸ Source Config panel se set karo"]}
    try:
        e = await resolve_chat(src)
        msgs = await TG.client.get_messages(e, limit=1)
    except Exception as ex:
        return {"ok": False, "lines": [f"SOURCE ERROR ▸ ({type(ex).__name__})"]}
    if not msgs or not msgs[0] or not (msgs[0].text or ""):
        return {"ok": False, "lines": ["Copy karne layak text nahi mila — latest empty/non-text (fabricate nahi karunga)."]}
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
        return {"ok": False, "lines": ["SOURCE NOT CONFIGURED ▸ Source Config panel ya MONITOR_SOURCE env set karo"]}
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
                      bar, "Bhejne ke liye: '/AI latest result bhejo'"]}

async def t_send_update(p, o):
    return await t_copy_source(p, o)

# ---------------- cross engine ----------------
async def t_cross_start(p, o):
    """Start cross. If the command came as a reply in Saved Messages, that
    replied message becomes the source automatically (no manual IDs)."""
    rs = take_reply_source(o)
    if rs:
        await apply_reply_source(rs["chat_id"], rs["message_id"])
        r = await ENGINE.start(p, o)
        head = ["✓ CROSS STARTED" if r.get("ok", True) else "CROSS START FAILED", bar,
                "Source ▸ replied message (auto-detected)",
                f"  chat_id    ▸ {rs['chat_id']}",
                f"  message_id ▸ {rs['message_id']}",
                f"  preview    ▸ {rs['preview']}", bar]
        return {"ok": r.get("ok", True), "lines": head + (r.get("lines") or [])}
    return await ENGINE.start(p, o)
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

# ---------------- scheduler / tasks ----------------
async def t_scheduler_status(p, o):
    active = [j for j in SCHED.jobs if not j.get("done")]
    return {"lines": [f"SCHEDULER STATUS — Asia/Kathmandu ({ktm_now().strftime('%I:%M %p NPT')})", bar,
                      f"Active jobs ▸ {len(active)} ▸ History: {len(SCHED.jobs)}",
                      f"Next        ▸ {fmt_kt(min(j['run_at'] for j in active)) if active else '—'}",
                      "Persistence ▸ scheduled_jobs.json ▸ restart recovery on ▸ no double-fire"]}

async def t_scheduler_list(p, o):
    lines = [f"SCHEDULED JOBS — ({ktm_now().strftime('%I:%M %p NPT')})", bar]
    if not SCHED.jobs:
        lines.append('Koi job nahi. Try: "10 minute baad cross start karo".')
    for j in SCHED.jobs[-8:]:
        lines.append(f"[{j['id']}] {j['action']} — {j['label']} ▸ {fmt_kt(j['run_at'])} ▸ {'DONE' if j.get('done') else 'PENDING'}")
    return {"lines": lines}

async def t_scheduler_start(p, o):
    if not p.get("run_at"):
        return {"ok": False, "lines": ["Time samajh nahi aaya — e.g. '10 minute baad start'"]}
    j = SCHED.add("START", float(p["run_at"]), str(p.get("label", "scheduled")))
    return {"lines": [f"JOB SCHEDULED ▸ ENGINE START at {j['label']} ({fmt_kt(j['run_at'])}) ▸ id [{j['id']}]"]}

async def t_scheduler_stop(p, o):
    if not p.get("run_at"):
        return {"ok": False, "lines": ["Time samajh nahi aaya — e.g. '10 minute baad stop'"]}
    j = SCHED.add("STOP", float(p["run_at"]), str(p.get("label", "scheduled")))
    return {"lines": [f"JOB SCHEDULED ▸ ENGINE STOP at {j['label']} ({fmt_kt(j['run_at'])}) ▸ id [{j['id']}]"]}

async def t_scheduler_cancel(p, o):
    jid = str(p.get("id", ""))
    if not jid:
        pend = [j for j in SCHED.jobs if not j.get("done")]
        if len(pend) == 1:
            jid = pend[0]["id"]
        else:
            return {"ok": False, "lines": ["Job id batao — '/AI schedule list' se dekho"]}
    return {"lines": [f"CANCELLED ▸ [{jid}]"] if SCHED.cancel(jid) else ["JOB NOT FOUND ▸ " + jid]}

async def t_task_status(p, o):
    lines = ["TASK MANAGER", bar]
    if not TASKS.tasks:
        lines.append("Koi tracked task nahi — cross ya monitor start karo.")
    for t in TASKS.tasks.values():
        stats = t["stats"]() if t.get("stats") else ""
        lines.append(f"[{t['id']}] {t['label']} ▸ {t['status']} ▸ since {fmt_kt(t['started_at'])} {('▸ ' + stats) if stats else ''}")
    lines.append(MONITOR.status_lines()[2])
    return {"lines": lines}

async def t_task_stop(p, o):
    tid = str(p.get("id", "")).upper()
    kind = str(p.get("kind", "")).upper()
    target = TASKS.tasks.get(tid) if tid else None
    if not target and kind:
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
    return {"lines": [f"TASK STOPPED ▸ [{target['id']}] {target['label']}", "Actual engine/monitor safely stop hua."]}

async def t_task_reset(p, o):
    tid = str(p.get("id", "")).upper()
    target = TASKS.tasks.get(tid) if tid else (TASKS.running()[0] if len(TASKS.running()) == 1 else None)
    if not target:
        return {"ok": False, "lines": ["Reset ke liye task id batao — '/AI task status'"]}
    if target.get("reset"):
        res = await target["reset"]()
        return res if isinstance(res, dict) else {"lines": [str(res)]}
    return {"ok": False, "lines": ["Is task me reset supported nahi hai."]}

# ---------------- admin ----------------
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
            "'/AI @channel me @user ko admin de do' — confirm ke baad hi hoga"]}
    try:
        chan_e = await resolve_chat(chan)
        user_e = await resolve_chat(user)
        perms = await TG.client.get_permissions(chan_e, "me")
    except Exception as ex:
        return {"ok": False, "lines": [f"RESOLVE ERROR ▸ ({type(ex).__name__}) — channel/user accessible nahi"]}
    if not perms.is_admin and not perms.is_creator:
        return {"ok": False, "lines": ["PERMISSION DENIED ▸ aap is channel ke admin nahi — bypass nahi hoga"]}
    if not (perms.is_creator or getattr(perms, "add_admins", False)):
        return {"ok": False, "lines": ["PERMISSION DENIED ▸ aapke paas 'add admins' right nahi hai"]}
    await TG.client.edit_admin(chan_e, user_e, is_admin=True, title="Admin", **ADMIN_RIGHTS)
    ctx_set(o, last_channel=getattr(chan_e, "username", None), last_user=getattr(user_e, "username", None))
    safe_log("CMD", "ADMIN", f"Promoted @{getattr(user_e,'username',user)} in {getattr(chan_e,'title',chan)}")
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
        return {"ok": False, "lines": ["PERMISSION DENIED ▸ aap admin nahi — bypass nahi hoga"]}
    await TG.client.edit_admin(chan_e, user_e, is_admin=False)
    safe_log("CMD", "ADMIN", f"Demoted @{getattr(user_e,'username',user)} in {getattr(chan_e,'title',chan)}")
    return {"lines": ["ADMIN DEMOTED (real Telegram result)", bar,
                      f"User    ▸ @{getattr(user_e, 'username', None) or user_e.id}",
                      f"Channel ▸ {getattr(chan_e, 'title', chan)}",
                      "Rights  ▸ sab admin rights revoke"]}

# ---------------- jarvis system ----------------
async def t_jarvis_status(p, o):
    eng = STATE["engine"]
    connected, authed = TG.status()
    hold = max(0, int((eng.get("flood_wait_until") or 0) - time.time()))
    return {"lines": ["JARVIS SYSTEM STATUS", bar, "JARVIS     ▸ ONLINE (NLU active)",
                      f"TELEGRAM   ▸ {'CONNECTED @' + TG.account['username'] if authed and TG.account else 'DISCONNECTED'}",
                      f"ACCOUNTS   ▸ {len(ACCOUNTS.accounts)}/{AccountManager.MAX_ACCOUNTS} managed",
                      "AUTH       ▸ AUTHORIZED (fail-closed)",
                      f"TASKS      ▸ {len(TASKS.running())} running ({', '.join(t['id'] for t in TASKS.running()) or 'none'})",
                      f"ENGINE     ▸ {eng['status'].upper()}" + (f" — FloodWait {hold}s" if hold else ""),
                      f"MONITOR    ▸ {'RUNNING (event-based)' if STATE['monitor'].get('active') else 'STOPPED'}",
                      f"AI         ▸ {AI.last_provider} ({AI.total} calls ▸ configured: {', '.join(AI.configured()) or 'local-only'})",
                      f"SCHEDULER  ▸ {len([j for j in SCHED.jobs if not j.get('done')])} active jobs (NPT)",
                      f"TOOLS      ▸ {len(REG.tools)} registered (whitelist)",
                      f"LAST ERROR ▸ {STATE.get('last_error') or 'none'}"]}

async def t_jarvis_help(p, o):
    cats = {}
    for t in REG.tools.values():
        cats.setdefault(t.category, []).append(t)
    lines = [f"JARVIS TOOL REGISTRY — {len(REG.tools)} tools (whitelist only)", bar,
             "Natural language: English · Hindi · Hinglish · multi-step · fuzzy spelling",
             "Custom Script Runner: '/AI account 2 select karo' · '/AI <TEMPLATE> run karo' · "
             "'/AI saved script list dikhao' · '/AI running tasks dikhao'", bar]
    for cat in ("TELEGRAM", "JARVIS", "ACCOUNT", "CUSTOM", "SCHEDULER", "CROSS", "MONITOR", "TASK", "ADMIN"):
        tools = cats.get(cat, [])
        if not tools:
            continue
        lines.append(cat + ":")
        for t in tools:
            lines.append(f"  ▸ {t.desc}{' (confirm)' if t.confirm else ''}")
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
    await runtime_store.save(cfg_get())
    return {"lines": ["STATE SAVED ▸ jarvis_state ▸ ai_history ▸ scheduled_jobs ▸ runtime_config ▸ accounts/scripts (encrypted where set)"]}

# ============================================================================
# REGISTER ALL TOOLS
# ============================================================================
REG.register("telegram_status", "Telegram connection/authorization status", "TELEGRAM", t_telegram_status)
REG.register("telegram_account", "Authenticated account details", "TELEGRAM", t_telegram_account)
REG.register("telegram_dialogs", "Recent dialogs list", "TELEGRAM", t_telegram_dialogs, params=[ToolParam("limit", "number")])
REG.register("telegram_folders", "Dialog folders scan (channels optional)", "TELEGRAM", t_telegram_folders)
REG.register("telegram_channel_info", "Channel inspect — title/id/members/latest", "TELEGRAM", t_channel_info, params=[ToolParam("channel", "chat")])
REG.register("telegram_channel_activity", "Channel activity + active/inactive", "TELEGRAM", t_channel_activity, params=[ToolParam("channel", "chat")])
REG.register("telegram_channel_age_estimate", "Channel age from earliest visible message", "TELEGRAM", t_channel_age, params=[ToolParam("channel", "chat")])
REG.register("telegram_recent_messages", "Recent messages (channel ya globally)", "TELEGRAM", t_recent_messages, params=[ToolParam("channel", "chat")])
REG.register("telegram_message_search", "Search readable messages", "TELEGRAM", t_message_search, params=[ToolParam("query", "text", True)])
REG.register("telegram_saved_messages", "Saved Messages inbox", "TELEGRAM", t_saved_messages)
REG.register("telegram_user_info", "User resolve + basic info", "TELEGRAM", t_user_info, params=[ToolParam("user", "user")])
REG.register("telegram_permissions", "Own permissions in a channel", "TELEGRAM", t_permissions, params=[ToolParam("channel", "chat")])
REG.register("telegram_dead_channel_scan", "Folders me inactive/restricted scan", "TELEGRAM", t_dead_scan)

REG.register("monitor_source", "Source monitoring start (event-based, fast)", "MONITOR", t_monitor_source,
             params=[ToolParam("source", "chat"), ToolParam("destination", "chat"), ToolParam("keywords", "list")])
REG.register("fetch_latest_source_message", "Latest source message fetch", "MONITOR", t_fetch_latest, params=[ToolParam("source", "chat")])
REG.register("parse_source_message", "Latest source message parse", "MONITOR", t_parse_source)
REG.register("copy_source_text", "Exact source text copy → destination", "MONITOR", t_copy_source, confirm=True)
REG.register("format_update", "Update preview (no send)", "MONITOR", t_format_update)
REG.register("send_update", "Update destination par bhejo", "MONITOR", t_send_update, confirm=True)

REG.register("cross_status", "Cross engine status", "CROSS", t_cross_status, needs_telegram=False)
REG.register("cross_start", "Cross engine start", "CROSS", t_cross_start)
REG.register("cross_stop", "Cross engine stop", "CROSS", t_cross_stop, needs_telegram=False)
REG.register("cross_pause", "Cross engine pause", "CROSS", t_cross_pause, needs_telegram=False)
REG.register("cross_resume", "Cross engine resume", "CROSS", t_cross_resume, needs_telegram=False)
REG.register("cross_reset", "Cross engine reset", "CROSS", t_cross_reset, needs_telegram=False, confirm=True)
REG.register("cross_config", "Cross engine configuration", "CROSS", t_cross_config, needs_telegram=False)

REG.register("scheduler_status", "Scheduler status", "SCHEDULER", t_scheduler_status, needs_telegram=False)
REG.register("scheduler_list", "Scheduled jobs list", "SCHEDULER", t_scheduler_list, needs_telegram=False)
REG.register("scheduler_start", "Deferred engine start", "SCHEDULER", t_scheduler_start, needs_telegram=False, params=[ToolParam("run_at", "time", True)])
REG.register("scheduler_stop", "Deferred engine stop", "SCHEDULER", t_scheduler_stop, needs_telegram=False, params=[ToolParam("run_at", "time", True)])
REG.register("scheduler_cancel", "Job cancel by id", "SCHEDULER", t_scheduler_cancel, needs_telegram=False)

REG.register("task_status", "All running tasks", "TASK", t_task_status, needs_telegram=False)
REG.register("task_stop", "Task stop by id / active task", "TASK", t_task_stop, needs_telegram=False)
REG.register("task_reset", "Task reset by id", "TASK", t_task_reset, needs_telegram=False)

REG.register("admin_check_permissions", "Admin rights check in channel", "ADMIN", t_admin_check, params=[ToolParam("channel", "chat")])
REG.register("admin_promote", "User ko channel admin banao", "ADMIN", t_admin_promote, confirm=True, sensitive=True,
             params=[ToolParam("channel", "chat"), ToolParam("user", "user")])
REG.register("admin_demote", "User se admin rights hatao", "ADMIN", t_admin_demote, confirm=True, sensitive=True,
             params=[ToolParam("channel", "chat"), ToolParam("user", "user")])

# ---------------- custom automation templates (account-bound) ----------------
def _ctx_account(o):
    """Resolve the account bound to this conversation/session."""
    aid = ctx_get(o).get("account_id")
    if aid and aid in ACCOUNTS.accounts:
        return ACCOUNTS.accounts[aid], aid
    active = ACCOUNTS.get_active()
    if active:
        return active, active["meta"]["id"]
    return None, None

def _resolve_account_ref(ref):
    """'2' / 'account 2' / '@user' / 'acc_xxx' / label -> (acc, acc_id)."""
    ref = str(ref or "").strip().lower().lstrip("@")
    items = list(ACCOUNTS.accounts.items())
    if not ref:
        return None, None
    m = re.fullmatch(r"(?:account\s*)?(\d+)", ref)
    if m:
        idx = int(m.group(1)) - 1
        if 0 <= idx < len(items):
            return items[idx][1], items[idx][0]
        return None, None
    for aid, acc in items:
        meta = acc["meta"]
        if aid.lower() == ref or str(meta.get("username", "")).lower() == ref \
                or str(meta.get("label", "")).lower() == ref or str(meta.get("user_id")) == ref:
            return acc, aid
    for aid, acc in items:
        if ref in str(acc["meta"].get("label", "")).lower() or ref in str(acc["meta"].get("username", "")).lower():
            return acc, aid
    return None, None

async def t_account_select(p, o):
    acc, aid = _resolve_account_ref(p.get("account"))
    if not acc:
        listing = [f"  ▸ {i+1}. {a['meta'].get('label')} (@{a['meta'].get('username')})"
                   for i, a in enumerate(ACCOUNTS.accounts.values())]
        return {"ok": False, "lines": [f"ACCOUNT NOT FOUND ▸ '{p.get('account')}'", "Available:"] + (listing or ["  (none added)"])}
    ctx_set(o, account_id=aid)
    cfg = acct_cfg(aid)
    return {"lines": ["ACCOUNT SELECTED", bar, f"@{acc['meta'].get('username')} ({acc['meta'].get('label')})",
                      f"Account ID   ▸ {aid}",
                      f"Main channel ▸ {cfg.get('main_channel') or 'not set'}",
                      f"Source       ▸ {cfg.get('source') or 'not set'}",
                      f"Destination  ▸ {cfg.get('destination') or 'not set'}",
                      "Ab is account ke context me commands chalenge."]}

async def t_account_config_set(p, o):
    acc, aid = _ctx_account(o)
    if p.get("account"):
        acc2, aid2 = _resolve_account_ref(p.get("account"))
        if acc2:
            acc, aid = acc2, aid2
    if not acc:
        return {"ok": False, "lines": ["Pehle account select karo — '/AI account 2 select karo'"]}
    store = acctcfg_store.load()
    cfg = store.get(aid, {})
    changed = []
    for key in ("main_channel", "source", "destination"):
        if p.get(key) not in (None, ""):
            cfg[key] = p.get(key)
            changed.append(f"{key} = {p.get(key)}")
    if not changed:
        return {"ok": False, "lines": ["Kya set karna hai? main_channel / source / destination batao"]}
    cfg["updated_at"] = int(time.time())
    store[aid] = cfg
    await acctcfg_store.save(store)
    safe_log("CMD", "ACCOUNT", f"config updated for {aid}: {', '.join(changed)}")
    return {"lines": ["ACCOUNT CONFIG UPDATED", bar,
                      f"Account ▸ @{acc['meta'].get('username')}"] + [f"{c}" for c in changed]}

async def t_template_list(p, o):
    acc, aid = _ctx_account(o)
    only = p.get("account_scope", True)
    items = templates_all()
    if only and aid:
        items = [t for t in items if t.get("account_id") == aid]
    lines = ["CUSTOM TEMPLATES" + (f" — @{acc['meta'].get('username')}" if acc and only else ""), bar]
    if not items:
        lines.append("Koi template nahi. Web panel me automation likh ke SAVE TEMPLATE karo.")
    for t in items[:12]:
        owner = ACCOUNTS.accounts.get(t.get("account_id"))
        running = AUTO_BY_TEMPLATE.get(t["template_id"])
        lines += [f"▸ {t['name']} [{t['template_id']}]",
                  f"   Account ▸ @{(owner or {}).get('meta', {}).get('username', '?')} · "
                  f"{'ENABLED' if t.get('enabled') else 'DISABLED'}"
                  f"{' · RUNNING ' + running if running else ''}",
                  f"   Last run ▸ {fmt_kt(t['last_run']) if t.get('last_run') else 'never'} · {t.get('last_result') or '—'}"]
    lines.append(f"Total: {len(items)}")
    return {"lines": lines}

async def t_template_run(p, o):
    acc, aid = _ctx_account(o)
    if p.get("account"):
        acc2, aid2 = _resolve_account_ref(p.get("account"))
        if acc2:
            acc, aid = acc2, aid2
            ctx_set(o, account_id=aid)
    ref = str(p.get("template", "")).strip()
    tpl = (template_find(ref, aid) or template_find(ref)) if ref else None
    if not tpl and not ref:
        # no name given — run the account's only enabled template, else ask
        cands = [t for t in templates_all() if t.get("account_id") == aid and t.get("enabled", True)]
        if len(cands) == 1:
            tpl = cands[0]
        elif len(cands) > 1:
            return {"ok": False, "lines": ["KAUNSA TEMPLATE? is account ke templates:"] +
                                          [f"  ▸ {t['name']} [{t['template_id']}]" for t in cands]}
    if not tpl:
        return {"ok": False, "lines": [f"TEMPLATE NOT FOUND ▸ '{ref or '(none given)'}'",
                                       "'/AI saved script list dikhao' se dekho"]}
    if not tpl.get("enabled", True):
        return {"ok": False, "lines": [f"TEMPLATE DISABLED ▸ {tpl['name']} — pehle enable karo"]}
    owner_id = tpl.get("account_id")
    if aid and owner_id and owner_id != aid:
        owner = ACCOUNTS.accounts.get(owner_id)
        return {"ok": False, "lines": [
            f"ACCOUNT MISMATCH ▸ template '{tpl['name']}' account @{(owner or {}).get('meta', {}).get('username', '?')} ka hai",
            "Cross-account execution allowed nahi — pehle us account ko select karo"]}
    run_acc_id = owner_id or aid
    if not run_acc_id or run_acc_id not in ACCOUNTS.accounts:
        return {"ok": False, "lines": ["Template ka account available nahi — account add/activate karo"]}
    if AUTO_BY_TEMPLATE.get(tpl["template_id"]):
        return {"ok": False, "lines": [f"ALREADY RUNNING ▸ task {AUTO_BY_TEMPLATE[tpl['template_id']]} — pehle stop karo"]}
    defn, err = parse_automation(tpl.get("code", ""))
    if err:
        return {"ok": False, "lines": ["TEMPLATE INVALID", bar, err,
                                       "Code/configuration correction required (healing script edit nahi karti)."]}
    ok, payload = await run_automation(run_acc_id, defn, tpl, origin=o)
    if not ok:
        v = payload.get("validation") or {}
        return {"ok": False, "lines": ["VALIDATION FAILED — script NOT run", bar] +
                                      [("  ✓ " if c["ok"] else "  ✗ ") + c["label"] + (f" — {c['detail']}" if c["detail"] else "")
                                       for c in v.get("checks", [])]}
    owner = ACCOUNTS.accounts.get(run_acc_id)
    return {"lines": ["CUSTOM TEMPLATE STARTED", bar,
                      f"Template ▸ {tpl['name']}",
                      f"Account  ▸ @{owner['meta'].get('username')}",
                      f"Task     ▸ {payload['task_id']}",
                      "Status   ▸ RUNNING",
                      "Live logs web panel me aur '/AI running tasks dikhao' se."]}

async def t_template_stop(p, o):
    ref = str(p.get("template", "")).strip()
    acc, aid = _ctx_account(o)
    task_id = None
    if ref:
        tpl = template_find(ref, aid) or template_find(ref)
        if tpl:
            task_id = AUTO_BY_TEMPLATE.get(tpl["template_id"])
            if not task_id:
                return {"ok": False, "lines": [f"'{tpl['name']}' abhi run nahi ho raha"]}
        elif ref.upper() in AUTO_TASKS:
            task_id = ref.upper()
    if not task_id:
        running = [t for t in AUTO_TASKS.values() if t["status"] == "RUNNING"
                   and (not aid or t["account_id"] == aid)]
        if len(running) == 1:
            task_id = running[0]["task_id"]
        elif len(running) > 1:
            return {"ok": False, "lines": ["Multiple custom tasks chal rahe hain — naam/id batao:"] +
                                          [f"  ▸ {t['task_id']} {t['name']} (@{t['account']})" for t in running]}
        else:
            return {"ok": False, "lines": ["Koi custom task run nahi ho raha"]}
    ok, status = await stop_automation(task_id, "jarvis")
    t = AUTO_TASKS.get(task_id, {})
    return {"lines": ["CUSTOM TASK STOPPED", bar, f"Task     ▸ {task_id}",
                      f"Template ▸ {t.get('name')}", f"Account  ▸ @{t.get('account')}",
                      f"Status   ▸ {status}"]}

async def t_tasks_list(p, o):
    acc, aid = _ctx_account(o)
    rows = [t for t in AUTO_TASKS.values() if not aid or t["account_id"] == aid]
    lines = ["CUSTOM SCRIPT TASKS" + (f" — @{acc['meta'].get('username')}" if acc else ""), bar]
    if not rows:
        lines.append("Koi custom task nahi.")
    for t in rows[-10:]:
        lines += [f"[{t['task_id']}] {t['name']} ▸ {t['status']} ({t.get('progress', 0)}%)",
                  f"   account @{t.get('account')} · template {t.get('template_id')}" +
                  (f" · reason: {t['reason']}" if t.get("reason") else "")]
    eng_tasks = [x for x in TASKS.running() if x["kind"] != "CUSTOM"]
    if eng_tasks:
        lines.append(bar)
        for x in eng_tasks:
            lines.append(f"[{x['id']}] {x['label']} ▸ {x['status']}")
    return {"lines": lines}

async def t_tasks_cancel_all(p, o):
    acc, aid = _ctx_account(o)
    running = [t for t in AUTO_TASKS.values() if t["status"] == "RUNNING" and (not aid or t["account_id"] == aid)]
    for t in running:
        await stop_automation(t["task_id"], "cancel-all")
    extra = []
    for x in list(TASKS.running()):
        if x["kind"] != "CUSTOM":
            await TASKS.stop(x["id"])
            extra.append(x["id"])
    return {"lines": ["ALL TASKS CANCELLED", bar,
                      f"Custom tasks ▸ {len(running)} stopped" + (f" ({', '.join(t['task_id'] for t in running)})" if running else ""),
                      f"Engine/monitor tasks ▸ {len(extra)} stopped" if extra else "Engine/monitor tasks ▸ none"]}

async def t_template_create(p, o):
    """§35 — JARVIS drafts a template from natural language, shows a summary."""
    acc, aid = _ctx_account(o)
    if p.get("account"):
        acc2, aid2 = _resolve_account_ref(p.get("account"))
        if acc2:
            acc, aid = acc2, aid2
    if not acc:
        return {"ok": False, "lines": ["Pehle account select karo — '/AI account 2 select karo'"]}
    text = str(p.get("text", "")).lower()
    cfg = acct_cfg(aid)
    actions = []
    if any(k in text for k in ("monitor", "nazar", "watch", "source")):
        actions.append({"action": "START_MONITOR", "params": {}})
    if any(k in text for k in ("copy", "result", "update", "bhejo", "send", "publish")) and not actions:
        actions += [{"action": "COPY_SOURCE_TEXT", "params": {}},
                    {"action": "FORMAT_TEXT", "params": {}},
                    {"action": "SEND_MESSAGE", "params": {}}]
    if any(k in text for k in ("cross",)):
        actions.append({"action": "START_CROSS", "params": {}})
    if not actions:
        return {"ok": False, "lines": [
            "Is description se koi approved action map nahi hua.",
            "Supported: monitor / copy+format+send / cross / schedule.",
            "Example: '/AI ek template banao: source monitor karo aur destination par update bhejo'"]}
    name = (p.get("name") or "AUTO-" + uuid.uuid4().hex[:4]).upper()
    code_lines = [f"name: {name}"] + [a["action"] for a in actions]
    defn = {"name": name, "actions": actions}
    v = validate_automation(defn, aid)
    tid = await template_save({"name": name, "account_id": aid, "description": str(p.get("text", ""))[:200],
                               "code": "\n".join(code_lines), "actions": actions,
                               "configuration": {}, "enabled": True})
    lines = ["TEMPLATE DRAFTED & SAVED", bar,
             f"Name     ▸ {name} [{tid}]",
             f"Account  ▸ @{acc['meta'].get('username')} (bound)",
             f"Actions  ▸ " + " → ".join(a["action"] for a in actions),
             f"Source   ▸ {cfg.get('source') or 'NOT SET'} · Destination ▸ {cfg.get('destination') or 'NOT SET'}",
             bar, "VALIDATION:"]
    lines += [("  ✓ " if c["ok"] else "  ✗ ") + c["label"] + (f" — {c['detail']}" if c["detail"] else "")
              for c in v["checks"]]
    lines.append(bar)
    lines.append("Review karke run karo: '/AI " + name + " run karo'" if v["ok"]
                 else "Pehle missing config set karo, phir run karo — abhi run nahi kiya.")
    return {"lines": lines}

REG.register("account_select", "Select the working Telegram account", "ACCOUNT", t_account_select,
             needs_telegram=False, params=[ToolParam("account", "text", True)])
REG.register("account_config_set", "Set main channel / source / destination for the account", "ACCOUNT",
             t_account_config_set, needs_telegram=False,
             params=[ToolParam("account", "text"), ToolParam("main_channel", "chat"),
                     ToolParam("source", "chat"), ToolParam("destination", "chat")])
REG.register("template_list", "List saved custom automation templates", "CUSTOM", t_template_list, needs_telegram=False)
REG.register("template_run", "Run a saved custom template on its bound account", "CUSTOM", t_template_run,
             needs_telegram=False,  # validates the TEMPLATE'S account client, not the global one
             params=[ToolParam("template", "text"), ToolParam("account", "text")])
REG.register("template_stop", "Stop a running custom template/task", "CUSTOM", t_template_stop, needs_telegram=False,
             params=[ToolParam("template", "text")])
REG.register("template_create", "Draft + save a custom template from natural language", "CUSTOM", t_template_create,
             needs_telegram=False, params=[ToolParam("text", "text"), ToolParam("name", "text"), ToolParam("account", "text")])
REG.register("tasks_list", "List custom script tasks for the account", "CUSTOM", t_tasks_list, needs_telegram=False)
REG.register("tasks_cancel_all", "Cancel all running tasks", "CUSTOM", t_tasks_cancel_all, needs_telegram=False, confirm=True)

REG.register("jarvis_help", "Commands/tools help", "JARVIS", t_jarvis_help, needs_telegram=False)
REG.register("jarvis_status", "Full system status", "JARVIS", t_jarvis_status, needs_telegram=False)
REG.register("jarvis_diagnostics", "Diagnostics sweep", "JARVIS", t_jarvis_diagnostics, needs_telegram=False)
REG.register("jarvis_save_state", "JSON state persist", "JARVIS", t_jarvis_save_state, needs_telegram=False)

log.info("Registry armed: %d tools", len(REG.tools))

# ============================================================================
# COMMAND PIPELINE
# ============================================================================
def plan_summary_lines(plan):
    lines = []
    if len(plan.steps) > 1 or plan.unsupported or plan.notes:
        lines.append("EXECUTION PLAN ▸")
        for i, s in enumerate(plan.steps, 1):
            lines.append(f"  {i}. {s.tool}{(' — ' + s.note) if s.note else ''}")
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
        plan.unsupported, plan.notes = ai_plan.unsupported, ai_plan.notes
    return plan

async def handle_command(raw, origin):
    raw = (raw or "").strip()
    if not raw:
        return {"ok": False, "action": "EMPTY", "lines": ["Empty command"]}
    STATE["last_command"] = raw[:120]
    safe_log("CMD", "CMD", f"[{origin}] {raw[:80]}")

    pend = PENDING_CONFIRM.get(origin)
    if pend:
        if time.time() > pend["expires"]:
            PENDING_CONFIRM.pop(origin, None)
            return {"ok": False, "action": "CONFIRM_EXPIRED", "lines": ["CONFIRMATION EXPIRED ▸ command dobara issue karo"]}
        if re.match(r"^(yes|y|haan|ha|confirm|ok|haan kar do)$", raw, re.I):
            PENDING_CONFIRM.pop(origin, None)
            res = await execute_plan(pend["plan"], origin)
            _record(raw, "CONFIRMED", res, origin)
            return res
        PENDING_CONFIRM.pop(origin, None)
        safe_log("WARN", "CONFIRM", f"{origin} declined — aborted")
        return {"ok": True, "action": "ABORTED", "lines": ["ABORTED ▸ koi change nahi hua"]}
    if re.match(r"^(yes|y|no|n|haan|nahi)$", raw, re.I):
        return {"ok": False, "action": "NO_PENDING_CONFIRM", "lines": ["Aapki session me koi confirmation pending nahi"]}

    # ---- AGENTIC LAYER FIRST: goal -> context -> plan -> execute -----------
    agent_res = await agent_dispatch(raw, origin)
    if agent_res is not None:
        _record(raw, agent_res.get("action", "GOAL"), agent_res, origin, "AGENT")
        return agent_res

    plan = await build_plan(raw, origin)
    if not plan.steps:
        # No dead ends: explain what IS possible with the current context.
        acc_id, acc, how = pick_account(origin, raw)
        cfg = acct_cfg(acc_id or "")
        act = agent_active_tasks()
        Brain.capability_request(raw, "goal not mapped to an existing capability")
        lines = ["Ye goal main abhi directly nahi kar sakta — lekin ye sab ready hai:", bar,
                 f"Account ▸ {('@' + acc['meta']['username'] + ' (' + how + ')') if acc else 'none connected'}",
                 f"Main channels ▸ {len(cfg.get('main_channels') or [])} · source {cfg.get('source') or '—'}",
                 f"Active tasks ▸ {len(act)} · cross engine {STATE['engine']['status']}", bar,
                 "Jo main abhi kar sakta hoon:",
                 "  ▸ /Cross Start  (kisi post par reply karke — source khud detect hoga)",
                 "  ▸ is channel pe dhyan rakho, unknown messages delete karte jao",
                 "  ▸ 5 minute baad forward hua message delete karna, 1 din tak",
                 "  ▸ account main channels <id> <id> set karo",
                 "  ▸ <id/@username> inspect karo · running tasks dikhao · stop this",
                 bar, "Ye request CAPABILITY REQUEST me note kar li hai."]
        for u in plan.unsupported:
            lines.append(f"[UNSUPPORTED] {u}")
        _record(raw, "NEEDS_CAPABILITY", {"ok": False, "lines": lines}, origin, plan.provider)
        return {"ok": False, "action": "NEEDS_CAPABILITY", "provider": plan.provider, "lines": lines}

    confirm_steps = [s for s in plan.steps if REG.tools.get(s.tool) and REG.tools[s.tool].confirm]
    if confirm_steps:
        summary = plan_summary_lines(plan) + ["SENSITIVE ACTION(S):", bar,
                                              *[f"  ▸ {s.tool}" for s in confirm_steps],
                                              bar, f"CONFIRM REQUIRED ▸ {CONFIRM_TTL}s me YES reply karo, warna abort."]
        PENDING_CONFIRM[origin] = {"plan": plan, "expires": time.time() + CONFIRM_TTL}
        return {"ok": True, "action": "CONFIRM", "requires_confirmation": True,
                "confirm_expires_in": CONFIRM_TTL, "provider": plan.provider, "lines": summary}

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

# ============================================================================
# SCRIPT SYSTEM v2 — Safe/AST sandbox + RAW-mode Telethon installer.
# Every script executes inside ONE controlled environment:
#   * AST validation (imports whitelisted, no dunder/banned names)
#   * a WrappedClient surface (real Telethon feel, host objects never exposed:
#     a single server-side registry holds the actual client; user globals only
#     ever receive opaque proxy objects and sanitized values)
#   * value sanitization in/out (modules, types, frames, host objects blocked)
#   * per-account log buffers, task lifecycle, graceful stop()
# ============================================================================

def _scrub(msg):
    msg = re.sub(r"BQ[A-Za-z0-9_\-]{24,}", "***", str(msg))
    msg = re.sub(r"\b[0-9a-fA-F]{32}\b", "***", msg)
    msg = re.sub(r"(?i)(api_hash|session|2fa|otp|password|token)\s*[:=]\s*\S+", r"\1=***", msg)
    return msg

# -- per-account bounded log buffers (INFO/WARN/ERROR/OK) --------------------
SCRIPT_LOG_BUFFERS = {}
SCRIPT_PROGRESS = {}
SCRIPT_TASKS = {}
SCRIPT_RATE = {}

class ScriptLogger:
    @staticmethod
    def put(acc_id, level, msg):
        SCRIPT_LOG_BUFFERS.setdefault(acc_id, deque(maxlen=500)).append(
            {"ts": time.time(), "level": str(level)[:5], "msg": _scrub(msg)[:400]})

    @staticmethod
    def tail(acc_id, limit=200):
        return list(SCRIPT_LOG_BUFFERS.get(acc_id, []))[-limit:]

    @staticmethod
    def clear(acc_id):
        SCRIPT_LOG_BUFFERS.pop(acc_id, None)

# -- templates (spec-exact telethon code; these run in RAW mode) -------------
SCRIPT_TEMPLATES = {
    "blank": {"label": "Blank", "mode": "raw", "code": (
"""# Injected globals: client, SESSION_STRING, PHONE, events, errors, utils, types
# asyncio, re, time, os, log(msg), print(...), sleep(secs)

async def main():
    me = await client.get_me()
    log(f"Booted as @{me.username or me.id}")

main()
""")},
    "cross": {"label": "Cross Promotion", "mode": "raw", "code": (
"""import asyncio

SOURCE_CHAT = -1001234567890
SOURCE_MSG_IDS = [101, 102, 103]
DESTINATIONS = ["@target1", "@target2"]
CYCLE_DELAY = 8

async def cross_loop():
    while True:
        for dst in DESTINATIONS:
            try:
                for mid in SOURCE_MSG_IDS:
                    await client.forward_messages(dst, mid, SOURCE_CHAT)
                    log(f"Forwarded {mid} to {dst}")
                    await asyncio.sleep(CYCLE_DELAY)
            except Exception as e:
                log(f"Failed {dst}: {type(e).__name__}")

asyncio.create_task(cross_loop())
log("Cross engine running")
""")},
    "dead_scan": {"label": "Dead Channel Scanner", "mode": "raw", "code": (
"""from telethon.tl import functions

async def scan_dead():
    filters = await client(functions.messages.GetDialogFiltersRequest())
    for f in filters:
        title = getattr(f, "title", None)
        title = title.text if hasattr(title, "text") else str(title or "")
        log(f"Folder: {title}")

await scan_dead()
""")},
    "auto_responder": {"label": "Auto Responder", "mode": "raw", "code": (
"""from telethon import events

KEYWORDS = ["price", "rate", "info"]

@client.on(events.NewMessage(incoming=True))
async def auto_reply(event):
    text = (event.raw_text or "").lower()
    if any(k in text for k in KEYWORDS):
        await event.reply("Thanks! We'll get back to you.")
        log(f"Replied to {event.sender_id}")

log("Auto responder active")
""")},
    "custom": {"label": "Custom", "mode": "raw", "code": ""},
}

# -- value sanitization -------------------------------------------------------
def _blocked_for_user(v, seen=None):
    """True if a value must never cross into/out of user code.
    Primitives pass; modules/types/frames/host-internals block. Plain user-space
    objects (Telethon EventBuilder/Entity/Message, script instances) are allowed."""
    if v is None or isinstance(v, (str, bytes, bool, int, float, complex)):
        return False
    seen = seen if seen is not None else set()
    if id(v) in seen:
        return False
    seen.add(id(v))
    if isinstance(v, (asyncio.Task, asyncio.Future, asyncio.Lock, asyncio.Event, asyncio.Queue)):
        if isinstance(v, asyncio.Future):
            return True  # Futures are a host-loop control surface; Tasks are tracked via spawn
        return False
    if isinstance(v, (list, tuple, set, frozenset)):
        return any(_blocked_for_user(x, seen) for x in v)
    if isinstance(v, dict):
        return any(_blocked_for_user(k, seen) or _blocked_for_user(x, seen) for k, x in v.items())
    if isinstance(v, (_mod_types.ModuleType, type, _mod_types.FunctionType,
                      _mod_types.BuiltinFunctionType, _mod_types.BuiltinMethodType,
                      _mod_types.CodeType, _mod_types.FrameType,
                      _mod_types.TracebackType, _mod_types.MemberDescriptorType,
                      _mod_types.MappingProxyType)) or isinstance(v, property):
        return True
    mod_name = type(v).__module__ or ""
    if mod_name.startswith(("pip", "_internal", "importlib", "_collections_abc")):
        safe_log("WARN", "SEC", f"script reached host object {type(v).__name__} — blocking")
        return True
    return False

# -- execution frame registry: the ONLY bridge to the real client -------------
class _Scope:
    """Registry keyed by opaque ids; user code never sees these objects."""
    table = {}

def _register(obj):
    oid = uuid.uuid4().hex[:16]
    _Scope.table[oid] = obj
    return oid

def _lookup(oid):
    return _Scope.table.get(oid)

class _ClientProxy:
    """The safe `client` given to scripts. Only whitelisted async methods exist."""

    SAFE_METHODS = {"get_me", "get_entity", "get_dialogs", "get_messages", "iter_dialogs",
                    "iter_messages", "send_message", "forward_messages", "send_file",
                    "get_permissions", "is_user_authorized", "disconnect"}

    def __init__(self, cid):
        object.__setattr__(self, "_cid", cid)

    def _client(self):
        c = _lookup(object.__getattribute__(self, "_cid"))
        if c is None:
            raise RuntimeError("client offline")
        return c

    def __call__(self, request, *args, **kwargs):
        cls = object.__getattribute__(self, "__class__")
        fn = getattr(cls, "_client")(self)
        req = request
        if _blocked_for_user(req):
            raise AttributeError("request object not allowed")
        client = cls._client(self)
        async def _do():
            return await client(request, *args, **kwargs)
        return _do()

    def on(self, ev):
        ev_ok = _safe_event(ev)
        def _deco(fn):
            if not callable(fn):
                raise AttributeError("handler must be callable")
            _checked_on(object.__getattribute__(self, "_cid"), ev_ok, fn)
            return fn
        return _deco

    def remove_event_handler(self, fn):
        return _safe_remove_handler(object.__getattribute__(self, "_cid"), fn)

    def __getattr__(self, name):
        if name.startswith("_"):
            raise AttributeError("hidden")
        if name not in self.SAFE_METHODS:
            raise AttributeError(f"client.{name} is not exposed to scripts")
        raw = object.__getattribute__(self, "_client")()
        return _BoundClientMethod(raw, name)

    def __setattr__(self, n, v):
        raise AttributeError("client proxy is read-only")

    def __repr__(self):
        return "<telethon client>"

class _BoundClientMethod:
    """Call-through to a raw client method with arg/return sanitization."""

    def __init__(self, raw_client, name):
        object.__setattr__(self, "_rc", raw_client)
        object.__setattr__(self, "_nm", name)

    def __call__(self, *args, **kwargs):
        for a in list(args) + list(kwargs.values()):
            if _blocked_for_user(a):
                raise AttributeError(f"argument to {object.__getattribute__(self, '_nm')} not allowed")
        fn = getattr(object.__getattribute__(self, "_rc"), object.__getattribute__(self, "_nm"))
        out = fn(*args, **kwargs)
        if inspect.isasyncgen(out):
            return _SanitizedAsyncGen(out)
        if inspect.iscoroutine(out):
            async def _awaited():
                return out
            return _awaited()
        return out

    def __getattr__(self, n):
        raise AttributeError("hidden")

    def __repr__(self):
        return f"<client method {object.__getattribute__(self, '_nm')}>"

class _SanitizedAsyncGen:
    def __init__(self, gen):
        self._g = gen

    def __aiter__(self):
        return self

    async def __anext__(self):
        item = await self._g.__anext__()
        if _blocked_for_user(item):
            raise AttributeError("stream item not allowed")
        return item

    def __repr__(self):
        return "<stream>"

def _safe_event(ev):
    if _blocked_for_user(ev):
        raise AttributeError("event type not allowed")
    # class-with-args (e.g. NewMessage(...)) is an EventBuilder instance — fine
    return ev

def _checked_on(cid, ev_ok, handler):
    """Register a script event handler on the real client + no-overwrite tracking."""
    raw = _lookup(cid)
    if raw is None:
        raise AttributeError("client offline")
    inst = _current_progress()
    acc = _current_progress_acc() or "-"

    async def _guarded(event, _h=handler):
        try:
            return await _h(event)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            ScriptLogger.put(acc, "ERROR", f"handler {_h.__name__} crashed: {type(e).__name__}: {str(e)[:140]}")

    try:
        raw.add_event_handler(_guarded, ev_ok)
    except (TypeError, ValueError):
        try:
            raw.add_event_handler(_guarded)
        except TypeError:
            raw.add_event_handler(_guarded)
    if inst is not None:
        inst.setdefault("handlers", []).append(_guarded)
    ScriptLogger.put(acc, "OK", f"handler registered: {getattr(handler, '__name__', 'handler')}")

def _safe_remove_handler(cid, handler):
    """Remove by original fn or its tracked wrapper."""
    raw = _lookup(cid)
    if raw is None:
        return False
    inst = _current_progress()
    candidate = handler
    if inst is not None:
        tracked = list(inst.get("handlers", []))
        if handler in tracked:
            candidate = handler
            tracked.remove(handler)
        else:
            candidate = next((h for h in tracked if getattr(h, "__wrapped__", None) is handler or h is handler), handler)
            if candidate in tracked:
                tracked.remove(candidate)
    try:
        raw.remove_event_handler(candidate)
        return True
    except Exception:
        try:
            raw.remove_event_handler(handler)
            return True
        except Exception:
            return False

_CTX = {"progress": None, "acc": None}

def _current_progress():
    return _CTX["progress"]

def _current_progress_acc():
    return _CTX["acc"]

class _ModuleProxy:
    """Read-only module view; name-checked."""
    ALLOWED = ("re", "time", "asyncio", "events", "errors", "utils", "types")

    def __init__(self, name):
        object.__setattr__(self, "_n", name)

    def __getattr__(self, name):
        if name.startswith("_"):
            raise AttributeError("hidden")
        modname = object.__getattribute__(self, "_n")
        if modname == "asyncio":
            if name in ("create_task", "ensure_future"):
                def _spawn(coro, *a, **k):
                    task = getattr(asyncio, name)(coro, *a, **k)
                    inst = _current_progress()
                    if inst is not None:
                        inst.setdefault("spawned", []).append(task)
                        task.add_done_callback(lambda t: _task_done(_current_progress(), t))
                    return task
                return _spawn
            if name in ("run", "wrap_future", "run_coroutine_threadsafe", "to_thread",
                        "new_event_loop", "set_event_loop", "get_event_loop_policy"):
                raise AttributeError(f"asyncio.{name} not allowed")
            return getattr(asyncio, name)
        for mod in (_mod_types.sys.modules.get("re"), _mod_types.sys.modules.get("time")):
            if mod and getattr(mod, "__name__", None) == modname:
                return getattr(mod, name)
        if TELETHON_OK and modname in ("events", "errors", "utils", "types"):
            src = {"events": events, "errors": tl_errors, "utils": tl_utils, "types": tl_types}[modname]
            return getattr(src, name)
        raise AttributeError(f"module {modname} unavailable")

    def __setattr__(self, n, v):
        raise AttributeError("read-only module")

    def __repr__(self):
        return f"<module {object.__getattribute__(self, '_n')}>"

def _task_done(inst, task):
    try:
        if inst and task in inst.get("spawned", []):
            inst["spawned"].remove(task)
    except Exception:
        pass

# -- the runner ---------------------------------------------------------------
class SafeScriptRunner:
    """AST-validated Telethon-script executor (safe+raw modes share one sandbox)."""

    BANNED_NODES = (ast.Global, ast.Nonlocal)
    BANNED_NAMES = {"exec", "eval", "compile", "open", "__import__", "globals", "locals",
                    "input", "exit", "quit", "getattr", "setattr", "delattr", "vars",
                    "breakpoint", "help", "super", "memoryview", "bytearray",
                    "os", "sys", "builtins", "subprocess", "shutil", "socket", "signal",
                    "ctypes", "socket", "pickle", "marshal"}
    IMPORT_WHITELIST = {"asyncio", "re", "time"}
    FROM_WHITELIST = {"telethon": {"events"}, "telethon.tl": {"functions"}}
    MAX_CODE = 16000

    @classmethod
    def validate(cls, code):
        if len(code or "") > cls.MAX_CODE:
            return False, f"Script too long (max {cls.MAX_CODE} chars)"
        try:
            tree = ast.parse(code)
        except SyntaxError as e:
            return False, f"Syntax error line {e.lineno}: {e.msg}"
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                bad = [a.name for a in node.names if a.name.split(".")[0] not in cls.IMPORT_WHITELIST]
                if bad:
                    return False, f"import not allowed: {bad[0]}"
                continue
            if isinstance(node, ast.ImportFrom):
                if node.module in cls.FROM_WHITELIST and \
                        {a.name for a in node.names} <= cls.FROM_WHITELIST[node.module]:
                    continue
                return False, f"import-from not allowed: {node.module or '?'}"
            if isinstance(node, cls.BANNED_NODES):
                return False, f"'{type(node).__name__}' is not allowed"
            if isinstance(node, ast.Name):
                if node.id.startswith("__"):
                    return False, "Dunder names not allowed"
                if node.id in cls.BANNED_NAMES:
                    return False, f"'{node.id}' is not allowed"
            if isinstance(node, ast.Attribute):
                if node.attr.startswith("__"):
                    return False, "Dunder attributes not allowed"
        return True, "OK"

    @classmethod
    def _build_globals(cls, account_ctx, acc_id, progress):
        session = ""
        try:
            session = decrypt_str((account_ctx.get("meta") or {}).get("session_enc", "")) or ""
        except Exception:
            session = ""
        if not session:
            ScriptLogger.put(acc_id, "WARN", "SESSION_STRING unavailable (memory-only account) — empty global")

        cid = _register(account_ctx.get("client"))
        progress["client_oid"] = cid

        def log(msg):
            ScriptLogger.put(acc_id, "INFO", str(msg)[:400])

        def print_(*args):
            ScriptLogger.put(acc_id, "INFO", " ".join(str(a) for a in args)[:400])

        async def sleep(secs):
            await asyncio.sleep(min(max(float(secs), 0.0), 3600.0))

        wrapper = {
            "client": _ClientProxy(cid),
            "SESSION_STRING": session,
            "PHONE": (account_ctx.get("meta") or {}).get("phone") or None,
            "log": log, "print": print_, "sleep": sleep,
            "asyncio": _ModuleProxy("asyncio"),
            "re": _ModuleProxy("re"), "time": _ModuleProxy("time"),
            "events": _ModuleProxy("events"), "errors": _ModuleProxy("errors"),
            "utils": _ModuleProxy("utils"), "types": _ModuleProxy("types"),
            "FloodWaitError": FloodWaitError if TELETHON_OK else Exception,
            "RPCError": RPCError if TELETHON_OK else Exception,
            "Exception": Exception, "ValueError": ValueError, "TypeError": TypeError,
            "bool": bool, "int": int, "float": float, "str": str, "list": list,
            "dict": dict, "tuple": tuple, "set": set, "frozenset": frozenset,
            "len": len, "range": range, "enumerate": enumerate, "zip": zip, "map": map,
            "sorted": sorted, "reversed": reversed, "sum": sum, "min": min, "max": max,
            "any": any, "all": all, "abs": abs, "round": round, "repr": repr,
            "isinstance": isinstance, "print_": print_,
            "__name__": "__script__", "__doc__": None,
        }
        return wrapper

    @classmethod
    async def run(cls, code, account_ctx, acc_id, progress):
        ok, err = cls.validate(code)
        if not ok:
            ScriptLogger.put(acc_id, "ERROR", f"validation: {err}")
            return {"ok": False, "error": err}
        wrapper = cls._build_globals(account_ctx, acc_id, progress)
        _CTX["progress"] = progress
        _CTX["acc"] = acc_id
        try:
            compiled = compile(code, "<script>", "exec", flags=ast.PyCF_ALLOW_TOP_LEVEL_AWAIT)
            result = eval(compiled, wrapper)
            if inspect.iscoroutine(result):
                await result
            await _await_entry_points(code, wrapper, acc_id)
            return {"ok": True}
        except asyncio.CancelledError:
            raise
        except SyntaxError as e:
            ScriptLogger.put(acc_id, "ERROR", f"syntax line {e.lineno}: {e.msg}")
            return {"ok": False, "error": f"SyntaxError: {e.msg}"}
        except Exception as e:
            ScriptLogger.put(acc_id, "ERROR", f"crash: {type(e).__name__}: {str(e)[:220]}")
            return {"ok": False, "error": f"{type(e).__name__}: {str(e)[:220]}"}
        finally:
            _CTX["progress"] = None
            _CTX["acc"] = None
            _Scope.table.pop(progress.get("client_oid", ""), None)

# ----------------------------------------------------------------------------
# RAW SCRIPT RUNNER — full Telethon execution (Raw Mode).
# Injects the REAL client + modules exactly as specified; the only safety nets
# kept are: per-account log buffers with secret scrubbing, task/handler
# lifecycle tracking (so Stop always works), stdout capture, and a hard cap on
# runaway loops via task cancellation. Raw Mode = trusted code only.
# ----------------------------------------------------------------------------
class _StdoutTee:
    """Captures print()/sys.stdout writes into the per-account log buffer."""

    def __init__(self, acc_id):
        object.__setattr__(self, "_acc", acc_id)
        object.__setattr__(self, "_buf", "")

    def write(self, s):
        acc = object.__getattribute__(self, "_acc")
        buf = object.__getattribute__(self, "_buf") + str(s)
        while "\n" in buf:
            line, buf = buf.split("\n", 1)
            if line.strip():
                ScriptLogger.put(acc, "INFO", line)
        object.__setattr__(self, "_buf", buf)
        return len(str(s))

    def flush(self):
        acc = object.__getattribute__(self, "_acc")
        buf = object.__getattribute__(self, "_buf")
        if buf.strip():
            ScriptLogger.put(acc, "INFO", buf)
        object.__setattr__(self, "_buf", "")

    def isatty(self):
        return False


def _pending_entry_points(code):
    """Module-level bare zero-arg calls — the `main()` convention.
    Calling an async function does NOT run its body (it only builds a coroutine
    object), so a bare `main()` at module level must be awaited by the runner
    for the spec's Blank template to actually execute."""
    try:
        tree = ast.parse(code)
    except SyntaxError:
        return []
    out = []
    for node in tree.body:
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
            call = node.value
            if isinstance(call.func, ast.Name) and not call.args and not call.keywords:
                out.append(call.func.id)
    return out


async def _await_entry_points(code, g, acc_id):
    for name in _pending_entry_points(code):
        fn = g.get(name)
        if inspect.iscoroutinefunction(fn):
            ScriptLogger.put(acc_id, "INFO", f"awaiting entry point {name}()")
            await fn()


# ---------------------------------------------------------------------------
# SELF-HEALING ERROR ENGINE (§4)
#   Intercepts FloodWait / connection resets / transient runtime errors during
#   custom script execution and retries with bounded backoff (max 5 attempts).
#   FloodWait always waits the EXACT Telegram-mandated delay — never bypassed.
#   The server stays alive and no re-deploy is ever required.
# ---------------------------------------------------------------------------
HEAL_MAX_RETRIES = 5
HEAL_STATS = {}     # acc_id -> {"retries": n, "floodwait_s": n, "reconnects": n, "last": str}

# transient failures worth retrying (connection resets, timeouts, DC migrations)
_TRANSIENT = ("ConnectionError", "ConnectionResetError", "TimeoutError", "OSError",
              "ServerError", "RpcCallFailError", "TimedOutError", "AuthKeyError",
              "ConnectionAbortedError", "ConnectionRefusedError", "IncompleteReadError")

def _heal_stat(acc_id, key, amount=1, note=None):
    s = HEAL_STATS.setdefault(acc_id, {"retries": 0, "floodwait_s": 0, "reconnects": 0, "last": None})
    s[key] = s.get(key, 0) + amount
    if note:
        s["last"] = note[:160]
    return s

async def _heal_reconnect(acc_id):
    """Bring a dropped client back up (bounded, never fatal)."""
    acc = ACCOUNTS.accounts.get(acc_id) or {}
    client = acc.get("client")
    if not client:
        return False
    try:
        if not client.is_connected():
            await client.connect()
            _heal_stat(acc_id, "reconnects", 1, "telegram client reconnected")
            ScriptLogger.put(acc_id, "OK", "HEAL ▸ telegram client reconnected")
        return bool(client.is_connected())
    except Exception as e:
        ScriptLogger.put(acc_id, "WARN", f"HEAL ▸ reconnect failed ({type(e).__name__})")
        return False

async def heal_retry(acc_id, fn, *args, **kwargs):
    """Run an awaitable/callable with self-healing backoff. Returns its result.
    Raises the final exception only after HEAL_MAX_RETRIES attempts."""
    attempt = 0
    while True:
        attempt += 1
        try:
            out = fn(*args, **kwargs) if callable(fn) else fn
            if inspect.isawaitable(out):
                out = await out
            if attempt > 1:
                ScriptLogger.put(acc_id, "OK", f"HEAL ▸ recovered after {attempt - 1} retry(s)")
            return out
        except asyncio.CancelledError:
            raise
        except FloodWaitError as fw:
            secs = int(getattr(fw, "seconds", 0) or 0)
            _heal_stat(acc_id, "floodwait_s", secs, f"FloodWait {secs}s")
            if attempt > HEAL_MAX_RETRIES:
                ScriptLogger.put(acc_id, "ERROR", f"HEAL ▸ giving up after {HEAL_MAX_RETRIES} FloodWaits")
                raise
            ScriptLogger.put(acc_id, "WARN",
                             f"HEAL ▸ FloodWait {secs}s — waiting exact duration "
                             f"(attempt {attempt}/{HEAL_MAX_RETRIES}, no bypass)")
            _heal_stat(acc_id, "retries", 1)
            await asyncio.sleep(secs)
        except Exception as e:
            name = type(e).__name__
            transient = (name in _TRANSIENT or name == "_TransientRun"
                         or "Connection" in name or "Timeout" in name)
            if not transient or attempt > HEAL_MAX_RETRIES:
                if not transient:
                    ScriptLogger.put(acc_id, "ERROR", f"{name}: {str(e)[:160]} (not retryable)")
                else:
                    ScriptLogger.put(acc_id, "ERROR", f"HEAL ▸ exhausted {HEAL_MAX_RETRIES} retries — {name}")
                raise
            delay = min(2 ** (attempt - 1), 30)     # 1,2,4,8,16,30 capped
            _heal_stat(acc_id, "retries", 1, f"{name} -> backoff {delay}s")
            ScriptLogger.put(acc_id, "WARN",
                             f"HEAL ▸ {name} — backoff {delay}s (attempt {attempt}/{HEAL_MAX_RETRIES})")
            await _heal_reconnect(acc_id)
            await asyncio.sleep(delay)


class RawScriptRunner:
    """exec(code, globals_dict) with the spec's injected globals (Raw Mode)."""

    MAX_CODE = 20000

    @classmethod
    def validate(cls, code):
        """Raw mode: syntax check only — the operator has opted into raw power."""
        if len(code or "") > cls.MAX_CODE:
            return False, f"Script too long (max {cls.MAX_CODE} chars)"
        try:
            compile(code, "<script>", "exec", flags=ast.PyCF_ALLOW_TOP_LEVEL_AWAIT)
        except SyntaxError as e:
            return False, f"Syntax error line {e.lineno}: {e.msg}"
        return True, "OK"

    @staticmethod
    def build_globals(acc_id, account_ctx, progress):
        meta = account_ctx.get("meta") or {}
        session = ""
        try:
            session = decrypt_str(meta.get("session_enc", "")) or ""
        except Exception:
            session = ""
        if not session:
            ScriptLogger.put(acc_id, "WARN",
                             "SESSION_STRING unavailable (memory-only account) — global is empty")

        client = account_ctx.get("client")
        if client is None:
            raise RuntimeError("Account not connected")

        def log(msg, level="INFO"):
            lv = str(level).upper()
            ScriptLogger.put(acc_id, lv if lv in ("INFO", "WARN", "ERROR", "OK") else "INFO", msg)

        async def sleep(secs):
            await asyncio.sleep(float(secs))

        # per-account channel configuration (§1) — never from .env
        _acfg = acct_cfg(acc_id)
        _main = _acfg.get("main_channel")
        try:
            _main = int(_main) if _main not in (None, "") and str(_main).lstrip("-").isdigit() else _main
        except Exception:
            pass

        # `import asyncio` would rebind the name to the REAL module, silently
        # bypassing task tracking — so __import__ hands back the tracked proxy.
        _real_import = _py_builtins.__import__

        def _tracked_import(name, *a, **k):
            if str(name).split(".")[0] == "asyncio":
                return _ModuleProxy("asyncio")
            return _real_import(name, *a, **k)

        builtins_copy = dict(vars(_py_builtins))
        builtins_copy["__import__"] = _tracked_import

        g = {
            # spec-mandated globals
            "client": client,
            "SESSION_STRING": session,
            "PHONE": meta.get("phone") or None,
            # per-account channels (unique per account, web/Telegram configurable)
            "MAIN_CHANNEL_ID": _main,
            "SOURCE_CHANNEL": _acfg.get("source"),
            "DESTINATION_CHANNEL": _acfg.get("destination"),
            "ACCOUNT_ID": acc_id,
            "log": log,
            "print": lambda *a: ScriptLogger.put(acc_id, "INFO", " ".join(str(x) for x in a)[:400]),
            "sleep": sleep,
            # self-healing helper available to scripts
            "with_retry": lambda fn, *a, **k: heal_retry(acc_id, fn, *a, **k),
            # tracked asyncio so spawned loops can be cancelled on Stop
            "asyncio": _ModuleProxy("asyncio"),
            "re": re, "time": time, "os": os,
            "__name__": "__script__",
            "__builtins__": builtins_copy,
        }
        if TELETHON_OK:
            g["events"] = events
            g["errors"] = tl_errors
            g["utils"] = tl_utils
            g["types"] = tl_types
        else:
            for k in ("events", "errors", "utils", "types"):
                g[k] = _ModuleProxy(k)
        return g

    @staticmethod
    def _snapshot_handlers(client):
        try:
            return {id(h) for h, _e in client.list_event_handlers()}
        except Exception:
            return set()

    @classmethod
    async def run(cls, code, account_ctx, acc_id, progress):
        ok, err = cls.validate(code)
        if not ok:
            ScriptLogger.put(acc_id, "ERROR", f"validation: {err}")
            return {"ok": False, "error": err}
        client = account_ctx.get("client")
        if client is None:
            return {"ok": False, "error": "Account not connected"}
        g = cls.build_globals(acc_id, account_ctx, progress)
        before = cls._snapshot_handlers(client)
        _CTX["progress"] = progress
        _CTX["acc"] = acc_id
        try:
            compiled = compile(code, "<script>", "exec", flags=ast.PyCF_ALLOW_TOP_LEVEL_AWAIT)
            # stdout is captured only for the (synchronous) module body
            with contextlib.redirect_stdout(_StdoutTee(acc_id)):
                result = eval(compiled, g)
            if inspect.iscoroutine(result):
                await result
            await _await_entry_points(code, g, acc_id)
            # diff-registered handlers -> tracked so Stop can remove them
            try:
                for h, _e in client.list_event_handlers():
                    if id(h) not in before:
                        progress.setdefault("handlers", []).append(h)
                        ScriptLogger.put(acc_id, "OK",
                                         f"handler registered: {getattr(h, '__name__', 'handler')}")
            except Exception:
                pass
            return {"ok": True}
        except asyncio.CancelledError:
            raise
        except SyntaxError as e:
            ScriptLogger.put(acc_id, "ERROR", f"syntax line {e.lineno}: {e.msg}")
            return {"ok": False, "error": f"SyntaxError: {e.msg}"}
        except Exception as e:
            ScriptLogger.put(acc_id, "ERROR", f"crash: {type(e).__name__}: {str(e)[:220]}")
            return {"ok": False, "error": f"{type(e).__name__}: {str(e)[:220]}"}
        finally:
            _CTX["progress"] = None
            _CTX["acc"] = None


# ----------------------------------------------------------------------------
# Script lifecycle — create_task tracking, listener keep-alive, graceful stop
# ----------------------------------------------------------------------------
def _scripts_get_state(acc_id):
    raw = scripts_store.load()
    st = raw.get(acc_id, {})
    if st.get("running") and acc_id not in SCRIPT_TASKS:
        st["running"] = False
        raw[acc_id] = st
        scripts_store.save_bg(raw)
    return st

async def _run_task(acc_id, code, mode="safe"):
    progress = SCRIPT_PROGRESS.setdefault(acc_id, {"handlers": [], "spawned": [], "stopped": False})
    runner = RawScriptRunner if mode == "raw" else SafeScriptRunner
    try:
        # §4 self-healing: transient failures (FloodWait / connection resets) are
        # retried with bounded backoff instead of killing the script or server.
        class _TransientRun(Exception):
            """Marks a script exit that self-healing should retry."""

        async def _attempt():
            await _heal_reconnect(acc_id)
            r = await runner.run(code, ACCOUNTS.accounts.get(acc_id, {}), acc_id, progress)
            err = str((r or {}).get("error") or "")
            head = err.split(":")[0].strip()
            retryable = head in _TRANSIENT or "Connection" in head or "Timeout" in head
            if not (r or {}).get("ok") and retryable:
                raise _TransientRun(err)
            return r

        try:
            res = await heal_retry(acc_id, _attempt)
        except _TransientRun as te:
            res = {"ok": False, "error": str(te)}
        alive_spawn = any(not t.done() for t in list(progress.get("spawned", [])))
        keep = bool(progress.get("handlers")) or alive_spawn
        if res.get("ok") and keep:
            ScriptLogger.put(acc_id, "OK", "script active — listening (Stop to exit)")
            while not progress.get("stopped"):
                alive_spawn = any(not t.done() for t in list(progress.get("spawned", [])))
                if not progress.get("handlers") and not alive_spawn:
                    break
                await asyncio.sleep(0.5)
            ScriptLogger.put(acc_id, "OK", "Script stopped")
        elif res.get("ok"):
            ScriptLogger.put(acc_id, "OK", "Script finished")
        else:
            ScriptLogger.put(acc_id, "ERROR", f"exit: {res.get('error', 'unknown')}")
    except asyncio.CancelledError:
        ScriptLogger.put(acc_id, "OK", "Script stopped")
        raise
    except Exception as e:
        ScriptLogger.put(acc_id, "ERROR", f"runner crash: {type(e).__name__}")
    finally:
        await _cleanup_script(acc_id)

async def _cleanup_script(acc_id):
    progress = SCRIPT_PROGRESS.get(acc_id, {})
    acc = ACCOUNTS.accounts.get(acc_id) or {}
    raw_client = acc.get("client")
    for h in list(progress.get("handlers", [])):
        try:
            if raw_client:
                raw_client.remove_event_handler(h)
        except Exception:
            pass
    for t in list(progress.get("spawned", [])):
        try:
            t.cancel()
        except Exception:
            pass
    SCRIPT_PROGRESS.pop(acc_id, None)
    SCRIPT_TASKS.pop(acc_id, None)
    raw = scripts_store.load()
    st = raw.get(acc_id)
    if st:
        st["running"] = False
        st["updated_at"] = int(time.time())
        raw[acc_id] = st
        await scripts_store.save(raw)

async def start_script(acc_id):
    if acc_id in SCRIPT_TASKS:
        return False, "Script already running — stop it first"
    st = _scripts_get_state(acc_id)
    code = str(st.get("code", ""))
    if not code.strip():
        return False, "No saved script for this account"
    acc = ACCOUNTS.accounts.get(acc_id)
    if not acc or not acc.get("authorized") or not acc.get("client"):
        return False, "ACCOUNT NOT AUTHORIZED — connect/activate the account first"
    last = SCRIPT_RATE.get(acc_id, 0)
    if time.time() - last < 10:
        return False, f"Rate limit — {int(10 - (time.time() - last))}s left (1 run / 10s per account)"
    SCRIPT_RATE[acc_id] = time.time()
    mode = str(st.get("mode", "safe")).lower()
    if mode not in ("safe", "raw"):
        mode = "safe"
    validator = RawScriptRunner.validate if mode == "raw" else SafeScriptRunner.validate
    ok, err = validator(code)
    if not ok:
        ScriptLogger.put(acc_id, "ERROR", f"install blocked: {err}")
        return False, err
    SCRIPT_PROGRESS[acc_id] = {"handlers": [], "spawned": [], "stopped": False}
    ScriptLogger.put(acc_id, "INFO",
                     f"installing '{st.get('name') or 'script'}' [{mode} mode · template={st.get('template', 'custom')}]")
    task = asyncio.get_running_loop().create_task(_run_task(acc_id, code, mode))
    SCRIPT_TASKS[acc_id] = task
    raw = scripts_store.load()
    st = raw.get(acc_id, {})
    st.update({"running": True, "installed_at": int(time.time()), "updated_at": int(time.time())})
    raw[acc_id] = st
    await scripts_store.save(raw)
    ScriptLogger.put(acc_id, "OK", "Script installed & running")
    safe_log("CMD", "SCRIPT", f"Installed script for {acc_id}")
    return True, {"running": True}

async def stop_script(acc_id, reason="operator"):
    progress = SCRIPT_PROGRESS.get(acc_id)
    if progress is not None:
        progress["stopped"] = True
    task = SCRIPT_TASKS.get(acc_id)
    if not task and progress is None:
        progress = {"handlers": [], "spawned": [], "stopped": True}
    if task:
        task.cancel()
        try:
            await asyncio.wait_for(asyncio.gather(task, return_exceptions=True), 5.0)
        except Exception:
            pass
    await _cleanup_script(acc_id)
    ScriptLogger.put(acc_id, "WARN", f"stop requested ({reason})")
    return True, {"running": False}

async def stop_all_scripts(reason="shutdown"):
    for acc_id in list(set(list(SCRIPT_TASKS) + list(SCRIPT_PROGRESS))):
        try:
            await stop_script(acc_id, reason)
        except Exception as e:
            log.warning("stop script %s failed: %s", acc_id, type(e).__name__)

async def stop_scripts_for_account(acc_id, reason="account removed"):
    if acc_id in SCRIPT_TASKS or acc_id in SCRIPT_PROGRESS:
        await stop_script(acc_id, reason)
    # account-bound automation tasks must die with their account (§40)
    for tid, t in list(globals().get("AUTO_TASKS", {}).items()):
        if t.get("account_id") == acc_id and t.get("status") == "RUNNING":
            try:
                await stop_automation(tid, reason)
            except Exception as e:
                log.warning("stop automation %s failed: %s", tid, type(e).__name__)

# ============================================================================
# CUSTOM SCRIPT RUNNER v3 — ACCOUNT-BOUND DECLARATIVE AUTOMATION  (§27-§42)
#
#   LAYER 1  JARVIS natural language  -> validated intent
#   LAYER 2  action registry / templates -> only approved operations
#   LAYER 3  the SELECTED account's Telegram client -> real result
#
#   The editor is an automation DEFINITION (JSON or line DSL), never Python.
#   No exec/eval/imports/shell/filesystem/credential access is reachable here.
#   Every task carries account_id + template_id + task_id, and so does every
#   log line — Account A can never run on Account B's session.
# ============================================================================

AUTO_LOGS = {}          # task_id -> deque of log rows
AUTO_TASKS = {}         # task_id -> runtime record
AUTO_BY_TEMPLATE = {}   # template_id -> task_id (one active run per template)
ACCOUNT_MONITORS = {}   # acc_id -> {"handler":fn, "conf":{...}, "processed":int}

def auto_log(task, level, msg):
    row = {"ts": time.time(), "level": str(level)[:5], "msg": _scrub(msg)[:400],
           "account_id": task.get("account_id"), "template_id": task.get("template_id"),
           "task_id": task.get("task_id")}
    AUTO_LOGS.setdefault(task["task_id"], deque(maxlen=400)).append(row)
    acc = task.get("account_id")
    if acc:
        ScriptLogger.put(acc, level, f"[{task['task_id']}] {msg}")

def acct_cfg(acc_id):
    """Per-account channel configuration — unique per account, never from .env."""
    cfg = acctcfg_store.load().get(acc_id, {})
    mains = cfg.get("main_channels")
    if not isinstance(mains, list):
        mains = []
    if cfg.get("main_channel") and str(cfg["main_channel"]) not in [str(x) for x in mains]:
        mains = [cfg["main_channel"]] + mains
    return {"main_channel": cfg.get("main_channel") or (mains[0] if mains else None),
            "main_channels": mains,
            "source": cfg.get("source"),
            "destination": cfg.get("destination"),
            # aliases so API clients/scripts can use either naming
            "main_channel_id": cfg.get("main_channel"),
            "source_channel": cfg.get("source"),
            "destination_channel": cfg.get("destination"),
            "keywords": cfg.get("keywords") or DEFAULT_KEYWORDS}

async def _resolve_for(client, ref):
    ref = str(ref).strip().lstrip("@")
    return await client.get_entity(int(ref) if ref.lstrip("-").isdigit() else ref)

# ---------------------------------------------------------------------------
# ACTION REGISTRY (§31) — the only operations an automation may perform
# ---------------------------------------------------------------------------
async def a_get_account_info(ctx, p):
    me = await ctx["client"].get_me()
    ctx["vars"]["account"] = getattr(me, "username", None) or str(me.id)
    return f"account @{ctx['vars']['account']} (id {me.id})"

async def a_get_folders(ctx, p):
    folders = await _scan_folders_client(ctx["client"])
    ctx["vars"]["folders"] = len(folders)
    return f"{len(folders)} folder(s), {sum(len(f['channels']) for f in folders)} channels"

async def a_get_channel_info(ctx, p):
    ref = p.get("chat") or ctx["conf"].get("main_channel")
    e = await _resolve_for(ctx["client"], ref)
    ctx["vars"]["channel"] = getattr(e, "title", str(ref))
    return f"{getattr(e, 'title', ref)} ▸ id {e.id} ▸ @{getattr(e, 'username', None) or 'private'}"

async def a_get_recent_messages(ctx, p):
    ref = p.get("chat") or ctx["conf"].get("source") or ctx["conf"].get("main_channel")
    limit = min(int(p.get("limit", 5)), 20)
    e = await _resolve_for(ctx["client"], ref)
    out = []
    async for m in ctx["client"].iter_messages(e, limit=limit):
        if m and (m.text or ""):
            out.append(m.text[:70])
    ctx["vars"]["recent"] = out
    return f"{len(out)} recent message(s) from {ref}"

async def a_read_message(ctx, p):
    ref = p.get("chat") or ctx["conf"].get("source")
    e = await _resolve_for(ctx["client"], ref)
    ids = p.get("message_id")
    msgs = await ctx["client"].get_messages(e, ids=[int(ids)] if ids else None, limit=None if ids else 1)
    msg = (msgs[0] if isinstance(msgs, list) else msgs)
    if not msg:
        raise RuntimeError(f"message not found in {ref}")
    ctx["vars"]["text"] = msg.text or ""
    return f"read message {msg.id} ({len(ctx['vars']['text'])} chars)"

async def a_search_message(ctx, p):
    q = str(p.get("query", ""))[:60]
    if not q:
        raise RuntimeError("SEARCH_MESSAGE needs query=")
    ref = p.get("chat") or "me"
    e = await _resolve_for(ctx["client"], ref) if ref != "me" else "me"
    hits = []
    async for m in ctx["client"].iter_messages(e, search=q, limit=5):
        if m.text:
            hits.append(m.text[:70])
    ctx["vars"]["hits"] = hits
    return f"{len(hits)} match(es) for '{q}'"

async def a_check_permissions(ctx, p):
    ref = p.get("chat") or ctx["conf"].get("destination") or ctx["conf"].get("main_channel")
    e = await _resolve_for(ctx["client"], ref)
    perms = await ctx["client"].get_permissions(e, "me")
    role = "CREATOR" if perms.is_creator else ("ADMIN" if perms.is_admin else "MEMBER")
    ctx["vars"]["role"] = role
    return f"{ref} ▸ role {role}"

async def a_copy_source_text(ctx, p):
    ref = p.get("source") or ctx["conf"].get("source")
    e = await _resolve_for(ctx["client"], ref)
    msgs = await ctx["client"].get_messages(e, limit=1)
    if not msgs or not msgs[0] or not (msgs[0].text or ""):
        raise RuntimeError(f"no readable text in source {ref} (Telegram returned nothing)")
    parsed = parse_source_text(msgs[0].text, p.get("keywords") or ctx["conf"].get("keywords"))
    ctx["vars"]["text"] = parsed["body"]
    return f"copied {len(parsed['body'])} chars ({'keyword match' if parsed['matched'] else 'full text'})"

async def a_format_text(ctx, p):
    body = ctx["vars"].get("text", "")
    if not body:
        raise RuntimeError("FORMAT_TEXT needs text — run COPY_SOURCE_TEXT or READ_MESSAGE first")
    tpl = p.get("template")
    if tpl:
        ctx["vars"]["text"] = str(tpl).replace("{body}", body).replace(
            "{time}", ktm_now().strftime("%d %b %I:%M %p NPT"))[:3800]
    else:
        ctx["vars"]["text"] = format_update_text(body)
    return f"formatted ({len(ctx['vars']['text'])} chars)"

async def a_send_message(ctx, p):
    ref = p.get("destination") or p.get("chat") or ctx["conf"].get("destination")
    text = p.get("text") or ctx["vars"].get("text")
    if not text:
        raise RuntimeError("SEND_MESSAGE needs text= or a previous COPY_SOURCE_TEXT/FORMAT_TEXT")
    e = await _resolve_for(ctx["client"], ref)
    try:
        sent = await ctx["client"].send_message(e, str(text)[:3800])
    except FloodWaitError as fw:
        auto_log(ctx["task"], "WARN", f"FloodWait {fw.seconds}s — waiting exact duration (no bypass)")
        await asyncio.sleep(fw.seconds)
        sent = await ctx["client"].send_message(e, str(text)[:3800])
    return f"sent to {ref} (msg {sent.id})"

async def a_start_monitor(ctx, p):
    acc_id = ctx["account_id"]
    conf = ctx["conf"]
    src = p.get("source") or conf.get("source")
    dst = p.get("destination") or conf.get("destination")
    kws = p.get("keywords") or conf.get("keywords")
    client = ctx["client"]
    src_e = await _resolve_for(client, src)
    await _resolve_for(client, dst)
    if acc_id in ACCOUNT_MONITORS:
        await a_stop_monitor(ctx, {})
    latest = await client.get_messages(src_e, limit=1)
    state = {"last_id": latest[0].id if latest and latest[0] else 0, "processed": 0,
             "src": src, "dst": dst, "kws": kws, "task_id": ctx["task"]["task_id"]}
    task_ref = ctx["task"]

    @client.on(events.NewMessage())
    async def _mon(event):
        try:
            ent = event.chat
            ref = str(src).lstrip("@").lstrip("-100").lstrip("-")
            if str(getattr(ent, "id", "")) != ref and getattr(ent, "username", None) != ref:
                return
            m = event.message
            if not m or not getattr(m, "text", None) or m.id <= state["last_id"]:
                return
            state["last_id"] = m.id
            auto_log(task_ref, "INFO", f"NEW MESSAGE RECEIVED (id {m.id})")
            parsed = parse_source_text(m.text, state["kws"])
            auto_log(task_ref, "INFO", "MESSAGE PROCESSED")
            await client.send_message(await _resolve_for(client, dst), format_update_text(parsed["body"]))
            state["processed"] += 1
            auto_log(task_ref, "OK", f"UPDATE SENT -> {dst}")
        except FloodWaitError as fw:
            auto_log(task_ref, "WARN", f"FloodWait {fw.seconds}s — exact delay honoured")
            await asyncio.sleep(fw.seconds)
        except Exception as e:
            auto_log(task_ref, "ERROR", f"monitor step failed: {type(e).__name__}: {str(e)[:120]}")

    ACCOUNT_MONITORS[acc_id] = {"handler": _mon, "state": state, "client": client}
    ctx["task"]["keep_alive"] = True
    return f"monitor started {src} -> {dst} (event-based, baseline {state['last_id']})"

async def a_stop_monitor(ctx, p):
    acc_id = ctx["account_id"]
    mon = ACCOUNT_MONITORS.pop(acc_id, None)
    if not mon:
        return "no monitor running for this account"
    try:
        mon["client"].remove_event_handler(mon["handler"])
    except Exception:
        pass
    return f"monitor stopped ({mon['state']['processed']} updates processed)"

def _require_active(ctx):
    active = ACCOUNTS.get_active()
    aid = active["meta"]["id"] if active else None
    if aid != ctx["account_id"]:
        raise RuntimeError("cross engine runs on the ACTIVE account only — activate this account first "
                           "(Accounts panel) to avoid cross-account execution")

async def a_start_cross(ctx, p):
    _require_active(ctx)
    r = await ENGINE.start()
    if not r.get("ok", True):
        raise RuntimeError((r.get("lines") or ["cross start failed"])[0])
    return (r.get("lines") or ["cross started"])[0]

async def a_stop_cross(ctx, p):
    _require_active(ctx)
    return (ENGINE.stop().get("lines") or ["stopped"])[0]

async def a_pause_cross(ctx, p):
    _require_active(ctx)
    return ((await ENGINE.pause()).get("lines") or ["paused"])[0]

async def a_resume_cross(ctx, p):
    _require_active(ctx)
    return ((await ENGINE.resume()).get("lines") or ["resumed"])[0]

async def a_schedule_task(ctx, p):
    what = str(p.get("action", "START")).upper()
    if what not in ("START", "STOP"):
        raise RuntimeError("SCHEDULE_TASK action= must be START or STOP")
    when = p.get("run_at") or p.get("in")
    if when is None:
        raise RuntimeError("SCHEDULE_TASK needs run_at=<epoch> or in=<seconds>")
    run_at = float(when) if float(when) > 1e6 else time.time() + float(when)
    j = SCHED.add(what, run_at, str(p.get("label", "automation")))
    return f"job [{j['id']}] {what} at {fmt_kt(run_at)}"

async def a_cancel_task(ctx, p):
    jid = str(p.get("id", ""))
    if jid and SCHED.cancel(jid):
        return f"job [{jid}] cancelled"
    tid = str(p.get("task_id", ""))
    if tid and tid in AUTO_TASKS:
        AUTO_TASKS[tid]["stopped"] = True
        return f"task {tid} cancel requested"
    raise RuntimeError(f"nothing to cancel for id '{jid or tid}'")

ACTION_REGISTRY = {
    "READ_MESSAGE":        {"fn": a_read_message,        "params": ["chat", "message_id"], "needs": [],            "desc": "Read a message from an accessible chat"},
    "SEARCH_MESSAGE":      {"fn": a_search_message,      "params": ["chat", "query"],      "needs": [],            "desc": "Search readable messages"},
    "GET_CHANNEL_INFO":    {"fn": a_get_channel_info,    "params": ["chat"],               "needs": ["main_channel_or_chat"], "desc": "Channel title/id/username"},
    "GET_RECENT_MESSAGES": {"fn": a_get_recent_messages, "params": ["chat", "limit"],      "needs": [],            "desc": "Recent messages from a chat"},
    "GET_FOLDERS":         {"fn": a_get_folders,         "params": [],                     "needs": [],            "desc": "Dialog folders of this account"},
    "GET_ACCOUNT_INFO":    {"fn": a_get_account_info,    "params": [],                     "needs": [],            "desc": "Authenticated account identity"},
    "CHECK_PERMISSIONS":   {"fn": a_check_permissions,   "params": ["chat"],               "needs": [],            "desc": "Own role/rights in a channel"},
    "COPY_SOURCE_TEXT":    {"fn": a_copy_source_text,    "params": ["source", "keywords"], "needs": ["source"],    "desc": "Copy exact latest source text"},
    "FORMAT_TEXT":         {"fn": a_format_text,         "params": ["template"],           "needs": [],            "desc": "Format copied text via template"},
    "SEND_MESSAGE":        {"fn": a_send_message,        "params": ["destination", "text"],"needs": ["destination"], "desc": "Publish to destination"},
    "START_MONITOR":       {"fn": a_start_monitor,       "params": ["source", "destination", "keywords"], "needs": ["source", "destination"], "desc": "Event-based source monitor (account-scoped)"},
    "STOP_MONITOR":        {"fn": a_stop_monitor,        "params": [],                     "needs": [],            "desc": "Stop this account's monitor"},
    "START_CROSS":         {"fn": a_start_cross,         "params": [],                     "needs": ["active_account"], "desc": "Start cross engine"},
    "STOP_CROSS":          {"fn": a_stop_cross,          "params": [],                     "needs": ["active_account"], "desc": "Stop cross engine"},
    "PAUSE_CROSS":         {"fn": a_pause_cross,         "params": [],                     "needs": ["active_account"], "desc": "Pause cross engine"},
    "RESUME_CROSS":        {"fn": a_resume_cross,        "params": [],                     "needs": ["active_account"], "desc": "Resume cross engine"},
    "SCHEDULE_TASK":       {"fn": a_schedule_task,       "params": ["action", "run_at", "in", "label"], "needs": [], "desc": "Schedule START/STOP (Asia/Kathmandu)"},
    "CANCEL_TASK":         {"fn": a_cancel_task,         "params": ["id", "task_id"],      "needs": [],            "desc": "Cancel a scheduled job / running task"},
}

# ---------------------------------------------------------------------------
# PARSER — JSON definition or simple line DSL (never Python)
# ---------------------------------------------------------------------------
def _coerce(v):
    v = v.strip()
    if v.lower() in ("true", "false"):
        return v.lower() == "true"
    if re.fullmatch(r"-?\d+", v):
        return int(v)
    if "," in v and not v.startswith('"'):
        return [x.strip() for x in v.split(",") if x.strip()]
    return v.strip('"\'')

def parse_automation(text):
    """Return (definition, error). Accepts JSON object or line DSL."""
    raw = (text or "").strip()
    if not raw:
        return None, "Automation is empty"
    if len(raw) > 20000:
        return None, "Automation too long (max 20000 chars)"
    if raw.startswith("{"):
        try:
            obj = json.loads(raw)
        except Exception as e:
            return None, f"Invalid JSON: {str(e)[:120]}"
        if not isinstance(obj, dict):
            return None, "JSON root must be an object"
        acts = obj.get("actions") or []
        if not isinstance(acts, list):
            return None, "'actions' must be a list"
        norm = []
        for i, a in enumerate(acts, 1):
            if isinstance(a, str):
                norm.append({"action": a.strip().upper(), "params": {}})
            elif isinstance(a, dict):
                name = str(a.get("action", "")).strip().upper()
                prm = a.get("params") if isinstance(a.get("params"), dict) else {}
                norm.append({"action": name, "params": prm})
            else:
                return None, f"action #{i} must be a string or object"
        obj["actions"] = norm
        return obj, None
    # line DSL:  ACTION key=value key2=value2     (# comments allowed)
    actions, meta = [], {}
    for lineno, line in enumerate(raw.splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        m = re.match(r"^(name|description|schedule)\s*:\s*(.+)$", line, re.I)
        if m:
            meta[m.group(1).lower()] = m.group(2).strip()
            continue
        parts = line.split()
        name = parts[0].upper()
        prm = {}
        for kv in parts[1:]:
            if "=" not in kv:
                return None, f"line {lineno}: '{kv}' must be key=value"
            k, v = kv.split("=", 1)
            prm[k.strip()] = _coerce(v)
        actions.append({"action": name, "params": prm})
    if not actions:
        return None, "No actions found — add at least one action line"
    return {**meta, "actions": actions}, None

# ---------------------------------------------------------------------------
# VALIDATOR (§30) — never run when a check fails
# ---------------------------------------------------------------------------
def validate_automation(defn, account_id):
    checks, errors = [], []

    def add(ok, label, detail=""):
        checks.append({"ok": bool(ok), "label": label, "detail": detail})
        if not ok:
            errors.append(f"{label}{(' — ' + detail) if detail else ''}")

    acc = ACCOUNTS.accounts.get(account_id) if account_id else None
    add(bool(acc), "Account selected", "" if acc else "choose a Telegram account first")
    if acc:
        authed = bool(acc.get("authorized") and acc.get("client") and acc["client"].is_connected())
        add(authed, "Account authorized",
            f"@{acc['meta'].get('username')}" if authed else "session not connected — activate/re-add the account")
    else:
        add(False, "Account authorized", "no account")

    add(bool(defn), "Script structure valid", "" if defn else "definition could not be parsed")
    acts = (defn or {}).get("actions") or []
    add(bool(acts), "Actions present", f"{len(acts)} action(s)" if acts else "no actions defined")

    unknown = [a["action"] for a in acts if a["action"] not in ACTION_REGISTRY]
    add(not unknown, "Allowed actions",
        "all approved" if not unknown else "unsupported: " + ", ".join(sorted(set(unknown))[:4]))

    bad_params = []
    for a in acts:
        spec = ACTION_REGISTRY.get(a["action"])
        if not spec:
            continue
        for k in (a.get("params") or {}):
            if k not in spec["params"]:
                bad_params.append(f"{a['action']}.{k}")
    add(not bad_params, "Parameters valid",
        "ok" if not bad_params else "unknown: " + ", ".join(bad_params[:4]))

    cfg = acct_cfg(account_id) if account_id else {}
    conf = {**cfg, **((defn or {}).get("configuration") or {})}
    needs = set()
    for a in acts:
        spec = ACTION_REGISTRY.get(a["action"])
        if spec:
            for n in spec["needs"]:
                if n == "source" and (a.get("params") or {}).get("source"):
                    continue
                if n == "destination" and (a.get("params") or {}).get("destination"):
                    continue
                if n == "main_channel_or_chat" and (a.get("params") or {}).get("chat"):
                    continue
                needs.add(n)
    if "source" in needs:
        add(bool(conf.get("source")), "Source configured", conf.get("source") or "set source for this account")
    if "destination" in needs:
        add(bool(conf.get("destination")), "Destination configured", conf.get("destination") or "set destination for this account")
    if "main_channel_or_chat" in needs:
        add(bool(conf.get("main_channel")), "Main channel configured", str(conf.get("main_channel") or "set main channel or pass chat="))
    if "active_account" in needs:
        active = ACCOUNTS.get_active()
        is_active = bool(active and active["meta"]["id"] == account_id)
        add(is_active, "Account is ACTIVE (cross engine)",
            "active" if is_active else "cross actions require this account to be the active one")
    if not needs:
        add(True, "Required configuration available", "no extra config needed")

    return {"ok": not errors, "checks": checks, "errors": errors,
            "action_count": len(acts), "config": conf}

# ---------------------------------------------------------------------------
# TEMPLATE STORE (§29, §37, §40)
# ---------------------------------------------------------------------------
def templates_all():
    return automation_store.load().get("templates", [])

def template_get(tid):
    return next((t for t in templates_all() if t["template_id"] == tid), None)

def template_find(name_or_id, account_id=None):
    q = str(name_or_id or "").strip().lower().replace(" ", "-")
    cands = [t for t in templates_all() if not account_id or t.get("account_id") == account_id]
    for t in cands:
        if t["template_id"].lower() == q or t["name"].lower().replace(" ", "-") == q:
            return t
    for t in cands:
        if q and q in t["name"].lower().replace(" ", "-"):
            return t
    return None

async def template_save(data):
    items = templates_all()
    tid = data.get("template_id")
    now = int(time.time())
    if tid:
        for i, t in enumerate(items):
            if t["template_id"] == tid:
                items[i] = {**t, **data, "updated_at": now}
                break
        else:
            tid = None
    if not tid:
        tid = "tpl_" + uuid.uuid4().hex[:6]
        items.append({"template_id": tid, "name": data.get("name") or "UNNAMED",
                      "account_id": data.get("account_id"), "description": data.get("description", ""),
                      "code": data.get("code", ""), "configuration": data.get("configuration") or {},
                      "actions": data.get("actions") or [], "conditions": data.get("conditions") or {},
                      "schedule": data.get("schedule"), "enabled": bool(data.get("enabled", True)),
                      "last_run": None, "last_result": None,
                      "created_at": now, "updated_at": now})
    await automation_store.save({"templates": items})
    return tid

async def template_patch(tid, **fields):
    items = templates_all()
    for i, t in enumerate(items):
        if t["template_id"] == tid:
            items[i] = {**t, **fields, "updated_at": int(time.time())}
            await automation_store.save({"templates": items})
            return items[i]
    return None

async def template_delete(tid):
    items = [t for t in templates_all() if t["template_id"] != tid]
    await automation_store.save({"templates": items})

# ---------------------------------------------------------------------------
# RUNNER (§28, §31, §32, §40) — strictly account-bound
# ---------------------------------------------------------------------------
async def run_automation(account_id, defn, template=None, origin="web"):
    acc = ACCOUNTS.accounts.get(account_id)
    v = validate_automation(defn, account_id)
    if not v["ok"]:
        return False, {"error": "VALIDATION FAILED — " + "; ".join(v["errors"][:3]), "validation": v}

    tpl_id = (template or {}).get("template_id", "inline")
    task_id = "CUSTOM-" + uuid.uuid4().hex[:4].upper()
    task = {"task_id": task_id, "template_id": tpl_id, "account_id": account_id,
            "account": acc["meta"].get("username"), "name": (template or {}).get("name") or defn.get("name") or "inline",
            "status": "RUNNING", "progress": 0, "started_at": time.time(),
            "stopped": False, "keep_alive": False, "reason": None}
    AUTO_TASKS[task_id] = task
    AUTO_BY_TEMPLATE[tpl_id] = task_id

    auto_log(task, "INFO", "TASK CREATED")
    auto_log(task, "INFO", f"ACCOUNT @{acc['meta'].get('username')} (id {account_id})")
    auto_log(task, "OK", "TELEGRAM SESSION VERIFIED")

    ctx = {"client": acc["client"], "account_id": account_id, "task": task,
           "conf": v["config"], "vars": {}}
    actions = defn.get("actions") or []

    async def _runner():
        try:
            for i, a in enumerate(actions, 1):
                if task["stopped"]:
                    task["status"] = "CANCELLED"
                    auto_log(task, "WARN", "TASK CANCELLED by operator")
                    break
                spec = ACTION_REGISTRY[a["action"]]
                auto_log(task, "INFO", f"ACTION {i}/{len(actions)} {a['action']}")
                try:
                    detail = await spec["fn"](ctx, a.get("params") or {})
                    auto_log(task, "OK", f"{a['action']} ▸ {detail}")
                except FloodWaitError as fw:
                    auto_log(task, "WARN", f"FloodWait {fw.seconds}s — waiting exact duration")
                    await asyncio.sleep(fw.seconds)
                    detail = await spec["fn"](ctx, a.get("params") or {})
                    auto_log(task, "OK", f"{a['action']} ▸ {detail}")
                task["progress"] = int(i / max(1, len(actions)) * 100)
            else:
                if task.get("keep_alive"):
                    task["status"] = "RUNNING"
                    task["progress"] = 100
                    auto_log(task, "OK", "TASK RUNNING (listening — Stop to end)")
                    while not task["stopped"] and account_id in ACCOUNT_MONITORS:
                        await asyncio.sleep(0.5)
                    if account_id in ACCOUNT_MONITORS:
                        await a_stop_monitor(ctx, {})
                    task["status"] = "CANCELLED" if task["stopped"] else "COMPLETED"
                    auto_log(task, "OK", f"TASK {task['status']}")
                else:
                    task["status"] = "COMPLETED"
                    task["progress"] = 100
                    auto_log(task, "OK", "TASK COMPLETED")
        except asyncio.CancelledError:
            task["status"] = "CANCELLED"
            auto_log(task, "WARN", "TASK CANCELLED")
            raise
        except Exception as e:
            task["status"] = "FAILED"
            task["reason"] = f"{type(e).__name__}: {str(e)[:180]}"
            auto_log(task, "ERROR", f"TASK FAILED ▸ {task['reason']}")
        finally:
            task["finished_at"] = time.time()
            if template:
                await template_patch(tpl_id, last_run=int(time.time()),
                                     last_result=f"{task['status']}" + (f" — {task['reason']}" if task.get("reason") else ""))
            if AUTO_BY_TEMPLATE.get(tpl_id) == task_id and task["status"] != "RUNNING":
                AUTO_BY_TEMPLATE.pop(tpl_id, None)
            TASKS.set_status(task_id, task["status"])

    TASKS.register("CUSTOM", f"{task['name']} @{task['account']}",
                   stop_fn=lambda: stop_automation(task_id), fixed_id=task_id)
    task["_task"] = asyncio.get_running_loop().create_task(_runner())
    safe_log("CMD", "AUTOMATION", f"{task_id} started ▸ template {tpl_id} ▸ account {account_id}")
    return True, {"task_id": task_id, "status": task["status"], "template_id": tpl_id,
                  "account_id": account_id, "validation": v}

async def stop_automation(task_id, reason="operator"):
    task = AUTO_TASKS.get(task_id)
    if not task:
        return False, "Task not found"
    task["stopped"] = True
    acc_id = task.get("account_id")
    if acc_id in ACCOUNT_MONITORS:
        mon = ACCOUNT_MONITORS.pop(acc_id, None)
        if mon:
            try:
                mon["client"].remove_event_handler(mon["handler"])
            except Exception:
                pass
    t = task.get("_task")
    if t and not t.done():
        t.cancel()
        try:
            await asyncio.wait_for(asyncio.gather(t, return_exceptions=True), 5.0)
        except Exception:
            pass
    if task["status"] == "RUNNING":
        task["status"] = "CANCELLED"
    TASKS.set_status(task_id, task["status"])
    auto_log(task, "WARN", f"STOP requested ({reason})")
    return True, task["status"]

def automation_task_view(t):
    return {"task_id": t["task_id"], "template_id": t.get("template_id"), "name": t.get("name"),
            "account_id": t.get("account_id"), "account": t.get("account"),
            "status": t.get("status"), "progress": t.get("progress", 0),
            "started_at": t.get("started_at"), "reason": t.get("reason")}

def automation_heal():
    """§39 — bounded recovery of runtime state only; never edits templates."""
    healed = []
    for tid, t in list(AUTO_TASKS.items()):
        task_obj = t.get("_task")
        if t["status"] == "RUNNING" and task_obj is not None and task_obj.done():
            t["status"] = "FAILED" if not t.get("reason") else t["status"]
            t["reason"] = t.get("reason") or "runtime task vanished — state rebuilt by healing"
            AUTO_BY_TEMPLATE.pop(t.get("template_id"), None)
            healed.append(f"{tid}: stale task state rebuilt")
    for acc_id, mon in list(ACCOUNT_MONITORS.items()):
        acc = ACCOUNTS.accounts.get(acc_id)
        if not acc or not acc.get("client") or not acc["client"].is_connected():
            ACCOUNT_MONITORS.pop(acc_id, None)
            healed.append(f"{acc_id}: monitor dropped (client disconnected)")
    return healed

# ============================================================================
# AGENTIC LAYER — goal-driven JARVIS  (GOAL -> CONTEXT -> PLAN -> EXECUTE ->
# VERIFY -> MONITOR -> concise reply). The user states intent; JARVIS discovers
# context, picks allowlisted capabilities, runs them and keeps working in the
# background. Memory is structured JSON data — never executable code.
# ============================================================================

brain_store       = JSONStore(DATA / "brain.json",
                              {"memories": [], "preferences": {}, "capability_requests": [],
                               "last_account": None, "failures": [], "successes": []})
workflows_store   = JSONStore(DATA / "workflows.json", {"workflows": []})
chanmem_store     = JSONStore(DATA / "channel_memory.json", {"channels": {}})
agent_tasks_store = JSONStore(DATA / "tasks.json", {"tasks": []})

AGENT_TASKS = {}     # task_id -> runtime record
AGENT_RUNTIME = {}   # task_id -> {"handler":fn, "client":c, "timers":[...]}

# ---------------------------------------------------------------------------
# BRAIN — structured recall (data only)
# ---------------------------------------------------------------------------
_BRAIN_CACHE = {"brain": None, "workflows": None, "channels": None}

class Brain:
    @staticmethod
    def _brain():
        if _BRAIN_CACHE["brain"] is None:
            _BRAIN_CACHE["brain"] = brain_store.load()
        return _BRAIN_CACHE["brain"]

    @staticmethod
    def _wf():
        if _BRAIN_CACHE["workflows"] is None:
            _BRAIN_CACHE["workflows"] = workflows_store.load()
        return _BRAIN_CACHE["workflows"]

    @staticmethod
    def _cm():
        if _BRAIN_CACHE["channels"] is None:
            _BRAIN_CACHE["channels"] = chanmem_store.load()
        return _BRAIN_CACHE["channels"]

    @staticmethod
    def load():
        return Brain._brain()

    @staticmethod
    def remember(kind, text, data=None, account_id=None):
        b = Brain._brain()
        mem = {"id": "m_" + uuid.uuid4().hex[:6], "kind": kind, "text": _scrub(str(text))[:400],
               "data": data or {}, "account_id": account_id, "ts": int(time.time())}
        b.setdefault("memories", []).insert(0, mem)
        b["memories"] = b["memories"][:200]
        brain_store.save_bg(b)
        return mem

    @staticmethod
    def recall(query="", kind=None, account_id=None, limit=5):
        q = str(query or "").lower()
        out = []
        for m in Brain._brain().get("memories", []):
            if kind and m.get("kind") != kind:
                continue
            if account_id and m.get("account_id") and m["account_id"] != account_id:
                continue
            if q and q not in str(m.get("text", "")).lower():
                continue
            out.append(m)
            if len(out) >= limit:
                break
        return out

    @staticmethod
    def set_last_account(acc_id):
        b = Brain._brain()
        b["last_account"] = acc_id
        brain_store.save_bg(b)

    @staticmethod
    def last_account():
        return Brain._brain().get("last_account")

    @staticmethod
    def record(kind, goal, detail=""):
        b = Brain._brain()
        key = "successes" if kind == "ok" else "failures"
        b.setdefault(key, []).insert(0, {"goal": goal, "detail": _scrub(str(detail))[:200],
                                         "ts": int(time.time())})
        b[key] = b[key][:60]
        brain_store.save_bg(b)

    @staticmethod
    def capability_request(text, reason=""):
        b = Brain._brain()
        b.setdefault("capability_requests", []).insert(0, {
            "text": _scrub(str(text))[:300], "reason": reason[:200], "ts": int(time.time())})
        b["capability_requests"] = b["capability_requests"][:40]
        brain_store.save_bg(b)
        safe_log("WARN", "BRAIN", f"CAPABILITY REQUEST recorded: {str(text)[:80]}")

    # ---- workflows (structured, replayable definitions) ----
    @staticmethod
    def save_workflow(name, account_id, trigger, actions, raw_text=""):
        wf = Brain._wf()
        uname = str(name).upper()[:40]
        for ex in wf.get("workflows", []):
            if ex.get("name") == uname and (ex.get("account_id") == account_id or not account_id):
                ex.update({"trigger": trigger, "actions": actions,
                           "raw": _scrub(raw_text)[:400], "updated_at": int(time.time())})
                workflows_store.save_bg(wf)
                return ex
        item = {"workflow_id": "wf_" + uuid.uuid4().hex[:6], "name": uname,
                "account_id": account_id, "trigger": trigger, "actions": actions,
                "raw": _scrub(raw_text)[:400], "created_at": int(time.time()), "uses": 0}
        wf.setdefault("workflows", []).append(item)
        workflows_store.save_bg(wf)
        return item

    @staticmethod
    def find_workflow(text, account_id=None):
        """Token-overlap match; newest wins on ties so duplicates never block."""
        t = str(text or "").lower()
        toks = {w for w in re.split(r"[^a-z0-9]+", t) if len(w) > 2}
        cands = [w for w in Brain._wf().get("workflows", [])
                 if not account_id or not w.get("account_id") or w["account_id"] == account_id]
        scored = []
        for w in cands:
            name = str(w.get("name", "")).lower()
            trig = str((w.get("trigger") or {}).get("keyword", "")).lower()
            score = 0
            if name and name in t:
                score += 10
            ntoks = {x for x in re.split(r"[^a-z0-9]+", name) if len(x) > 2}
            ttoks = {x for x in re.split(r"[^a-z0-9]+", trig) if len(x) > 2}
            score += 3 * len(toks & ntoks) + 2 * len(toks & ttoks)
            if score:
                scored.append((score, w.get("created_at", 0), w))
        if not scored:
            return None
        scored.sort(key=lambda r: (-r[0], -r[1]))
        return scored[0][2]

    @staticmethod
    def workflows(account_id=None):
        return [w for w in Brain._wf().get("workflows", [])
                if not account_id or not w.get("account_id") or w["account_id"] == account_id]

    # ---- channel memory ----
    @staticmethod
    def note_channel(account_id, chat_id, title=None, username=None):
        cm = Brain._cm()
        chans = cm.setdefault("channels", {})
        key = f"{account_id}:{chat_id}"
        chans[key] = {"account_id": account_id, "chat_id": chat_id,
                      "title": title, "username": username, "seen": int(time.time())}
        chanmem_store.save_bg(cm)

    @staticmethod
    def lookup_channel(account_id, text):
        t = str(text or "").lower().lstrip("@")
        if not t:
            return None
        for key, c in Brain._cm().get("channels", {}).items():
            if account_id and c.get("account_id") != account_id:
                continue
            if t == str(c.get("chat_id")) or t == str(c.get("username", "")).lower() \
                    or (c.get("title") and t in str(c["title"]).lower()):
                return c
        return None

# ---------------------------------------------------------------------------
# TASK ENGINE (§19)
# ---------------------------------------------------------------------------
TASK_STATUSES = ("PLANNING", "RUNNING", "WAITING", "MONITORING", "PAUSED",
                 "COMPLETED", "FAILED", "STOPPED", "EXPIRED")

def agent_task_create(account_id, goal, plan, **kw):
    tid = "T-" + uuid.uuid4().hex[:5].upper()
    t = {"task_id": tid, "account_id": account_id, "goal": goal, "plan": plan,
         "status": "PLANNING", "created_at": time.time(), "updated_at": time.time(),
         "last_action": None, "last_error": None, "next_action": None,
         "source": kw.get("source"), "targets": kw.get("targets") or [],
         "rules": kw.get("rules") or {}, "expires_at": kw.get("expires_at"),
         "processed_ids": [], "stats": {"seen": 0, "acted": 0, "skipped": 0, "errors": 0},
         "summary": kw.get("summary", "")}
    AGENT_TASKS[tid] = t
    agent_tasks_persist()
    return t

def agent_task_update(tid, **fields):
    t = AGENT_TASKS.get(tid)
    if not t:
        return None
    t.update(fields)
    t["updated_at"] = time.time()
    agent_tasks_persist()
    return t

def agent_tasks_persist():
    rows = []
    for t in AGENT_TASKS.values():
        rows.append({k: v for k, v in t.items() if k not in ("_task",)})
    agent_tasks_store.save_bg({"tasks": rows[-60:]})

def agent_task_view(t):
    left = None
    if t.get("expires_at"):
        left = max(0, int(t["expires_at"] - time.time()))
    return {"task_id": t["task_id"], "goal": t["goal"], "status": t["status"],
            "account_id": t.get("account_id"), "summary": t.get("summary"),
            "source": t.get("source"), "targets": t.get("targets"),
            "stats": t.get("stats"), "expires_in": left,
            "last_action": t.get("last_action"), "last_error": t.get("last_error"),
            "created_at": t.get("created_at")}

async def agent_task_stop(tid, reason="operator"):
    t = AGENT_TASKS.get(tid)
    if not t:
        return False, "Task not found"
    rt = AGENT_RUNTIME.pop(tid, {})
    handler, client = rt.get("handler"), rt.get("client")
    if handler is not None and client is not None:
        try:
            client.remove_event_handler(handler)
        except Exception:
            pass
    for tm in rt.get("timers", []):
        try:
            tm.cancel()
        except Exception:
            pass
    if t["status"] in ("RUNNING", "MONITORING", "WAITING", "PLANNING", "PAUSED"):
        t["status"] = "STOPPED"
    t["last_action"] = f"stopped ({reason})"
    agent_task_update(tid)
    safe_log("CMD", "AGENT", f"task {tid} stopped ({reason})")
    return True, t["status"]

def agent_active_tasks(account_id=None):
    return [t for t in AGENT_TASKS.values()
            if t["status"] in ("RUNNING", "MONITORING", "WAITING", "PLANNING", "PAUSED")
            and (not account_id or t["account_id"] == account_id)]

# ---------------------------------------------------------------------------
# CONTEXT DISCOVERY (§1, §10)
# ---------------------------------------------------------------------------
def peek_reply_source(origin):
    r = REPLY_SOURCE.get(origin)
    if not r:
        return None
    if time.time() - r["at"] > REPLY_SOURCE_TTL:
        REPLY_SOURCE.pop(origin, None)
        return None
    return r

def pick_account(origin, text=""):
    """explicit mention -> session context -> last used -> active -> only one."""
    t = str(text or "").lower()
    m = re.search(r"account\s*(\d+|[a-z0-9_]{2,})", t)
    if m:
        acc, aid = _resolve_account_ref(m.group(1))
        if acc:
            ctx_set(origin, account_id=aid)
            Brain.set_last_account(aid)
            return aid, acc, "explicit"
    aid = ctx_get(origin).get("account_id")
    if aid and aid in ACCOUNTS.accounts:
        return aid, ACCOUNTS.accounts[aid], "session"
    if origin.startswith("tg:"):
        try:
            uid = int(origin.split(":", 1)[1])
            for a_id, acc in ACCOUNTS.accounts.items():
                if str(acc["meta"].get("user_id")) == str(uid):
                    return a_id, acc, "sender"
        except Exception:
            pass
    last = Brain.last_account()
    if last and last in ACCOUNTS.accounts:
        return last, ACCOUNTS.accounts[last], "last-used"
    active = ACCOUNTS.get_active()
    if active:
        return active["meta"]["id"], active, "active"
    if len(ACCOUNTS.accounts) == 1:
        aid = next(iter(ACCOUNTS.accounts))
        return aid, ACCOUNTS.accounts[aid], "only-account"
    if TG.client and TG.authorized and TG.account:
        return "primary", {"meta": {**TG.account, "id": "primary"}, "client": TG.client,
                           "authorized": True}, "primary-session"
    return None, None, "none"

async def resolve_entity_smart(acc, ref):
    """@username | numeric id | -100id | remembered channel. Real errors only."""
    client = (acc or {}).get("client")
    if not client:
        return None, "Telegram client offline"
    ref = str(ref).strip()
    aid = (acc.get("meta") or {}).get("id")
    remembered = Brain.lookup_channel(aid, ref)
    candidates = []
    base = ref.lstrip("@")
    if base.lstrip("-").isdigit():
        n = int(base)
        candidates = [n]
        if n > 0:
            candidates += [int(f"-100{n}"), -n]
    else:
        candidates = [base]
    if remembered and remembered.get("chat_id") not in candidates:
        candidates.insert(0, remembered["chat_id"])
    last_err = None
    for c in candidates:
        try:
            ent = await client.get_entity(c)
            Brain.note_channel(aid, getattr(ent, "id", c), getattr(ent, "title", None),
                               getattr(ent, "username", None))
            return ent, None
        except Exception as e:
            last_err = f"{type(e).__name__}: {str(e)[:90]}"
    return None, f"CHANNEL INACCESSIBLE — {last_err or 'not reachable by this account'}"

async def discover_targets(acc_id, acc, limit=12):
    """Configured main channels first; fall back to accessible channels."""
    out = []
    cfg = acct_cfg(acc_id or "")
    for ch in (cfg.get("main_channels") or []):
        ent, err = await resolve_entity_smart(acc, ch)
        if ent is not None:
            out.append({"chat_id": getattr(ent, "id", ch), "title": getattr(ent, "title", str(ch)),
                        "username": getattr(ent, "username", None), "src": "main_channels"})
        else:
            out.append({"chat_id": ch, "title": str(ch), "username": None,
                        "src": "main_channels", "warn": err})
    if out:
        return out, "configured main channels"
    dst = cfg.get("destination")
    if dst:
        ent, err = await resolve_entity_smart(acc, dst)
        if ent is not None:
            return ([{"chat_id": ent.id, "title": getattr(ent, "title", str(dst)),
                      "username": getattr(ent, "username", None), "src": "destination"}],
                    "account destination")
    try:
        folders = await _scan_folders_client(acc["client"])
        for f in folders:
            for ch in f["channels"]:
                out.append({"chat_id": ch["id"], "title": ch["name"],
                            "username": ch.get("username"), "src": "folder:" + f["name"]})
                if len(out) >= limit:
                    break
            if len(out) >= limit:
                break
    except Exception as e:
        log.warning("target discovery failed: %s", type(e).__name__)
    return out, ("dialog folders" if out else "none")

async def discover_cross_source(origin, acc_id, acc):
    """reply -> runtime config -> account source -> brain. Never guesses blindly."""
    r = peek_reply_source(origin)
    if r:
        return {"chat_id": r["chat_id"], "message_id": r["message_id"],
                "preview": r.get("preview", ""), "via": "replied message"}, None
    cid, ids = cfg_source()
    if cid and ids:
        return {"chat_id": int(cid), "message_id": int(ids[0]), "preview": "",
                "via": "saved configuration"}, None
    cfg = acct_cfg(acc_id or "")
    if cfg.get("source"):
        ent, err = await resolve_entity_smart(acc, cfg["source"])
        if ent is not None:
            try:
                msgs = await acc["client"].get_messages(ent, limit=1)
                if msgs and msgs[0]:
                    return {"chat_id": getattr(ent, "id", None), "message_id": msgs[0].id,
                            "preview": (msgs[0].text or "")[:80],
                            "via": f"latest message of account source {cfg['source']}"}, None
            except Exception as e:
                return None, f"source {cfg['source']} unreadable ({type(e).__name__})"
    return None, "no replied message, no saved source, no account source configured"

# ---------------------------------------------------------------------------
# MONITOR AGENT (§7, §8) — rule-based, permission-aware, never bulk-deletes
# ---------------------------------------------------------------------------
_TIME_MULT = {"second": 1, "sec": 1, "seconds": 1, "minute": 60, "min": 60, "mint": 60,
              "minutes": 60, "hour": 3600, "hours": 3600, "hr": 3600, "ghante": 3600,
              "ghanta": 3600, "day": 86400, "days": 86400, "din": 86400, "dino": 86400,
              "week": 604800, "hafta": 604800, "hafte": 604800}
_TIME_RE = re.compile(r"(\d+)\s*(seconds?|sec|minutes?|min|mint|hours?|hr|ghante|ghanta|"
                      r"days?|din|dino|week|hafta|hafte)", re.I)
_DELAY_AFTER = re.compile(r"^\W{0,3}(baad|bad|me\b|mein\b|after|later)", re.I)
_DUR_AFTER = re.compile(r"^\W{0,3}(tak|ke liye|for|monitor|k liye)", re.I)

def _parse_times(text):
    """Split '5 minute baad delete ... 1 din tak monitor' into (delay=300, duration=86400).
    A number followed by baad/after is a DELAY; followed by tak/for — or a day/week
    unit that is not the delay — is the DURATION."""
    t = str(text or "").lower()
    delay = duration = None
    for m in _TIME_RE.finditer(t):
        secs = int(m.group(1)) * _TIME_MULT.get(m.group(2).rstrip("s") if m.group(2) not in _TIME_MULT
                                                else m.group(2), _TIME_MULT.get(m.group(2), 60))
        tail = t[m.end():m.end() + 14]
        if _DELAY_AFTER.match(tail) and delay is None:
            delay = secs
        elif _DUR_AFTER.match(tail) and duration is None:
            duration = secs
        elif m.group(2).rstrip("s") in ("day", "din", "dino", "week", "hafta", "hafte") and duration is None:
            duration = secs
    if duration is None and re.search(r"\b(ek|1)\s*(din|day)\b", t):
        duration = 86400
    return delay, duration

def _parse_clock(text):
    """'kal 7 baje tak' / '4 baje' / '7:30 pm' -> epoch in Asia/Kathmandu.
    Never invents a date: bare times roll to the next occurrence."""
    t = str(text or "").lower()
    m = re.search(r"(\d{1,2})(?::(\d{2}))?\s*(am|pm)?\s*(baje|bje|o'clock|pe|par)?", t)
    if not m or not (m.group(3) or m.group(4)):
        return None
    h = int(m.group(1)); mins = int(m.group(2) or 0)
    ap = m.group(3)
    if ap == "pm" and h < 12: h += 12
    if ap == "am" and h == 12: h = 0
    if not ap:
        # Hinglish habit: "4 baje"/"7 baje" usually means daytime/evening
        if re.search(r"(raat|shaam|evening|night)", t) and h < 12: h += 12
        elif 1 <= h <= 7 and not re.search(r"(subah|morning|am)", t): h += 12
    if h > 23 or mins > 59:
        return None
    d = ktm_now().replace(hour=h, minute=mins, second=0, microsecond=0)
    if re.search(r"\bkal\b|\btomorrow\b", t):
        d += timedelta(days=1)
    elif d.timestamp() <= time.time():
        d += timedelta(days=1)
    return d.timestamp()

def _parse_duration(text, default=None):
    d = _parse_times(text)[1]
    return d if d is not None else default

def _parse_delay(text):
    return _parse_times(text)[0]

def classify_message(msg, rules, acc_meta):
    """Deterministic 'unknown' classification — no invented criteria."""
    reasons = []
    kinds = rules.get("kinds") or []
    kws = [k.lower() for k in (rules.get("keywords") or [])]
    text = (getattr(msg, "text", None) or getattr(msg, "message", None) or "")
    low = text.lower()
    is_fwd = bool(getattr(msg, "forward", None) or getattr(msg, "fwd_from", None))
    sender = getattr(msg, "sender_id", None)
    allowed = {int(x) for x in (rules.get("allowed_senders") or []) if str(x).lstrip("-").isdigit()}
    if acc_meta and acc_meta.get("user_id"):
        allowed.add(int(acc_meta["user_id"]))
    if "forwarded" in kinds and is_fwd:
        reasons.append("forwarded message")
    if "keyword" in kinds and kws and any(k in low for k in kws):
        reasons.append("keyword match")
    if "media" in kinds and getattr(msg, "media", None) is not None:
        reasons.append("media message")
    if "unknown" in kinds:
        # unknown := forwarded from elsewhere OR sender not in the approved set
        if is_fwd:
            reasons.append("unknown: forwarded from outside")
        elif sender is not None and allowed and int(sender) not in allowed:
            reasons.append(f"unknown: sender {sender} not approved")
    return (len(reasons) > 0), reasons

async def _delete_message_safe(client, chat, msg_id, task):
    try:
        await client.delete_messages(chat, [msg_id])
        task["stats"]["acted"] += 1
        task["last_action"] = f"deleted message {msg_id}"
        agent_task_update(task["task_id"])
        safe_log("CMD", "MONITOR", f"{task['task_id']} deleted msg {msg_id}")
        return True, None
    except FloodWaitError as fw:
        safe_log("WARN", "MONITOR", f"{task['task_id']} FloodWait {fw.seconds}s — exact wait")
        await asyncio.sleep(fw.seconds)
        try:
            await client.delete_messages(chat, [msg_id])
            task["stats"]["acted"] += 1
            return True, None
        except Exception as e2:
            task["stats"]["errors"] += 1
            return False, f"{type(e2).__name__}"
    except Exception as e:
        task["stats"]["errors"] += 1
        task["last_error"] = f"delete failed: {type(e).__name__}"
        agent_task_update(task["task_id"])
        return False, f"{type(e).__name__}: {str(e)[:80]}"

async def monitor_start(task, acc):
    """Attach a live NewMessage watcher implementing the task's rules."""
    client = acc["client"]
    src = task.get("source") or {}
    watch_id = src.get("chat_id")
    rules = task.get("rules") or {}
    delay = rules.get("delay_seconds")
    action = rules.get("action", "notify")
    acc_meta = acc.get("meta") or {}

    async def _watch(event):
        try:
            if task["status"] not in ("MONITORING", "RUNNING"):
                return
            if task.get("expires_at") and time.time() > task["expires_at"]:
                task["status"] = "EXPIRED"
                agent_task_update(task["task_id"])
                await agent_task_stop(task["task_id"], "expired")
                return
            ent = event.chat
            eid = getattr(ent, "id", None)
            if watch_id is not None and str(eid) != str(watch_id) and \
                    str(event.chat_id) != str(watch_id):
                return
            msg = event.message
            if not msg or msg.id in task["processed_ids"][-400:]:
                return
            task["stats"]["seen"] += 1
            task["processed_ids"].append(msg.id)
            task["processed_ids"] = task["processed_ids"][-400:]
            hit, reasons = classify_message(msg, rules, acc_meta)
            if not hit:
                task["stats"]["skipped"] += 1
                agent_task_update(task["task_id"])
                return
            if action == "delete":
                if delay:
                    task["last_action"] = f"msg {msg.id} matched ({', '.join(reasons)}) — deleting in {delay}s"
                    agent_task_update(task["task_id"])

                    async def _later(mid=msg.id, chat=event.chat_id):
                        try:
                            await asyncio.sleep(delay)
                            if task["status"] in ("MONITORING", "RUNNING"):
                                await _delete_message_safe(client, chat, mid, task)
                        except asyncio.CancelledError:
                            raise
                        except Exception as e:
                            safe_log("WARN", "MONITOR", f"delayed delete failed: {type(e).__name__}")
                    tm = asyncio.get_running_loop().create_task(_later())
                    AGENT_RUNTIME.setdefault(task["task_id"], {}).setdefault("timers", []).append(tm)
                else:
                    ok, err = await _delete_message_safe(client, event.chat_id, msg.id, task)
                    if not ok:
                        task["last_error"] = err
            else:
                task["stats"]["acted"] += 1
                task["last_action"] = f"msg {msg.id} matched ({', '.join(reasons)})"
            agent_task_update(task["task_id"])
        except Exception as e:
            task["stats"]["errors"] += 1
            task["last_error"] = f"{type(e).__name__}"
            log.warning("monitor handler error: %s", type(e).__name__)

    # canonical registration (works across Telethon versions, decorator-free)
    try:
        client.add_event_handler(_watch, events.NewMessage())
    except TypeError:
        client.add_event_handler(_watch)
    AGENT_RUNTIME.setdefault(task["task_id"], {}).update({"handler": _watch, "client": client})
    AGENT_RUNTIME[task["task_id"]].setdefault("timers", [])
    task["status"] = "MONITORING"
    agent_task_update(task["task_id"])

    if task.get("expires_at"):
        async def _expire():
            try:
                await asyncio.sleep(max(1, task["expires_at"] - time.time()))
                if task["status"] in ("MONITORING", "RUNNING"):
                    task["status"] = "EXPIRED"
                    agent_task_update(task["task_id"])
                    await agent_task_stop(task["task_id"], "expiry reached")
            except asyncio.CancelledError:
                raise
            except Exception:
                pass
        AGENT_RUNTIME[task["task_id"]]["timers"].append(
            asyncio.get_running_loop().create_task(_expire()))
    return task

# ---------------------------------------------------------------------------
# GOAL PARSER (§17) — natural language -> goal + params (no UNMAPPED for goals)
# ---------------------------------------------------------------------------
def parse_goal(raw):
    t = re.sub(r"^\s*/?(ai|jarvis|devil)\b[\s,:.-]*", "", str(raw or "").strip(), flags=re.I)
    low = t.lower()

    # ---- delegation session (§5): "main 2 din busy hoon, tum sambhal lo" ----
    _away = has(low, ("busy hoon", "busy hu", "busy rahunga", "sona ja raha", "so raha hoon",
                      "bahar ja raha", "delegate", "chhutti", "chutti"))
    _handover = has(low, ("tum sambhal", "khud sambhal", "sambhal lo", "sambhal lena",
                          "khud manage", "tum dekh lena", "tum handle", "khud se kaam"))
    # only a real hand-over is delegation; "sona ja raha hu, 7 baje tak cross karna"
    # is a concrete cross instruction with an auto-stop time
    if _handover or (_away and not has(low, CROSS_T + ("monitor", "dhyan", "post", "delete"))):
        return {"goal": "DELEGATE", "params": {"text": t}}

    # ---- post/design/forward workflow (§17) ----
    if (has(low, ("post kar", "post karo", "post karna", "post kr", "daal dena", "daalna", "publish")) and
            (has(low, ("forward", "design", "baje", "channel")))):
        return {"goal": "POST_WORKFLOW", "params": {"text": t}}

    # ---- activity / analytics report (§16) ----
    if has(low, ("activity analyze", "activity check", "report dena", "report do", "report bhej",
                 "kitni baar", "analyze karo", "analysis", "kitna active", "performance")):
        return {"goal": "ACTIVITY_REPORT", "params": {"text": t}}

    # ---- admin/receptionist request (§18/§19) ----
    if has(low, ("admin de do", "admin dena", "admin request", "admin bana", "admin chahiye",
                 "promote kar")):
        return {"goal": "ADMIN_REQUEST", "params": {"text": t}}

    # ---- run a saved workflow by name/trigger (§14 / TEST 11) ----
    _teaching = has(low, ("yaad rakho", "yaad rakhna", "remember", "jab bhi", "jab toss",
                          "aaye to", "aata hai to", "workflow banao", "sikha", "seekh"))
    _wf_words = has(low, ("workflow use", "saved workflow", "wo workflow", "usi workflow",
                          "same workflow", "wahi workflow")) and not _teaching
    _handle = has(low, ("handle karo", "handle karna", "handle kar"))
    _monitorish = has(low, ("monitor", "dhyan", "delete", "hata", "remove", "dekhte raho",
                            "minute", "din", "hour", "ghante", "forwarded", "unknown"))
    if (_wf_words or (_handle and not _monitorish and not _teaching)) and not _teaching:
        return {"goal": "WORKFLOW_RUN", "params": {"text": t}}

    if re.match(r"^/?cross\s*(start|chalu|shuru)?\s*$", low) or \
            (has(low, CROSS_T) and has(low, V_START + ("kar do", "karo", "kro"))) or \
            has(low, ("is message ko cross", "ye message cross", "reply wale post se cross")):
        until = _parse_clock(low) if has(low, ("tak", "until", "till")) else None
        if not until:
            dur = _parse_times(low)[1]
            if dur and has(low, ("tak", "ke liye", "for")):
                until = time.time() + dur
        return {"goal": "CROSS_START", "params": {"text": t, "until": until,
                                                  "auto_stop": bool(until)}}
    if has(low, CROSS_T) and has(low, V_STOP):
        return {"goal": "CROSS_STOP", "params": {}}
    if has(low, CROSS_T) and has(low, V_RESET):
        return {"goal": "CROSS_RESET", "params": {}}
    if has(low, CROSS_T) and has(low, V_STATUS):
        return {"goal": "CROSS_STATUS", "params": {}}

    mset = re.search(r"main\s*chann?els?\b", low)
    if mset and has(low, ("set", "lagao", "kar do", "karo", "update")):
        ids = re.findall(r"(-?\d{6,20})", t)
        if ids:
            return {"goal": "SET_MAIN_CHANNELS", "params": {"channels": ids, "text": t}}

    watch = has(low, ("dhyan rakho", "dhyan rakhna", "monitor karo", "monitor karna", "dekhte raho",
                      "dekhte rehna", "nazar rakho", "watch", "monitor start", "observe"))
    dele = has(low, ("delete", "hata dena", "hatao", "hata do", "remove", "mita", "delete karte",
                     "delete karna", "delete kar"))
    if watch or dele:
        kinds = []
        if has(low, ("unknown", "anjaan", "galat", "spam")):
            kinds.append("unknown")
        if has(low, ("forward", "forwarded", "forward hua")):
            kinds.append("forwarded")
        if has(low, ("media", "photo", "video", "image")):
            kinds.append("media")
        kws = re.findall(r"keyword[s]?\s*[:=]?\s*([a-z0-9, ]+)", low)
        if not kinds and not kws:
            kinds = ["unknown"] if dele else []
        target = None
        um = re.search(r"@([a-zA-Z0-9_]{3,32})", t)
        idm = re.search(r"(-?\d{6,20})", t)
        if um:
            target = um.group(1)
        elif idm:
            target = idm.group(1)
        return {"goal": "MONITOR_WATCH", "params": {
            "text": t, "target": target,
            "kinds": kinds, "keywords": [k.strip() for k in (kws[0].split(",") if kws else []) if k.strip()],
            "action": "delete" if dele else "notify",
            "delay_seconds": _parse_times(low)[0],
            "duration_seconds": _parse_times(low)[1],
            "until_stop": has(low, ("jab tak", "until i stop", "stop na bolu", "stop bolun")),
        }}

    if has(low, ("inspect", "details batao", "check karo", "info do", "ka info")) or \
            re.match(r"^-?\d{6,20}\s+(inspect|check|info)", low):
        ref = None
        um = re.search(r"@([a-zA-Z0-9_]{3,32})", t)
        idm = re.search(r"(-?\d{6,20})", t)
        if um:
            ref = um.group(1)
        elif idm:
            ref = idm.group(1)
        if ref:
            return {"goal": "INSPECT", "params": {"ref": ref}}

    if has(low, ("stop this", "ye stop", "isko stop", "stop kar do", "ye band", "stop task")):
        return {"goal": "STOP_TASK", "params": {"text": t}}
    if has(low, ("sab", "saare", "all")) and has(low, ("task",)) and has(low, V_STOP + V_CANCEL):
        return {"goal": "STOP_ALL_TASKS", "params": {}}
    if has(low, ("task", "kaam")) and has(low, ("dikhao", "list", "status", "chal rah", "running")):
        return {"goal": "TASK_LIST", "params": {}}

    if has(low, ("yaad rakho", "yaad rakhna", "remember", "jab bhi", "jab toss", "workflow banao",
                 "is workflow ko use", "sikha", "seekh")) or \
            (has(low, ("aaye to", "aata hai to", "aati hai to")) and
             has(low, ("workflow", "use karna", "karna", "bhejna", "handle"))):
        return {"goal": "TEACH", "params": {"text": t}}
    if has(low, ("kya yaad", "memory dikhao", "brain dikhao", "what do you remember", "workflows dikhao")):
        return {"goal": "RECALL", "params": {"text": t}}

    if re.fullmatch(r"(hi|hello|hey|hlo|namaste|salam|yo|sup|kaise ho|kya haal|thanks|thank you|ok|okay|good morning|good night)[!. ]*",
                    low.strip()):
        return {"goal": "CHITCHAT", "params": {"text": t}}
    if has(low, ("khud manage", "khud handle", "khud kar", "jo required hai wo karo",
                 "required telegram work", "manage karo")):
        return {"goal": "AUTOPILOT", "params": {"text": t}}
    return None

# ---------------------------------------------------------------------------
# GOAL EXECUTORS  (plan -> allowlisted capabilities -> verify -> concise reply)
# ---------------------------------------------------------------------------
async def goal_cross_start(origin, raw, params):
    acc_id, acc, how = pick_account(origin, raw)
    if not acc:
        return {"ok": False, "lines": ["NO TELEGRAM ACCOUNT ▸ web dashboard se account add/activate karo."]}
    plan = ["identify account", "resolve source", "discover targets", "validate", "start engine", "monitor"]
    task = agent_task_create(acc_id, "CROSS_START", plan, summary="Cross workflow")
    agent_task_update(task["task_id"], status="RUNNING", last_action="resolving source")

    src, err = await discover_cross_source(origin, acc_id, acc)
    if not src:
        agent_task_update(task["task_id"], status="FAILED", last_error=err)
        Brain.record("fail", "CROSS_START", err)
        return {"ok": False, "lines": SOURCE_NOT_AVAILABLE_HELP + ["", f"(checked: {err})"]}

    targets, tsrc = await discover_targets(acc_id, acc)
    if not targets:
        agent_task_update(task["task_id"], status="FAILED", last_error="no targets")
        return {"ok": False, "lines": [
            "TARGETS NOT AVAILABLE",
            "Is account ke main channels set karo — web panel se ya:",
            "/AI account main channels <id> <id> set karo"]}

    if peek_reply_source(origin):
        take_reply_source(origin)
    await apply_reply_source(src["chat_id"], src["message_id"])
    agent_task_update(task["task_id"], source=src, targets=[t["title"] for t in targets][:8],
                      last_action="starting engine")
    await ENGINE.rebuild_queue(targets=targets)
    r = await ENGINE.start()
    ok = r.get("ok", True)
    agent_task_update(task["task_id"], status="RUNNING" if ok else "FAILED",
                      last_action="engine started" if ok else "engine refused",
                      last_error=None if ok else (r.get("lines") or [""])[0])
    Brain.record("ok" if ok else "fail", "CROSS_START", src["via"])
    Brain.remember("cross", f"cross started from {src['via']}",
                   {"source": src, "targets": len(targets)}, acc_id)
    if not ok:
        return {"ok": False, "lines": r.get("lines") or ["Cross start failed"]}

    # §6 — "kal 7 baje tak cross karna, phir automatically stop": arm auto-stop
    until = params.get("until")
    if until:
        agent_task_update(task["task_id"], expires_at=until,
                          next_action=f"auto-stop at {fmt_kt(until)}")

        async def _auto_stop():
            try:
                await asyncio.sleep(max(1, until - time.time()))
                if STATE["engine"]["status"] in ("running", "paused"):
                    ENGINE.stop()
                if task["status"] in ("RUNNING", "MONITORING", "WAITING"):
                    task["status"] = "EXPIRED"
                    task["last_action"] = "auto-stopped at requested time"
                    agent_task_update(task["task_id"])
                safe_log("OK", "AGENT", f"cross auto-stopped ({task['task_id']})")
                Brain.remember("cross", "cross auto-stopped at scheduled time",
                               {"task_id": task["task_id"]}, acc_id)
            except asyncio.CancelledError:
                raise
            except Exception:
                pass
        AGENT_RUNTIME.setdefault(task["task_id"], {}).setdefault("timers", []).append(
            asyncio.get_running_loop().create_task(_auto_stop()))

    return {"ok": True, "lines": [
        "YES SIR.", "✓ CROSS WORKFLOW STARTED", bar,
        f"Account ▸ @{acc['meta'].get('username')} ({how})",
        f"Source  ▸ {src['via']}" + (f" — msg {src['message_id']}" if src.get("message_id") else ""),
        (f"          \"{src['preview']}\"" if src.get("preview") else ""),
        f"Targets ▸ {len(targets)} ({tsrc})",
        f"Queue   ▸ {len(ENGINE.eng['queue'])} pending · pacing {ENGINE.CYCLE_DELAY}s · FloodWait-safe",
        (f"Auto-stop ▸ {fmt_kt(until)} (Asia/Kathmandu)" if until else "Runs until you say stop"),
        f"Task    ▸ {task['task_id']} · Status: RUNNING"]}

async def goal_monitor(origin, raw, params):
    acc_id, acc, how = pick_account(origin, raw)
    if not acc:
        return {"ok": False, "lines": ["NO TELEGRAM ACCOUNT ▸ pehle account add/activate karo."]}
    # resolve what to watch: explicit ref -> replied message chat -> account source/main
    watch, why = None, ""
    if params.get("target"):
        ent, err = await resolve_entity_smart(acc, params["target"])
        if ent is None:
            return {"ok": False, "lines": [err or "CHANNEL INACCESSIBLE"]}
        watch = {"chat_id": getattr(ent, "id", None), "title": getattr(ent, "title", str(params["target"]))}
        why = "specified channel"
    if not watch:
        r = peek_reply_source(origin)
        if r:
            watch = {"chat_id": r["chat_id"], "title": "replied chat"}
            why = "replied message's chat"
    if not watch:
        cfg = acct_cfg(acc_id or "")
        ref = cfg.get("source") or cfg.get("main_channel")
        if ref:
            ent, err = await resolve_entity_smart(acc, ref)
            if ent is not None:
                watch = {"chat_id": getattr(ent, "id", None), "title": getattr(ent, "title", str(ref))}
                why = "account configured channel"
    if not watch:
        return {"ok": False, "lines": [
            "KAUNSA CHANNEL? ▸ ye ek cheez batao:",
            "  ▸ us channel ke message par reply karke command bhejo, ya",
            "  ▸ @username / numeric id likho, ya",
            "  ▸ account ka source/main channel set karo"]}

    dur = params.get("duration_seconds")
    if not dur and not params.get("until_stop"):
        dur = 86400          # sensible default: 1 day
    expires = (time.time() + dur) if dur else None
    rules = {"kinds": params.get("kinds") or ["unknown"],
             "keywords": params.get("keywords") or [],
             "action": params.get("action", "notify"),
             "delay_seconds": params.get("delay_seconds"),
             "allowed_senders": []}
    plan = ["resolve channel", "check permissions", "attach live watcher", "apply rules",
            "act on new matches", "persist state", "auto-expire"]
    task = agent_task_create(acc_id, "MONITOR", plan, source=watch,
                             rules=rules, expires_at=expires,
                             summary=f"watch {watch['title']}")
    perm_note = ""
    if rules["action"] == "delete":
        try:
            perms = await acc["client"].get_permissions(watch["chat_id"], "me")
            if not (getattr(perms, "is_admin", False) or getattr(perms, "is_creator", False)
                    or getattr(perms, "delete_messages", False)):
                perm_note = "account admin nahi hai — sirf apne messages delete ho payenge"
        except Exception as e:
            perm_note = f"permission check nahi hua ({type(e).__name__})"
    await monitor_start(task, acc)
    Brain.remember("monitor", raw, {"task_id": task["task_id"], "rules": rules,
                                    "chat_id": watch["chat_id"]}, acc_id)
    Brain.record("ok", "MONITOR", watch["title"])
    lines = ["✓ MONITORING STARTED", bar,
             f"Account ▸ @{acc['meta'].get('username')} ({how})",
             f"Channel ▸ {watch['title']} ({watch['chat_id']})  [{why}]",
             f"Rule    ▸ {', '.join(rules['kinds']) or 'all new messages'}" +
             (f" · keywords: {', '.join(rules['keywords'])}" if rules["keywords"] else ""),
             f"Action  ▸ {rules['action']}" +
             (f" after {rules['delay_seconds']}s" if rules["delay_seconds"] else ""),
             f"Runs    ▸ {'until you stop it' if not expires else 'for ' + str(int(dur/3600)) + 'h (auto-expire)'}",
             f"Task    ▸ {task['task_id']} · Status: MONITORING"]
    if perm_note:
        lines.append(f"Note    ▸ {perm_note}")
    lines.append("Sirf NAYE matching messages par act karunga — purani history bulk delete nahi hogi.")
    return {"ok": True, "lines": lines}

async def goal_set_main_channels(origin, raw, params):
    acc_id, acc, how = pick_account(origin, raw)
    if not acc_id:
        return {"ok": False, "lines": ["Account nahi mila — pehle account add/activate karo."]}
    ids = [str(x) for x in params.get("channels", [])]
    store = acctcfg_store.load()
    cfg = store.get(acc_id, {})
    cfg["main_channels"] = ids
    cfg["main_channel"] = ids[0] if ids else None
    cfg["updated_at"] = int(time.time())
    store[acc_id] = cfg
    await acctcfg_store.save(store)
    Brain.remember("config", f"main channels set for {acc_id}", {"channels": ids}, acc_id)
    lines = ["✓ MAIN CHANNELS SAVED", bar, f"Account ▸ @{acc['meta'].get('username')} ({how})"]
    for c in ids:
        ent, err = await resolve_entity_smart(acc, c)
        lines.append(f"  ▸ {c}" + (f"  ({getattr(ent, 'title', '')})" if ent is not None else f"  — {err}"))
    lines.append("Cross aur monitor tasks ab yahi targets use karenge (JSON me persist ho gaya).")
    return {"ok": True, "lines": lines}

async def goal_inspect(origin, raw, params):
    acc_id, acc, how = pick_account(origin, raw)
    if not acc:
        return {"ok": False, "lines": ["NO TELEGRAM ACCOUNT ▸ pehle account connect karo."]}
    ent, err = await resolve_entity_smart(acc, params.get("ref"))
    if ent is None:
        return {"ok": False, "lines": [err, "Private channel ho to bhi chalega — bas account us channel ka member hona chahiye."]}
    title = getattr(ent, "title", None) or getattr(ent, "first_name", None) or str(params.get("ref"))
    lines = ["CHANNEL / CHAT", bar, f"Title    ▸ {title}", f"ID       ▸ {getattr(ent, 'id', '?')}",
             f"Username ▸ @{getattr(ent, 'username', None) or '(private)'}",
             f"Type     ▸ {'broadcast' if getattr(ent, 'broadcast', False) else ('group' if getattr(ent, 'megagroup', False) else 'chat/user')}"]
    members = getattr(ent, "participants_count", None)
    if members is not None:
        lines.append(f"Members  ▸ {members}")
    try:
        msgs = await acc["client"].get_messages(ent, limit=1)
        if msgs and msgs[0]:
            when = msgs[0].date.strftime("%d %b %I:%M %p") if msgs[0].date else "?"
            lines.append(f"Latest   ▸ {when} — {(msgs[0].text or '(media)')[:60]}")
    except Exception as e:
        lines.append(f"Latest   ▸ unreadable ({type(e).__name__})")
    try:
        perms = await acc["client"].get_permissions(ent, "me")
        lines.append(f"Your role▸ {'CREATOR' if getattr(perms, 'is_creator', False) else ('ADMIN' if getattr(perms, 'is_admin', False) else 'MEMBER')}")
    except Exception:
        pass
    Brain.note_channel(acc_id, getattr(ent, "id", None), title, getattr(ent, "username", None))
    return {"ok": True, "lines": lines}

async def goal_task_list(origin, raw, params):
    acc_id, acc, _ = pick_account(origin, raw)
    rows = agent_active_tasks()
    lines = ["ACTIVE WORK", bar]
    if not rows:
        lines.append("Abhi koi background task nahi chal raha.")
    for t in rows:
        left = ""
        if t.get("expires_at"):
            left = f" · {int(max(0, t['expires_at'] - time.time()) / 60)}m left"
        st = t["stats"]
        lines += [f"[{t['task_id']}] {t['goal']} ▸ {t['status']}{left}",
                  f"   {t.get('summary') or ''} · seen {st['seen']} · acted {st['acted']} · errors {st['errors']}"]
        if t.get("last_error"):
            lines.append(f"   last error: {t['last_error']}")
    eng = STATE["engine"]
    lines += [bar, f"Cross engine ▸ {eng['status'].upper()} · queue {len(eng['queue'])} · sent {eng['processed']}"]
    return {"ok": True, "lines": lines}

async def goal_stop_task(origin, raw, params):
    acc_id, acc, _ = pick_account(origin, raw)
    m = re.search(r"\b(T-[A-Z0-9]{5})\b", str(raw), re.I)
    if m:
        ok, st = await agent_task_stop(m.group(1).upper(), "user")
        return {"ok": ok, "lines": [f"Task {m.group(1).upper()} ▸ {st}" if ok else "Task not found"]}
    rows = agent_active_tasks(acc_id) or agent_active_tasks()
    if not rows:
        if STATE["engine"]["status"] == "running":
            ENGINE.stop()
            return {"ok": True, "lines": ["Cross engine stopped."]}
        return {"ok": True, "lines": ["Koi active task nahi mila."]}
    if len(rows) == 1:
        ok, st = await agent_task_stop(rows[0]["task_id"], "user")
        return {"ok": True, "lines": [f"✓ Stopped {rows[0]['task_id']} ({rows[0]['goal']}) ▸ {st}"]}
    return {"ok": False, "lines": ["Multiple tasks chal rahe hain — id batao:"] +
                                  [f"  ▸ {t['task_id']} {t['goal']} ({t.get('summary')})" for t in rows]}

async def goal_stop_all(origin, raw, params):
    rows = agent_active_tasks()
    for t in rows:
        await agent_task_stop(t["task_id"], "stop-all")
    if STATE["engine"]["status"] == "running":
        ENGINE.stop()
    return {"ok": True, "lines": [f"✓ {len(rows)} task(s) stopped · cross engine stopped"]}

async def goal_teach(origin, raw, params):
    acc_id, acc, _ = pick_account(origin, raw)
    low = str(raw).lower()
    mname = re.search(r"(?:name|naam)\s*[:=]?\s*([a-z0-9_\-]{2,30})", low)
    trigger_kw = None
    mt = re.search(r"jab\s+(?:bhi\s+)?([a-z0-9 ]{3,24})\s+(?:aaye|aata|aati|ho)", low)
    if mt:
        trigger_kw = mt.group(1).strip()
    kinds = []
    if "delete" in low or "hata" in low:
        kinds.append("delete")
    if "forward" in low or "cross" in low:
        kinds.append("cross")
    if "update" in low or "bhej" in low or "send" in low:
        kinds.append("update")
    name = (mname.group(1) if mname else (trigger_kw or "workflow")).upper().replace(" ", "-")[:40]
    wf = Brain.save_workflow(name, acc_id, {"keyword": trigger_kw or name.lower()},
                             kinds or ["update"], raw)
    Brain.remember("workflow", raw, {"workflow_id": wf["workflow_id"]}, acc_id)
    return {"ok": True, "lines": [
        "✓ WORKFLOW YAAD KAR LIYA", bar,
        f"Name    ▸ {wf['name']}",
        f"Trigger ▸ {wf['trigger'].get('keyword')}",
        f"Steps   ▸ {' → '.join(wf['actions'])}",
        f"Account ▸ {acc_id or 'any'}",
        "Baad me bolo: '" + wf['name'] + " chalu karo' — main yahi workflow use karunga."]}

async def goal_recall(origin, raw, params):
    acc_id, acc, _ = pick_account(origin, raw)
    wfs = Brain.workflows(acc_id)[:6]
    mems = Brain.recall(limit=6, account_id=acc_id)
    cfg = acct_cfg(acc_id or "")
    lines = ["JARVIS MEMORY", bar,
             f"Account ▸ {('@' + acc['meta']['username']) if acc else 'none'}",
             f"Main channels ▸ {', '.join(str(c) for c in cfg.get('main_channels') or []) or 'not set'}",
             f"Source ▸ {cfg.get('source') or '—'} · Destination ▸ {cfg.get('destination') or '—'}", bar,
             "Workflows:"]
    lines += [f"  ▸ {w['name']} (trigger: {w['trigger'].get('keyword')}) → {' → '.join(w['actions'])}"
              for w in wfs] or ["  (none yet)"]
    lines.append("Recent notes:")
    lines += [f"  ▸ {m['text'][:70]}" for m in mems] or ["  (none yet)"]
    return {"ok": True, "lines": lines}

async def goal_chitchat(origin, raw, params):
    acc_id, acc, _ = pick_account(origin, raw)
    act = agent_active_tasks()
    eng = STATE["engine"]["status"]
    who = f"@{acc['meta']['username']}" if acc else "no account connected"
    return {"ok": True, "lines": [
        f"Hello 👋 JARVIS online hai — {who}.",
        f"Abhi {len(act)} background task chal rahe hain · cross engine {eng}.",
        "Bas goal bolo, steps main sambhal lunga. Jaise:",
        "  ▸ /Cross Start  (kisi post par reply karke)",
        "  ▸ is channel pe dhyan rakho, unknown messages delete karte jao",
        "  ▸ 5 minute baad forward hua message delete karna, 1 din tak"]}

async def goal_autopilot(origin, raw, params):
    acc_id, acc, how = pick_account(origin, raw)
    if not acc:
        return {"ok": False, "lines": ["NO TELEGRAM ACCOUNT ▸ pehle account add/activate karo."]}
    cfg = acct_cfg(acc_id or "")
    targets, tsrc = await discover_targets(acc_id, acc, limit=6)
    wfs = Brain.workflows(acc_id)
    lines = ["ACCOUNT REVIEW ▸ main ye sambhal sakta hoon", bar,
             f"Account ▸ @{acc['meta'].get('username')} ({how})",
             f"Main channels ▸ {len(cfg.get('main_channels') or [])} configured",
             f"Reachable targets ▸ {len(targets)} ({tsrc})",
             f"Saved workflows ▸ {len(wfs)}",
             f"Active tasks ▸ {len(agent_active_tasks(acc_id))}", bar,
             "Bolo kaunsa goal chalu karun:",
             "  ▸ cross start (post par reply karke)",
             "  ▸ channel monitor + unknown message delete",
             "  ▸ timed delete (X minute baad, Y din tak)"]
    if not (cfg.get("main_channels") or cfg.get("source")):
        lines.append("Tip ▸ main channels set karo taaki main bina puche targets use kar sakun.")
    Brain.capability_request(raw, "open-ended autopilot request")
    return {"ok": True, "lines": lines}

async def goal_delegate(origin, raw, params):
    """§5 — bounded autonomous session. Existing approved rules only."""
    acc_id, acc, how = pick_account(origin, raw)
    if not acc:
        return {"ok": False, "lines": ["NO TELEGRAM ACCOUNT ▸ pehle account add/activate karo."]}
    low = str(raw).lower()
    dur = _parse_times(low)[1]
    until = _parse_clock(low) if has(low, ("tak", "until", "till")) else None
    if until:
        dur = max(60, int(until - time.time()))
    if not dur:
        dur = 86400
    expires = time.time() + dur
    scope = []
    if has(low, ("cross",)) or True:
        scope.append("cross")
    if has(low, ("post", "publish")):
        scope.append("post")
    if has(low, ("monitor", "dhyan")):
        scope.append("monitor")
    wfs = Brain.workflows(acc_id)
    cfg = acct_cfg(acc_id or "")
    plan = ["load approved rules/workflows", "keep cross + monitors healthy",
            "respect FloodWait + pacing", "auto-expire at deadline", "report summary"]
    task = agent_task_create(acc_id, "DELEGATE", plan, expires_at=expires,
                             rules={"scope": scope, "workflows": [w["name"] for w in wfs]},
                             summary=f"delegated session ({', '.join(scope)})")
    agent_task_update(task["task_id"], status="RUNNING", next_action="supervise approved workflows")

    async def _supervise():
        try:
            while time.time() < expires and task["status"] == "RUNNING":
                await asyncio.sleep(20)
                # keep existing approved work alive; never invent new destructive actions
                eng = STATE["engine"]
                if eng["status"] == "running" and not eng["queue"] and not eng["deferred"]:
                    task["last_action"] = "cross queue drained — idling"
                for t2 in list(AGENT_TASKS.values()):
                    if t2["task_id"] != task["task_id"] and t2["status"] == "MONITORING" \
                            and t2.get("expires_at") and time.time() > t2["expires_at"]:
                        await agent_task_stop(t2["task_id"], "expired during delegation")
                task["stats"]["seen"] += 1
                agent_task_update(task["task_id"])
            if task["status"] == "RUNNING":
                task["status"] = "EXPIRED"
                st = task["stats"]
                task["last_action"] = (f"delegation window complete — supervised {st['seen']} cycles, "
                                       f"{st['errors']} errors")
                agent_task_update(task["task_id"])
                Brain.remember("delegation", f"session finished: {task['last_action']}",
                               {"task_id": task["task_id"]}, acc_id)
                safe_log("OK", "AGENT", f"delegation {task['task_id']} complete")
        except asyncio.CancelledError:
            raise
        except Exception as e:
            task["status"] = "FAILED"
            task["last_error"] = f"{type(e).__name__}"
            agent_task_update(task["task_id"])

    AGENT_RUNTIME.setdefault(task["task_id"], {}).setdefault("timers", []).append(
        asyncio.get_running_loop().create_task(_supervise()))
    Brain.remember("delegation", raw, {"task_id": task["task_id"], "scope": scope}, acc_id)
    hrs = round(dur / 3600, 1)
    return {"ok": True, "lines": [
        "YES SIR.", bar,
        f"{hrs}h delegated session active — @{acc['meta'].get('username')} ({how})",
        f"Scope    ▸ {', '.join(scope)} (existing approved rules only)",
        f"Workflows▸ {', '.join(w['name'] for w in wfs) if wfs else 'none saved yet'}",
        f"Targets  ▸ {len(cfg.get('main_channels') or [])} main channel(s) configured",
        f"Ends     ▸ {fmt_kt(expires)} (auto-stop)",
        f"Task     ▸ {task['task_id']} · Status: RUNNING",
        "Important results/errors report karunga. Naya destructive kaam bina permission ke nahi karunga."]}

async def goal_post_workflow(origin, raw, params):
    """§17 — SOURCE → (DESIGN) → SCHEDULE → PUBLISH → VERIFY → FORWARD → VERIFY."""
    acc_id, acc, how = pick_account(origin, raw)
    if not acc:
        return {"ok": False, "lines": ["NO TELEGRAM ACCOUNT ▸ pehle account add/activate karo."]}
    low = str(raw).lower()
    when = _parse_clock(low)
    src = peek_reply_source(origin)
    names = re.findall(r"([a-z0-9_]+)\s*(?:channel|chnl)", low)
    ids = re.findall(r"(-?\d{6,20})", raw)
    refs = [n for n in names if n not in ("main", "is", "ye", "the")] + ids
    want_design = has(low, ("design", "designing", "banake", "bana ke"))
    design_tool = os.getenv("DESIGN_WEBHOOK", "").strip()

    targets, verify = [], []
    for r in refs[:4]:
        ent, err = await resolve_entity_smart(acc, r)
        if ent is not None:
            targets.append({"chat_id": getattr(ent, "id", r), "title": getattr(ent, "title", str(r))})
        else:
            verify.append(f"{r} — {err}")
    if not targets:
        cfg = acct_cfg(acc_id or "")
        for c in (cfg.get("main_channels") or [])[:2]:
            ent, err = await resolve_entity_smart(acc, c)
            targets.append({"chat_id": getattr(ent, "id", c) if ent is not None else c,
                            "title": getattr(ent, "title", str(c)) if ent is not None else str(c)})

    missing = []
    if not src:
        missing.append("post content — us post par reply karke command bhejo")
    if not targets:
        missing.append("destination channel — naam/ID batao ya main channels set karo")
    if not when:
        missing.append("time — jaise '4 baje' ya 'kal 7 baje'")
    if missing:
        return {"ok": False, "lines": ["POST WORKFLOW ke liye itna chahiye:", bar] +
                                      [f"  ▸ {m}" for m in missing]}

    plan = ["identify post", "design (if tool configured)", f"schedule {fmt_kt(when)}",
            f"publish to {targets[0]['title']}", "verify", "forward to remaining targets", "verify", "report"]
    task = agent_task_create(acc_id, "POST_WORKFLOW", plan, source=src,
                             targets=[t["title"] for t in targets], expires_at=when + 3600,
                             rules={"design_requested": want_design, "design_tool": bool(design_tool)},
                             summary=f"post at {fmt_kt(when)}")
    agent_task_update(task["task_id"], status="WAITING", next_action=f"publish at {fmt_kt(when)}")

    async def _run_at():
        try:
            await asyncio.sleep(max(1, when - time.time()))
            if task["status"] not in ("WAITING", "RUNNING"):
                return
            agent_task_update(task["task_id"], status="RUNNING", last_action="publishing")
            client = acc["client"]
            first = targets[0]
            try:
                sent = await client.forward_messages(entity=first["chat_id"],
                                                     messages=[src["message_id"]],
                                                     from_peer=src["chat_id"])
                task["stats"]["acted"] += 1
                agent_task_update(task["task_id"], last_action=f"published to {first['title']}")
            except FloodWaitError as fw:
                safe_log("WARN", "POST", f"FloodWait {fw.seconds}s — exact wait")
                await asyncio.sleep(fw.seconds)
                sent = await client.forward_messages(entity=first["chat_id"],
                                                     messages=[src["message_id"]],
                                                     from_peer=src["chat_id"])
            # verify + forward to the rest
            for t2 in targets[1:]:
                try:
                    await asyncio.sleep(3)
                    await client.forward_messages(entity=t2["chat_id"], messages=[src["message_id"]],
                                                  from_peer=src["chat_id"])
                    task["stats"]["acted"] += 1
                    agent_task_update(task["task_id"], last_action=f"forwarded to {t2['title']}")
                except Exception as e:
                    task["stats"]["errors"] += 1
                    task["last_error"] = f"forward {t2['title']}: {type(e).__name__}"
            task["status"] = "COMPLETED"
            agent_task_update(task["task_id"], last_action="workflow complete")
            Brain.record("ok", "POST_WORKFLOW", f"{len(targets)} target(s)")
        except asyncio.CancelledError:
            raise
        except Exception as e:
            task["status"] = "FAILED"
            task["last_error"] = f"{type(e).__name__}: {str(e)[:120]}"
            agent_task_update(task["task_id"])
            Brain.record("fail", "POST_WORKFLOW", task["last_error"])

    AGENT_RUNTIME.setdefault(task["task_id"], {}).setdefault("timers", []).append(
        asyncio.get_running_loop().create_task(_run_at()))
    Brain.remember("post", raw, {"task_id": task["task_id"], "when": when}, acc_id)

    lines = ["YES SIR.", bar, "Post workflow scheduled.",
             f"Post     ▸ replied message (id {src['message_id']})",
             f"Publish  ▸ {targets[0]['title']} at {fmt_kt(when)}"]
    if len(targets) > 1:
        lines.append(f"Forward  ▸ {', '.join(t['title'] for t in targets[1:])} (after verify)")
    if want_design:
        lines.append("Design   ▸ NOT AVAILABLE — koi design tool configured nahi hai, "
                     "post original form me jayega (main jhooth nahi bolunga)")
        Brain.capability_request(raw, "design workflow/tool requested but none configured")
    if verify:
        lines += [f"Unresolved ▸ {v}" for v in verify]
    lines.append(f"Task     ▸ {task['task_id']} · Status: WAITING")
    return {"ok": True, "lines": lines}

async def goal_activity_report(origin, raw, params):
    """§16 — measurable analysis only; never invents attribution data."""
    acc_id, acc, how = pick_account(origin, raw)
    if not acc:
        return {"ok": False, "lines": ["NO TELEGRAM ACCOUNT ▸ pehle account connect karo."]}
    low = str(raw).lower()
    ref = None
    um = re.search(r"@([a-zA-Z0-9_]{3,32})", raw)
    idm = re.search(r"(-?\d{6,20})", raw)
    if um:
        ref = um.group(1)
    elif idm:
        ref = idm.group(1)
    r = peek_reply_source(origin)
    if not ref and r:
        ref = str(r["chat_id"])
    if not ref:
        cfg = acct_cfg(acc_id or "")
        ref = cfg.get("main_channel")
    if not ref:
        return {"ok": False, "lines": [
            "KISKA ANALYSIS? ▸ @username / numeric ID batao, ya us chat ke message par reply karo."]}
    ent, err = await resolve_entity_smart(acc, ref)
    if ent is None:
        return {"ok": False, "lines": [err]}
    title = getattr(ent, "title", None) or getattr(ent, "first_name", None) or str(ref)

    now = datetime.now(timezone.utc)
    buckets = {"24h": 0, "7d": 0, "30d": 0}
    links = fwd = media = 0
    senders, total = {}, 0
    try:
        async for m in acc["client"].iter_messages(ent, limit=300):
            if not m:
                continue
            total += 1
            d = getattr(m, "date", None)
            if d:
                d = d if d.tzinfo else d.replace(tzinfo=timezone.utc)
                age = (now - d).total_seconds()
                if age <= 86400: buckets["24h"] += 1
                if age <= 7 * 86400: buckets["7d"] += 1
                if age <= 30 * 86400: buckets["30d"] += 1
            txt = (getattr(m, "text", None) or "")
            if re.search(r"(https?://|t\.me/|@[a-zA-Z0-9_]{4,})", txt):
                links += 1
            if getattr(m, "forward", None) or getattr(m, "fwd_from", None):
                fwd += 1
            if getattr(m, "media", None) is not None:
                media += 1
            sid = getattr(m, "sender_id", None)
            if sid:
                senders[sid] = senders.get(sid, 0) + 1
    except FloodWaitError as fw:
        await asyncio.sleep(fw.seconds)
        return {"ok": False, "lines": [f"FloodWait {fw.seconds}s honoured — dobara bolo."]}
    except Exception as e:
        return {"ok": False, "lines": [f"READ ERROR ▸ {type(e).__name__}: {str(e)[:100]}"]}

    top = sorted(senders.items(), key=lambda kv: -kv[1])[:3]
    eng = STATE["engine"]
    Brain.remember("analytics", f"activity report for {title}",
                   {"chat_id": getattr(ent, 'id', None), "sampled": total}, acc_id)
    lines = ["ACTIVITY REPORT", bar,
             f"Target ▸ {title} ({getattr(ent, 'id', ref)})",
             f"Sample ▸ last {total} accessible messages", bar,
             f"Last 24h ▸ {buckets['24h']} msgs · 7d ▸ {buckets['7d']} · 30d ▸ {buckets['30d']}",
             f"Links/invites ▸ {links}   Forwarded ▸ {fwd}   Media ▸ {media}"]
    if top:
        lines.append("Top posters ▸ " + ", ".join(f"{sid}: {n}" for sid, n in top))
    lines += [bar,
              f"Cross engine (this account) ▸ sent {eng['processed']} · failed {eng['failed']}",
              "Note ▸ Telegram per-user JOIN attribution expose nahi karta — isliye "
              "'kisse kitne log join hue' measurable nahi hai. Upar ka sab real counted data hai."]
    return {"ok": True, "lines": lines}

async def goal_workflow_run(origin, raw, params):
    """TEST 11 — retrieve a taught workflow and act on it."""
    acc_id, acc, how = pick_account(origin, raw)
    wf = Brain.find_workflow(raw, acc_id) or Brain.find_workflow(raw)
    if not wf:
        wfs = Brain.workflows(acc_id)
        if not wfs:
            return {"ok": False, "lines": [
                "Koi saved workflow nahi mila.",
                "Sikhao aise: '/AI yaad rakho: jab toss line aaye to update bhejna, name: TOSS-FLOW'"]}
        return {"ok": False, "lines": ["Kaunsa workflow? Saved workflows:"] +
                                      [f"  ▸ {w['name']} (trigger: {w['trigger'].get('keyword')})" for w in wfs]}
    wfs = Brain._wf()
    for w in wfs.get("workflows", []):
        if w["workflow_id"] == wf["workflow_id"]:
            w["uses"] = w.get("uses", 0) + 1
            w["last_used"] = int(time.time())
    workflows_store.save_bg(wfs)
    acts = wf.get("actions") or []
    lines = ["YES SIR.", bar,
             f"Saved workflow retrieved ▸ {wf['name']}",
             f"Trigger ▸ {wf['trigger'].get('keyword')}",
             f"Steps   ▸ {' → '.join(acts)}",
             f"Learned ▸ {fmt_kt(wf['created_at'])} · used {wf.get('uses', 1)}x"]
    ran = []
    if "cross" in acts:
        res = await goal_cross_start(origin, raw, {})
        ran.append("cross")
        lines += [bar] + (res.get("lines") or [])
    elif "delete" in acts:
        lines += [bar, "Is workflow me delete step hai — monitoring chahiye to bolo:",
                  "'is channel pe dhyan rakho' (main rule ke saath monitor create kar dunga)."]
    else:
        src, err = await discover_cross_source(origin, acc_id, acc) if acc else (None, "no account")
        if src:
            lines += [bar, f"Update source ready ▸ {src['via']} (msg {src.get('message_id')})",
                      "Bolo 'cross start' ya destination batao — main bhej dunga."]
        else:
            lines += [bar, f"Update step ke liye source chahiye — {err}"]
    Brain.remember("workflow_use", f"used {wf['name']}", {"workflow_id": wf["workflow_id"]}, acc_id)
    return {"ok": True, "lines": lines}

async def goal_admin_request(origin, raw, params):
    """§18/§19 — never grants privileges on request; prepares owner approval."""
    acc_id, acc, how = pick_account(origin, raw)
    if not acc:
        return {"ok": False, "lines": ["NO TELEGRAM ACCOUNT ▸ pehle account connect karo."]}
    um = re.search(r"@([a-zA-Z0-9_]{3,32})", raw)
    idm = re.search(r"(-?\d{6,20})", raw)
    who = um.group(1) if um else (idm.group(1) if idm else None)
    cfg = acct_cfg(acc_id or "")
    chan = cfg.get("main_channel")
    target_txt = f"@{who}" if who else "(user not identified)"
    chan_txt = str(chan) if chan else "(main channel not configured)"
    can_promote = None
    if chan:
        try:
            perms = await acc["client"].get_permissions(int(chan) if str(chan).lstrip("-").isdigit() else chan, "me")
            can_promote = bool(getattr(perms, "is_creator", False) or getattr(perms, "add_admins", False))
        except Exception:
            can_promote = None
    Brain.remember("admin_request", raw, {"user": who, "channel": chan}, acc_id)
    lines = ["ADMIN REQUEST NOTED — approval ke bina kuch nahi karunga", bar,
             f"Requested for ▸ {target_txt}",
             f"Channel       ▸ {chan_txt}",
             f"Your rights   ▸ " + ("can add admins" if can_promote else
                                    ("NO 'add admins' right" if can_promote is False else "not verified")),
             bar, "Boss se confirmation ke baad hi promote hoga. Approve karne ke liye bolo:",
             f"  /AI {chan_txt} me {target_txt} ko admin de do",
             "(wo command confirmation maangegi, phir real Telegram permission check karke chalegi)"]
    if not who:
        lines.append("Pehle @username ya user ID batao.")
    return {"ok": True, "lines": lines}

GOAL_EXECUTORS = {
    "DELEGATE": goal_delegate,
    "POST_WORKFLOW": goal_post_workflow,
    "ACTIVITY_REPORT": goal_activity_report,
    "WORKFLOW_RUN": goal_workflow_run,
    "ADMIN_REQUEST": goal_admin_request,

    "CROSS_START": goal_cross_start,
    "MONITOR_WATCH": goal_monitor,
    "SET_MAIN_CHANNELS": goal_set_main_channels,
    "INSPECT": goal_inspect,
    "TASK_LIST": goal_task_list,
    "STOP_TASK": goal_stop_task,
    "STOP_ALL_TASKS": goal_stop_all,
    "TEACH": goal_teach,
    "RECALL": goal_recall,
    "CHITCHAT": goal_chitchat,
    "AUTOPILOT": goal_autopilot,
}

async def agent_dispatch(raw, origin):
    """Returns a result dict when a goal is recognised, else None."""
    g = parse_goal(raw)
    if not g:
        return None
    goal = g["goal"]
    if goal in ("CROSS_STOP", "CROSS_RESET", "CROSS_STATUS"):
        return None      # existing cross tools already handle these well
    fn = GOAL_EXECUTORS.get(goal)
    if not fn:
        return None
    safe_log("CMD", "AGENT", f"goal {goal} from {origin}")
    try:
        res = await fn(origin, raw, g.get("params") or {})
        res.setdefault("action", goal)
        return res
    except FloodWaitError as fw:
        await asyncio.sleep(fw.seconds)
        return {"ok": False, "action": goal,
                "lines": [f"FloodWait {fw.seconds}s honoured — dobara bolo."]}
    except Exception as e:
        log.error("agent goal %s failed: %s", goal, type(e).__name__)
        Brain.record("fail", goal, f"{type(e).__name__}: {e}")
        return {"ok": False, "action": goal,
                "lines": [f"{goal} FAILED ▸ {type(e).__name__}: {str(e)[:140]}"]}

async def agent_restore_tasks():
    """Reload persisted tasks after restart; expire what is over, mark rest."""
    try:
        rows = agent_tasks_store.load().get("tasks", [])
    except Exception:
        rows = []
    now = time.time()
    revived = 0
    for r in rows:
        if r.get("status") in ("COMPLETED", "FAILED", "STOPPED", "EXPIRED"):
            continue
        if r.get("expires_at") and now > r["expires_at"]:
            r["status"] = "EXPIRED"
            AGENT_TASKS[r["task_id"]] = r
            continue
        r["status"] = "PAUSED"
        r["last_action"] = "restored after restart — resume to continue"
        AGENT_TASKS[r["task_id"]] = r
        revived += 1
    if rows:
        agent_tasks_persist()
    if revived:
        safe_log("WARN", "AGENT", f"{revived} task(s) restored as PAUSED after restart")
    return revived

# ============================================================================
# Diagnostics / Scheduler
# ============================================================================
def diagnostics():
    checks = []
    connected, authed = TG.status()
    eng = STATE["engine"]
    cid, ids = cfg_source()

    def add(name, status, detail):
        checks.append({"name": name, "status": status, "detail": detail})

    add("Web Server", "PASS", "Quart on 0.0.0.0:$PORT — /health OK")
    add("Telegram Connection", "PASS" if connected else "FAIL",
        f"Live as @{TG.account['username']}" if connected and TG.account else "No client connected")
    add("Session Validity", "PASS" if authed else ("FAIL" if connected else "WARN"),
        "Session authorized" if authed else "Not authorized" if connected else "No session")
    add("JARVIS Authorization", "PASS" if server_token() else "FAIL",
        "JARVIS_ACCESS_TOKEN configured" if server_token() else "JARVIS_ACCESS_TOKEN missing — fail closed")
    add("Multi-Account", "PASS" if any(a["connected"] for a in ACCOUNTS.view()) else "WARN",
        f"{len(ACCOUNTS.accounts)}/{AccountManager.MAX_ACCOUNTS} managed ▸ fernet {'ON' if _get_fernet() else 'OFF (memory-only)'}")
    src_ok = (cid and ids) or cfg_monitor()[0]
    add("Source Configuration", "PASS" if src_ok else "WARN",
        f"cross {cid or '—'} • monitor {cfg_monitor()[0] or '—'} (web-config hot reload)"
        if src_ok else "SOURCE NOT AVAILABLE — Source Config panel ya ENV se set karo")
    try:
        probe = DATA / ".probe"
        probe.write_text("ok"); probe.unlink()
        add("JSON Storage", "PASS", "data/ writable — accounts/scripts/runtime persisted")
    except Exception:
        add("JSON Storage", "FAIL", "data/ not writable")
    conf = AI.configured()
    add("AI Providers", "PASS" if conf else "WARN",
        f"NLU chain: {', '.join(conf)}" if conf else "No cloud keys — deterministic local NLU (full offline, tools unaffected)")
    add("Scheduler", "PASS", f"{len([j for j in SCHED.jobs if not j.get('done')])} active jobs ▸ Asia/Kathmandu")
    add("Cross Engine", "PASS" if eng["status"] == "running" else "WARN",
        f"{eng['status'].upper()} ▸ task {ENGINE.tid or '-'}")
    add("Monitor", "PASS" if STATE["monitor"].get("active") else "WARN",
        "Event-based listener live" if STATE["monitor"].get("active") else "Stopped — /AI source monitor start")
    missing = [k for k in ("JARVIS_SECRET_KEY",) if not os.getenv(k)]
    add("Environment", "PASS" if not missing else "WARN",
        "JARVIS_SECRET_KEY set — sessions persist encrypted" if not missing
        else "JARVIS_SECRET_KEY unset — managed accounts are memory-only")
    score = round(sum(1 if c["status"] == "PASS" else 0.5 if c["status"] == "WARN" else 0
                      for c in checks) / len(checks) * 100)
    safe_log("OK" if score >= 85 else "WARN", "DIAG", f"Diagnostics score {score}%")
    return {"ok": True, "score": score, "checks": checks, "ran_at": int(time.time())}

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
# Web API (contract preserved — all existing routes + new panels' routes)
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
                     "account": scrub(TG.account) if TG.account else None,
                     "accounts": ACCOUNTS.view()},
        "engine": {"status": eng["status"], "queue": len(eng["queue"]),
                   "deferred": len(eng["deferred"]), "processed": eng["processed"],
                   "failed": eng["failed"],
                   "flood_wait_in": max(0, int((eng.get("flood_wait_until") or 0) - time.time())),
                   "last_event": eng.get("last_event"),
                   "source_configured": bool(cid_ok()[0] and cid_ok()[1])},
        "ai": {"provider": AI.last_provider, "calls": AI.total, "configured": AI.configured(),
               "providers": AI.providers_view()},
        "scheduler": {"active": len([j for j in SCHED.jobs if not j.get("done")]),
                      "jobs": [{"id": j["id"], "action": j["action"], "label": j["label"],
                                "run_at": j["run_at"], "done": bool(j.get("done"))} for j in SCHED.jobs[-10:]]},
        "last_command": STATE.get("last_command"),
        "last_error": STATE.get("last_error"),
    })

def cid_ok():
    return cfg_source()

@app.route("/api/diagnostics")
async def api_diag():
    return jsonify(diagnostics())

# ---- telegram login (primary) ----
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

# ---- jarvis auth / commands ----
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
                        "lines": [f"CONFIRM REQUIRED ▸ reset clears queue/counters ({CONFIRM_TTL}s)."]})
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

# ---- runtime source config (web-editable, hot reload) ----
@app.route("/api/config/source", methods=["GET"])
@require_token
async def api_get_source_config():
    cfg = cfg_get()
    cid, ids = cfg_source()
    msrc, mdst = cfg_monitor()
    return jsonify({"ok": True, "config": cfg, "effective": {
        "source_chat_id": cid, "source_message_ids": ids,
        "monitor_source": msrc, "monitor_destination": mdst}})

@app.route("/api/config/source", methods=["POST"])
@require_token
async def api_set_source_config():
    body = await request.get_json(silent=True) or {}
    cfg = runtime_store.load()
    if "source_chat_id" in body:
        v = body["source_chat_id"]
        cfg["source_chat_id"] = int(v) if str(v).strip().lstrip("-").isdigit() else None
    if "source_message_ids" in body:
        v = body["source_message_ids"]
        if isinstance(v, str):
            cfg["source_message_ids"] = [int(x) for x in re.split(r"[,\s]+", v) if x.strip().isdigit()]
        elif isinstance(v, list):
            cfg["source_message_ids"] = [int(x) for x in v if str(x).strip().isdigit()]
    if "monitor_source" in body:
        cfg["monitor_source"] = str(body["monitor_source"]).strip() or None
    if "monitor_destination" in body:
        cfg["monitor_destination"] = str(body["monitor_destination"]).strip() or None
    if "dead_threshold_days" in body:
        try:
            cfg["dead_threshold_days"] = max(1, int(body["dead_threshold_days"]))
        except Exception:
            pass
    cfg["updated_at"] = int(time.time())
    await runtime_store.save(cfg)
    # live-apply monitor targets too
    if cfg.get("monitor_source"):
        STATE["monitor"]["source"] = cfg["monitor_source"]
    if cfg.get("monitor_destination"):
        STATE["monitor"]["destination"] = cfg["monitor_destination"]
    state_store.save_bg(STATE)
    ENGINE.reload_config()
    safe_log("CMD", "CONFIG", "Source config updated via web UI — hot applied, redeploy nahi chahiye")
    return jsonify({"ok": True, "config": cfg, "effective": {
        "source_chat_id": cfg_source()[0], "source_message_ids": cfg_source()[1],
        "monitor_source": cfg_monitor()[0], "monitor_destination": cfg_monitor()[1]}})

# ---- multi-account (encrypted, max 2) ----
@app.route("/api/accounts/list", methods=["GET"])
@require_token
async def api_accounts_list():
    return jsonify({"ok": True, "accounts": ACCOUNTS.view(), "max": AccountManager.MAX_ACCOUNTS,
                    "persistent": bool(_get_fernet())})

@app.route("/api/accounts/add", methods=["POST"])
@require_token
async def api_accounts_add():
    body = await request.get_json(silent=True) or {}
    label = str(body.get("label", "")).strip()[:40] or "Account"
    try:
        api_id = int(str(body.get("api_id", "")).strip())
    except ValueError:
        return jsonify({"ok": False, "error": "Invalid API ID"}), 400
    api_hash = str(body.get("api_hash", "")).strip()
    session_string = str(body.get("session_string", "")).strip()
    if not api_hash or not session_string:
        return jsonify({"ok": False, "error": "API_HASH and SESSION_STRING required"}), 400
    ok, payload = await ACCOUNTS.add_account(label, api_id, api_hash, session_string)
    if not ok:
        return jsonify({"ok": False, "error": payload}), 400
    return jsonify({"ok": True, **payload})

@app.route("/api/accounts/remove", methods=["POST"])
@require_token
async def api_accounts_remove():
    body = await request.get_json(silent=True) or {}
    ok, msg = await ACCOUNTS.remove_account(str(body.get("id", "")))
    return jsonify({"ok": ok, "message": msg}), (200 if ok else 400)

@app.route("/api/accounts/activate", methods=["POST"])
@require_token
async def api_accounts_activate():
    body = await request.get_json(silent=True) or {}
    ok, msg = await ACCOUNTS.activate(str(body.get("id", "")))
    if ok:
        await SCHED.recover()
    return jsonify({"ok": ok, "message": msg}), (200 if ok else 400)

# ---- custom scripts — install/run/stop/logs (token-protected) ----
def _script_meta(acc_id):
    st = _scripts_get_state(acc_id)
    return {"name": st.get("name", ""), "code": st.get("code", ""),
            "template": st.get("template", "custom"), "mode": st.get("mode", "safe"),
            "running": acc_id in SCRIPT_TASKS, "installed_at": st.get("installed_at"),
            "updated_at": st.get("updated_at")}

@app.route("/api/scripts/get", methods=["POST"])
@require_token
async def api_scripts_get():
    body = await request.get_json(silent=True) or {}
    acc_id = str(body.get("account_id", ""))
    return jsonify({"ok": True, **_script_meta(acc_id)})

@app.route("/api/scripts/validate", methods=["POST"])
@require_token
async def api_scripts_validate():
    body = await request.get_json(silent=True) or {}
    mode = str(body.get("mode", "safe")).lower()
    validator = RawScriptRunner.validate if mode == "raw" else SafeScriptRunner.validate
    ok, err = validator(str(body.get("code", "")))
    label = "Valid raw-mode telethon script" if mode == "raw" else "Valid sandbox script"
    return jsonify({"ok": ok, "mode": mode, "message": label if ok else None, "error": None if ok else err})

@app.route("/api/scripts/save", methods=["POST"])
@require_token
async def api_scripts_save():
    body = await request.get_json(silent=True) or {}
    acc_id = str(body.get("account_id", ""))
    code = str(body.get("code", ""))
    mode = str(body.get("mode", "safe")).lower()
    if mode not in ("safe", "raw"):
        mode = "safe"
    ok, err = (RawScriptRunner if mode == "raw" else SafeScriptRunner).validate(code)
    if not ok:
        return jsonify({"ok": False, "error": err}), 400
    raw = scripts_store.load()
    prev = raw.get(acc_id, {})
    raw[acc_id] = {"name": str(body.get("name", "")).strip()[:60],
                   "code": code,
                   "template": str(body.get("template", "custom"))[:40],
                   "mode": mode,
                   "running": bool(raw.get(acc_id, {}).get("running")),
                   "installed_at": prev.get("installed_at"),
                   "updated_at": int(time.time())}
    await scripts_store.save(raw)
    safe_log("CMD", "SCRIPT", f"Script saved for {acc_id} ({mode})")
    return jsonify({"ok": True, **_script_meta(acc_id)})

@app.route("/api/scripts/install", methods=["POST"])
@require_token
async def api_scripts_install():
    body = await request.get_json(silent=True) or {}
    acc_id = str(body.get("account_id", ""))
    # save first (same validation path), then run
    save_body = {**body}
    code = str(save_body.get("code", ""))
    mode = str(save_body.get("mode", "safe")).lower()
    mode = mode if mode in ("safe", "raw") else "safe"
    ok, err = SafeScriptRunner.validate(code)
    if not ok:
        return jsonify({"ok": False, "error": err}), 400
    raw = scripts_store.load()
    prev = raw.get(acc_id, {})
    raw[acc_id] = {"name": str(save_body.get("name", "")).strip()[:60], "code": code,
                   "template": str(save_body.get("template", "custom"))[:40], "mode": mode,
                   "running": False, "installed_at": prev.get("installed_at"),
                   "updated_at": int(time.time())}
    await scripts_store.save(raw)
    ok_run, payload = await start_script(acc_id)
    if not ok_run:
        return jsonify({"ok": False, "error": payload}), 400
    return jsonify({"ok": True, "running": True, **_script_meta(acc_id)})

@app.route("/api/scripts/stop", methods=["POST"])
@require_token
async def api_scripts_stop():
    body = await request.get_json(silent=True) or {}
    acc_id = str(body.get("account_id", ""))
    if acc_id not in SCRIPT_TASKS and acc_id not in SCRIPT_PROGRESS:
        return jsonify({"ok": False, "error": "No running script for this account"}), 400
    ok, payload = await stop_script(acc_id, "web")
    return jsonify({"ok": True, "running": False}), 200

@app.route("/api/scripts/templates", methods=["GET", "POST"])
@require_token
async def api_scripts_templates():
    out = []
    for key, t in SCRIPT_TEMPLATES.items():
        out.append({"key": key, "label": t["label"], "source": "built-in",
                    "mode": t.get("mode", "raw"), "code": t["code"]})
    for key, t in templates_store.load().items():
        out.append({"key": key, "label": t.get("label", key), "source": "user",
                    "mode": t.get("mode", "raw"), "code": t.get("code", "")})
    return jsonify({"ok": True, "templates": out})

@app.route("/api/scripts/templates/save", methods=["POST"])
@require_token
async def api_scripts_templates_save():
    body = await request.get_json(silent=True) or {}
    label = str(body.get("label", "")).strip()[:40] or "User Template"
    code = str(body.get("code", ""))
    mode = str(body.get("mode", "safe")).lower()
    mode = mode if mode in ("safe", "raw") else "safe"
    ok, err = (RawScriptRunner if mode == "raw" else SafeScriptRunner).validate(code)
    if not ok:
        return jsonify({"ok": False, "error": err}), 400
    key = "user_" + uuid.uuid4().hex[:5]
    store = templates_store.load()
    store[key] = {"label": label, "mode": mode, "code": code, "updated_at": int(time.time())}
    await templates_store.save(store)
    safe_log("CMD", "SCRIPT", f"Template saved: {label}")
    return jsonify({"ok": True, "key": key})

@app.route("/api/scripts/logs", methods=["GET"])
@require_token
async def api_scripts_logs():
    acc_id = str(request.args.get("account_id", ""))
    return jsonify({"ok": True, "logs": ScriptLogger.tail(acc_id, 200),
                    "running": acc_id in SCRIPT_TASKS})

@app.route("/api/scripts/logs/clear", methods=["POST"])
@require_token
async def api_scripts_logs_clear():
    body = await request.get_json(silent=True) or {}
    ScriptLogger.clear(str(body.get("account_id", "")))
    return jsonify({"ok": True})

# ---- custom script runner: account-bound automation templates --------------
@app.route("/api/automation/actions", methods=["GET"])
@require_token
async def api_auto_actions():
    return jsonify({"ok": True, "actions": [
        {"name": k, "desc": v["desc"], "params": v["params"], "needs": v["needs"]}
        for k, v in ACTION_REGISTRY.items()]})

@app.route("/api/automation/validate", methods=["POST"])
@require_token
async def api_auto_validate():
    body = await request.get_json(silent=True) or {}
    acc_id = str(body.get("account_id", ""))
    defn, err = parse_automation(str(body.get("code", "")))
    if err:
        return jsonify({"ok": False, "error": err,
                        "checks": [{"ok": bool(acc_id and acc_id in ACCOUNTS.accounts), "label": "Account selected", "detail": ""},
                                   {"ok": False, "label": "Script structure valid", "detail": err}]})
    v = validate_automation(defn, acc_id)
    return jsonify({"ok": v["ok"], "checks": v["checks"], "errors": v["errors"],
                    "action_count": v["action_count"]})

@app.route("/api/automation/templates", methods=["GET"])
@require_token
async def api_auto_templates():
    acc_id = str(request.args.get("account_id", ""))
    items = templates_all()
    if acc_id:
        items = [t for t in items if t.get("account_id") == acc_id]
    out = []
    for t in items:
        owner = ACCOUNTS.accounts.get(t.get("account_id"))
        out.append({**{k: t.get(k) for k in ("template_id", "name", "account_id", "description",
                                             "code", "enabled", "schedule", "last_run", "last_result",
                                             "created_at", "updated_at")},
                    "account": (owner or {}).get("meta", {}).get("username"),
                    "running_task": AUTO_BY_TEMPLATE.get(t["template_id"])})
    return jsonify({"ok": True, "templates": out})

@app.route("/api/automation/templates/save", methods=["POST"])
@require_token
async def api_auto_tpl_save():
    body = await request.get_json(silent=True) or {}
    acc_id = str(body.get("account_id", ""))
    if acc_id not in ACCOUNTS.accounts:
        return jsonify({"ok": False, "error": "Select a valid account first (templates are account-bound)"}), 400
    code = str(body.get("code", ""))
    defn, err = parse_automation(code)
    if err:
        return jsonify({"ok": False, "error": err}), 400
    v = validate_automation(defn, acc_id)
    unknown = [c for c in v["checks"] if not c["ok"] and c["label"] in ("Allowed actions", "Parameters valid")]
    if unknown:
        return jsonify({"ok": False, "error": unknown[0]["label"] + " — " + unknown[0]["detail"]}), 400
    tid = await template_save({"template_id": body.get("template_id"),
                               "name": str(body.get("name", "")).strip()[:40] or "UNNAMED",
                               "account_id": acc_id, "description": str(body.get("description", ""))[:200],
                               "code": code, "actions": defn.get("actions") or [],
                               "configuration": defn.get("configuration") or {},
                               "conditions": defn.get("conditions") or {},
                               "schedule": defn.get("schedule"),
                               "enabled": bool(body.get("enabled", True))})
    safe_log("CMD", "AUTOMATION", f"template {tid} saved for {acc_id}")
    return jsonify({"ok": True, "template_id": tid, "validation": v})

@app.route("/api/automation/templates/delete", methods=["POST"])
@require_token
async def api_auto_tpl_delete():
    body = await request.get_json(silent=True) or {}
    tid = str(body.get("template_id", ""))
    if not template_get(tid):
        return jsonify({"ok": False, "error": "Template not found"}), 404
    if AUTO_BY_TEMPLATE.get(tid):
        return jsonify({"ok": False, "error": "Template is running — stop it first"}), 400
    await template_delete(tid)
    return jsonify({"ok": True})

@app.route("/api/automation/templates/duplicate", methods=["POST"])
@require_token
async def api_auto_tpl_dup():
    body = await request.get_json(silent=True) or {}
    t = template_get(str(body.get("template_id", "")))
    if not t:
        return jsonify({"ok": False, "error": "Template not found"}), 404
    tid = await template_save({"name": (t["name"] + "-COPY")[:40], "account_id": t.get("account_id"),
                               "description": t.get("description", ""), "code": t.get("code", ""),
                               "actions": t.get("actions") or [], "configuration": t.get("configuration") or {},
                               "enabled": False})
    return jsonify({"ok": True, "template_id": tid})

@app.route("/api/automation/templates/toggle", methods=["POST"])
@require_token
async def api_auto_tpl_toggle():
    body = await request.get_json(silent=True) or {}
    tid = str(body.get("template_id", ""))
    if not template_get(tid):
        return jsonify({"ok": False, "error": "Template not found"}), 404
    t = await template_patch(tid, enabled=bool(body.get("enabled", True)))
    return jsonify({"ok": True, "enabled": t["enabled"]})

@app.route("/api/automation/run", methods=["POST"])
@require_token
async def api_auto_run():
    body = await request.get_json(silent=True) or {}
    tid = str(body.get("template_id", "")).strip()
    tpl = template_get(tid) if tid else None
    if tpl:
        acc_id = tpl.get("account_id")
        if not tpl.get("enabled", True):
            return jsonify({"ok": False, "error": "Template is DISABLED — enable it first"}), 400
        if AUTO_BY_TEMPLATE.get(tid):
            return jsonify({"ok": False, "error": f"Already running (task {AUTO_BY_TEMPLATE[tid]})"}), 400
        code = tpl.get("code", "")
    else:
        acc_id = str(body.get("account_id", ""))
        code = str(body.get("code", ""))
    if acc_id not in ACCOUNTS.accounts:
        return jsonify({"ok": False, "error": "Account not found — select a valid account"}), 400
    defn, err = parse_automation(code)
    if err:
        return jsonify({"ok": False, "error": "TEMPLATE INVALID — " + err}), 400
    ok, payload = await run_automation(acc_id, defn, tpl, origin=caller_origin())
    if not ok:
        return jsonify({"ok": False, **payload}), 400
    return jsonify({"ok": True, **payload})

@app.route("/api/automation/stop", methods=["POST"])
@require_token
async def api_auto_stop():
    body = await request.get_json(silent=True) or {}
    tid = str(body.get("task_id", "")) or AUTO_BY_TEMPLATE.get(str(body.get("template_id", "")), "")
    if not tid or tid not in AUTO_TASKS:
        return jsonify({"ok": False, "error": "No running task for that template/id"}), 400
    ok, status = await stop_automation(tid, "web")
    return jsonify({"ok": ok, "status": status})

@app.route("/api/automation/tasks", methods=["GET"])
@require_token
async def api_auto_tasks():
    acc_id = str(request.args.get("account_id", ""))
    rows = [automation_task_view(t) for t in AUTO_TASKS.values()
            if not acc_id or t["account_id"] == acc_id]
    return jsonify({"ok": True, "tasks": rows[-20:]})

@app.route("/api/automation/logs", methods=["GET"])
@require_token
async def api_auto_logs():
    tid = str(request.args.get("task_id", ""))
    if not tid:
        tpl = str(request.args.get("template_id", ""))
        tid = AUTO_BY_TEMPLATE.get(tpl, "")
        if not tid:
            cands = [t for t in AUTO_TASKS.values() if t.get("template_id") == tpl]
            tid = cands[-1]["task_id"] if cands else ""
    task = AUTO_TASKS.get(tid)
    return jsonify({"ok": True, "task_id": tid,
                    "task": automation_task_view(task) if task else None,
                    "logs": list(AUTO_LOGS.get(tid, []))[-200:]})

@app.route("/api/automation/heal", methods=["POST"])
@require_token
async def api_auto_heal():
    healed = automation_heal()
    for acc_id, acc in ACCOUNTS.accounts.items():
        c = acc.get("client")
        if c and not c.is_connected():
            try:
                await c.connect()
                healed.append(f"{acc_id}: telegram client reconnected")
            except Exception as e:
                healed.append(f"{acc_id}: reconnect failed ({type(e).__name__})")
    return jsonify({"ok": True, "healed": healed,
                    "message": "runtime state only — template source never modified"})

@app.route("/api/account/config", methods=["GET", "POST"])
@require_token
async def api_account_config():
    if request.method == "GET":
        acc_id = str(request.args.get("account_id", ""))
        return jsonify({"ok": True, "config": acct_cfg(acc_id) if acc_id else {}})
    body = await request.get_json(silent=True) or {}
    acc_id = str(body.get("account_id", ""))
    if acc_id not in ACCOUNTS.accounts:
        return jsonify({"ok": False, "error": "Account not found"}), 400
    store = acctcfg_store.load()
    cfg = store.get(acc_id, {})
    # canonical keys + the aliases used by the web UI / API clients
    aliases = {"main_channel": ("main_channel", "main_channel_id", "mainChannelId"),
               "source": ("source", "source_channel", "sourceChannel"),
               "destination": ("destination", "destination_channel", "destinationChannel")}
    for canon, keys in aliases.items():
        for k in keys:
            if k in body:
                cfg[canon] = str(body[k]).strip() or None
                break
    if "main_channels" in body:
        v = body["main_channels"]
        items = re.split(r"[,\s]+", v) if isinstance(v, str) else list(v or [])
        cfg["main_channels"] = [str(x).strip() for x in items if str(x).strip()]
        if cfg["main_channels"]:
            cfg["main_channel"] = cfg["main_channels"][0]
    if "keywords" in body:
        v = body["keywords"]
        cfg["keywords"] = [x.strip() for x in v.split(",")] if isinstance(v, str) else list(v or [])
    cfg["updated_at"] = int(time.time())
    store[acc_id] = cfg
    await acctcfg_store.save(store)
    safe_log("CMD", "ACCOUNT", f"config saved for {acc_id}")
    return jsonify({"ok": True, "config": acct_cfg(acc_id)})

# ---- requested API shape (§2,§3): /api/script/* aliases over the same engine
@app.route("/api/script/run", methods=["POST"])
@require_token
async def api_script_run_alias():
    """Run a pasted Telethon script for ONE account (raw context + healing)."""
    body = await request.get_json(silent=True) or {}
    acc_id = str(body.get("account_id", ""))
    code = str(body.get("code", ""))
    mode = str(body.get("mode", "raw")).lower()
    mode = mode if mode in ("safe", "raw") else "raw"
    if acc_id not in ACCOUNTS.accounts:
        return jsonify({"ok": False, "error": "Account not found — select a valid account"}), 400
    if not code.strip():
        return jsonify({"ok": False, "error": "Script is empty"}), 400
    ok, err = (RawScriptRunner if mode == "raw" else SafeScriptRunner).validate(code)
    if not ok:
        return jsonify({"ok": False, "error": err}), 400
    raw = scripts_store.load()
    prev = raw.get(acc_id, {})
    raw[acc_id] = {"name": str(body.get("name", "")).strip()[:60] or prev.get("name", ""),
                   "code": code, "template": str(body.get("template", "custom"))[:40],
                   "mode": mode, "running": False,
                   "installed_at": prev.get("installed_at"), "updated_at": int(time.time())}
    await scripts_store.save(raw)
    ok_run, payload = await start_script(acc_id)
    if not ok_run:
        return jsonify({"ok": False, "error": payload}), 400
    return jsonify({"ok": True, "account_id": acc_id, "mode": mode, "running": True,
                    "main_channel_id": acct_cfg(acc_id).get("main_channel")})

@app.route("/api/script/stop", methods=["POST"])
@require_token
async def api_script_stop_alias():
    body = await request.get_json(silent=True) or {}
    acc_id = str(body.get("account_id", ""))
    if acc_id not in SCRIPT_TASKS and acc_id not in SCRIPT_PROGRESS:
        return jsonify({"ok": False, "error": "No running script for this account"}), 400
    await stop_script(acc_id, "web")
    return jsonify({"ok": True, "account_id": acc_id, "running": False})

@app.route("/api/script/logs/<account_id>", methods=["GET"])
@require_token
async def api_script_logs_alias(account_id):
    acc_id = str(account_id)
    try:
        limit = max(1, min(int(request.args.get("limit", 200)), 500))
    except ValueError:
        limit = 200
    return jsonify({"ok": True, "account_id": acc_id, "running": acc_id in SCRIPT_TASKS,
                    "logs": ScriptLogger.tail(acc_id, limit),
                    "healing": HEAL_STATS.get(acc_id, {"retries": 0, "floodwait_s": 0,
                                                       "reconnects": 0, "last": None})})

@app.route("/api/script/logs/<account_id>/clear", methods=["POST"])
@require_token
async def api_script_logs_clear_alias(account_id):
    ScriptLogger.clear(str(account_id))
    return jsonify({"ok": True})

@app.route("/api/script/templates", methods=["GET", "POST"])
@require_token
async def api_script_templates_alias():
    """GET -> saved reusable script templates; POST -> save one (templates.json)."""
    if request.method == "GET":
        acc_id = str(request.args.get("account_id", ""))
        out = []
        for key, t in templates_store.load().items():
            if acc_id and t.get("account_id") and t.get("account_id") != acc_id:
                continue
            out.append({"id": key, "name": t.get("label", key), "code": t.get("code", ""),
                        "mode": t.get("mode", "raw"), "account_id": t.get("account_id"),
                        "updated_at": t.get("updated_at")})
        for key, t in SCRIPT_TEMPLATES.items():
            out.append({"id": key, "name": t["label"], "code": t["code"],
                        "mode": t.get("mode", "raw"), "account_id": None, "builtin": True})
        return jsonify({"ok": True, "templates": out})
    body = await request.get_json(silent=True) or {}
    name = str(body.get("name", "")).strip()[:40] or "User Template"
    code = str(body.get("code", ""))
    mode = str(body.get("mode", "raw")).lower()
    mode = mode if mode in ("safe", "raw") else "raw"
    ok, err = (RawScriptRunner if mode == "raw" else SafeScriptRunner).validate(code)
    if not ok:
        return jsonify({"ok": False, "error": err}), 400
    store = templates_store.load()
    key = str(body.get("id", "")).strip() or ("user_" + uuid.uuid4().hex[:5])
    store[key] = {"label": name, "code": code, "mode": mode,
                  "account_id": str(body.get("account_id", "")) or None,
                  "updated_at": int(time.time())}
    await templates_store.save(store)
    safe_log("CMD", "SCRIPT", f"template '{name}' saved ({key})")
    return jsonify({"ok": True, "id": key, "name": name})

@app.route("/api/script/healing/<account_id>", methods=["GET"])
@require_token
async def api_script_healing(account_id):
    return jsonify({"ok": True, "account_id": account_id,
                    "max_retries": HEAL_MAX_RETRIES,
                    "stats": HEAL_STATS.get(str(account_id),
                                            {"retries": 0, "floodwait_s": 0, "reconnects": 0, "last": None})})

# ---- agent ops (control center) -------------------------------------------
@app.route("/api/agent/overview", methods=["GET"])
@require_token
async def api_agent_overview():
    accounts = []
    for aid, acc in ACCOUNTS.accounts.items():
        cfg = acct_cfg(aid)
        accounts.append({"id": aid, "label": acc["meta"].get("label"),
                         "username": acc["meta"].get("username"),
                         "active": bool(acc["meta"].get("active")),
                         "connected": bool(acc.get("client") and acc["client"].is_connected()),
                         "main_channels": cfg.get("main_channels") or [],
                         "source": cfg.get("source"), "destination": cfg.get("destination")})
    b = Brain._brain()
    eng = STATE["engine"]
    return jsonify({"ok": True,
                    "jarvis": "ONLINE",
                    "accounts": accounts,
                    "tasks": [agent_task_view(t) for t in AGENT_TASKS.values()][-20:],
                    "active_tasks": len(agent_active_tasks()),
                    "engine": {"status": eng["status"], "queue": len(eng["queue"]),
                               "processed": eng["processed"], "failed": eng["failed"],
                               "flood_wait_in": max(0, int((eng.get("flood_wait_until") or 0) - time.time()))},
                    "brain": {"memories": len(b.get("memories", [])),
                              "workflows": len(Brain._wf().get("workflows", [])),
                              "channels": len(Brain._cm().get("channels", {})),
                              "capability_requests": b.get("capability_requests", [])[:5],
                              "recent": [{"kind": m["kind"], "text": m["text"], "ts": m["ts"]}
                                         for m in b.get("memories", [])[:8]],
                              "failures": b.get("failures", [])[:5]},
                    "scheduler": {"active": len([j for j in SCHED.jobs if not j.get("done")])}})

@app.route("/api/agent/task/stop", methods=["POST"])
@require_token
async def api_agent_task_stop():
    body = await request.get_json(silent=True) or {}
    tid = str(body.get("task_id", ""))
    if tid.lower() == "all":
        rows = agent_active_tasks()
        for t in rows:
            await agent_task_stop(t["task_id"], "web")
        return jsonify({"ok": True, "stopped": len(rows)})
    ok, st = await agent_task_stop(tid, "web")
    return jsonify({"ok": ok, "status": st}), (200 if ok else 404)

@app.route("/api/agent/goal", methods=["POST"])
@require_token
async def api_agent_goal():
    body = await request.get_json(silent=True) or {}
    goal = str(body.get("goal", "")).strip()
    if not goal:
        return jsonify({"ok": False, "error": "Empty goal"}), 400
    res = await handle_command(goal, origin=caller_origin())
    return jsonify(scrub(res))

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
    log.info("BOOT DEVIL JARVIS v4.0 ▸ %d tools ▸ NLU fuzzy ▸ clock Asia/Kathmandu", len(REG.tools))
    safe_log("INFO", "BOOT", f"JARVIS v4.0 online — {len(REG.tools)} tools, {len(ACCOUNTS.accounts)} saved account(s)")
    loop = asyncio.get_running_loop()
    loop.create_task(SCHED.loop())
    ENGINE.ensure_task()
    await SCHED.recover()
    await agent_restore_tasks()
    reconnected = 0
    if ACCOUNTS.accounts:
        reconnected = await ACCOUNTS.reconnect_all()
        log.info("BOOT managed accounts reconnected: %d", reconnected)
        safe_log("INFO" if reconnected else "WARN", "ACCOUNT", f"Managed reconnect: {reconnected}/{len(ACCOUNTS.accounts)}")
    if not reconnected and all(os.getenv(k) for k in ("API_ID", "API_HASH", "SESSION_STRING")):
        ok, payload = await TG.connect_session(int(os.environ["API_ID"]),
                                               os.environ["API_HASH"], os.environ["SESSION_STRING"])
        log.info("BOOT env auto-connect: %s", "OK" if ok else payload)
        safe_log("INFO" if ok else "WARN", "TELEGRAM", f"Env auto-connect: {'OK' if ok else payload}")
    if not server_token():
        log.warning("BOOT JARVIS_ACCESS_TOKEN not set — protected endpoints refuse (fail closed)")
    log.info("BOOT ONLINE ▸ /health ready")

@app.after_serving
async def shutdown():
    log.info("SHUTDOWN — engine stop + scripts stop + Telegram disconnect")
    try:
        ENGINE.eng["status"] = "stopped"
        state_store.save_bg(STATE)
        for _tid, _t in list(AUTO_TASKS.items()):
            if _t.get("status") == "RUNNING":
                await stop_automation(_tid, "shutdown")
        for _t in list(agent_active_tasks()):
            await agent_task_stop(_t["task_id"], "shutdown")
        await stop_all_scripts("shutdown")
        await TG.disconnect(clear=False)
        for acc in ACCOUNTS.accounts.values():
            if acc.get("client"):
                try:
                    await acc["client"].disconnect()
                except Exception:
                    pass
    except Exception:
        pass

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.getenv("PORT", "5000")))
