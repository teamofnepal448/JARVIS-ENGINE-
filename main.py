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
templates_store = JSONStore(DATA / "script_templates.json", {})

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
            return {"ok": False, "lines": ["SOURCE NOT AVAILABLE ▸ Source Configuration panel me source set karo (ya ENV) — engine start nahi hui"]}
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

LEV_WORDS = ("channel", "channels", "cross", "folder", "folders", "monitor", "task", "status",
             "admin", "user", "message", "messages", "search", "start", "stop", "pause", "resume",
             "reset", "scheduler", "schedule", "dead", "inactive", "account", "saved", "recent",
             "diagnostics", "help", "latest", "config", "list", "update")

def fuzzy_norm(t):
    """BUG FIX 6: spelling-tolerant lexicon ('cros'->cross, 'chanel'->channel, 'usr'->user)."""
    out = []
    for tok in t.split(" "):
        if len(tok) < 3 or tok.startswith("@") or any(ch.isdigit() for ch in tok) or tok in LEV_WORDS:
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
        filters = await client(functions.messages.GetDialogFiltersRequest())
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
             "Natural language: English · Hindi · Hinglish · multi-step · fuzzy spelling", bar]
    for cat in ("TELEGRAM", "JARVIS", "SCHEDULER", "CROSS", "MONITOR", "TASK", "ADMIN"):
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

    plan = await build_plan(raw, origin)
    if not plan.steps:
        lines = ["I couldn't map this request to an available Telegram/JARVIS action.",
                 "Ye instruction registry ke kisi tool se match nahi hua.", "Available actions: /AI HELP"]
        for u in plan.unsupported:
            lines.append(f"[UNSUPPORTED] {u}")
        _record(raw, "UNMAPPED", {"ok": False, "lines": lines}, origin, plan.provider)
        return {"ok": False, "action": "UNMAPPED", "provider": plan.provider, "lines": lines}

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

        def log(msg):
            ScriptLogger.put(acc_id, "INFO", msg)

        async def sleep(secs):
            await asyncio.sleep(float(secs))

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
            "log": log,
            "print": lambda *a: ScriptLogger.put(acc_id, "INFO", " ".join(str(x) for x in a)[:400]),
            "sleep": sleep,
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
        res = await runner.run(code, ACCOUNTS.accounts.get(acc_id, {}), acc_id, progress)
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
