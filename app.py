# app.py — LINE Bungfai Bot (Flask + line-bot-sdk) — STABLE NO-DUPLICATE SEND
# (c) SITTIPONG — hardened, anti-abuse, anti-kick, 1-bill-per-round, @mention admin/mod, uid lookup

from dotenv import load_dotenv
load_dotenv()


from waitress import serve

import os, re, time, base64, json, tempfile, uuid
import requests
from datetime import datetime
from hmac import new as hmac_new, compare_digest
from hashlib import sha256
from html import escape as html_escape
from math import ceil, floor
from collections import deque
from functools import lru_cache
import threading


from contextlib import contextmanager

# ==== REGEX (precompiled) ====
R_PARSE_BET = re.compile(r"^([ลสยต])\s*[\/\s]*([0-9]+)$", re.IGNORECASE)
R_O         = re.compile(r"^\s*o\b", re.IGNORECASE)
R_ANN = re.compile(
    r"^\s*([^\s].+?)\s*ล\s*(\d+)\s*[-/]\s*(\d+)\s*ย\s*(\d+)\s*[-/]\s*(\d+)\s*$",
    re.IGNORECASE
)
R_O_ANN = re.compile(
    r"^\s*o\s+(.+?)\s*ล\s*(\d+)\s*[-/]\s*(\d+)\s*ย\s*(\d+)\s*[-/]\s*(\d+)\s*$",
    re.IGNORECASE
)
R_CLEAR     = re.compile(r"^(clear|reset)\b", re.IGNORECASE)
R_CM        = re.compile(r"^cm$", re.IGNORECASE)
R_CALL      = re.compile(r"^call$", re.IGNORECASE)
R_UID       = re.compile(r"^uid\b", re.IGNORECASE)
R_SET_RESULT= re.compile(r"^[sS]\s*(.+)$")
R_MUTING    = re.compile(r"^(ban|unban|mute|unmute)\b(?:\s+(.*))?$", re.IGNORECASE)
R_CANCEL_BY_CID = re.compile(r"^x\s+(\d+)$", re.IGNORECASE)
R_ADMIN_ADD = re.compile(r"^\s*(?:admin(?:\s+add)?|เพิ่มแอดมิน)(?:\s+|(?=@)|$)", re.IGNORECASE)
R_ADMIN_DEL   = re.compile(r"^\s*(?:admin\s+del|ลบแอดมิน)\b", re.IGNORECASE)
R_CLOSE_TH    = re.compile(r"^(ปิดรอบ|หยุดแทง|ปิด)$")
R_YCONFIRM    = re.compile(r"^(?:T/|/Y|Y)\s*$", re.IGNORECASE)
R_CLEAR_PROFIT = re.compile(r"^ล้างกำไร$", re.IGNORECASE)
R_GETID = re.compile(r"^getid\b", re.IGNORECASE)
R_DEL_USER = re.compile(r"^del\s+(\d+)$", re.IGNORECASE)



# ====== GLOBAL LOCKS ======
_users_lock = threading.RLock()
_rooms_lock = threading.RLock()

# ====== WEBHOOK IDEMPOTENCY / กัน LINE retry ประมวลผลซ้ำ ======
# ถ้า LINE ส่ง event เดิมซ้ำเพราะ webhook ช้า/เน็ตแกว่ง จะไม่ตัดเครดิต/รับบิลซ้ำ
_processed_event_lock = threading.RLock()
_processed_event_ids = {}  # event_id/message_id -> timestamp
PROCESSED_EVENT_TTL_SEC = int(os.getenv("PROCESSED_EVENT_TTL_SEC", "900"))

def _event_unique_id(event):
    try:
        msg = getattr(event, "message", None)
        mid = getattr(msg, "id", None)
        if mid:
            return f"msg:{mid}"
    except Exception:
        pass
    try:
        wid = getattr(event, "webhook_event_id", None)
        if wid:
            return f"webhook:{wid}"
    except Exception:
        pass
    return None

def _is_duplicate_event(event) -> bool:
    eid = _event_unique_id(event)
    if not eid:
        return False
    now = int(time.time())
    with _processed_event_lock:
        # cleanup แบบเบา ๆ เฉพาะตอน dict เริ่มใหญ่ เพื่อไม่เปลือง CPU
        if len(_processed_event_ids) > 5000:
            cutoff = now - PROCESSED_EVENT_TTL_SEC
            for k, ts in list(_processed_event_ids.items()):
                if ts < cutoff:
                    _processed_event_ids.pop(k, None)
        if eid in _processed_event_ids:
            return True
        _processed_event_ids[eid] = now
        return False


def has_active_bet(uid):
    for stx in rooms.values():
        if uid in stx.get("bet_index", {}):
            return True
    return False


@contextmanager
def with_users_lock():
    _users_lock.acquire()
    try:
        yield
    finally:
        _users_lock.release()

@contextmanager
def with_rooms_lock():
    _rooms_lock.acquire()
    try:
        yield
    finally:
        _rooms_lock.release()


from flask import Flask, request, make_response
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError
from linebot.models import (
    MessageEvent, TextMessage, TextSendMessage,
    FlexSendMessage, UnsendEvent,
    MemberJoinedEvent, MemberLeftEvent,
    ImageMessage,   # <<< เพิ่มบรรทัดนี้
)


# ====== CONFIG (ปรับได้) ======
DEPOSIT_URL = os.getenv("DEPOSIT_URL", "https://page.line.me/957gvogc")
PROFIT_RATE = float(os.getenv("PROFIT_RATE", "0.95"))   # กำไรสุทธิของฝั่งชนะ (1:0.90) 5
MIDDLE_FEE  = float(os.getenv("MIDDLE_FEE",  "0.03"))   # หักเมื่อคืนเงิน (กลาง/เสมอแบบหัก)
MIN_BET = int(os.getenv("MIN_BET", "30"))
MAX_BET = int(os.getenv("MAX_BET", "10000"))
USER_SIDE_CAP = {"HI": 10000, "LO": 10000}
SIDE_CAP      = {"HI": 50000, "LO": 30000}
ROUND_CAP     = 80000

# ====== SIMPLE PER-USER COOLDOWN (anti-spam reply gap) ======
REPLY_COOLDOWN_SEC = int(os.getenv("REPLY_COOLDOWN_SEC", "6"))
_LAST_REPLIED_AT = {}        # scope_key -> epoch seconds
_COOLDOWN_LOCK = threading.Lock()  # <<< เพิ่มตัวล็อก

def _should_reply_now(scope_key: str) -> bool:
    """
    ป้องกันตอบถี่เกินไปแบบอะตอมิก: เช็ค + อัปเดต ภายใต้ล็อกเดียวกัน
    scope_key = คีย์สำหรับคูลดาวน์ (เช่น uid:room)
    """
    if REPLY_COOLDOWN_SEC <= 0:
        return True
    now = _now()
    with _COOLDOWN_LOCK:  # <<< ล็อกกันชนกันข้ามเธรด
        last = _LAST_REPLIED_AT.get(scope_key, 0)
        if (now - last) < REPLY_COOLDOWN_SEC:
            return False
        _LAST_REPLIED_AT[scope_key] = now
        return True



# ====== PERSISTENCE (users + nextCustomerId) ======
DATA_DIR = os.getenv("DATA_DIR", "./data")
os.makedirs(DATA_DIR, exist_ok=True)
# ====== LAST SETTLE (free backoffice) ======
LAST_SETTLE_JSON = os.path.join(DATA_DIR, "last_settle_global.json")

def save_last_settle(payload: dict):
    """เก็บสรุปล่าสุดไว้ให้หลังบ้านเรียกดูได้ โดยไม่ต้อง push (ประหยัดโควต้า)"""
    try:
        _atomic_write_json(LAST_SETTLE_JSON, payload)
    except Exception:
        app.logger.exception("save_last_settle failed")

def load_last_settle():
    try:
        if not os.path.exists(LAST_SETTLE_JSON):
            return None
        with open(LAST_SETTLE_JSON, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        app.logger.exception("load_last_settle failed")
        return None

def settle_payload_to_text(p: dict) -> str:
    """แปลง payload เป็นข้อความสั้น ๆ (Text)
    หมายเหตุ: แสดง 'ได้เสีย' = payout - stake (มุมมองลูกค้า)
             และ 'กำไรรอบนี้' = มุมมองเจ้ามือ (profit = stake - payout)
    """
    try:
        def _fmt(n):
            try:
                # รองรับ int/float/str
                if n is None:
                    n = 0
                n = float(n)
                if n.is_integer():
                    return f"{int(n):,}"
                return f"{n:,.2f}"
            except Exception:
                return str(n)

        def _signed(n):
            try:
                n = float(n or 0)
            except Exception:
                n = 0
            return f"+{_fmt(n)}" if n >= 0 else f"-{_fmt(abs(n))}"

        round_no = p.get("round")
        camp = p.get("camp_name") or "-"
        code = p.get("code") or "-"
        profit = p.get("profit", 0)  # มุมมองเจ้ามือ
        accum = p.get("accum") or {}
        net = accum.get("net", 0)
        ts = p.get("ts_iso") or ""

        rows = p.get("rows") or []
        lines = []
        for r in rows[:12]:  # กันยาวเกิน
            name = r.get("name") or r.get("uid") or "-"
            stake = r.get("stake", 0) or 0
            payout = r.get("payout", 0) or 0
            pl = payout - stake  # มุมมองลูกค้า (ได้เสีย)
            # ถ้ามี bet ก็แสดงแบบสั้น ๆ
            bet = (r.get("bet") or "").strip()
            bet_txt = f" [{bet}]" if bet else ""
            lines.append(f"- {name}{bet_txt} {_signed(pl)}")
        if len(rows) > 12:
            lines.append(f"...และอีก {len(rows)-12} ราย")

        return (
            f"📌 สรุปผลรอบ {round_no} | ค่าย: {camp} | ผล: {code}\n"
            f"ลูกค้า: {len(rows)} คน\n"
            f"💰 กำไรรอบนี้ (เจ้ามือ): {_signed(profit)}\n"
            f"🧮 กำไรสุทธิสะสม: {_signed(net)}\n"
            f"🕒 เวลา: {ts}\n\n"
            + ("\n".join(lines) if lines else "")
        ).strip()
    except Exception:
        app.logger.exception("settle_payload_to_text failed")
        return "📌 สรุปผลล่าสุด (แปลงข้อความไม่สำเร็จ)"


USERS_JSON = os.path.join(DATA_DIR, "users.json")
_user_store_lock = threading.Lock()


# --- JSON encoder/decoder with orjson fallback ---
try:
    import orjson as _orjson
    def _dumps_bytes(obj) -> bytes:
        return _orjson.dumps(obj)               # ได้ bytes เลย
    def _loads_bytes(buf: bytes):
        return _orjson.loads(buf)
except Exception:
    import json as _json
    def _dumps_bytes(obj) -> bytes:
        # ให้ได้ bytes เหมือน orjson
        return _json.dumps(
            obj,
            ensure_ascii=False,
            separators=(",", ":")
        ).encode("utf-8")
    def _loads_bytes(buf: bytes):
        return _json.loads(buf.decode("utf-8"))

def _atomic_write_json(path: str, data: dict):
    dirname = os.path.dirname(path) or "."
    fd, tmp = tempfile.mkstemp(prefix=".tmp_", dir=dirname)
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(_dumps_bytes(data))
        os.replace(tmp, path)  # atomic replace
    except Exception:
        try:
            os.remove(tmp)
        except Exception:
            pass
        raise





def save_users_persist():
    # ไม่เขียนทันที — แค่จุด event ให้ worker ไปเขียนเป็นก้อน
    _save_event.set()



def load_users_persist():
    global nextCustomerId, users
    try:
        if not os.path.exists(USERS_JSON): return
        with _user_store_lock:
            with open(USERS_JSON, "rb") as f:
                data = _loads_bytes(f.read())


        disk_users = data.get("users", {})
        disk_next = int(data.get("nextCustomerId", 0) or 0)
        with with_users_lock():
            if isinstance(disk_users, dict):
                users.clear()
                for k, v in disk_users.items():
                    users[k] = {
                        "uid": v.get("uid", k),
                        "cid": int(v.get("cid", 0) or 0),
                        "name": v.get("name", "ผู้เล่น"),
                        "pictureUrl": v.get("pictureUrl"),
                        "credit": int(v.get("credit", 0) or 0),
                    }
            if disk_next > 0:
                nextCustomerId = disk_next
    except Exception:
        try:
            app.logger.exception("load_users_persist failed")
        except Exception:
            pass





# ====== LINE BOOTSTRAP ======
CHANNEL_ACCESS_TOKEN = os.getenv("LINE_CHANNEL_ACCESS_TOKEN", "REPLACE_ME")
CHANNEL_SECRET = os.getenv("LINE_CHANNEL_SECRET", "REPLACE_ME")

ADMIN_IDS = [s.strip() for s in os.getenv(
    "ADMIN_IDS", "U1e072b43acc7aee214780cdd8e063585,U065104dbbe4cecf17386e1411487d222,Ufc67671b43ff1ef6c7dfdb394dd44168,U7248ad458d99d9dfa07b8d8cd544eb86,Ud6affc193442d633c3c19ef553e706a6,Ud63195ad71df53fff155da5ffb982b48,Uad6aacb08a82161f86856985b17e4724"
).split(",") if s.strip()]

BACKOFFICE_GROUP_IDS = {  # กลุ่มหลังบ้าน (รับสรุปพร้อมกำไรสุทธิ)
    "Ce8bea8832b97854a16c434f3c8e16302",
}

BASE_URL = os.getenv("BASE_URL", "https://example.ngrok-free.app")

BANK = {
    "brand": os.getenv("BANK_BRAND", "กรุงเทพ"),
    "accountNo": os.getenv("BANK_ACCOUNT", "977-4-550132"),
    "owner": os.getenv("BANK_OWNER", "ฐิมาพร กากแก้ว"),
}
PORT = int(os.getenv("PORT", "5000"))

# ====== LINE API TIMEOUT / RETRY — STABLE MODE ======
# แก้ปัญหา HTTPSConnectionPool(host='api.line.me') Read timed out (read timeout=5)
# โหมดนิ่ง: ไม่ fallback push หลัง reply timeout เป็นค่าเริ่มต้น เพื่อกันข้อความซ้ำ
# LINE docs เตือนว่า timeout อาจส่งข้อความสำเร็จแล้ว แต่ response กลับมาช้า
LINE_CONNECT_TIMEOUT = float(os.getenv("LINE_CONNECT_TIMEOUT", "5"))
LINE_READ_TIMEOUT    = float(os.getenv("LINE_READ_TIMEOUT", "20"))
LINE_API_TIMEOUT     = (LINE_CONNECT_TIMEOUT, LINE_READ_TIMEOUT)

# retry เฉพาะ push เท่านั้น และใช้ X-Line-Retry-Key กันส่งซ้ำ
LINE_SEND_RETRY      = int(os.getenv("LINE_SEND_RETRY", "2"))
LINE_RETRY_SLEEP     = float(os.getenv("LINE_RETRY_SLEEP", "1.5"))
LINE_PUSH_USE_RETRY_KEY = os.getenv("LINE_PUSH_USE_RETRY_KEY", "1").strip().lower() in ("1", "true", "yes", "y", "on")

# 0 = นิ่งสุด/กันข้อความซ้ำ: reply timeout แล้ว log เท่านั้น
# 1 = ถ้า reply timeout ให้ push ตามไปยังห้องเดิม (มีโอกาสข้อความซ้ำ ไม่แนะนำสำหรับบอทแทง/ธุรกรรม)
LINE_REPLY_FALLBACK_PUSH = os.getenv("LINE_REPLY_FALLBACK_PUSH", "0").strip().lower() in ("1", "true", "yes", "y", "on")

# จำกัดจำนวนงานส่งข้อความพร้อมกัน กันเธรดบานเวลาฝั่ง LINE/อินเทอร์เน็ตมีปัญหา
LINE_SEND_MAX_WORKERS = int(os.getenv("LINE_SEND_MAX_WORKERS", "8"))
_LINE_SEND_SEMAPHORE = threading.BoundedSemaphore(max(1, LINE_SEND_MAX_WORKERS))

line_bot_api = LineBotApi(CHANNEL_ACCESS_TOKEN, timeout=LINE_API_TIMEOUT)
handler = WebhookHandler(CHANNEL_SECRET)
app = Flask(__name__)

# ====== STATE ======
rooms = {}   # room_key -> state
users = {}   # uid -> {uid,cid,name,pictureUrl,credit}
nextCustomerId = 201


PLAY_HELP_TEXT = (
"กติกาการเล่น\n"
"ต/1000 = แทงต่ำ 1000 บาท\n"
"ย/1000 = แทงต่ำ 1000 บาท\n"
"ล/1000 = แทงสูง 1000 บาท\n"
"ส/1000 = แทงสูง 1000 บาท\n"
"สามารถใส่เครื่องหมาย /\n"
"หรือไม่ใส่ก็ได้ \n\n"
"✅ยอดเล่นได้หัก 5%\n"
"⛔ออกกลาง หัก 3%\n"
"⛔บั้งไฟหาย = ไม่หัก\n\n"

"___________________\n\n"

"👉 รับสูงสุดยั้ง 30,000 ต่อ 1 บั้ง\n"
"👉 รับสูงสุดไล่ 50,000 ต่อ 1 บั้ง\n"
"👉 แทงขั้นต่ำ ยั้ง 30-10,000 ต่อ \n"
"1คน\n"
"🫱🏻 แทงขั้นต่ำ ไล่ 30-10,000 ต่อ 1คน\n\n"
"📢 เพิ่ม ID ตัวเอง พิมพ์ ADD\n"
"📢 ดูยอดบัญชีตัวเอง กด C\n"
"📢 ยกเลิกการแทง กด X\n\n\n"
"***ห้ามเว้นวรรค ***\n"
"🙏พิมพ์ยอดการเล่นให้ถูกต้องด้วยนะครับ🙏\n"
"ตัวอย่าง:\n"
"ล/1000 ส/1000 ล1000 ส1000=ไล่\n"
"ย/1000 ต/1000 ย1000 ต1000=ยั้ง\n"
"(ไม่ต้องเว้นวรรค)\n\n"
"หมายเหตุ // 💥กรณีออกราคา บั้งไฟ หลังปิด ถือว่า จาวทุกรณี\n"
"และสนามราคารูด ทางกลุ่มจะไม่เปิดราคา จาวทุกกรณี 💥"
)

PLAY_HELP_COMMANDS = {
    "วิธีเล่น",
    "เล่นยังไง",
    "เล่นไง",
    "วิธีการเล่น",
    "เล่นแบบใด",
}

# ===== Debounced Saver =====
_save_event = threading.Event()

def _save_users_snapshot():
    with with_users_lock():
        payload = {"nextCustomerId": nextCustomerId, "users": users}
    _atomic_write_json(USERS_JSON, payload)

def _persist_worker():
    while True:
        _save_event.wait()
        time.sleep(0.35)  # รวมคำสั่งภายใน 350ms ก่อนเขียน
        _save_users_snapshot()
        _save_event.clear()

threading.Thread(target=_persist_worker, daemon=True).start()


# โหลดข้อมูลลูกค้า+เครดิตจากดิสก์ (ถ้ามี)
load_users_persist()

# ====== ACCUMULATED METRICS (backoffice) ======
METRICS = {"profit_sum": 0, "loss_sum": 0}
def net_profit(): return METRICS["profit_sum"] - METRICS["loss_sum"]

def fmt(n: int) -> str: return f"{n:,}"

msgCache = {}
CACHE_TTL_SEC = 900

# --- Rounding policy helpers ---
def _round_refund(x: float) -> int:
    # เลือกได้: floor = ปัดลง, ceil = ปัดขึ้น
    return floor(x)

def _round_profit(x: float) -> int:
    # กำไรก็ใช้ policy เดียวกันเพื่อความคงเส้นคงวา
    return floor(x)


# ====== RESULT DEFINITIONS ======
RESULT_DEFS = {
    # ปกติ: ฝั่งชนะจ่ายกำไรสุทธิ PROFIT_RATE, ฝั่งแพ้เสียเต็ม (แต่เรา “ตัดตอนวางบิลแล้ว” จึงไม่ต้องหักเพิ่มตอนสรุป)
    "ส":  {"label": "สูงชนะ (จ่าย 1 : %.2f)" % PROFIT_RATE, "winner": "HI"},
    "ต":  {"label": "ต่ำชนะ (จ่าย 1 : %.2f)" % PROFIT_RATE, "winner": "LO"},

    # กลาง/จาว/เสมอ-หาย
    "ก":  {"label": "กลาง (หัก %.0f%%)" % (MIDDLE_FEE*100), "special": "MIDDLE_FEE"},
    "จ":  {"label": "จาว (คืนเต็ม ไม่หัก)", "special": "DRAW_0"},
    "ม":  {"label": "เสมอ-หาย (คืนเต็ม ไม่หัก)", "special": "DRAW_0"},

    # เคสนโยบายพิเศษ
    "ตจ": {"label": "ต่ำเสมอ (หัก %.0f%%) / สูงเสียเต็ม" % (MIDDLE_FEE*100), "special": "LOW_DRAWFEE_HIGH_LOSE"},
    "ตส": {"label": "ต่ำเสียเต็ม / สูงเสมอ (หัก %.0f%%)" % (MIDDLE_FEE*100), "special": "LOW_LOSE_HIGH_DRAWFEE"},
}

def normalize_result_code(code: str) -> str:
    code = (code or "").strip()
    if code.startswith(("S", "s")) and len(code) >= 2:
        return code[1:].strip()
    return code

# ====== HELPERS ======
def room_key(src):
    return getattr(src, "group_id", None) or getattr(src, "room_id", None) or getattr(src, "user_id", None)

def in_group_or_room(src) -> bool:
    return bool(
        getattr(src, "group_id", None)
        or getattr(src, "room_id", None)
        or getattr(src, "user_id", None)
    )


def is_backoffice_group_id(gid): return gid in BACKOFFICE_GROUP_IDS

def start_state():
    return {
        "phase": "NONE",  # NONE | OPEN | PAUSED
        "pairNo": 0,
        "note": None,
        "pendingCode": None,
        "totals": {"HI": 0, "LO": 0},
        "bet_index": {},  # uid -> {uid,name,side,amount}
        "funds": {},      # uid -> ทุนรอบนี้
        "price": {"camp": None, "HI": (None, None), "LO": (None, None)},
        "escrow": {},     # เงินที่ถูกหักออกไปทันทีเมื่อรับบิล uid -> amount
    }

# แก้ไขในฟังก์ชัน start_state()
def start_state():
    return {
        "phase": "NONE",  # NONE | OPEN | PAUSED
        "pairNo": 0,
        "note": None,
        "pendingCode": None,
        "totals": {"HI": 0, "LO": 0},
        "bet_index": {},  
        "funds": {},      
        "price": {"camp": None, "HI": (None, None), "LO": (None, None)},
        "escrow": {},     
        "score_history": [],  # <--- [เพิ่มบรรทัดนี้] เก็บประวัติผลสกอ บั้งไฟวันนี้
    }

def get_profile_display(src, user_id):
    try:
        if getattr(src, "group_id", None):
            p = line_bot_api.get_group_member_profile(src.group_id, user_id)
        elif getattr(src, "room_id", None):
            p = line_bot_api.get_room_member_profile(src.room_id, user_id)
        else:
            p = line_bot_api.get_profile(user_id)
        return (p.display_name, p.picture_url)
    except Exception:
        return ("ผู้เล่น", None)

def parse_bet(text):
    m = R_PARSE_BET.match(text)
    if not m: return None
    ch = m.group(1).lower()
    amount = int(m.group(2))
    side = "HI" if ch in ("ล", "ส") else "LO"
    return {"side": side, "amount": amount}


def get_user_bet(state, uid): return state["bet_index"].get(uid)
def user_stake_this_round(state, uid): return get_user_bet(state, uid)["amount"] if get_user_bet(state, uid) else 0

def user_fund_remain(state, uid):
    u = users.get(uid)
    if not u: return 0
    return max(u.get("credit", 0), 0)

# ==== 1 บิล/รอบ + กันแทงสวน ====
def can_bet(state, uid, side, amount):
    if state["phase"] != "OPEN":
        return (False, "ยังไม่เปิดรอบ")

    existing = get_user_bet(state, uid)
    if existing:
        exist_side_th = "สูง" if existing["side"] == "HI" else "ต่ำ"
        if side != existing["side"]:
            return (False, f"❌ ห้ามแทงสวน — คุณมีบิลเดิม: {exist_side_th} {fmt(existing['amount'])}  (พิมพ์ X เพื่อยกเลิกก่อน)")
        else:
            return (False, f"❌ จำกัด 1 บิล/รอบ — คุณมีบิล {exist_side_th} {fmt(existing['amount'])} อยู่แล้ว  (พิมพ์ X เพื่อยกเลิกก่อน)")

    if amount < MIN_BET:
        return (False, f"ขั้นต่ำ {MIN_BET}")
    if amount > MAX_BET:
        return (False, f"สูงสุด {MAX_BET}")

    remain = user_fund_remain(state, uid)
    if remain < amount:
        return (False, f"ทุนคงเหลือไม่พอ (มี {fmt(remain)})")

    if amount > USER_SIDE_CAP[side]:
        side_th = "สูง" if side == "HI" else "ต่ำ"
        return (False, f"ฝั่ง{side_th} ต่อคนเกิน {fmt(USER_SIDE_CAP[side])}")

    # ✅ เช็คเพดานต่อฝั่ง (ย้ายออกมาให้อยู่นอก if ด้านบน)
    if state["totals"][side] + amount > SIDE_CAP[side]:
        side_th = "สูง" if side == "HI" else "ต่ำ"
        side_cap = SIDE_CAP[side]
        side_total = state["totals"][side]
        remain_to_cap = max(side_cap - side_total, 0)
        return (
            False,
            f"❌รับบิลไม่ได้❌: ฝั่ง{side_th} เต็ม {fmt(side_cap)} - เหลือรับได้อีก {fmt(remain_to_cap)}"
        )

    # ✅ เช็คเพดานรวมรอบ + แจ้งคงเหลือ
    round_total = state["totals"]["HI"] + state["totals"]["LO"]
    if round_total + amount > ROUND_CAP:
        remain_round = max(ROUND_CAP - round_total, 0)
        return (False, f"❌รับบิลไม่ได้❌: รอบนี้เต็ม {fmt(ROUND_CAP)} - เหลือรับได้อีก {fmt(remain_round)}")

    return (True, "")

# ==== mention helpers ====
def first_mentioned_uid(event):
    try:
        m = getattr(event.message, "mention", None)
        if not m: return None
        for me in (getattr(m, "mentionees", None) or []):
            uid = getattr(me, "user_id", None) or getattr(me, "userId", None)
            if uid and str(uid).lower() != "all":
                return uid
    except Exception:
        pass
    return None

def format_user_table(data):
    if not data:
        return "ไม่มีข้อมูล"

    import re

    def clean_name(name):
        return re.sub(r'[^\w\sก-๙]', '', name or "")

    ID_W = 4
    NAME_W = 16
    CREDIT_W = 8

    header = f"{'ID':<{ID_W}} | {'ชื่อ':<{NAME_W}} | {'เครดิต':>{CREDIT_W}}"
    sep = "-" * len(header)

    lines = []
    lines.append("📋 รายชื่อสมาชิก")
    lines.append(sep)
    lines.append(header)
    lines.append(sep)

    total_credit = 0

    for u in data:
        cid = str(u.get("cid", ""))
        name = clean_name(u.get("name", ""))[:NAME_W]
        credit = u.get("credit", 0)

        total_credit += credit

        line = f"{cid:<{ID_W}} | {name:<{NAME_W}} | {credit:>{CREDIT_W},}"
        lines.append(line)

    lines.append(sep)

    # ===== รวมเครดิต =====
    lines.append(f"💰 รวมเครดิตทั้งหมด: {total_credit:,} บาท")

    return "\n".join(lines)


# ====== FLEX ======
def flex_open(pair_no, note=None):
    body_contents = [
        {"type": "text", "text": "🎯 เริ่มแทงได้ 🎯", "weight": "bold", "size": "xxl", "align": "center", "color": "#22C55E"},
        {"type": "text", "text": "บอทไม่จับ ไม่ได้เสีย ทุกกรณี •", "size": "md", "align": "center", "color": "#EF4444"},
        {"type": "separator", "margin": "lg", "color": "#4B5563"},
        {"type": "text", "text": f"รอบที่ {pair_no}", "align": "center", "size": "lg", "weight": "bold", "color": "#FFFFFF"},
        {"type": "text", "text": f"รอแอดมินออกราคาสักครู่", "align": "center", "size": "lg", "weight": "bold", "color": "#DB0A0A"},
    ]
    if note:
        body_contents += [
            {"type": "separator", "margin": "lg", "color": "#4B5563"},
            {"type": "text", "text": f"ชื่อค่าย: {note}", "size": "md", "wrap": True, "align": "center", "color": "#FACC15"},
        ]

    return FlexSendMessage(
        alt_text=f"เริ่มแทงได้ รอบที่ {pair_no}",
        contents={
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "0px",
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#22C55E",
                        "cornerRadius": "20px",
                        "paddingAll": "3px",
                        "contents": [
                            {
                                "type": "box",
                                "layout": "vertical",
                                "backgroundColor": "#111827",
                                "cornerRadius": "16px",
                                "paddingAll": "3px",
                                "contents": [
                                    {
                                        "type": "box",
                                        "layout": "vertical",
                                        "backgroundColor": "#1F2937",
                                        "cornerRadius": "12px",
                                        "paddingAll": "20px",
                                        "contents": body_contents
                                    }
                                ]
                            }
                        ]
                    }
                ]
            }
        }
    )



def flex_resume(pair_no: int, camp: str):
    return FlexSendMessage(
        alt_text=f"กลับมาเปิดรอบ {pair_no}",
        contents={
            "type": "bubble",
            "styles": {"body": {"backgroundColor": "#0B1220"}},
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "14px",
                "spacing": "12px",
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#16A34A",
                        "cornerRadius": "12px",
                        "paddingAll": "12px",
                        "contents": [
                            {
                                "type": "text",
                                "text": "เปิดให้เล่นอีกรอบ!!",
                                "weight": "bold",
                                "size": "lg",
                                "align": "center",
                                "color": "#FFFFFF"
                            },
                            {
                                "type": "text",
                                "text": f"รอบที่ {pair_no}",
                                "size": "sm",
                                "align": "center",
                                "color": "#E5E7EB"
                            }
                        ]
                    },
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#111827",
                        "cornerRadius": "12px",
                        "paddingAll": "12px",
                        "spacing": "8px",
                        "contents": [
                            {
                                "type": "text",
                                "text": f"ค่าย: {camp}",
                                "size": "md",
                                "weight": "bold",
                                "color": "#FACC15",
                                "wrap": True
                            },
                            {"type": "separator", "color": "#334155"},
                            {
                                "type": "text",
                                "text": "ฮ่ำมันเข้าไปคักๆ หมานๆนะสมาชิก",
                                "size": "sm",
                                "color": "#CBD5E1",
                                "wrap": True
                            },
                            {
                                "type": "text",
                                "text": "ยกเลิกบิลพิมพ์ X • ดูบัตรสมาชิกพิมพ์ C",
                                "size": "xs",
                                "color": "#94A3B8",
                                "wrap": True
                            }
                        ]
                    }
                ]
            }
        }
    )


def flex_open_with_prices(pair_no, camp, hi_min, hi_max, lo_min, lo_max):
    hi_txt = f"{hi_min}-{hi_max}" if hi_min is not None and hi_max is not None else "-"
    lo_txt = f"{lo_min}-{lo_max}" if lo_min is not None and lo_max is not None else "-"

    return FlexSendMessage(
        alt_text=f"เริ่มแทงได้ รอบที่ {pair_no}",
        contents={
            "type": "bubble",
            "styles": {"body": {"backgroundColor": "#D1FAE5"}},
            "body": {
                "type": "box",
                "layout": "vertical",
                "spacing": "sm",
                "paddingAll": "14px",
                "contents": [
                    {"type": "text", "text": "🎯 ราคามาแล้วว!! 🎯", "weight": "bold", "size": "xl", "align": "center", "color": "#16A34A"},
                    {"type": "text", "text": "บอทไม่จับ ไม่ได้เสีย ทุกกรณี", "size": "sm", "align": "center", "color": "#EF4444"},
                    {"type": "separator", "margin": "md"},
                    {"type": "text", "text": f"🟢🚀ชื่อค่าย :  {camp}", "size": "md", "weight": "bold", "wrap": True},
                    {"type": "text", "text": f"🟢ไล่ราคานี้🟢{hi_txt}🟢", "size": "lg", "weight": "bold"},
                    {"type": "separator", "margin": "md"},
                    {"type": "text", "text": "🏡 ราคาบั้งไฟแอดมินกำหนดตามความเหมาะสม", "size": "sm", "wrap": True},
                    {"type": "text", "text": "🏡 ออกราคาบั้งไฟหลังปิด ถือว่าจาวทุกกรณี", "size": "sm", "wrap": True},
                    {"type": "text", "text": f"👉 แทงขั้นต่ำ {MIN_BET} - {fmt(MAX_BET)} บาท/คน/รอบ", "size": "sm"},
                    {"type": "text", "text": f"👉 รวมต่อฝั่ง/รอบ: สูง {fmt(SIDE_CAP['HI'])} • ต่ำ {fmt(SIDE_CAP['LO'])}", "size": "sm"},
                    {"type": "text", "text": f"👉 อัตราจ่ายชนะ 1 : {PROFIT_RATE:.2f}", "size": "sm"},
                    {"type": "text", "text": f"👉 ออกกลางหัก {int(MIDDLE_FEE*100)}%", "size": "sm"},
                    {"type": "text", "text": "👉 ซุแตกคาถาน,หาย = จาว", "size": "sm"},
                    {"type": "separator", "margin": "md"},
                    {"type": "text", "text": f"🟢🚀ชื่อค่าย :  {camp}", "size": "md", "weight": "bold", "wrap": True},
                    {"type": "text", "text": f"🔴ยั้งราคานี้🔴{lo_txt}🔴", "size": "lg", "weight": "bold"},
                    {"type": "separator", "margin": "md"},
                    {"type": "text", "text": "📢 ยกเลิกการแทง กด X", "size": "sm"},
                    {"type": "text", "text": "📢 ดูยอดหน้าบัญชีตัวเอง กด C", "size": "sm"},
                    {"type": "text", "text": "‼️กรณีหน้าฐานราคารูดผิดปกติแอดมินสามารถแจ้งยกเลิกได้‼", "size": "xs", "wrap": True},
                ]
            }
        }
    )

def flex_close_notice(pair_no):
    # การ์ดแจ้งหยุดแทง (ปิดรอบ) โทนเดียวกับตัวอย่าง
    return FlexSendMessage(
        alt_text=f"ปิดรอบ #{pair_no}",
        contents={
            "type": "bubble",
            "styles": {"body": {"backgroundColor": "#E5F0FF"}},
            "body": {
                "type": "box",
                "layout": "vertical",
                "spacing": "md",
                "paddingAll": "16px",
                "contents": [
                    {"type": "text", "text": f"ปิดรอบ #{pair_no}", "weight": "bold",
                     "size": "xl", "align": "center", "color": "#1F2937"},
                    {"type": "box", "layout": "vertical", "backgroundColor": "#111827",
                     "cornerRadius": "12px", "paddingAll": "14px", "contents": [
                         {"type": "text", "text": "หยุดแทง", "weight": "bold",
                          "size": "xxl", "align": "center", "color": "#EF4444"},
                         {"type": "text", "text": "บอทไม่จับ ไม่ได้เสีย ทุกกรณี",
                          "size": "md", "align": "center", "color": "#FDE68A"}
                     ]},
                    {"type": "text",
                     "text": "ระบบปิดรับบิลแล้ว กรุณารอสรุปผล/ประกาศราคาถัดไป",
                     "size": "sm", "align": "center", "wrap": True, "color": "#374151"}
                ]
            }
        }
    )

def flex_pause_notice(pair_no: int, camp: str):
    """การ์ดแจ้ง 'พักรอบชั่วคราว' พร้อมชื่อค่าย"""
    if not camp:
        camp = "ไม่ระบุค่าย"
    return FlexSendMessage(
        alt_text=f"พักรอบชั่วคราว #{pair_no}",
        contents={
            "type": "bubble",
            "styles": {"body": {"backgroundColor": "#FFF7ED"}},
            "body": {
                "type": "box",
                "layout": "vertical",
                "spacing": "md",
                "paddingAll": "16px",
                "contents": [
                    {
                        "type": "text",
                        "text": f"หยุดแทงชั่วคราว #{pair_no}",
                        "weight": "bold",
                        "size": "xl",
                        "align": "center",
                        "color": "#1F2937"
                    },
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#111827",
                        "cornerRadius": "12px",
                        "paddingAll": "14px",
                        "contents": [
                            {
                                "type": "text",
                                "text": "⏸️ ปิดรับบิลชั่วคราว",
                                "weight": "bold",
                                "size": "lg",
                                "align": "center",
                                "color": "#F59E0B"
                            },
                            {
                                "type": "text",
                                "text": f"ค่าย {camp} รอแอดมินเปิดอีกรอบ",
                                "size": "sm",
                                "align": "center",
                                "color": "#FDE68A"
                            }
                        ]
                    },
                    {
                        "type": "text",
                        "text": "หยุดแล้วจะไม่สามารถแทงหรือยกเลิกได้ รอแอดมินเปิดอีกรอบ",
                        "size": "xs",
                        "align": "center",
                        "wrap": True,
                        "color": "#6B7280"
                    }
                ]
            }
        }
    )



def flex_customer_card(st, user):
    """
    การ์ดสมาชิกแบบเรียบง่าย โทนสว่าง เหมือนตัวอย่างในรูป
    แสดง: รูป • ID • ชื่อ • เครดิตคงเหลือ • รายการเล่น (ถ้ามี)
    """
    uid = user["uid"]
    cid = user["cid"]
    name = user.get("name", "ผู้เล่น")
    picture = user.get("pictureUrl") or "https://via.placeholder.com/48"
    credit_total = int(user.get("credit", 0) or 0)

    bet = get_user_bet(st, uid)
    have_bet = bet is not None
    side_th = "สูง" if (bet and bet["side"] == "HI") else ("ต่ำ" if bet else "")
    stake_used = int(bet["amount"]) if bet else 0

    # สีตามฝั่ง
    side_color = "#3B82F6" if side_th == "สูง" else "#EF4444"

    # แถบสถานะ (progress look) ความยาวตามสัดส่วน (ปรับได้)
    # หมายเหตุ: Flex ไม่มี progress จริง ๆ ใช้กล่องสองชั้นเลียนแบบ
    max_bar = max(stake_used, 1)
    filled_flex = 8 if have_bet else 0
    empty_flex = (12 - filled_flex) if have_bet else 12

    # ส่วนหัว: โปรไฟล์ + ID/ชื่อ + เครดิตคงเหลือ
    header = {
        "type": "box", "layout": "horizontal", "spacing": "12px",
        "contents": [
            {
                "type": "image", "url": picture, "size": "48px",
                "aspectMode": "cover", "aspectRatio": "1:1",
                "cornerRadius": "10px"
            },
            {
                "type": "box", "layout": "vertical", "flex": 7, "spacing": "2px",
                "contents": [
                    {
                        "type": "text",
                        "text": f"ID : {cid} {name}",
                        "weight": "bold",
                        "size": "md",
                        "color": "#111827",
                        "wrap": True,
                        "maxLines": 2
                    },
                    {
                        "type": "text",
                        "text": f"คงเหลือ {fmt(credit_total)} บ.",
                        "size": "sm",
                        "color": "#6B7280"
                    }
                ]
            }
        ]
    }

    # กล่อง "รายการเล่น" ถ้ามีบิล
    bet_block = {
        "type": "box", "layout": "vertical", "spacing": "6px",
        "contents": [
            # แถวหัวข้อ + จำนวน
            {
                "type": "box", "layout": "horizontal", "contents": [
                    {
                        "type": "text",
                        "text": side_th or "ยังไม่ได้เดิมพัน",
                        "weight": "bold",
                        "size": "sm",
                        "color": "#111827",
                        "flex": 7
                    },
                    {
                        "type": "text",
                        "text": f"{fmt(stake_used)} บ." if have_bet else "",
                        "size": "sm",
                        "align": "end",
                        "color": "#111827",
                        "flex": 5
                    }
                ]
            },
            # แถบสถานะ
            {
                "type": "box", "layout": "horizontal",
                "backgroundColor": "#E5E7EB",
                "height": "10px",
                "cornerRadius": "10px",
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": side_color,
                        "cornerRadius": "10px",
                        "contents": [],
                        "flex": filled_flex
                    },
                    {"type": "filler", "flex": empty_flex}
                ]
            },
            # บรรทัดหักล่วงหน้า + เครดิตคงเหลือ (สไตล์ภาพตัวอย่าง)
            {
                "type": "box", "layout": "horizontal", "contents": [
                    {
                        "type": "text",
                        "text": f"หักล่วงหน้า -{fmt(stake_used)}" if have_bet else "",
                        "size": "xs",
                        "color": "#6B7280",
                        "flex": 7
                    },
                    {
                        "type": "text",
                        "text": f"คงเหลือ {fmt(credit_total)} บ.",
                        "size": "xs",
                        "color": "#6B7280",
                        "align": "end",
                        "flex": 5
                    }
                ]
            }
        ]
    }

    # ถ้าไม่มีบิล ให้แสดงบรรทัด “ยังไม่มีการเดิมพัน”
    if not have_bet:
        bet_block = {
            "type": "text",
            "text": "ยังไม่มีการเดิมพันในรอบนี้",
            "size": "sm",
            "color": "#6B7280",
            "wrap": True
        }

    return FlexSendMessage(
        alt_text=f"ID {cid} — การ์ดสมาชิก",
        contents={
            "type": "bubble",
            "size": "mega",
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "12px",
                "backgroundColor": "#F3F4F6",   # เทาอ่อนเหมือนแชตตัวอย่าง
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "cornerRadius": "16px",
                        "paddingAll": "12px",
                        "backgroundColor": "#FFFFFF",
                        "contents": [
                            header,
                            {"type": "box", "layout": "vertical", "margin": "md", "spacing": "8px",
                             "contents": [
                                 {"type": "separator", "color": "#E5E7EB"},
                                 bet_block
                             ]}
                        ]
                    }
                ]
            }
        }
    )


def text_bank():
    return TextSendMessage(
        text=(
            "📌 บั้งไฟแสนพญานาค777\n\n"
            "⚠️แจ้งเลขบัญชีฝาก⚠️\n\n"
            "🏳️ 9640253176\n"
            "🏦 กรุงเทพ\n"
            "👤 กิติพร ศักดิ์ศรี\n\n"
            "📌 เพื่อป้องกันมิจฉาชีพ ชื่อผู้ฝาก-ถอน ต้องเป็นชื่อเดียวกันเท่านั้น⚠️\n"
            "📌 กด C ดูไอดีตัวเองส่งให้แอดมินได้เลย\n"
        )
    )


def flex_backoffice_button(url: str, label: str = "เปิดหน้าฝากเงิน"):
    """ปุ่ม Flex สำหรับเปิดหน้าแจ้งฝาก/ฝากเงิน (ลิงก์ DEPOSIT_URL)

    แก้ปัญหา NameError: flex_backoffice_button ไม่ถูกประกาศ
    """
    u = (url or '').strip() or DEPOSIT_URL
    # กันพิมพ์ลิงก์แบบไม่มี scheme
    if not re.match(r'^https?://', u, re.IGNORECASE):
        u = 'https://' + u.lstrip('/')

    return FlexSendMessage(
        alt_text='ฝากเงิน/แจ้งโอน',
        contents={
            'type': 'bubble',
            'size': 'mega',
            'styles': {'body': {'backgroundColor': '#F3F4F6'}},
            'body': {
                'type': 'box',
                'layout': 'vertical',
                'paddingAll': '12px',
                'contents': [
                    {
                        'type': 'box',
                        'layout': 'vertical',
                        'backgroundColor': '#FFFFFF',
                        'cornerRadius': '16px',
                        'paddingAll': '16px',
                        'spacing': '10px',
                        'contents': [
                            {
                                'type': 'text',
                                'text': '💳 ฝากเงิน / แจ้งโอน',
                                'weight': 'bold',
                                'size': 'lg',
                                'align': 'center',
                                'color': '#111827'
                            },
                            {
                                'type': 'text',
                                'text': 'กดปุ่มด้านล่างเพื่อไปหน้าแจ้งฝาก/แนบสลิป',
                                'size': 'sm',
                                'align': 'center',
                                'wrap': True,
                                'color': '#6B7280'
                            },
                            {'type': 'separator', 'margin': 'md', 'color': '#E5E7EB'},
                            {
                                'type': 'button',
                                'style': 'primary',
                                'color': '#16A34A',
                                'height': 'sm',
                                'action': {'type': 'uri', 'label': label, 'uri': u}
                            }
                        ]
                    }
                ]
            }
        }
    )



def flex_result_preview(code: str, pair_no: int):
    # ---- mapping สี/ไอคอน/คำอธิบาย ตามผล ----
    meta = {
        "ส": {"title": "สูงชนะ", "accent": "#00C853", "icon": "✅", "desc": f"จ่าย 1 : {PROFIT_RATE:.2f}"},
        "ต": {"title": "ต่ำชนะ", "accent": "#A51212CA", "icon": "❌", "desc": f"จ่าย 1 : {PROFIT_RATE:.2f}"},
        "ก": {"title": f"กลาง (คืนเงิน หัก {int(MIDDLE_FEE*100)}%)", "accent": "#F59E0B", "icon": "🟡", "desc": "คืนเงินแบบหักค่าธรรมเนียม"},
        "จ": {"title": "จาว (คืนเต็ม)", "accent": "#22C55E", "icon": "🟢", "desc": "คืนเงินเต็มจำนวน"},
        "ม": {"title": "เสมอ-หาย (คืนเต็ม)", "accent": "#22C55E", "icon": "🟢", "desc": "คืนเงินเต็มจำนวน"},
        "ตจ": {"title": f"ต่ำเสมอ (หัก {int(MIDDLE_FEE*100)}%) / สูงเสียเต็ม", "accent": "#A855F7", "icon": "🟣", "desc": "ตามนโยบายพิเศษ"},
        "ตส": {"title": f"ต่ำเสียเต็ม / สูงเสมอ (หัก {int(MIDDLE_FEE*100)}%)", "accent": "#A855F7", "icon": "🟣", "desc": "ตามนโยบายพิเศษ"},
    }
    m = meta.get(code, {"title": "ใส่ผลผิดใส่ใหม่", "accent": "#94A3B8", "icon": "⚪", "desc": "ตรวจสอบรหัสผลอีกครั้ง"})
    title = m["title"]
    accent = m["accent"]
    icon = m["icon"]
    desc = m["desc"]

    # สีตัวอักษรผล: โทนเขียวสำหรับคืนเต็ม/จาว/ม, โทนปกติกรณีอื่น
    text_color = "#10B981" if any(k in code for k in ("จ", "ม")) else "#E5E7EB"

    return FlexSendMessage(
        alt_text=f"สรุปผล: {title}",
        contents={
            "type": "bubble",
            "size": "mega",
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "0px",
                "contents": [
                    # ---- Header (แถบสี) ----
                    {
                        "type": "box",
                        "layout": "vertical",
                        "paddingAll": "14px",
                        "backgroundColor": accent,
                        "contents": [
                            {
                                "type": "text",
                                "text": f"{icon} สรุปผลรอบที่ {pair_no}",
                                "weight": "bold",
                                "size": "lg",
                                "align": "center",
                                "color": "#0B1220"
                            }
                        ]
                    },
                    # ---- Card ----
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#0F172A",
                        "paddingAll": "16px",
                        "spacing": "12px",
                        "contents": [
                            # Title row
                            {
                                "type": "box",
                                "layout": "horizontal",
                                "contents": [
                                    {
                                        "type": "box",
                                        "layout": "vertical",
                                        "width": "6px",
                                        "backgroundColor": accent,
                                        "cornerRadius": "6px",
                                        "height": "52px"
                                    },
                                    {
                                        "type": "box",
                                        "layout": "vertical",
                                        "paddingAll": "10px",
                                        "contents": [
                                            {
                                                "type": "text",
                                                "text": title,
                                                "weight": "bold",
                                                "size": "xl",
                                                "wrap": True,
                                                "color": text_color,
                                                "align": "start"
                                            },
                                            {
                                                "type": "text",
                                                "text": desc,
                                                "size": "xs",
                                                "color": "#94A3B8",
                                                "wrap": True
                                            }
                                        ]
                                    }
                                ],
                                "spacing": "10px",
                                "cornerRadius": "10px"
                            },

                            {"type": "separator", "color": "#334155"},

                            # Quick tips
                            {
                                "type": "box",
                                "layout": "vertical",
                                "spacing": "6px",
                                "contents": [
                                    {
                                        "type": "text",
                                        "text": "ขั้นตอนถัดไป",
                                        "size": "sm",
                                        "weight": "bold",
                                        "color": "#CBD5E1"
                                    },
                                    {
                                        "type": "box",
                                        "layout": "vertical",
                                        "backgroundColor": "#111827",
                                        "cornerRadius": "8px",
                                        "paddingAll": "10px",
                                        "contents": [
                                            {
                                                "type": "text",
                                                "text": "พิมพ์  เพื่อยืนยันผล",
                                                "size": "sm",
                                                "color": "#E5E7EB",
                                                "wrap": True
                                            },
                                            {
                                                "type": "text",
                                                "text": "หากต้องการเปลี่ยนผล: พิมพ์ s<โค้ดผล> อีกครั้ง",
                                                "size": "xs",
                                                "color": "#94A3B8",
                                                "wrap": True
                                            }
                                        ]
                                    }
                                ]
                            }
                        ]
                    }
                ]
            }
        }
    )


def flex_settle(pair_no, rows, footer_text,
                show_profit=False, profit_value=0,
                balance_map=None,
                accum=None,
                camp_name=None):  # <--- รับตัวแปร camp_name เพิ่ม
    
    def _fmt_signed(n: int) -> str:
        return f"+{fmt(n)}" if n >= 0 else f"-{fmt(abs(n))}"

    has_balance = bool(balance_map)
    has_accum   = bool(accum)

    # --- 1. ส่วนหัวข้อ (Header) ปรับใหม่ให้โชว์ รอบ และ ค่าย ---
    header_contents = [
        # บรรทัดที่ 1: รอบที่ (ตัวใหญ่ สีทอง)
        {
            "type": "text",
            "text": f"รอบที่ {pair_no}",
            "weight": "bold",
            "align": "center",
            "size": "xxl",
            "color": "#FDE68A"  # สีทอง
        }
    ]
    
    # บรรทัดที่ 2: ชื่อค่าย (ถ้ามี)
    if camp_name:
        header_contents.append({
            "type": "text",
            "text": f"🚀 ค่าย: {camp_name}",
            "weight": "bold",
            "align": "center",
            "size": "md",
            "color": "#FFFFFF",
            "margin": "sm"
        })
    else:
        # ถ้าไม่มีชื่อค่าย ให้ขึ้นว่า สรุปผลการแทง แทน
        header_contents.insert(0, {
             "type": "text", "text": "📊 สรุปผลการแทง", 
             "weight": "bold", "align": "center", "size": "md", "color": "#FFFFFF"
        })

    # --- 2. ส่วนรายการผู้เล่น (Body) ---
    header_cols = [
        {"type": "text", "text": "ผู้เล่น",  "flex": 4, "size": "md", "weight": "bold", "color": "#FFFFFF"},
        {"type": "text", "text": "ยอดเล่น", "flex": 3, "size": "md", "align": "end", "weight": "bold", "color": "#FFFFFF"},
        {"type": "text", "text": "ได้เสีย",  "flex": 3, "size": "md", "align": "end", "weight": "bold", "color": "#FFFFFF"},
    ]
    if has_balance:
        header_cols.append({"type": "text", "text": "คงเหลือ", "flex": 3, "size": "md", "align": "end", "weight": "bold", "color": "#FFFFFF"})

    lines = []
    if rows:
        lines.append({"type": "box", "layout": "horizontal", "contents": header_cols})
        lines.append({"type": "separator", "margin": "sm", "color": "#4B5563"})
        for r in rows:
            pl = (r.get("payout", 0) or 0) - (r.get("stake", 0) or 0)
            pl_color = "#10B981" if pl > 0 else ("#EF4444" if pl < 0 else "#E5E7EB")

            row_cols = [
                {"type": "text", "text": r["name"],       "flex": 4, "size": "md", "color": "#E5E7EB"},
                {"type": "text", "text": fmt(r["stake"]), "flex": 3, "size": "md", "align": "end", "color": "#F9FAFB"},
                {"type": "text", "text": _fmt_signed(pl), "flex": 3, "size": "md", "align": "end", "color": pl_color},
            ]
            if has_balance:
                bal = balance_map.get(r["uid"], 0)
                row_cols.append({"type": "text", "text": fmt(bal), "flex": 3, "size": "md", "align": "end", "color": "#FACC15"})
            lines.append({"type": "box", "layout": "horizontal", "contents": row_cols})
    else:
        lines.append({"type": "text", "text": "(ไม่มีผู้เล่น)", "size": "md", "align": "center", "color": "#9CA3AF"})

    # --- 3. ส่วนสรุปกำไร (Footer) ---
    if show_profit:
        lines.append({"type": "separator", "margin": "md", "color": "#4B5563"})
        lines.append({"type": "text", "text": f"💰 กำไรรอบนี้: {_fmt_signed(profit_value)}",
                      "align": "end", "weight": "bold", "size": "md", "color": "#FACC15"})
        if has_accum:
            lines.append({"type": "text",
                          "text": f"📈 สะสมกำไร: {fmt(accum['profit_sum'])} • ขาดทุน: {fmt(accum['loss_sum'])}",
                          "align": "end", "size": "sm", "color": "#E5E7EB"})
            lines.append({"type": "text",
                          "text": f"🧮 สุทธิสะสม: {_fmt_signed(accum['net'])}",
                          "align": "end", "weight": "bold", "size": "md",
                          "color": "#10B981" if accum["net"] >= 0 else "#EF4444"})

    return FlexSendMessage(
        alt_text=f"สรุปผล รอบ {pair_no}",
        contents={
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "0px",
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#16A34A",
                        "paddingAll": "14px",
                        "contents": header_contents # ใช้ส่วนหัวที่สร้างไว้ด้านบน
                    },
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#1F2937",
                        "paddingAll": "18px",
                        "spacing": "md",
                        "contents": lines + [
                            {"type": "separator", "margin": "md", "color": "#4B5563"},
                            {"type": "text", "text": footer_text, "align": "end", "size": "md", "color": "#9CA3AF"}
                        ]
                    }
                ]
            }
        }
    )

def flex_scoreboard(history_list):
    # Mapping ผล: เปลี่ยนจากสีพื้นหลัง เป็นสีตัวอักษร (color)
    res_map = {
        "ส":  {"text": "สูง ✅", "color": "#22C55E"},
        "ต":  {"text": "ต่ำ ❌", "color": "#EF4444"},
        "ก":  {"text": "กลาง ⛔", "color": "#EAB308"},
        "จ":  {"text": "จาว ⛔", "color": "#3B82F6"},
        "ม":  {"text": "เสมอ ⛔", "color": "#3B82F6"},
        "ตจ": {"text": "ต่ำเสมอ สูงเสียเต็ม ⛔❌", "color": "#A855F7"},
        "ตส": {"text": "ต่ำเสียเต็ม สูงเสมอ ✅⛔", "color": "#A855F7"},
    }

    # ===== 🔥 จุดแก้จริง: คัดเหลือผลล่าสุดต่อรอบ =====
    latest_by_round = {}
    for h in history_list or []:
        r = h.get("round")
        if r is None:
            continue
        latest_by_round[r] = h   # ตัวหลังทับตัวก่อน (ผลล่าสุด)

    # เรียงตามรอบ แล้วเอา 10 รอบล่าสุด
    recent = [latest_by_round[r] for r in sorted(latest_by_round)][-10:]

    rows = []

    # --- ส่วนหัวตาราง ---
    rows.append({
        "type": "box",
        "layout": "horizontal",
        "paddingBottom": "10px",
        "contents": [
            {"type": "text", "text": "#", "flex": 1, "size": "xs", "color": "#6B7280", "align": "center"},
            {"type": "text", "text": "ชื่อค่าย ", "flex": 3, "size": "xs", "color": "#6B7280", "offsetStart": "10px"},
            {"type": "text", "text": "ผล ", "flex": 4, "size": "xs", "align": "center", "color": "#6B7280"},
        ]
    })

    # วนลูปสร้างแถวข้อมูล
    for idx, item in enumerate(recent):
        code_key = item.get('code', '?')

        if code_key in res_map:
            style = res_map[code_key]
        else:
            base_code = code_key[0] if code_key else "?"
            style = res_map.get(base_code, {"text": code_key, "color": "#FFFFFF"})

        camp_name = item.get('camp') or "-"

        rows.append({
            "type": "box",
            "layout": "horizontal",
            "paddingVertical": "8px",
            "alignItems": "center",
            "contents": [
                {
                    "type": "text",
                    "text": str(item['round']),
                    "flex": 1,
                    "size": "xs",
                    "color": "#9CA3AF",
                    "align": "center"
                },
                {
                    "type": "text",
                    "text": camp_name,
                    "flex": 3,
                    "size": "sm",
                    "color": "#E5E7EB",
                    "wrap": False,
                    "offsetStart": "10px"
                },
                {
                    "type": "text",
                    "text": style['text'],
                    "flex": 4,
                    "color": style['color'],
                    "weight": "bold",
                    "align": "center",
                    "size": "xxs" if len(style['text']) > 8 else "xs",
                    "wrap": True
                }
            ]
        })

        if idx < len(recent) - 1:
            rows.append({"type": "separator", "color": "#1F2937", "margin": "none"})

    return FlexSendMessage(
        alt_text="สกอบั้งไฟล่าสุด",
        contents={
            "type": "bubble",
            "size": "mega",
            "styles": {
                "header": {"backgroundColor": "#111827"},
                "body": {"backgroundColor": "#111827"}
            },
            "header": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "20px",
                "contents": [
                    {
                        "type": "text",
                        "text": "📜 สกอบั้งไฟ",
                        "weight": "bold",
                        "size": "lg",
                        "color": "#FBBF24",
                        "align": "center"
                    }
                ]
            },
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingTop": "0px",
                "contents": [
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#1F2937",
                        "cornerRadius": "10px",
                        "paddingAll": "12px",
                        "contents": rows if rows else [
                            {
                                "type": "text",
                                "text": "(ยังไม่มีประวัติ)",
                                "align": "center",
                                "color": "#6B7280",
                                "size": "sm",
                                "paddingAll": "20px"
                            }
                        ]
                    }
                ]
            }
        }
    )


def flex_call_pages(user_rows, title="ตารางเครดิตลูกค้า", per_page=30):
    pages = []
    total = len(user_rows)
    num_pages = max(1, ceil(total / per_page))
    sum_credit_all = sum(int(r.get("credit", 0) or 0) for r in user_rows)

    def fmt2(n):
        try:
            return f"{int(float(n or 0)):,}"
        except:
            return "0"

    updated_at = datetime.now().strftime("%d/%m/%Y %H:%M")

    # ========== HEAD TABLE: ขนาดเล็กลง 100% ทำงานได้ ==========
    def table_head():
        return {
            "type": "box",
            "layout": "horizontal",
            "paddingAll": "6px",
            "backgroundColor": "#E6F0FF",
            "contents": [
                {"type": "text", "text": "ID", "flex": 3, "size": "xs", "weight": "bold", "color": "#1E3A8A"},
                {"type": "text", "text": "ชื่อ", "flex": 6, "size": "xs", "weight": "bold", "color": "#1E3A8A"},
                {"type": "text", "text": "เครดิต", "flex": 3, "size": "xs", "weight": "bold", "align": "end", "color": "#1E3A8A"},
            ]
        }

    for i in range(num_pages):
        chunk = user_rows[i * per_page:(i + 1) * per_page]
        page_credit = sum(int(r.get("credit", 0) or 0) for r in chunk)

        header = {
            "type": "box",
            "layout": "vertical",
            "paddingAll": "6px",
            "contents": [
                {"type": "text", "text": title, "weight": "bold", "size": "sm", "align": "center"},
                {"type": "text", "text": f"หน้า {i+1}/{num_pages} • อัปเดต {updated_at}", "size": "xs", "align": "center", "color": "#6B7280"}
            ]
        }

        rows = []
        rows.append(table_head())
        rows.append({"type": "separator", "margin": "md", "color": "#D1D5DB"})

        # ========== ROWS ==========
        if chunk:
            for idx, r in enumerate(chunk):
                cid = str(r.get("cid", "-"))
                name = str(r.get("name", "-"))
                cred = int(r.get("credit", 0) or 0)

                row_bg = "#FFFFFF"

                rows.append({
                    "type": "box",
                    "layout": "horizontal",
                    "paddingAll": "4px",   # ลด padding แต่ไม่ถึงขั้นพัง
                    "backgroundColor": row_bg,
                    "contents": [
                        {"type": "text", "text": cid, "flex": 3, "size": "xs", "color": "#111827"},
                        {"type": "text", "text": name, "flex": 6, "size": "xs", "wrap": True, "color": "#111827"},
                        {"type": "text", "text": fmt2(cred), "flex": 3, "size": "xs", "align": "end", "color": "#111827"},
                    ]
                })

                if idx != len(chunk) - 1:
                    rows.append({"type": "separator", "margin": "md", "color": "#E5E7EB"})
        else:
            rows.append({
                "type": "box",
                "layout": "vertical",
                "paddingAll": "8px",
                "contents": [{"type": "text", "text": "(ยังไม่มีข้อมูล)", "align": "center", "size": "xs", "color": "#9CA3AF"}]
            })

        # ========== SUMMARY ==========
        summary = {
            "type": "box",
            "layout": "vertical",
            "spacing": "4px",
            "paddingAll": "6px",
            "contents": [
                {"type": "box", "layout": "horizontal", "contents": [
                    {"type": "text", "text": "ลูกค้าในหน้านี้", "flex": 6, "size": "xs", "color": "#6B7280"},
                    {"type": "text", "text": str(len(chunk)), "flex": 6, "size": "xs", "align": "end"},
                ]},
                {"type": "box", "layout": "horizontal", "contents": [
                    {"type": "text", "text": "รวมเครดิต (หน้านี้)", "flex": 6, "size": "xs", "color": "#6B7280"},
                    {"type": "text", "text": fmt2(page_credit), "flex": 6, "size": "xs", "align": "end", "color": "#16A34A"},
                ]},
                {"type": "separator", "margin": "md"},
                {"type": "box", "layout": "horizontal", "contents": [
                    {"type": "text", "text": "รวมเครดิต (ทั้งหมด)", "flex": 6, "size": "xs", "color": "#6B7280"},
                    {"type": "text", "text": fmt2(sum_credit_all), "flex": 6, "size": "xs", "align": "end", "color": "#16A34A"},
                ]}
            ]
        }

        bubble = {
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "spacing": "4px",
                "paddingAll": "8px",
                "contents": [
                    header,
                    {"type": "box", "layout": "vertical", "contents": rows},
                    summary
                ]
            }
        }

        pages.append(FlexSendMessage(
            alt_text=f"{title} {i+1}/{num_pages}",
            contents=bubble
        ))

    return pages




@lru_cache(maxsize=None)
def rules_text() -> str:
    return (
        "🎉🎊กติกา🎊🎉\n"
        f"✨แทงขั้นต่ำ{MIN_BET}-{fmt(MAX_BET)}บาท/คน/รอบ\n"
        "\n"
        "🏆การจ่าย🎖️\n"
        f"ชนะ จ่าย 1 : {PROFIT_RATE:.2f}\n"
        "\n"
        f"🔴อั้นต่ำ = {fmt(SIDE_CAP['LO'])}\n"
        f"🔵อั้นสูง = {fmt(SIDE_CAP['HI'])}\n"
        f"🟢ออกกลางเจ๊า หัก {int(MIDDLE_FEE*100)}%\n"
        "\n"
        "- จำกัด 1 บิล/รอบ และห้ามแทงสวน (ต้องยกเลิกบิลเดิมก่อน)\n"
        "- พิมพ์ x เพื่อยกเลิกบิล / พิมพ์ C เพื่อดูบัตรสมาชิก\n"
    )


# ====== RESULT CALC (ตามโมเดล escrow) ======
def settle_by_code(st, code):
    """
    โมเดลเครดิต:
    - ตอนรับบิล: หักเครดิต = amount และเก็บ st['escrow'][uid] += amount
    - ตอนสรุป:
        * ชนะ: คืนต้นทุน + กำไรสุทธิ (amount + amount*PROFIT_RATE)
        * แพ้: ไม่คืนอะไร (ต้นทุนถูกหักไปแล้ว)
        * คืนเงินหัก fee: คืน amount*(1 - fee)
        * คืนเต็ม: คืน amount
    ฟังก์ชันนี้คืน rows: [{'uid','name','stake','payout'}...], footer_text
    """
    acc = {}
    def add(uid, name, stake, payout):
        row = acc.get(uid, {"uid": uid, "name": name, "stake": 0, "payout": 0})
        row["stake"] += stake
        row["payout"] += payout
        acc[uid] = row

    d = RESULT_DEFS.get(code)

    # DRAW (คืนเต็ม)
    if (not d) or d.get("special") == "DRAW_0":
        for b in st["bet_index"].values():
            add(b["uid"], b["name"], b["amount"], b["amount"])
        label = RESULT_DEFS.get(code, {"label": "จาว (คืนเต็ม)"} )["label"]
        return list(acc.values()), f"ผล: {label}"

    # กลางคืนเงิน หัก MIDDLE_FEE
    if d.get("special") == "MIDDLE_FEE":
        for b in st["bet_index"].values():
            refund = _round_refund(b["amount"] * (1 - MIDDLE_FEE))
            add(b["uid"], b["name"], b["amount"], refund)
        return list(acc.values()), f"ผล: กลาง (คืนเงิน หัก {int(MIDDLE_FEE*100)}%)"

    # ต่ำเสมอ (หัก fee) / สูงเสียเต็ม
    if d.get("special") == "LOW_DRAWFEE_HIGH_LOSE":
        for b in st["bet_index"].values():
            if b["side"] == "LO":
                refund = _round_refund(b["amount"] * (1 - MIDDLE_FEE))
                add(b["uid"], b["name"], b["amount"], refund)
            else:
                add(b["uid"], b["name"], b["amount"], 0)
        return list(acc.values()), f"ผล: ต่ำเสมอ (หัก {int(MIDDLE_FEE*100)}%) / สูงเสียเต็ม"

    # ต่ำเสียเต็ม / สูงเสมอ (หัก fee)
    if d.get("special") == "LOW_LOSE_HIGH_DRAWFEE":
        for b in st["bet_index"].values():
            if b["side"] == "HI":
                refund = round(b["amount"] * (1 - MIDDLE_FEE))
                add(b["uid"], b["name"], b["amount"], refund)
            else:
                add(b["uid"], b["name"], b["amount"], 0)
        return list(acc.values()), f"ผล: ต่ำเสียเต็ม / สูงเสมอ (หัก {int(MIDDLE_FEE*100)}%)"

    # ปกติ: มีฝั่งชนะ/แพ้
    win = d["winner"]
    for b in st["bet_index"].values():
        if b["side"] == win:
            payout = b["amount"] + _round_profit(b["amount"] * PROFIT_RATE)
            add(b["uid"], b["name"], b["amount"], payout)
        else:
            add(b["uid"], b["name"], b["amount"], 0)
    return list(acc.values()), f"ผล: {d['label']}"

# ========= HARDENING / SECURITY =========
MAX_BODY_BYTES = int(os.getenv("MAX_BODY_BYTES", "200000"))
WEBHOOK_DRIFT_SEC = int(os.getenv("WEBHOOK_DRIFT_SEC", "600"))  # DEV-friendly
REQUIRE_LINE_UA = os.getenv("REQUIRE_LINE_UA", "0") == "1"




RL_IP_LIMIT, RL_IP_PERIOD = int(os.getenv("RL_IP_LIMIT", "150")), int(os.getenv("RL_IP_PERIOD", "60"))
RL_UID_BURST_LIMIT, RL_UID_BURST_PERIOD = int(os.getenv("RL_UID_BURST_LIMIT", "20")), int(os.getenv("RL_UID_BURST_PERIOD", "10"))
RL_ROOM_BURST_LIMIT, RL_ROOM_BURST_PERIOD = int(os.getenv("RL_ROOM_BURST_LIMIT", "220")), int(os.getenv("RL_ROOM_BURST_PERIOD", "10"))
RL_UID_DAILY_LIMIT, RL_UID_DAILY_PERIOD = int(os.getenv("RL_UID_DAILY_LIMIT", "3000")), 86400

MUTE_SECONDS_DEFAULT = int(os.getenv("MUTE_SECONDS_DEFAULT", "300"))
ABUSE_STRIKE_TO_MUTE  = int(os.getenv("ABUSE_STRIKE_TO_MUTE", "3"))

ALLOW_GROUP_IDS = {s.strip() for s in os.getenv("ALLOW_GROUP_IDS", "").split(",") if s.strip()}
DENY_GROUP_IDS  = {s.strip() for s in os.getenv("DENY_GROUP_IDS", "").split(",") if s.strip()}

ADMIN_PIN = os.getenv("ADMIN_PIN", "1234")

PROTECTED_UIDS = {s.strip() for s in os.getenv("PROTECTED_UIDS", "").split(",") if s.strip()}
LOCKDOWN_SECONDS_DEFAULT = int(os.getenv("LOCKDOWN_SECONDS_DEFAULT", "900"))  # 15m

class RateLimiter:
    def __init__(self): self._buckets = {}
    def allow(self, key: str, limit: int, period: int) -> bool:
        now = time.time()
        dq = self._buckets.get(key)
        if dq is None:
            dq = deque(); self._buckets[key] = dq
        while dq and (now - dq[0]) > period:
            dq.popleft()
        if len(dq) >= limit:
            return False
        dq.append(now)
        return True

rl = RateLimiter()
MUTED_UNTIL = {}       # uid -> ts
BANNED_UIDS = set()    # uid
BANNED_GROUPS = set()  # gid
STRIKES = {}           # uid -> count
_last_notice_at = {}   # uid -> ts
LOCKDOWN_UNTIL = {}    # gid -> ts

@lru_cache(maxsize=1024)
def _safe_is_line_ua(ua: str) -> bool:
    if not ua: return False
    ua = ua.lower()
    return ("linebotwebhook" in ua) or ("line-bot-sdk" in ua) or ("line" in ua and "webhook" in ua)

def _client_ip():
    xff = request.headers.get("X-Forwarded-For", "")
    if xff:
        return xff.split(",")[0].strip()
    return request.remote_addr or "0.0.0.0"

def _now(): return int(time.time())
def _muted(uid: str) -> bool: return MUTED_UNTIL.get(uid, 0) > _now()
def _locked_group(gid: str) -> bool: return LOCKDOWN_UNTIL.get(gid, 0) > _now()

def _notice_throttled(uid: str) -> bool:
    last = _last_notice_at.get(uid, 0)
    if _now() - last >= 30:
        _last_notice_at[uid] = _now()
        return False
    return True

def _admin_auth_pin(text: str) -> str:
    m = re.search(r"(?:\s|!!)(\d{4,8})\s*$", text)
    return m.group(1) if m else ""

def is_allowed_group(gid: str) -> bool:
    if gid in DENY_GROUP_IDS or gid in BANNED_GROUPS: return False
    if ALLOW_GROUP_IDS: return gid in ALLOW_GROUP_IDS or gid in BACKOFFICE_GROUP_IDS
    return True

def _line_target_id(event_or_source):
    """คืนค่าเป้าหมายสำหรับ push fallback: group_id > room_id > user_id"""
    src = getattr(event_or_source, "source", event_or_source)
    return (
        getattr(src, "group_id", None)
        or getattr(src, "room_id", None)
        or getattr(src, "user_id", None)
    )


def _line_send_attempts() -> int:
    try:
        return max(1, int(LINE_SEND_RETRY))
    except Exception:
        return 1


def _line_retry_sleep(attempt: int):
    try:
        delay = float(LINE_RETRY_SLEEP) * attempt
        if delay > 0:
            time.sleep(delay)
    except Exception:
        pass


def _as_line_message_dict(msg):
    """แปลง LINE SDK message object เป็น dict สำหรับยิง API ตรงแบบใส่ retry key ได้"""
    if isinstance(msg, dict):
        return msg
    if hasattr(msg, "as_json_dict"):
        return msg.as_json_dict()
    if isinstance(msg, str):
        return {"type": "text", "text": msg}
    # fallback กันเคส object แปลก ๆ
    return {"type": "text", "text": str(msg)}


def _normalize_line_messages(messages):
    """LINE จำกัดสูงสุด 5 messages ต่อครั้ง"""
    if messages is None:
        return []
    if isinstance(messages, (list, tuple)):
        raw = list(messages)
    else:
        raw = [messages]
    return [_as_line_message_dict(m) for m in raw[:5]]


def _safe_reply_worker(reply_token, to_id, messages, fallback_push):
    """ส่ง reply ใน background เพื่อไม่ให้ webhook/room lock ค้างเวลาฝั่ง LINE timeout"""
    try:
        line_bot_api.reply_message(reply_token, messages, timeout=LINE_API_TIMEOUT)
        return True
    except Exception as e:
        try:
            app.logger.warning(
                "safe_reply failed: %s: %s | fallback_push=%s",
                type(e).__name__, e, fallback_push
            )
        except Exception:
            pass

        if fallback_push and to_id:
            # fallback push ปิดเป็น default เพื่อกันข้อความซ้ำ; เปิดได้ด้วย LINE_REPLY_FALLBACK_PUSH=1
            return safe_push(to_id, messages, label="reply_fallback")
        return False


def safe_reply(event, messages, fallback_push=None):
    """
    Reply กลับ LINE แบบไม่บล็อก handler — STABLE MODE
    - ไม่ retry reply เพราะ reply token ใช้ได้ครั้งเดียว
    - ไม่ fallback push เป็นค่าเริ่มต้น เพื่อกันข้อความซ้ำ
    - ส่งใน background เพื่อลด webhook timeout และไม่ให้ lock ห้องค้าง
    """
    if fallback_push is None:
        fallback_push = LINE_REPLY_FALLBACK_PUSH

    reply_token = getattr(event, "reply_token", None)
    if not reply_token:
        return False
    to_id = _line_target_id(event)

    if not _LINE_SEND_SEMAPHORE.acquire(blocking=False):
        try:
            app.logger.warning("LINE send queue is full; drop reply to prevent server stall")
        except Exception:
            pass
        return False

    def _runner():
        try:
            _safe_reply_worker(reply_token, to_id, messages, fallback_push)
        finally:
            try:
                _LINE_SEND_SEMAPHORE.release()
            except Exception:
                pass

    try:
        threading.Thread(target=_runner, daemon=True).start()
        return True
    except Exception:
        try:
            _LINE_SEND_SEMAPHORE.release()
        except Exception:
            pass
        try:
            app.logger.exception("start safe_reply thread failed")
        except Exception:
            pass
        return False

def _safe_push_request(to_id, messages, retry_key=None):
    """ยิง Push API ตรง เพื่อใส่ X-Line-Retry-Key ได้ กัน retry แล้วข้อความซ้ำ"""
    payload = {
        "to": to_id,
        "messages": _normalize_line_messages(messages),
    }
    headers = {
        "Authorization": f"Bearer {CHANNEL_ACCESS_TOKEN}",
        "Content-Type": "application/json",
    }
    if retry_key:
        headers["X-Line-Retry-Key"] = retry_key

    return requests.post(
        "https://api.line.me/v2/bot/message/push",
        headers=headers,
        json=payload,
        timeout=LINE_API_TIMEOUT,
    )


def safe_push(to_id, messages, label: str = "", return_reason: bool = False):
    """
    Push message แบบ retry ที่กันข้อความซ้ำ
    - ใช้ X-Line-Retry-Key เดิมทุก attempt
    - ถ้า retry แล้วได้ 409 ให้ถือว่า request ก่อนหน้าถูก LINE รับไปแล้ว จึงหยุด retry
    - reason: quota_exceeded / line_error_xxx / timeout_or_network
    """
    last_exc = None
    reason = None
    retry_key = str(uuid.uuid4()) if LINE_PUSH_USE_RETRY_KEY else None

    for attempt in range(1, _line_send_attempts() + 1):
        try:
            resp = _safe_push_request(to_id, messages, retry_key=retry_key)

            # 200 = ส่งสำเร็จ
            if 200 <= resp.status_code < 300:
                return (True, None) if return_reason else True

            # 409 + retry key = LINE บล็อกการส่งซ้ำ แปลว่า request ก่อนหน้าถูก accepted แล้ว
            if resp.status_code == 409 and retry_key:
                try:
                    app.logger.info(f"safe_push duplicate blocked by LINE retry key to={to_id} {label}")
                except Exception:
                    pass
                return (True, "duplicate_blocked") if return_reason else True

            msg = ""
            try:
                msg = resp.text or ""
            except Exception:
                pass

            if resp.status_code == 429 and (
                "monthly limit" in msg.lower()
                or "reached your monthly limit" in msg.lower()
            ):
                reason = "quota_exceeded"
                break

            reason = f"line_error_{resp.status_code}"
            # 4xx ส่วนใหญ่ไม่ควร retry ยกเว้น 429 ที่จัดการข้างบนแล้ว
            if 400 <= resp.status_code < 500:
                break

            try:
                app.logger.warning(
                    f"safe_push attempt {attempt}/{_line_send_attempts()} failed status={resp.status_code} to={to_id} {label} body={msg[:300]}".strip()
                )
            except Exception:
                pass

        except requests.exceptions.RequestException as e:
            last_exc = e
            reason = "timeout_or_network"
            try:
                app.logger.warning(
                    f"safe_push attempt {attempt}/{_line_send_attempts()} network failed to={to_id} {label}".strip(),
                    exc_info=True,
                )
            except Exception:
                pass

        except Exception as e:
            last_exc = e
            reason = "unknown_error"
            try:
                app.logger.warning(
                    f"safe_push attempt {attempt}/{_line_send_attempts()} failed to={to_id} {label}".strip(),
                    exc_info=True,
                )
            except Exception:
                pass

        if attempt < _line_send_attempts():
            _line_retry_sleep(attempt)

    try:
        app.logger.error(
            f"safe_push failed permanently to={to_id} {label} reason={reason} err={last_exc}".strip()
        )
    except Exception:
        pass

    return (False, reason) if return_reason else False


def _member_name(gid, uid):
    try:
        p = line_bot_api.get_group_member_profile(gid, uid)
        return p.display_name
    except Exception:
        return uid

def _lockdown_and_alert(gid, uid):
    """ป้องกัน kick สำคัญ: ล็อกดาวน์ + แจ้งเตือน (no-op safety)."""
    LOCKDOWN_UNTIL[gid] = _now() + LOCKDOWN_SECONDS_DEFAULT
    try:
        name = _member_name(gid, uid)
        safe_push(gid, TextSendMessage(f"⚠️ กลุ่มล็อกดาวน์ชั่วคราว {LOCKDOWN_SECONDS_DEFAULT} วินาที เพราะสมาชิกสำคัญออก: {name}"))
    except Exception:
        pass

# ====== ROUTES (secured webhook) ======
@app.route("/webhook", methods=["POST"])
@app.route("/callback", methods=["POST"])
def webhook():
    if request.content_length and request.content_length > MAX_BODY_BYTES:
        time.sleep(0.2)
        return "payload too large", 413

    if REQUIRE_LINE_UA:
        ua = request.headers.get("User-Agent", "")
        if not _safe_is_line_ua(ua):
            time.sleep(0.2)
            return "forbidden ua", 403

    ip = _client_ip()
    if not rl.allow(f"ip:{ip}", RL_IP_LIMIT, RL_IP_PERIOD):
        time.sleep(0.2)
        return "too many", 429

    body = request.get_data(as_text=True)
    ts_hdr = request.headers.get("X-Line-Request-Timestamp", "").strip()
    if ts_hdr.isdigit():
        try:
            tsv = int(ts_hdr)
            if tsv > 10**12: tsv = int(tsv / 1000)
            drift = abs(_now() - tsv)
            if drift > WEBHOOK_DRIFT_SEC:
                return "stale request", 401
        except Exception:
            pass

    sig = request.headers.get("X-Line-Signature", "")
    expected = base64.b64encode(hmac_new(CHANNEL_SECRET.encode(), body.encode(), sha256).digest()).decode()
    if not sig or not compare_digest(sig, expected):
        return "signature error", 400

    try:
        handler.handle(body, sig)
    except InvalidSignatureError:
        return "signature error", 400
    except Exception as e:
        app.logger.exception("err: %s", e)
        return "error", 500
    return "OK"

@app.get("/health")
def health(): return "OK", 200

@app.get("/copy/<acct>")
def copy_page(acct):
    acct = html_escape(acct.strip())
    logo_url = "https://image.tnews.co.th/uploads/images/contents/w1024/2025/01/CxaKtWLdkIgsdkMFfda3.webp?x-image-process=style/lg-webp"
    html = f"""<!doctype html>
<html lang="th">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>คัดลอกเลขบัญชี • กสิกรไทย</title>
<style>
  :root {{
    --bg:#0b1323; --card:#0f172a; --border:#334155; --text:#e5e7eb; --muted:#94a3b8;
    --brand:#16a34a; --brand-dark:#12803c; --warn:#f59e0b;
  }}
  html,body{{height:100%}}
  body{{margin:0;font-family:system-ui,-apple-system,"Segoe UI",Roboto,"Noto Sans Thai","Noto Sans",sans-serif;
       background:var(--bg);color:var(--text);display:flex;align-items:center;justify-content:center;padding:16px}}
  .card{{background:var(--card);border:1px solid var(--border);border-radius:18px;padding:28px;max-width:520px;width:100%;
         box-shadow:0 10px 30px rgba(0,0,0,.35)}}
  .bank{{display:flex;align-items:center;gap:14px;margin-bottom:10px}}
  .bank-logo{{width:54px;height:54px;border-radius:50%;object-fit:cover;flex:0 0 54px;display:block}}
  .bank-title{{font-size:26px;font-weight:800;line-height:1.15}}
  .subtitle{{font-size:18px;color:var(--muted);margin-top:2px}}
  .acct-wrap{{margin:18px 0 8px;background:#091121;border:1px dashed var(--border);border-radius:14px;padding:18px;text-align:center}}
  .label{{font-size:18px;color:var(--muted);margin-bottom:6px}}
  .acct{{font-variant-numeric:tabular-nums;letter-spacing:.5px;font-size:34px;font-weight:800;color:#fde68a;word-break:break-word}}
  .help{{font-size:16px;color:var(--muted);margin:10px 0 18px}}
  .btns{{display:flex;gap:12px;flex-wrap:wrap}}
  button{{flex:1 1 180px;padding:16px 18px;border:0;border-radius:14px;cursor:pointer;font-size:20px;font-weight:800}}
  .primary{{background:var(--brand);color:#052e16}}
  .primary:hover{{background:var(--brand-dark)}}
  .secondary{{background:#0b1222;color:var(--text);border:1px solid var(--border)}}
  .status{{margin-top:16px;font-size:18px;font-weight:700}}
  .ok{{color:var(--brand)}} .warn{{color:var(--warn)}} .err{{color:#ef4444}}
  :is(button,.acct-wrap):focus-visible{{outline:3px solid #93c5fd;outline-offset:3px;border-radius:14px}}
  .sr{{position:absolute;left:-9999px}}
</style>
</head>
<body>
  <main class="card" role="main" aria-labelledby="title">
    <div class="bank">
      <img src="{logo_url}" alt="ธนาคารกสิกรไทย" class="bank-logo" loading="lazy" decoding="async"
           referrerpolicy="no-referrer"
           onerror="this.remove();document.getElementById('kbank-fallback').style.display='block';">
      <div>
        <div id="title" class="bank-title">ธนาคารกสิกรไทย</div>
        <div class="subtitle" aria-hidden="true">ธนาคารกสิกรไทย</div>
        <div id="kbank-fallback" class="subtitle" style="display:none">KBank</div>
      </div>
    </div>

    <div class="acct-wrap" tabindex="0" aria-live="polite" aria-atomic="true">
      <div class="label">เลขบัญชี</div>
      <div id="acct" class="acct" data-raw="{acct}"></div>
    </div>

    <p class="help">แตะ “คัดลอกเลขบัญชี” แล้วสลับไปที่แอปธนาคารเพื่อวางและโอนเงิน</p>

    <div class="btns">
      <button id="copyBtn" class="primary" aria-label="คัดลอกเลขบัญชี">คัดลอกเลขบัญชี</button>
      <button id="closeBtn" class="secondary" aria-label="ปิดหน้านี้">ปิดหน้านี้</button>
    </div>

    <div id="status" class="status warn">กำลังเตรียมคัดลอกให้อัตโนมัติ…</div>
    <p class="help" style="margin-top:14px">เคล็ดลับ: ถ้าคัดลอกไม่ติด ให้กดปุ่ม “คัดลอกเลขบัญชี” อีกครั้ง</p>
    <p class="sr" id="rawValue">{acct}</p>
  </main>

<script>
(function() {{
  const acctEl   = document.getElementById('acct');
  const statusEl = document.getElementById('status');
  const copyBtn  = document.getElementById('copyBtn');
  const closeBtn = document.getElementById('closeBtn');
  const raw      = (acctEl.getAttribute('data-raw') || '').trim();

  function formatReadable(v) {{
    const digits = v.replace(/\\D+/g,'');
    if (digits.length === 10) {{
      return digits.replace(/(\\d{{3}})(\\d)(\\d{{5}})(\\d)/, '$1-$2-$3-$4'); // 123-4-56789-0
    }}
    return digits.replace(/(\\d{{4}})(?=\\d)/g, '$1 ').trim();
  }}

  acctEl.textContent = formatReadable(raw);

  async function doCopy() {{
    const value = raw;
    try {{
      if (navigator.clipboard?.writeText) {{
        await navigator.clipboard.writeText(value);
      }} else {{
        const ta = document.createElement('textarea');
        ta.value = value; ta.style.position='fixed'; ta.style.opacity='0';
        document.body.appendChild(ta); ta.focus(); ta.select(); document.execCommand('copy'); ta.remove();
      }}
      statusEl.textContent = 'คัดลอกแล้ว ✓ นำไปวางในแอปธนาคารได้เลย';
      statusEl.className = 'status ok';
    }} catch(e) {{
      statusEl.textContent = 'คัดลอกไม่สำเร็จ กรุณากดปุ่ม “คัดลอกเลขบัญชี” อีกครั้ง';
      statusEl.className = 'status err';
    }}
  }}

  function robustClose() {{
    window.close();
    setTimeout(() => {{
      if (history.length > 1) {{
        history.back();
        return;
      }}
      const selfWin = window.open('', '_self');
      if (selfWin) {{
        try {{ selfWin.close(); }} catch(_) {{}}
      }}
      try {{
        location.replace('about:blank');
        statusEl.textContent = 'ปิดแท็บนี้ได้เลย';
        statusEl.className = 'status warn';
      }} catch(_) {{}}
    }}, 150);
  }}

  copyBtn.addEventListener('click', doCopy);
  closeBtn.addEventListener('click', robustClose);
  doCopy();
}})();
</script>
</body>
</html>"""
    resp = make_response(html, 200)
    resp.headers["Content-Type"] = "text/html; charset=utf-8"
    resp.headers["ngrok-skip-browser-warning"] = "true"
    return resp






def flex_register_success(cid: int):
    return FlexSendMessage(
        alt_text="ลงทะเบียนสำเร็จ",
        contents={
            "type": "bubble",
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "10px",
                "backgroundColor": "#111827",
                "cornerRadius": "12px",
                "spacing": "sm",
                "contents": [
                    {"type": "text", "text": "✅ ลงทะเบียนสำเร็จ", "weight": "bold", "size": "md", "align": "center", "color": "#22C55E"},
                    {"type": "text", "text": f"🎫 ID ของคุณคือ {cid}", "size": "sm", "weight": "bold", "align": "center", "color": "#FACC15"},
                    {"type": "text", "text": "พิมพ์ C เพื่อดูบัตรสมาชิก", "size": "xs", "align": "center", "color": "#9CA3AF"}
                ]
            }
        }
    )


from linebot.models import FlexSendMessage

def flex_summary(st, event=None):
    bets = list(st["bet_index"].values())
    rows = []

    if not bets:
        rows.append({
            "type": "text",
            "text": "❌ ยังไม่มีบิล",
            "size": "md",
            "align": "center",
            "color": "#9CA3AF",
            "weight": "bold"
        })
    else:
        # ===== หัวตาราง =====
        rows.append({
            "type": "box", "layout": "horizontal", "contents": [
                {"type": "text", "text": "👤 ผู้เล่น", "flex": 5, "size": "sm", "weight": "bold", "color": "#F9FAFB"},
                {"type": "text", "text": "🚀 สูง/ต่ำ", "flex": 3, "size": "sm", "align": "center", "weight": "bold", "color": "#F9FAFB"},
                {"type": "text", "text": "💰 ยอดเล่น", "flex": 3, "size": "sm", "align": "end", "weight": "bold", "color": "#F9FAFB"},
            ]
        })
        rows.append({"type": "separator", "margin": "sm", "color": "#6B7280"})

        # ===== รายการบิล =====
        for i, b in enumerate(bets):
            bg_color = "#1E293B"   # ใช้สีเดียวทุกแถว
            name = b["name"]
            if b["side"] == "HI":
                side_display = "✅ สูง"
                side_color = "#22C55E"
            else:
                side_display = "❌ ต่ำ"
                side_color = "#EF4444"

            # กล่องข้อมูลลูกค้า
            rows.append({
                "type": "box",
                "layout": "vertical",
                "contents": [
                    {
                        "type": "box",
                        "layout": "horizontal",
                        "backgroundColor": bg_color,
                        "cornerRadius": "6px",
                        "paddingAll": "6px",
                        "contents": [
                            {"type": "text", "text": name, "flex": 5, "size": "sm", "color": "#E5E7EB"},
                            {"type": "text", "text": side_display, "flex": 3, "size": "sm", "align": "center", "color": side_color},
                            {"type": "text", "text": fmt(b["amount"]), "flex": 3, "size": "sm", "align": "end", "color": "#FACC15"},
                        ]
                    },
                    # ==== เส้นคั่นใต้แต่ละชื่อ ====
                    {"type": "separator", "color": "#334155", "margin": "xs"}
                ]
            })

    # ===== Flex Message =====
    return FlexSendMessage(
        alt_text=f"📋 สรุปการแทง คู่ที่ {st['pairNo']}",
        contents={
            "type": "bubble",
            "styles": {"body": {"backgroundColor": "#111827"}},
            "body": {
                "type": "box",
                "layout": "vertical",
                "paddingAll": "0px",
                "contents": [
                    # ส่วนหัว
                    {
                        "type": "box",
                        "layout": "vertical",
                        "paddingAll": "14px",
                        "backgroundColor": "#22C55E",
                        "contents": [{
                            "type": "text",
                            "text": f"📊 สรุปการแทง รอบ {st['pairNo']} ({len(bets)})",
                            "weight": "bold",
                            "align": "center",
                            "size": "lg",
                            "color": "#FFFFFF"
                        }]
                    },
                    # ส่วนตาราง
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#1E293B",
                        "paddingAll": "12px",
                        "spacing": "sm",
                        "contents": rows
                    },
                    # ส่วนท้าย
                    {
                        "type": "box",
                        "layout": "vertical",
                        "backgroundColor": "#0F172A",
                        "paddingAll": "10px",
                        "contents": [
                            {"type": "text",
                             "text": f"รวมทั้งหมด {len(bets)} บิล",
                             "align": "end",
                             "size": "sm",
                             "color": "#E5E7EB"}
                        ]
                    }
                ]
            }
        }
    )



_admin_ids_lock = threading.RLock()

def is_admin(uid):
    with _admin_ids_lock:
        return uid in ADMIN_IDS

def add_admin(uid):
    with _admin_ids_lock:
        if uid not in ADMIN_IDS:
            ADMIN_IDS.append(uid)

def get_user_by_cid(cid_int):
    with with_users_lock():
        for u in users.values():
            if u["cid"] == cid_int:
                return u
    return None

def register_customer_by_uid(src, target_uid):
    """สมัครสมาชิกให้ target_uid และคืน (user_dict, created_new: bool)"""
    global nextCustomerId
    with with_users_lock():
        if target_uid in users:
            return users[target_uid], False
        name, pic = get_profile_display(src, target_uid)
        users[target_uid] = {
            "uid": target_uid,
            "cid": nextCustomerId,
            "name": name,
            "pictureUrl": pic,
            "credit": 0,
        }
        nextCustomerId += 1
        save_users_persist()
        return users[target_uid], True

def process_credit_command(text, uid):
    if not is_admin(uid):
        return "คำสั่งนี้ใช้ได้เฉพาะแอดมิน"
    m = re.match(r"^@([^\s]+)\s*/\s*(\d+)$", text)
    if not m: return "รูปแบบคำสั่งไม่ถูกต้อง (ตัวอย่าง: @สมชาย/500)"
    target_name, amt = m.group(1), int(m.group(2))

    with with_users_lock():
        target_user = next((u for u in users.values() if u["name"] == target_name), None)
        if not target_user:
            return f"ไม่พบผู้ใช้ {target_name}"
        target_user["credit"] = target_user.get("credit", 0) + amt
        save_users_persist()
        return (f"เติมเครดิต {fmt(amt)} บาท  "
                f"ID : {target_user['cid']}  {target_user['name']}  "
                f"คงเหลือ {fmt(target_user['credit'])} บาท")

def save_score_history_latest(state, round_no, camp, code):
    # ลบผลรอบเดิมออกทั้งหมด
    state["score_history"] = [
        h for h in state.get("score_history", [])
        if h.get("round") != round_no
    ]

    # ใส่ผลล่าสุดเท่านั้น
    state["score_history"].append({
        "round": round_no,
        "camp": camp,
        "code": code,
        "updated_at": datetime.now().isoformat()
    })






# ====== MESSAGE HANDLER ======
@handler.add(MessageEvent, message=TextMessage)
def on_message(event: MessageEvent):
    global nextCustomerId

    if _is_duplicate_event(event):
        return

    uid = event.source.user_id
    gid = getattr(event.source, "group_id", None)
    key = room_key(event.source)
    
    # [FIXED] กำหนด text ที่นี่ครั้งเดียว
    text = (event.message.text or "").strip()

    if not in_group_or_room(event.source):
     return

    # Group allow/deny/ban
    if gid:
        if gid in BANNED_GROUPS or gid in DENY_GROUP_IDS:
            return
        if not is_allowed_group(gid):
            return
        if _locked_group(gid) and not is_admin(uid):
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("ระบบ: กลุ่มกำลังล็อกดาวน์ชั่วคราว ติดต่อแอดมินเพื่อปลดล็อก"))
            return

    # user ban/mute
    if uid in BANNED_UIDS:
        return
    if MUTED_UNTIL.get(uid, 0) > _now():
        if not _notice_throttled(uid):
            safe_reply(event, TextSendMessage("ระบบ: คุณถูกจำกัดการส่งข้อความชั่วคราว (anti-spam)"))
        return

    # rate limit room/user
    if not rl.allow(f"room:{key}", RL_ROOM_BURST_LIMIT, RL_ROOM_BURST_PERIOD):
        return
    if not rl.allow(f"uid:{uid}:burst", RL_UID_BURST_LIMIT, RL_UID_BURST_PERIOD) or \
       not rl.allow(f"uid:{uid}:day", RL_UID_DAILY_LIMIT, RL_UID_DAILY_PERIOD):
        STRIKES[uid] = STRIKES.get(uid, 0) + 1
        if STRIKES[uid] >= ABUSE_STRIKE_TO_MUTE:
            MUTED_UNTIL[uid] = _now() + MUTE_SECONDS_DEFAULT
            STRIKES[uid] = 0
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage(f"ระบบ: มิวท์ {MUTE_SECONDS_DEFAULT} วินาที เนื่องจากข้อความถี่ผิดปกติ"))
        else:
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("ระบบ: ข้อความถี่เกินกำหนด ช่วยเว้นช่วงหน่อยนะ"))
        return

    # cache for unsend monitor
    msgCache[event.message.id] = {"text": (event.message.text or ""), "ts": time.time()}
    now = time.time()
    if len(msgCache) > 4000:
        for k, v in list(msgCache.items()):
            if now - v["ts"] > CACHE_TTL_SEC: msgCache.pop(k, None)

    # [FIXED] รวบรวมตรรกะทั้งหมดที่เกี่ยวข้องกับ Room State (st) ไว้ใน Lock เดียว
    with with_rooms_lock():
        if key not in rooms:
            rooms[key] = start_state()
        st = rooms[key]

        # [FIXED] ตรวจสอบ Cooldown ภายใน Lock
        if not is_admin(uid):
            whitelist = {"add", "c", "กต", "บช", "x", "xx", "x*", "ถอน", "วิธีเล่น", "วิธีการเล่น", "เล่น"}
            text_preview = text.lower()
            head = text_preview.split(" ", 1)[0] if text_preview else ""
            scope_key = f"{uid}:{key}"

            if head not in whitelist:
                if not _should_reply_now(scope_key):
                    # เงียบ: ไม่ตอบและไม่ประมวลผลคำสั่ง เพื่อกันรัวจริง ๆ
                    return
        # --- คำสั่งล้างกำไรทั้งหมด (เฉพาะ Admin) ---
        if R_CLEAR_PROFIT.match(text):
            if uid not in ADMIN_IDS:
                return  # ไม่ใช่แอดมินไม่ต้องตอบโต้
            
            with with_rooms_lock(): # ใช้ lock เพื่อความปลอดภัยของข้อมูล
                METRICS["profit_sum"] = 0
                METRICS["loss_sum"] = 0
                
            now = datetime.now().strftime("%H:%M:%S")
            reply_msg = (
                "✅ รีเซ็ตข้อมูลกำไรทั้งหมดเรียบร้อยแล้ว\n"
                f"🕒 เวลา: {now}\n"
                "💰 ยอดคงเหลือปัจจุบัน: 0"
            )
            safe_reply(event, TextSendMessage(text=reply_msg))
            return
        


        # ===== วิธีเล่น / เล่นยังไง / เล่นไง / วิธีการเล่น / เล่นแบบใด =====
        t = text.strip()
        t2 = " ".join(t.split())  # บีบช่องว่างซ้ำให้เหลือ 1

        if t in PLAY_HELP_COMMANDS or t2 in PLAY_HELP_COMMANDS:
            safe_reply(event, TextSendMessage(PLAY_HELP_TEXT))
            return

        # กรณีผู้ใช้พิมพ์แบบมีเว้นวรรค เช่น "เล่น ยังไง"
        if t2.startswith("เล่น") and ("ยังไง" in t2 or "ไง" in t2 or "แบบใด" in t2):
            safe_reply(event, TextSendMessage(PLAY_HELP_TEXT))
            return

        if t2.startswith("วิธี") and ("เล่น" in t2):
            safe_reply(event, TextSendMessage(PLAY_HELP_TEXT))
            return
    

        # ===== Admin: add/del with @mention or Uxxxxxxxx + optional PIN =====
        # ตัวอย่างโค้ดส่วนที่ควรจะเป็นใน on_message
        if R_ADMIN_ADD.match(text):
            if uid not in ADMIN_IDS: # ตรวจสอบว่าเป็นแอดมินตัวจริงสั่งหรือไม่
                return
                
            target_uid = first_mentioned_uid(event) # ดึง UID จากคนที่ถูกแท็ก
            if target_uid:
                if target_uid not in ADMIN_IDS:
                    ADMIN_IDS.append(target_uid)
                    # โค้ดสำหรับบันทึกลง .env หรือฐานข้อมูล (ถ้ามี)
                    safe_reply(event, TextSendMessage(text="✅ เพิ่มแอดมินใหม่เรียบร้อยแล้ว"))
                else:
                    safe_reply(event, TextSendMessage(text="ℹ️ ผู้ใช้นี้เป็นแอดมินอยู่แล้ว"))
            else:
                safe_reply(event, TextSendMessage(text="❌ กรุณาแท็กชื่อผู้ใช้ที่ต้องการเพิ่ม"))
            return

        if R_ADMIN_DEL.match(text):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
            target_uid = first_mentioned_uid(event)
            if not target_uid:
                m = re.match(r"^admin\s+del\s+([Uu][0-9a-f]{32})(.*)$", text)
                if m: target_uid = m.group(1)
            if not target_uid:
                safe_reply(event, TextSendMessage("โปรดแท็กผู้ใช้ หรือระบุ userId ที่ขึ้นต้นด้วย U...")); return
            pin = _admin_auth_pin(text)
            if ADMIN_PIN and not compare_digest(pin, ADMIN_PIN):
                safe_reply(event, TextSendMessage("PIN ไม่ถูกต้อง")); return
            try:
                ADMIN_IDS.remove(target_uid)
                safe_reply(event, TextSendMessage("ลบแอดมินสำเร็จ ✓"))
            except ValueError:
                safe_reply(event, TextSendMessage("ไม่พบไอดีนี้ในรายชื่อแอดมิน"))
            return
        
        # ===== เช็คแอดมิน: แสดงรายชื่อแอดมินทั้งหมด (เฉพาะแอดมิน) =====
        if re.match(r"^เช็คแอดมิน$", text.strip()):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
            lines = [f"👑 รายชื่อแอดมินทั้งหมด ({len(ADMIN_IDS)} คน)", "─" * 28]
            for i, admin_uid in enumerate(ADMIN_IDS, 1):
                try:
                    if gid:
                        p = line_bot_api.get_group_member_profile(gid, admin_uid)
                        admin_name = p.display_name
                    else:
                        p = line_bot_api.get_profile(admin_uid)
                        admin_name = p.display_name
                except Exception:
                    admin_name = "(ดึงชื่อไม่ได้)"
                marker = " ⭐" if admin_uid == uid else ""
                lines.append(f"{i}. {admin_name}{marker}")
                lines.append(f"   └ {admin_uid}")
            safe_reply(event, TextSendMessage("\n".join(lines))); return

        # ===== Group ID (gid) =====
        if re.match(r"^gid\b", text, re.IGNORECASE):
            if not gid:
                safe_reply(event, TextSendMessage("ใช้คำสั่งนี้ได้เฉพาะในกลุ่ม/ห้อง"))
                return
            safe_reply(event, TextSendMessage(f"GID ของกลุ่มนี้: {gid}"))
            return


        # ==== ดูตารางรายการเดิมพัน (cm — เฉพาะกลุ่มหลังบ้าน) ====
        if text.lower() == "cm":
            if not gid or not is_backoffice_group_id(gid):
                return
            snapshot = [(rk, stx.copy()) for rk, stx in rooms.items()]  # shallow ก็พอ
            all_bets, total_hi, total_lo = [], 0, 0
            hi_count, lo_count = 0, 0
            active_round_labels = []
            seen_round_labels = set()

            for rk, stx in snapshot:
                pair_no = stx.get("pairNo", 0)
                camp_name = current_camp(stx)
                round_label = f"{camp_name} • รอบ {pair_no}"
                if pair_no and round_label not in seen_round_labels:
                    active_round_labels.append(round_label)
                    seen_round_labels.add(round_label)

                for b in stx.get("bet_index", {}).values():
                    all_bets.append({
                        "name": b["name"],
                        "side": b["side"],
                        "amount": b["amount"],
                        "pairNo": pair_no,
                        "camp": camp_name,
                    })
                    if b["side"] == "HI":
                        total_hi += b["amount"]
                        hi_count += 1
                    else:
                        total_lo += b["amount"]
                        lo_count += 1

            if not all_bets:
                safe_reply(event, TextSendMessage("(ยังไม่มีบิลในระบบ)"))
                return

            title_text = "ตารางบิลทั้งหมด"
            if len(active_round_labels) == 1:
                title_text = f"ตารางบิลทั้งหมด ({active_round_labels[0]})"
            elif len(active_round_labels) > 1:
                title_text = "ตารางบิลทั้งหมด (หลายค่าย/หลายรอบ)"

            rows = [
                {"type":"box","layout":"vertical","spacing":"xs","contents":[
                    {"type":"text","text":title_text,"weight":"bold","align":"center","size":"md","wrap":True},
                    {"type":"text","text":f"จำนวนบิลสูง {hi_count} บิล • จำนวนบิลต่ำ {lo_count} บิล","size":"sm","align":"center","weight":"bold","wrap":True,
                     "color":"#1565C0" if lo_count == 0 else "#374151"},
                ]},
                {"type":"separator","margin":"md"},
            ]

            if len(active_round_labels) > 1:
                rows.append({
                    "type":"box","layout":"vertical","spacing":"xs","contents":[
                        {"type":"text","text":"ค่าย / รอบที่เปิดอยู่","size":"sm","weight":"bold","color":"#374151"},
                        *[
                            {"type":"text","text":f"• {label}","size":"xs","wrap":True,"color":"#6B7280"}
                            for label in active_round_labels[:8]
                        ]
                    ]
                })
                rows.append({"type":"separator","margin":"md"})

            rows.extend([
                {"type":"box","layout":"horizontal","spacing":"sm","contents":[
                    {"type":"text","text":"ผู้เล่น","flex":5,"size":"xs","weight":"bold","wrap":True},
                    {"type":"text","text":"จำนวนเดิมพัน/กี่บาท","flex":5,"size":"xs","align":"center","weight":"bold","wrap":True},
                    {"type":"text","text":"รอบ","flex":2,"size":"xs","align":"center","weight":"bold","wrap":True},
                ]},
                {"type":"separator","margin":"sm"},
            ])

            def _short_name(name, limit=14):
                name = (name or "").strip()
                if len(name) <= limit:
                    return name
                return name[:limit-1].rstrip() + "…"

            sorted_bets = sorted(
                all_bets,
                key=lambda x: (
                    -(x.get("amount", 0) or 0),
                    x.get("pairNo", 0),
                    x.get("camp", "") or "",
                    x.get("name", "") or "",
                )
            )

            for b in sorted_bets:
                bet_text = f'{"สูง" if b["side"]=="HI" else "ต่ำ"} {fmt(b["amount"])} บาท'
                rows.append({"type":"box","layout":"horizontal","spacing":"sm","contents":[
                    {"type":"text","text":_short_name(b["name"]),"flex":5,"size":"xs","wrap":True},
                    {"type":"text","text":bet_text,
                     "flex":5,"size":"xs","align":"center",
                     "color":"#1565C0" if b["side"]=="HI" else "#E53935","wrap":True},
                    {"type":"text","text":str(b["pairNo"]),"flex":2,"size":"xs","align":"center","wrap":True},
                ]})
            rows.append({"type":"separator","margin":"md"})
            rows.append({"type":"text","text":f"รวมสูง: {fmt(total_hi)} บาท ({hi_count} บิล)","size":"sm","align":"end","weight":"bold","color":"#1565C0"})
            rows.append({"type":"text","text":f"รวมต่ำ: {fmt(total_lo)} บาท ({lo_count} บิล)","size":"sm","align":"end","weight":"bold","color":"#E53935"})
            safe_reply(event, FlexSendMessage(
                alt_text="ตารางบิลทั้งหมด",
                contents={"type":"bubble","size":"mega","body":{"type":"box","layout":"vertical","spacing":"sm","paddingAll":"12px","contents":rows}}
            ))
            return

        # ===== Moderator: ban/mute/unban/unmute =====
        m_cmd = re.match(r"^(ban|unban|mute|unmute)\b(?:\s+(.*))?$", text, re.IGNORECASE)
        if m_cmd:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
            cmd = m_cmd.group(1).lower()
            args = (m_cmd.group(2) or "").strip()
            target_uid = first_mentioned_uid(event)
            sec = None
            if not target_uid:
                m_uid = re.match(r"^(U[0-9a-f]{32})\b(?:\s+(\d+))?$", args, re.IGNORECASE)
                if m_uid:
                    target_uid = m_uid.group(1)
                    sec = int(m_uid.group(2) or MUTE_SECONDS_DEFAULT) if cmd == "mute" else None
                else:
                    m_at = re.match(r"^@(.+?)(?:\s+(\d+))?$", args)
                    if m_at:
                        safe_reply(event, TextSendMessage("โปรดแท็กผู้ใช้จาก UI ของ LINE (ชื่อเป็นลิงก์สีน้ำเงิน)"))
                        return
            if not target_uid:
                safe_reply(event, TextSendMessage("รูปแบบ: mute @ผู้ใช้ [วินาที] / unmute @ผู้ใช้ / ban @ผู้ใช้ / unban @ผู้ใช้"))
                return
            if cmd == "mute":
                if sec is None:
                    m_sec = re.search(r"\b(\d+)\b$", args) if args else None
                    sec = int(m_sec.group(1)) if m_sec else MUTE_SECONDS_DEFAULT
                MUTED_UNTIL[target_uid] = _now() + max(1, sec); safe_reply(event, TextSendMessage(f"มิวท์ {sec} วินาทีแล้ว")); return
            if cmd == "unmute":
                MUTED_UNTIL.pop(target_uid, None); safe_reply(event, TextSendMessage("ปลดมิวท์แล้ว")); return
            if cmd == "ban":
                BANNED_UIDS.add(target_uid); safe_reply(event, TextSendMessage("แบนผู้ใช้แล้ว")); return
            if cmd == "unban":
                BANNED_UIDS.discard(target_uid); safe_reply(event, TextSendMessage("ปลดแบนแล้ว")); return

        # ===== Admin/User: เช็ค UID =====
        if re.match(r"^uid\b", text, re.IGNORECASE):
            target_uid = first_mentioned_uid(event)
            # ถ้าไม่แท็กใคร: โชว์ UID ของตัวเอง (ไม่ต้องเป็นแอดมิน)
            if not target_uid or target_uid == uid:
                name, _ = get_profile_display(event.source, uid)
                safe_reply(event, TextSendMessage(f"UID ของคุณ ({name}): {uid}"))
                return
            # ถ้าจะดู UID คนอื่น ต้องเป็นแอดมิน
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("เฉพาะแอดมินเท่านั้นที่ดู UID คนอื่นได้")); 
                return
            name, _ = get_profile_display(event.source, target_uid)
            safe_reply(event, TextSendMessage(f"UID ของ {name}: {target_uid}"))
            return

                # ===== Backoffice (FREE): ดูสรุป/กำไรล่าสุด =====
        # ใช้ในกลุ่มหลังบ้านเท่านั้น (ไม่ต้อง push ลดโควต้า)
        if gid and gid in BACKOFFICE_GROUP_IDS and re.match(r"^(?:กำไรล่าสุด|ยอด|lastprofit|last)\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); 
                return
            p = load_last_settle()
            if not p:
                safe_reply(event, TextSendMessage("ยังไม่มีสรุปผลล่าสุดในระบบ")); 
                return
            safe_reply(event, TextSendMessage(settle_payload_to_text(p)))
            return

        # ===== Helper: คืน escrow ทุกคนในห้อง =====
        def _refund_all_escrow_to_users(st):
            refunded_map = {}  # uid -> amount
            for tuid, esc_amt in list(st.get("escrow", {}).items()):
                if esc_amt > 0 and tuid in users:
                    users[tuid]["credit"] = users[tuid].get("credit", 0) + esc_amt
                    refunded_map[tuid] = esc_amt
            st["escrow"].clear()
            return refunded_map
        
        # -

        text = (event.message.text or "").strip()

        # ====== GET GROUP ID ======
        if R_GETID.match(text):
            src = event.source

            group_id = getattr(src, "group_id", None)
            room_id = getattr(src, "room_id", None)

            if group_id:
                msg = f"Group ID: {group_id}"
            elif room_id:
                msg = f"Room ID: {room_id}"
            else:
                msg = "❌ คำสั่งนี้ใช้ได้เฉพาะในกลุ่มหรือห้องเท่านั้น"

            safe_reply(event, TextSendMessage(text=msg))
            return


        # ==== CLEAR / RESET ====
        if re.match(r"^(clear|reset)\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            total_refund_sum = 0
            total_refund_users = 0

            with with_users_lock(): # [FIXED] ใช้แค่ with_users_lock() เพราะ with_rooms_lock() คลุมอยู่แล้ว
                if re.search(r"\ball\b", text, re.IGNORECASE):
                    # เคลียร์ทั้งระบบ — คืน escrow ทุกห้อง
                    for rk in list(rooms.keys()):
                        stx = rooms[rk]
                        refunded_map = _refund_all_escrow_to_users(stx)
                        total_refund_sum += sum(refunded_map.values())
                        total_refund_users += len(refunded_map)
                        rooms[rk] = start_state()

                    # 👉 เพิ่มบรรทัดนี้: รีเซ็ตกำไรสะสม
                    METRICS["profit_sum"] = 0
                    METRICS["loss_sum"] = 0

                    msg = "เคลียร์ทั้งระบบ (รอบ/ทุน) สำเร็จ ✓"
                else:
                    # เคลียร์เฉพาะห้องนี้ — คืน escrow ห้องนี้
                    stx = rooms.get(key) or start_state()
                    refunded_map = _refund_all_escrow_to_users(stx)
                    total_refund_sum += sum(refunded_map.values())
                    total_refund_users += len(refunded_map)
                    rooms[key] = start_state()
                    msg = "เคลียร์ห้องนี้ (รอบ/ทุน) สำเร็จ ✓"

                save_users_persist()

            msg += f"\nคืนเครดิต {fmt(total_refund_sum)} บาท ให้ {total_refund_users} คน"
            safe_reply(event, TextSendMessage(msg)); return

        # ==== เติม/ลบทุน+เครดิต แบบ $+ <cid> <amt> / $- <cid> <amt> ====
        m_add = re.match(r"^\$\+\s*(\d+)\s+(\d+)$", text)
        m_sub = re.match(r"^\$-\s*(\d+)\s+(\d+)$", text)
        if m_add or m_sub:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            cid = int((m_add or m_sub).group(1))
            amt = int((m_add or m_sub).group(2))
            with with_users_lock(): # [FIXED] ใช้แค่ with_users_lock() เพราะ with_rooms_lock() คลุมอยู่แล้ว
                target = get_user_by_cid(cid)
                if not target:
                    safe_reply(event, TextSendMessage(f"ไม่พบ ID {cid}")); return
                tuid = target["uid"]
                # [FIXED] เข้าถึง rooms[key] ได้โดยตรง เพราะ with_rooms_lock() คลุมอยู่
                fund_before = rooms[key]["funds"].get(tuid, 0) 
                credit_before = target.get("credit", 0)

                if m_add:
                    target["credit"] = credit_before + amt
                    rooms[key]["funds"][tuid] = fund_before + amt
                    msg = f"✅เติมเครดิต {fmt(amt)} บาท  ID : {cid}  {target['name']}  คงเหลือ {fmt(target['credit'])} บาท"
                else:
                    target["credit"] = max(credit_before - amt, 0)
                    rooms[key]["funds"][tuid] = max(fund_before - amt, 0)
                    msg = f"✅ลบเครดิต {fmt(amt)} บาท  ID : {cid}  {target['name']}  คงเหลือ {fmt(target['credit'])} บาท"

                save_users_persist()
            safe_reply(event, TextSendMessage(msg)); return
        



        m_del = R_DEL_USER.match(text)
        if m_del:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน"))
                return

            cid = int(m_del.group(1))

            with with_users_lock():
                target_uid = None
                target = None

                for u in users.values():
                    if u["cid"] == cid:
                        target_uid = u["uid"]
                        target = u
                        break

                if not target:
                    safe_reply(event, TextSendMessage(f"ไม่พบ ID {cid}"))
                    return

                if has_active_bet(target_uid):
                    safe_reply(event, TextSendMessage("❌ ลบไม่ได้: ลูกค้ามีบิลค้างอยู่"))
                    return

                users.pop(target_uid)
                save_users_persist()

            safe_reply(event, TextSendMessage(f"✅ ลบลูกค้า ID {cid} สำเร็จ"))
            return        



        # ===== เติมเครดิตรูปแบบ @ชื่อ/จำนวน =====
        if text.startswith("@") and "/" in text:
            msg = process_credit_command(text, uid)
            safe_reply(event, TextSendMessage(msg)); return

        # ==== ลูกค้า: สมัคร/การ์ด/บัญชี/กต ====
        if re.match(r"^add\b", text, re.IGNORECASE):
            target_uid = first_mentioned_uid(event)

            # แอดมินสมัครสมาชิกแทนลูกค้าด้วยการแท็กชื่อ
            if target_uid and target_uid != uid:
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("เฉพาะแอดมินเท่านั้นที่สมัครสมาชิกแทนลูกค้าได้"))
                    return
                target_user, created = register_customer_by_uid(event.source, target_uid)
                if created:
                    safe_reply(event, TextSendMessage(
                        f"✅ สมัครสมาชิกให้ {target_user['name']} สำเร็จ\n🎫 ID: {target_user['cid']}\nพิมพ์ C @ชื่อไลน์ เพื่อดูบัตรสมาชิก"
                    ))
                else:
                    safe_reply(event, TextSendMessage(
                        f"ℹ️ {target_user['name']} มี ID อยู่แล้ว: {target_user['cid']}"
                    ))
                return

            # สมัครสมาชิกด้วยตัวเอง
            if text.lower() == "add":
                target_user, created = register_customer_by_uid(event.source, uid)
                if not created:
                    safe_reply(event, TextSendMessage(f"คุณมี ID แล้ว: {target_user['cid']}"))
                    return
                safe_reply(event, flex_register_success(target_user["cid"])); return

        # ลูกค้าพิมพ์ "ถอน" ที่ไหนก็ได้ในข้อความ → แสดงการ์ด C
        if "ถอน" in text:
            u = users.get(uid)
            if not u:
                safe_reply(event, TextSendMessage("พิมพ์ add เพื่อรับไอดีก่อน"))
                return
            safe_reply(event, flex_customer_card(st, u)); return




        if re.match(r"^c\b", text, re.IGNORECASE):
            target_uid = first_mentioned_uid(event)

            # แอดมินดูบัตร/ID ของลูกค้าที่ถูกแท็ก
            if target_uid and target_uid != uid:
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("เฉพาะแอดมินเท่านั้นที่ดูข้อมูลลูกค้าคนอื่นได้"))
                    return
                u = users.get(target_uid)
                if not u:
                    safe_reply(event, TextSendMessage("ลูกค้ายังไม่ได้สมัครสมาชิก\nให้แอดมินพิมพ์ add @ชื่อไลน์ ก่อน"))
                    return
                safe_reply(event, flex_customer_card(st, u)); return

            # ลูกค้าดูบัตรของตัวเอง
            if text.lower() == "c":
                u = users.get(uid)
                if not u:
                    safe_reply(event, TextSendMessage("พิมพ์ add เพื่อรับไอดีก่อน"))
                    return
                safe_reply(event, flex_customer_card(st, u)); return

        if text.strip().lower() in ("บช", "บัญชี", "เลขบัญชี"):
            # ส่ง "ข้อความอย่างเดียว" ไม่ส่งปุ่ม Flex
            safe_reply(event, text_bank())
            return

        if text == "กต":
            safe_reply(event, TextSendMessage(rules_text())); return

        # ==== ประกาศราคาแบบ "ส่งข้อความอย่างเดียว" (ไม่เปิดรอบ) ====
        # ==== ประกาศราคาแบบ "ส่งข้อความอย่างเดียว" (ไม่เปิดรอบ) ====
        m_announce = R_ANN.match(text)

        if m_announce and not re.match(r"^\s*o\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งประกาศราคานี้ใช้ได้เฉพาะแอดมิน"))
                return

            camp   = m_announce.group(1).strip()
            hi_min = int(m_announce.group(2)); hi_max = int(m_announce.group(3))
            lo_min = int(m_announce.group(4)); lo_max = int(m_announce.group(5))

            safe_reply(event, flex_open_with_prices(
                st["pairNo"], camp, hi_min, hi_max, lo_min, lo_max
            )); return

        # ==== เปิดรอบ (O) ====
        if re.match(r"^\s*o\b", text, re.IGNORECASE):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            if st["phase"] != "NONE":
                phase_th = "เปิดอยู่" if st["phase"] == "OPEN" else "พักรอบอยู่"
                safe_reply(
                    event,
                    TextSendMessage(
                        f"❌ เปิดรอบใหม่ไม่ได้: ยังมีรอบค้างอยู่ ({phase_th})\n"
                        f"ขั้นตอนที่ถูกต้อง: กด E เพื่อพัก → พิมพ์ s<รหัสผล> → /y เพื่อยืนยันผล\n"
                        f"เมื่อสรุปรอบเสร็จแล้ว จึงค่อยเปิดรอบใหม่ได้"
                    )
                ); return

            m = R_O_ANN.match(text)
            if m:
                camp = m.group(1).strip()
                hi_min, hi_max = int(m.group(2)), int(m.group(3))
                lo_min, lo_max = int(m.group(4)), int(m.group(5))

                st["pairNo"] += 1
                st["totals"] = {"HI": 0, "LO": 0}
                st["bet_index"] = {}
                st["pendingCode"] = None
                st["escrow"] = {}
                st["phase"] = "OPEN"
                st["price"] = {"camp": camp, "HI": (hi_min, hi_max), "LO": (lo_min, lo_max)}

                safe_reply(event, flex_open_with_prices(
                    st["pairNo"], camp, hi_min, hi_max, lo_min, lo_max
                )); return
            else:
                note = (re.match(r"^\s*o\b\s*(.*)$", text, re.IGNORECASE).group(1) or "").strip()

                st["pairNo"] += 1
                st["totals"] = {"HI": 0, "LO": 0}
                st["bet_index"] = {}
                st["pendingCode"] = None
                st["escrow"] = {}
                st["phase"] = "OPEN"
                st["note"] = note or st.get("note")

                safe_reply(event, flex_open(st["pairNo"], st.get("note"))); return

        t = text.upper()
        if t == "E":
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน"))
                return
            if st["phase"] != "OPEN":
                safe_reply(event, TextSendMessage("ไม่มีรอบที่เปิดอยู่"))
                return
            st["phase"] = "PAUSED"
            camp = current_camp(st)

            # ส่ง 2 ข้อความ: (1) การ์ดพักรอบ (2) สรุปบิล
            try:
                safe_reply(event, [
                    flex_pause_notice(st["pairNo"], camp),
                    flex_summary(st, event)
                ])
            except Exception as e:
                # กันตก ถ้ามีปัญหา Flex จะยังตอบเป็นข้อความได้
                safe_reply(event, TextSendMessage(f"พักรอบชั่วคราว #{st['pairNo']} — ค่าย {camp}"))
            return

        
        if t in ("R", "RESUME"):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); 
                return
            if st["phase"] != "PAUSED":
                safe_reply(event, TextSendMessage("ไม่มีรอบที่พักอยู่")); return
            st["phase"] = "OPEN"
            camp = current_camp(st)
            safe_reply(event, flex_resume(st["pairNo"], camp)); return




        

        
            # ==== ปิดรอบ (ข้อความไทย: ปิดรอบ / หยุดแทง / ปิด) ====
        if R_CLOSE_TH.match(text.strip()):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            if st["phase"] == "NONE":
                # ไม่มีรอบเปิดอยู่
                safe_reply(event, TextSendMessage("ไม่มีรอบที่เปิดอยู่")); return

            # เปลี่ยนสถานะเป็นพักรอบ (ไม่รับบิลต่อ)
            st["phase"] = "PAUSED"

            # ส่งการ์ดแจ้งหยุดแทง + สรุปบิลรอบนี้
            safe_reply(event, [
                flex_close_notice(st["pairNo"]),
                flex_summary(st, event)
            ]); return


        # ==== ตั้งผล s... ====
        sm = re.match(r"^[sS]\s*(.+)$", text)
        if sm:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
            if st["phase"] != "PAUSED":
                safe_reply(event, TextSendMessage("❌ ต้องกด E (พักรอบ) ก่อนจึงจะตั้งผลได้")); return
            st["pendingCode"] = normalize_result_code(sm.group(1))
            safe_reply(event, flex_result_preview(st["pendingCode"], st["pairNo"])); return

        # ==== ยืนยันผล: T/ หรือ /y ====
        if R_YCONFIRM.match(text.strip()):
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
            if st["phase"] != "PAUSED":
                safe_reply(event, TextSendMessage("❌ ต้องกด E (พักรอบ) ก่อนจึงจะสามารถสรุปผลได้")); return

            code = normalize_result_code(st["pendingCode"] or "จ")
            if code not in RESULT_DEFS:
                safe_reply(event, TextSendMessage("❌ ไม่สามารถยืนยันผลได้: โค้ดผลไม่ถูกต้อง")); return
            

            # ================= [เริ่มส่วนที่เพิ่ม] =================
            # 1. บันทึกประวัติลง State
            current_camp_name = current_camp(st)
            if "score_history" not in st: 
                st["score_history"] = []
                
            st["score_history"].append({
                "round": st["pairNo"],
                "camp": current_camp_name,
                "code": code
            })

            # === [เพิ่มใหม่] บันทึก snapshot เครดิต + สถานะห้อง ก่อนสรุปผล ===
            try:
                backup_path = os.path.join(DATA_DIR, f"backup_round_{st['pairNo']}.json")
                with with_users_lock(): # [FIXED] ใช้แค่ with_users_lock()
                    snapshot = {
                        "round": st["pairNo"],
                        "users": users,
                        "room_state": st.copy(),   # ✅ st อยู่ใน with_rooms_lock() อยู่แล้ว
                        "metrics": METRICS.copy(), 
                    }
                    _atomic_write_json(backup_path, snapshot)
                app.logger.info(f"[Backup] บันทึกเครดิตก่อนสรุปผล รอบ {st['pairNo']} สำเร็จ")
            except Exception as e:
                app.logger.warning(f"[Backup] ไม่สามารถบันทึก snapshot รอบ {st['pairNo']}: {e}")
            # === [จบส่วนเพิ่มใหม่] ===


            # คำนวณยอด และคืนเครดิตให้ผู้เล่น
            sum_stake = sum(b["amount"] for b in st["bet_index"].values())
            rows, footer = settle_by_code(st, code)

            with with_users_lock():
                for r in rows:
                    u = users.get(r["uid"])
                    if u:
                        u["credit"] = max(u.get("credit", 0) + r["payout"], 0)
                save_users_persist()

            # ล้าง state ห้อง
            st["phase"] = "NONE"
            st["pendingCode"] = None
            st["bet_index"].clear()
            st["totals"] = {"HI": 0, "LO": 0}
            st["escrow"].clear()

            sum_payout = sum(r["payout"] for r in rows)
            profit = sum_stake - sum_payout
            if profit >= 0:
                METRICS["profit_sum"] += profit
            else:
                METRICS["loss_sum"] += (-profit)

            accum_now = {"profit_sum": METRICS["profit_sum"], "loss_sum": METRICS["loss_sum"], "net": net_profit()}
            balance_map = {r["uid"]: users.get(r["uid"], {}).get("credit", 0) for r in rows}
            # 1. ดึงชื่อค่ายมารอไว้
            current_camp_name = current_camp(st)

            # [FREE] เก็บสรุปล่าสุดไว้ให้หลังบ้านเรียกดูได้ (ไม่ต้อง push = ประหยัดโควต้า)
            try:
                rows_payload = []
                for r in rows:
                    rr = dict(r)
                    rr["name"] = users.get(r.get("uid"), {}).get("name")
                    rows_payload.append(rr)

                save_last_settle({
                    "round": st["pairNo"],
                    "camp_name": current_camp_name,
                    "code": code,
                    "profit": profit,
                    "accum": accum_now,
                    "rows": rows_payload,
                    "footer": footer,
                    "ts": _now(),
                    "ts_iso": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                })
            except Exception:
                app.logger.exception("build/save last_settle failed")

            # 2. ส่งให้ห้องลูกค้า (แสดงชื่อค่ายด้วย)
            safe_reply(event, [
                flex_settle(st["pairNo"], rows, footer,
                            show_profit=False,
                            balance_map=balance_map,
                            camp_name=current_camp_name),
                flex_scoreboard(st["score_history"])
            ]);

            # 3) หลังบ้านแบบฟรี (แนะนำ): ให้พิมพ์ "กำไรล่าสุด" ในกลุ่มหลังบ้านเพื่อดึงผลล่าสุด
            #    * ถ้าจำเป็นต้องส่งอัตโนมัติจริง ๆ ให้ตั้ง env: BACKOFFICE_PUSH_ENABLED=1
            if os.getenv("BACKOFFICE_PUSH_ENABLED", "0") == "1":
                p = load_last_settle()
                if p:
                    msg = TextSendMessage(settle_payload_to_text(p))
                    # ส่งแค่ 1 กลุ่มแรก เพื่อลดโควต้า (ปรับได้ถ้าต้องการ)
                    bo_targets = BACKOFFICE_GROUP_IDS[:1]
                    for gid_to in bo_targets:
                        safe_push(gid_to, msg, label="backoffice_text")

            return
        # ==== ย้อนผล (Rollback) ====
        m_rollback = re.match(r"^(?:ย้อนผล|rollback)\s*(\d+)$", text.strip(), re.IGNORECASE)
        if m_rollback:
            if not is_admin(uid):
                safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return

            round_no = int(m_rollback.group(1))
            backup_file = os.path.join(DATA_DIR, f"backup_round_{round_no}.json")
            if not os.path.exists(backup_file):
                safe_reply(event, TextSendMessage(f"❌ ไม่พบข้อมูลสำรองของรอบ {round_no}")); return

            with open(backup_file, "rb") as f:
                data = _loads_bytes(f.read())

            # ✅ คืนเครดิตทั้งหมด
            with with_users_lock(): # [FIXED] ใช้แค่ with_users_lock()
                users.clear()
                users.update(data["users"])
            save_users_persist()

            # ✅ คืนสถานะห้อง (บิล, ยอดรวม ฯลฯ)
            # st อยู่ภายใต้ with_rooms_lock() อยู่แล้ว
            st.update(data.get("room_state", {}))
            st["phase"] = "PAUSED"

            # ✅ คืนค่ากำไรสะสม (METRICS)
            if "metrics" in data:
                METRICS.clear()
                METRICS.update(data["metrics"])

            safe_reply(event, TextSendMessage(
                f"✅ ย้อนเครดิตและข้อมูลรอบ {round_no} สำเร็จแล้ว\nพร้อมตั้งผลใหม่ได้เลย"
            )); return


        if text.strip().lower() == "call":
            if not gid or not is_backoffice_group_id(gid):
                return

            with with_users_lock():
                table = [u for u in users.values() if int(u.get("credit", 0) or 0) > 0]

            if not table:
                safe_reply(event, TextSendMessage("ยังไม่มีลูกค้าที่มีเครดิต"))
                return

            table = sorted(table, key=lambda x: (-int(x.get("credit", 0) or 0), int(x.get("cid", 0) or 0)))
            table = table[:100]

            msg = format_user_table(table)

            safe_reply(event, TextSendMessage(msg))
            return


        # ==== ยกเลิกบิล ====
        m_cancel_by_cid = re.match(r"^x\s+(\d+)$", text.strip(), re.IGNORECASE)
        # เช็คว่าเป็นคำสั่งยกเลิกหรือไม่
        if text.strip().lower() in ("xx", "x*") or m_cancel_by_cid or text.strip().upper() == "X":
            if st["phase"] == "NONE":
                safe_reply(event, TextSendMessage("ยกเลิกไม่ได้: รอบนี้สรุปจบแล้ว")); return

            # แอดมินยกเลิกทั้งหมด
            if text.strip().lower() in ("xx", "x*"):
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
                n = len(st["bet_index"])
                # คืน escrow ทุกคน
                with with_users_lock():
                    for tuid, esc_amt in list(st["escrow"].items()):
                        if esc_amt > 0 and tuid in users:
                            users[tuid]["credit"] = users[tuid].get("credit", 0) + esc_amt
                    st["escrow"].clear()
                    st["bet_index"].clear()
                    st["totals"] = {"HI": 0, "LO": 0}
                    save_users_persist()
                extra = " (กำลังพักรอบ)" if st["phase"] == "PAUSED" else ""
                safe_reply(event, TextSendMessage(f"ยกเลิกบิลทั้งหมดสำเร็จ{extra} ({n} บิล)")); return

            # แอดมินยกเลิกตาม ID ลูกค้า
            if m_cancel_by_cid:
                if not is_admin(uid):
                    safe_reply(event, TextSendMessage("คำสั่งนี้ใช้ได้เฉพาะแอดมิน")); return
                cid = int(m_cancel_by_cid.group(1))
                with with_users_lock():
                    target = get_user_by_cid(cid)
                    if not target:
                        safe_reply(event, TextSendMessage(f"ไม่พบ ID {cid}")); return
                    tuid = target["uid"]
                    bet = st["bet_index"].pop(tuid, None)
                    if not bet:
                        safe_reply(event, TextSendMessage(f"ID {cid} ไม่มีบิลในรอบนี้")); return

                    st["totals"][bet["side"]] -= bet["amount"]
                    esc = st["escrow"].get(tuid, 0)
                    refund = min(esc, bet["amount"])
                    if refund > 0:
                        users[tuid]["credit"] = users[tuid].get("credit", 0) + refund
                        st["escrow"][tuid] = esc - refund
                        if st["escrow"][tuid] <= 0:
                            st["escrow"].pop(tuid, None)
                    save_users_persist()
                extra = " (กำลังพักรอบ)" if st["phase"] == "PAUSED" else ""
                safe_reply(event, TextSendMessage(f"ยกเลิกบิลของ ID {cid} สำเร็จ{extra} ({'สูง' if bet['side']=='HI' else 'ต่ำ'} {fmt(bet['amount'])})")); return

            # ลูกค้ายกเลิกบิลตัวเอง
            if text.strip().upper() == "X":
                if st["phase"] == "PAUSED":
                    safe_reply(event, TextSendMessage("กำลังพักรอบ: ลูกค้าไม่สามารถยกเลิกได้ โปรดให้แอดมินดำเนินการ")); return
                bet = st["bet_index"].pop(uid, None)
                if not bet:
                    safe_reply(event, TextSendMessage("คุณยังไม่มีการเดิมพันในรอบนี้")); return

                with with_users_lock():
                    st["totals"][bet["side"]] -= bet["amount"]
                    esc = st["escrow"].get(uid, 0)
                    refund = min(esc, bet["amount"])
                    if refund > 0:
                        users[uid]["credit"] = users[uid].get("credit", 0) + refund
                        st["escrow"][uid] = esc - refund
                        if st["escrow"][uid] <= 0:
                            st["escrow"].pop(uid, None)
                    save_users_persist()
                
                try:
                    profile = line_bot_api.get_profile(uid)
                    line_name = profile.display_name
                except Exception:
                    line_name = users.get(uid, {}).get("name", "ไม่ทราบชื่อ")
                safe_reply(event, TextSendMessage(f"คุณ {line_name} ❌ยกเลิกการเดิมพันเดิมสำเร็จ❌ ({'สูง' if bet['side']=='HI' else 'ต่ำ'} {fmt(bet['amount'])})")); return

        # ==== FAST PATH: ส่วนนี้ต้องอยู่นอก if ด้านบน ====
        bet = parse_bet(text)
        if bet:
            # แอดมินเล่นได้ (ปิดการเช็ค is_admin ไว้แล้ว)
            # if is_admin(uid):
            #     return
            
            with with_users_lock(): # [FIXED] ใช้แค่ with_users_lock()
                if uid not in users:
                    safe_reply(event, TextSendMessage("กรุณาพิมพ์ add เพื่อรับไอดีก่อนวางบิล")); return

                ok, why = can_bet(st, uid, bet["side"], bet["amount"])
                if not ok:
                    safe_reply(event, TextSendMessage(f"❌รับบิลไม่ได้❌: {why}")); return

                u = users[uid]
                if u.get("credit", 0) < bet["amount"]:
                    safe_reply(event, TextSendMessage(f"ทุนคงเหลือไม่พอ (มี {fmt(u.get('credit',0))})")); return

                u["credit"] -= bet["amount"]
                st["escrow"][uid] = st["escrow"].get(uid, 0) + bet["amount"]
                save_users_persist()

                name = u["name"]
                st["bet_index"][uid] = {"uid": uid, "name": name, "side": bet["side"], "amount": bet["amount"]}
                st["totals"][bet["side"]] += bet["amount"]

                side_th = "สูง" if bet["side"] == "HI" else "ต่ำ"
                safe_reply(event, TextSendMessage(
                    f"คุณ {name} ✅ เล่น {side_th} = {fmt(bet['amount'])} • ยอดเงินคงเหลือ {fmt(u['credit'])}"
                )); return


    # ----- ที่เหลือค่อยไปเช็คคำสั่งแอดมิน/ยูทิลต่างๆ เหมือนเดิม -----

@handler.add(MessageEvent, message=ImageMessage)
def on_image(event: MessageEvent):
    if _is_duplicate_event(event):
        return

    uid = event.source.user_id
    gid = getattr(event.source, "group_id", None)
    key = room_key(event.source)



    

    # ต้องอยู่ในกลุ่ม/ห้องเท่านั้น
    if not in_group_or_room(event.source):
        return

    # ตรวจ allow/deny/lockdown ของกลุ่ม
    if gid:
        if gid in BANNED_GROUPS or gid in DENY_GROUP_IDS:
            return
        if not is_allowed_group(gid):
            return
        if _locked_group(gid) and not is_admin(uid):
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("ระบบ: กลุ่มกำลังล็อกดาวน์ชั่วคราว ติดต่อแอดมินเพื่อปลดล็อก"))
            return

    # ตรวจสถานะผู้ใช้ ban/mute
    if uid in BANNED_UIDS:
        return
    if _muted(uid):
        if not _notice_throttled(uid):
            safe_reply(event, TextSendMessage("ระบบ: คุณถูกจำกัดการส่งข้อความชั่วคราว (anti-spam)"))
        return

    # rate limit แบบเดียวกับข้อความตัวหนังสือ
    if not rl.allow(f"room:{key}", RL_ROOM_BURST_LIMIT, RL_ROOM_BURST_PERIOD):
        return
    if not rl.allow(f"uid:{uid}:burst", RL_UID_BURST_LIMIT, RL_UID_BURST_PERIOD) or \
       not rl.allow(f"uid:{uid}:day", RL_UID_DAILY_LIMIT, RL_UID_DAILY_PERIOD):
        STRIKES[uid] = STRIKES.get(uid, 0) + 1
        if STRIKES[uid] >= ABUSE_STRIKE_TO_MUTE:
            MUTED_UNTIL[uid] = _now() + MUTE_SECONDS_DEFAULT
            STRIKES[uid] = 0
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage(f"ระบบ: มิวท์ {MUTE_SECONDS_DEFAULT} วินาที เนื่องจากกิจกรรมถี่ผิดปกติ"))
        else:
            if not _notice_throttled(uid):
                safe_reply(event, TextSendMessage("ระบบ: กิจกรรมถี่เกินกำหนด ช่วยเว้นช่วงหน่อยนะ"))
        return

    # เตรียม state ห้อง
    with with_rooms_lock():
        if key not in rooms:
            rooms[key] = start_state()
        st = rooms[key]

    # ต้องมีข้อมูลผู้ใช้ก่อน (พิมพ์ add มาก่อน)
    with with_users_lock():
        u = users.get(uid)

    if not u:
        safe_reply(event, TextSendMessage("กรุณาพิมพ์ add เพื่อรับไอดีก่อน"))
        return

    # ตอบการ์ด C ของผู้ที่ส่งรูป
    try:
        safe_reply(event, flex_customer_card(st, u))
    except Exception:
        app.logger.exception("on_image flex_customer_card failed uid=%s", uid)
        safe_reply(event, TextSendMessage(
            f"ID {u.get('cid', '-')} • {u.get('name', 'ผู้เล่น')} • เครดิต {fmt(u.get('credit', 0))} บ."
        ))


def current_camp(st):
    return (st.get("price", {}) or {}).get("camp") or (st.get("note") or "ไม่ระบุค่าย")

def push_batch(to_id, messages, batch=5):
    for i in range(0, len(messages), batch):
        safe_push(to_id, messages[i:i+batch])



# ====== ANTI-KICK MONITOR ======
@handler.add(MemberLeftEvent)
def on_member_left(event: MemberLeftEvent):
    gid = getattr(event.source, "group_id", None)
    if not gid: return
    try:
        members = getattr(getattr(event, "left", None), "members", []) or []
    except Exception:
        members = []
    left_uids = []
    for m in members:
        uid = getattr(m, "user_id", None) or getattr(m, "mid", None) or getattr(m, "id", None)
        if uid: left_uids.append(uid)
    for lu in left_uids:
        if lu in PROTECTED_UIDS:
            _lockdown_and_alert(gid, lu)
            break
    


# ====== FREE BACKOFFICE VIEW (no LINE quota) ======
# เปิดดูสรุปล่าสุดผ่านเว็บ: /backoffice/latest?token=YOURTOKEN
# ตั้ง token ได้ด้วย env: BACKOFFICE_VIEW_TOKEN (ถ้าไม่ตั้ง จะเปิดได้เฉพาะในวงแลน/เครื่องตัวเองตามไฟร์วอลล์)
@app.route("/backoffice/latest", methods=["GET"])
def backoffice_latest():
    token = os.getenv("BACKOFFICE_VIEW_TOKEN", "").strip()
    if token:
        if request.args.get("token", "").strip() != token:
            return make_response("forbidden", 403)

    p = load_last_settle()
    if not p:
        return make_response(json.dumps({"ok": False, "message": "no last_settle yet"}, ensure_ascii=False),
                             404, {"Content-Type": "application/json; charset=utf-8"})

    return make_response(json.dumps({"ok": True, "data": p}, ensure_ascii=False),
                         200, {"Content-Type": "application/json; charset=utf-8"})

if __name__ == "__main__":
    print(f"Starting Waitress on http://0.0.0.0:{PORT}")
    serve(
        app,
        host="0.0.0.0",
        port=PORT,
        threads=8,
        connection_limit=200,
        channel_timeout=60
    )
