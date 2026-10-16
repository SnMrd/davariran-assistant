# -*- coding: utf-8 -*-
"""
دستیار هوشمند سامانه جامع داوری ایران (داورایران) — بسته v11
- اجرای اصلی با کتابخانه استاندارد پایتون
- پایگاه دانش منتخب: davariran_kb.csv
- جست‌وجوی BM25، نرمال‌سازی فارسی، حافظه جلسه و پاسخ‌های قالب‌بندی‌شده
- شامل محافظت‌های پایه HTTP؛ برای استقرار عمومی راهنمای SECURITY.md و DEPLOYMENT.md را بخوانید
اجرا:  python chatbot.py   ←   http://127.0.0.1:8000
"""

import csv
import html
import json
import math
import os
import re
import threading
import time
import urllib.parse
import urllib.request
from collections import Counter, defaultdict
from difflib import SequenceMatcher, get_close_matches
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer

csv.field_size_limit(10 ** 7)

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
KB_PATH = os.environ.get("KB_PATH", os.path.join(BASE_DIR, "davariran_kb.csv"))
HOST = os.environ.get("HOST", "127.0.0.1")
PORT = int(os.environ.get("PORT", "8000"))
OPENAI_API_KEY = os.environ.get("OPENAI_API_KEY", "")
ALLOWED_ORIGIN = os.environ.get("ALLOWED_ORIGIN", "").strip()
CONTACT_URL = "https://davariran.com/ContactUs/Create"
MAX_QUERY_LEN = 500

# ==========================================
# ۱. نرمال‌سازی و توکن‌سازی
# ==========================================
_CHAR_MAP = str.maketrans({
    "ي": "ی", "ى": "ی", "ك": "ک", "ۀ": "ه", "ة": "ه", "ؤ": "و", "أ": "ا", "إ": "ا", "آ": "ا",
    "ـ": "", "\u200f": "", "\u200e": "", "\u2063": "", "\u2060": "", "\u200c": " ",
})
_DIGITS = str.maketrans("۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩", "01234567890123456789")

# عبارت‌های چندکلمه‌ای که باید یکی شوند
PHRASES = [
    ("گواهی نامه", "گواهینامه"), ("ثبت نام", "ثبتنام"), ("رمز عبور", "رمز"), ("کلمه عبور", "رمز"),
    ("کد ملی", "کدملی"), ("شماره همراه", "موبایل"), ("تلفن همراه", "موبایل"), ("شماره موبایل", "موبایل"),
    ("داور بشم", "داور شدن"), ("داور بشوم", "داور شدن"), ("داور شوم", "داور شدن"), ("داور بشیم", "داور شدن"),
    ("نمی خوام", "نمیخواهم"), ("می خوام", "خواهم"), ("می خواهم", "خواهم"), ("میخوام", "خواهم"),
    ("میخام", "خواهم"), ("میخواهم", "خواهم"), ("نمی تونم", "نتوانم"), ("نمیتونم", "نتوانم"),
    ("نمی توانم", "نتوانم"), ("نمیشه", "نمیشود"), ("نمی شه", "نمیشود"), ("نمی شود", "نمیشود"),
    ("عودت وجه", "عودت"),
]
WORD_MAP = {
    "پسورد": "رمز", "پسوورد": "رمز", "پاسوورد": "رمز", "پسوردم": "رمز", "رمزم": "رمز", "رم": "رمز", "مز": "رمز", "لاگین": "ورود", "وارد": "ورود",
    "ارور": "خطا", "اکانت": "حساب", "حساب": "حساب", "اپلود": "بارگذاری", "اپلودش": "بارگذاری",
    "بارگزاری": "بارگذاری", "بارگزار": "بارگذاری", "اپلیکیشن": "اپلیکیشن", "اپ": "اپلیکیشن", "برنامه": "اپلیکیشن",
    "دانلودش": "دانلود", "دانلودم": "دانلود", "کارتم": "کارت", "کارتو": "کارت", "کارتمو": "کارت",
    "گواهی": "گواهینامه", "کارگا": "دوره", "شم": "شوم", "مدارک": "مدرک", "امتحان": "ازمون", "ازمونم": "ازمون", "تعرفه": "هزینه",
    "قیمت": "هزینه", "پول": "هزینه", "مبلغ": "هزینه", "استرداد": "عودت", "برگشت": "عودت",
    "پشتیبان": "پشتیبانی", "کلاس": "دوره", "کارگاه": "دوره", "کجاس": "کجا", "کجاست": "کجا", "ثبتنام": "ثبتنام", "عضو": "عضویت",
}
STOPWORDS = set("""
و در به از که این آن با برای را است هست بود شد شود می نمی نمیشود خواهم بخواهم هم یا اما اگر تا بر
من ما شما او ایشان بنده اینجانب جناب سلام درود خسته نباشید نباشی لطفا احتراما احترام عرض ادب وقت بخیر
سایت سامانه مرکز واحد درباره درخصوص مورد خواهشمندم ممنون متشکرم تشکر سپاس مرسی ببخشید
چی چه چرا کی کدام چند چقدر آیا میشه میتونم میتوان امکان باشه خب اوکی وای عه آخ چطور کجا چطوری چگونه میشود شه
کنم کنید کردم کردن کرده دارم دارد داشتم دادم نتوانم توانم میشود
""".split())
# واژه‌های «مشکل» عمومی که به‌تنهایی معنا ندارند
GENERIC_PROBLEM = {"مشکل", "خراب", "خطا", "ایراد", "کمک", "راهنمایی", "مسئله", "باگ", "سوال", "پرسش"}


def normalize(text: str) -> str:
    if text is None:
        return ""
    t = html.unescape(str(text))
    t = re.sub(r"<[^>]+>", " ", t)
    t = t.translate(_CHAR_MAP).translate(_DIGITS).lower()
    t = re.sub(r"[^\w\s؟?]", " ", t, flags=re.UNICODE)
    t = re.sub(r"(.)\1{2,}", lambda m: m.group(1) * 2, t)  # کشیدن حروف: سلامممم ← سلامم
    t = re.sub(r"\s+", " ", t).strip()
    t = f" {t} "
    for old, new in PHRASES:
        t = t.replace(f" {old} ", f" {new} ")
    return t.strip()


def _stem(w: str) -> str:
    if len(w) > 5 and w.endswith("های"):
        return w[:-3]
    if len(w) > 4 and (w.endswith("ها") or w.endswith("ان") or w.endswith("ات")):
        return w[:-2]
    return w


def tokenize(text: str, keep_stop: bool = False) -> list:
    out = []
    for w in normalize(text).replace("؟", " ").replace("?", " ").split():
        w = WORD_MAP.get(w, w)
        w = _stem(w)
        if len(w) < 2 or w.isdigit():
            continue
        if not keep_stop and w in STOPWORDS:
            continue
        out.append(w)
    return out


# ==========================================
# ۲. قالب‌بندی پاسخ‌ها
# ==========================================
FOOTER_TICKET = (
    "\n\n━━━━━━━━━━━━━━\n"
    "🔔 اگر پاسخ، مسئله شما را برطرف نکرد، از بخش **«تیکت‌های من»** یا "
    "[فرم تماس با ما](" + CONTACT_URL + ") اقدام فرمایید."
)
TOPIC_FOLLOWUPS = {
    "card": ["مدت زمان صدور کارت عضویت", "عودت وجه", "تماس با پشتیبانی"],
    "certificate": ["مدت زمان صدور گواهینامه", "آزمون دوره", "بارگذاری گواهینامه"],
    "exam": ["آزمون مجدد", "گواهینامه دوره", "مشکل فنی آزمون"],
    "course": ["دانلود فایل دوره", "مهلت گذراندن دوره", "گواهینامه دوره"],
    "login": ["فراموشی رمز عبور", "نصب اپلیکیشن", "تماس با پشتیبانی"],
    "payment": ["عودت وجه", "هزینه نمایش سالیانه", "تماس با پشتیبانی"],
    "display": ["چگونه داور شوم", "کارت عضویت", "عودت وجه"],
    "score": ["امتیاز علمی", "بارگذاری گواهینامه", "مدرک تحصیلی"],
    "edu_doc": ["امتیاز علمی", "بارگذاری گواهینامه", "تغییر عکس"],
    "legal_info": ["چگونه داور شوم", "دوره‌های آموزشی", "تماس با پشتیبانی"],
    "case": ["انتخاب داور", "ابطال رأی داور", "تماس با پشتیبانی"],
    "general": ["چگونه داور شوم", "کارت عضویت", "تماس با پشتیبانی"],
}
DEFAULT_CHIPS = ["چگونه داور شوم", "کارت عضویت", "گواهینامه", "آزمون", "دانلود دوره", "مشکل ورود", "تماس با پشتیبانی"]


def build_reply(entry: dict, confidence: float, show_footer: bool = True) -> dict:
    body = entry["answer"].strip()
    if show_footer and entry.get("slug") != "contact":
        body += FOOTER_TICKET
    return {
        "intent": entry.get("slug") or "kb_match",
        "subject": entry.get("topic_title") or entry.get("title", "راهنمای داورایران"),
        "answer": body,
        "confidence": confidence,
        "topic": entry["topic"],
        "suggestions": TOPIC_FOLLOWUPS.get(entry["topic"], TOPIC_FOLLOWUPS["general"]),
    }


# ==========================================
# ۳. حافظه جلسه (با پاک‌سازی خودکار)
# ==========================================
class SessionManager:
    def __init__(self, expire_seconds=1800, max_sessions=5000):
        self.sessions = {}
        self.expire = expire_seconds
        self.max_sessions = max_sessions
        self.lock = threading.Lock()

    def get(self, sid):
        if not sid:
            return {}
        with self.lock:
            data = self.sessions.get(sid)
            if not data:
                return {}
            if time.time() - data.get("last_time", 0) > self.expire:
                self.sessions.pop(sid, None)
                return {}
            return dict(data)

    def update(self, sid, **kw):
        if not sid:
            return
        with self.lock:
            if len(self.sessions) > self.max_sessions:
                now = time.time()
                for k in [k for k, v in self.sessions.items() if now - v.get("last_time", 0) > self.expire]:
                    self.sessions.pop(k, None)
            cur = self.sessions.get(sid, {})
            cur["last_time"] = time.time()
            cur.update({k: v for k, v in kw.items() if v})
            self.sessions[sid] = cur


sessions = SessionManager()

# ==========================================
# ۴. موتور جست‌وجو
# ==========================================
FIELD_W = {"title": 3.0, "question": 2.0, "answer": 0.6}


class KnowledgeEngine:
    def __init__(self, path: str):
        self.entries = []
        self.postings = defaultdict(list)   # token -> [(doc, weighted_tf)]
        self.doc_len = []
        self.vocab = set()
        self.df = Counter()
        self.avg_len = 1.0
        self.k1, self.b = 1.4, 0.7
        self.by_slug = {}
        self._load(path)

    def _load(self, path: str):
        if not os.path.exists(path):
            print(f"⚠️ فایل پایگاه دانش یافت نشد: {path}")
            return
        with open(path, encoding="utf-8-sig", newline="") as f:
            for row in csv.DictReader(f):
                if not row.get("answer"):
                    continue
                row["source_count"] = int(row.get("source_count") or 1)
                row["questions_list"] = [q.strip() for q in (row.get("questions") or "").split("|||") if q.strip()]
                self.entries.append(row)
        total = 0
        for i, e in enumerate(self.entries):
            tf = Counter()
            for t in tokenize(e["title"]):
                tf[t] += FIELD_W["title"]
            for q in e["questions_list"]:
                for t in tokenize(q):
                    tf[t] += FIELD_W["question"]
            for t in tokenize(e["answer"][:400]):
                tf[t] += FIELD_W["answer"]
            length = sum(tf.values()) or 1
            self.doc_len.append(length)
            total += length
            for tok, w in tf.items():
                self.postings[tok].append((i, w))
                self.df[tok] += 1
            if e.get("slug"):
                self.by_slug[e["slug"]] = e
        self.avg_len = total / max(len(self.entries), 1)
        self.vocab = set(self.postings)
        print(f"✅ {len(self.entries)} رکورد از {os.path.basename(path)} بارگذاری شد ({len(self.vocab)} واژه).")

    def _correct(self, tok: str):
        """اصلاح غلط املایی بر اساس واژگان پایگاه دانش."""
        if tok in self.vocab or len(tok) < 4:
            return tok
        m = get_close_matches(tok, self.vocab, n=1, cutoff=0.82)
        return m[0] if m else tok

    def search(self, query: str, topic_hint: str = None, top_k: int = 3):
        all_tokens = [self._correct(t) for t in tokenize(query)]
        all_tokens = [t for t in all_tokens if t not in GENERIC_PROBLEM]
        q_tokens = [t for t in all_tokens if t in self.vocab]
        if not q_tokens or not self.entries:
            return []
        N = len(self.entries)
        scores = defaultdict(float)
        matched = defaultdict(set)
        for tok in set(q_tokens):
            df = self.df[tok]
            idf = math.log(1 + (N - df + 0.5) / (df + 0.5))
            for doc, w in self.postings[tok]:
                denom = w + self.k1 * (1 - self.b + self.b * self.doc_len[doc] / self.avg_len)
                scores[doc] += idf * (w * (self.k1 + 1)) / denom
                matched[doc].add(tok)
        n_q = len(set(all_tokens))
        ranked = []
        for doc, sc in scores.items():
            e = self.entries[doc]
            coverage = len(matched[doc]) / n_q
            # پاسخ مستقیم فقط با هم‌پوشانی معنایی کافی؛ پرسش‌های مبهم/خارج از دانش پاسخ حدسی نمی‌گیرند.
            if n_q >= 2 and coverage < 0.68:
                continue
            if n_q == 1 and len(q_tokens) == 1 and q_tokens[0] in {"داوری", "داور", "کتاب", "عضویت", "مدرک", "سایت", "مشکل", "هزینه"}:
                continue
            sc *= (0.55 + 0.45 * coverage)
            sc *= 1 + 0.04 * math.log(1 + e["source_count"])
            if e.get("quality") == "curated":
                sc *= 1.1
            if topic_hint and e["topic"] == topic_hint:
                sc *= 1.12
            ranked.append((sc, coverage, doc))
        ranked.sort(reverse=True)
        return [(self.entries[d], sc, cov) for sc, cov, d in ranked[:top_k]]


engine = KnowledgeEngine(KB_PATH)

# ==========================================
# ۵. مسیریابی نیت و پاسخ‌گویی
# ==========================================
GREETINGS = {"سلام", "درود", "سلام علیکم", "صبح بخیر", "عصر بخیر", "شب بخیر", "وقت بخیر", "روز بخیر",
             "سلام وقت بخیر", "سلام خسته نباشید", "خسته نباشید", "عرض ادب", "hi", "hello"}
THANKS = ("ممنون", "مرسی", "متشکر", "سپاس", "دمتون گرم", "تشکر", "thanks")
AMBIGUOUS = {"مشکل دارم", "مشکل", "کمک", "کمک کنید", "سوال دارم", "خرابه", "کار نمیکنه", "راهنمایی", "ارور میده",
             "خطا میده", "تماس گرفتم", "زنگ زدم", "پیام دادم", "پاسخ ندادید", "جواب ندادید", "مشکل پیش اومده",
             "به مشکل خوردم", "سوال", "پرسش"}

BECOME_MARKERS = ("داور شدن", "شرایط داور", "عضویت داور", "داور شو", "میخوام داور بشم", "می خواهم داور شوم", "خودم داور بشم", "اسمم در لیست داورها", "خودم داور بشم", "اسمم در لیست داورها")
GET_MARKERS = ("داور بگیرم", "گرفتن داور", "درخواست داور", "انتخاب داور", "تعیین داور", "معرفی داور",
               "ارجاع به داور", "انتصاب داور", "داور پرونده", "جستجوی داور", "داور خواهم", "خواهم داور",
               "داور میخوام", "داور می خواهم", "داور میخام", "نیاز به داور دارم", "برای اختلاف داور میخواهم", "داور برای قراردادم", "نیاز به داور دارم", "برای اختلاف داور", "داور برای قراردادم")
ANNUL_MARKERS = ("ابطال رای", "اعتراض به رای", "شکایت از رای", "باطل کردن رای", "ابطال داوری")
CONTACT_MARKERS = ("شماره تماس", "شماره تلفن", "تلفن پشتیبانی", "تماس با ما", "ارتباط با ما", "تماس با پشتیبانی",
                   "پشتیبانی", "تماس", "ارتباط")
PERSONAL_STATUS = ("کی تماس", "چه ساعتی تماس", "ساعت چند تماس", "فردا تماس", "وضعیت تیکت", "تیکت شماره",
                   "پرداخت من", "پرداختم تایید", "کارشناس با من تماس", "کارشناس سایت با من تماس",
                   "درخواست من هنوز بررسی نشده", "درخواست هنوز بررسی نشده", "درخواست من بررسی نشده", "وضعیت درخواست من")

PHONE_RE = re.compile(r"(?<!\d)(0?9\d{9})(?!\d)")


def simple(subject, answer, intent, suggestions=None, confidence=0.0, topic="general"):
    return {"intent": intent, "subject": subject, "answer": answer, "confidence": confidence,
            "topic": topic, "suggestions": suggestions or DEFAULT_CHIPS[:4]}



def _redact_for_external_model(text: str) -> str:
    """حذف الگوهای رایج اطلاعات شناسایی قبل از ارسال احتمالی به سرویس بیرونی."""
    text = re.sub(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}", "[ایمیل حذف شد]", str(text))
    text = re.sub(r"(?<!\d)(?:\+?98|0)?9\d{9}(?!\d)", "[شماره حذف شد]", text)
    text = re.sub(r"(?<!\d)\d{10,11}(?!\d)", "[شناسه عددی حذف شد]", text)
    return text


def generate_grounded_answer(question: str, hits):
    """پاسخ محدود به رکوردهای بازیابی‌شده؛ در نبود کلید، پاسخ قالبی استفاده می‌شود."""
    if not OPENAI_API_KEY or not hits:
        return None
    allowed = {entry.get("slug") for entry, *_ in hits if entry.get("slug")}
    if not allowed:
        return None
    records = [{"slug": e.get("slug"), "title": e.get("title"), "answer": e.get("answer", "")} for e, *_ in hits]
    payload = {"model": os.environ.get("OPENAI_MODEL", "gpt-4o-mini"), "messages": [
        {"role": "system", "content": "به فارسی پاسخ کوتاه بده. فقط از اطلاعات رکوردهای داده‌شده استفاده کن. خروجی JSON با کلیدهای answer و used_slugs باشد؛ used_slugs فقط شامل slugهای منبع استفاده‌شده باشد. اگر اطلاعات کافی نیست، صریحاً بگو اطلاعات کافی نیست."},
        {"role": "user", "content": json.dumps({"question": _redact_for_external_model(question), "records": records}, ensure_ascii=False)}
    ], "temperature": 0}
    req = urllib.request.Request("https://api.openai.com/v1/chat/completions", data=json.dumps(payload).encode("utf-8"), headers={"Authorization": "Bearer " + OPENAI_API_KEY, "Content-Type": "application/json"}, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=12) as response:
            data = json.loads(response.read().decode("utf-8"))
        raw = data["choices"][0]["message"]["content"]
        parsed = json.loads(raw)
        used = parsed.get("used_slugs", [])
        answer = str(parsed.get("answer", "")).strip()
        if answer and isinstance(used, list) and used and set(used).issubset(allowed):
            return answer
    except (OSError, ValueError, KeyError, TypeError, IndexError):
        return None
    return None


def answer_query(query: str, session_id: str = None) -> dict:
    query = (query or "").strip()[:MAX_QUERY_LEN]
    ctx = sessions.get(session_id)
    digits = query.translate(_DIGITS)

    # --- شماره موبایل ---
    m = PHONE_RE.search(digits)
    if m:
        hint = ""
        if ctx.get("last_title"):
            hint = f"\n\n📌 موضوع آخر گفت‌وگو: **{ctx['last_title']}**"
        return simple(
            "📞 راهنمای پیگیری",
            "📋 شماره شما در همین گفت‌وگو دیده می‌شود، اما این چت به سامانه تیکتینگ متصل نیست و "
            "**درخواست تماس ثبت نمی‌کند.**" + hint + "\n\n"
            "برای پیگیری رسمی:\n"
            "۱. از بخش **«تیکت‌های من»** در صفحه شخصی خود تیکت ثبت کنید.\n"
            f"۲. یا از [فرم تماس با ما]({CONTACT_URL}) استفاده نمایید.\n\n"
            "🔒 لطفاً رمز عبور یا کد ورود خود را برای هیچ‌کس ارسال نکنید.",
            "phone_received", ["تماس با پشتیبانی"], 0.0)
    if re.fullmatch(r"0?9\d{2,8}", digits.strip()):
        return simple("📞 شماره ناقص", "لطفاً شماره موبایل **۱۱ رقمی** را کامل ارسال فرمایید.", "phone_incomplete")

    qn = normalize(query).replace("؟", "").replace("?", "").strip()
    # اصلاح غلط‌های تایپی کوتاه و رایج در درخواست بازیابی رمز
    qn = re.sub(r"\bرم\b", "رمز", qn)
    qn = re.sub(r"\bیادم نی\b", "یادم نیست", qn)
    qn = re.sub(r"\bیادم نیس\b", "یادم نیست", qn)
    qn = re.sub(r"\bیام نیست\b", "یادم نیست", qn)
    qn = re.sub(r"\bیام نیس\b", "یادم نیست", qn)
    qn = re.sub(r"\bمز عبور", "رمز عبور", qn)
    qn = re.sub(r"\bفراموش کردم\b", "فراموش کردم", qn)
    # غلط‌های رایج سلام و کشیدن حروف در گفت‌وگوی محاوره‌ای
    qn = re.sub(r"سلاوم", "سلام", qn)
    qn = re.sub(r"سبام", "سلام", qn)
    qn = re.sub(r"شلام", "سلام", qn)
    qn = re.sub(r"سلم", "سلام", qn)
    greeting_compact = re.sub(r"(.)\1{1,}", r"\1", qn)
    for word, replacement in WORD_MAP.items():
        qn = re.sub(rf"(?<!\w){re.escape(word)}(?!\w)", replacement, qn)
    if len(qn) <= 1:
        return simple("🌸 راهنمای دستیار داورایران",
                      "👋 سلام! پرسش خود را مطرح فرمایید یا یکی از موضوعات زیر را انتخاب کنید.", "short_help", DEFAULT_CHIPS)

    # سلام همراه با احوال‌پرسی، حتی با غلط تایپی رایج «سبام».
    if re.search(r"(?:^| )(?:سلام|درود|صبح بخیر|عصر بخیر|شب بخیر)(?: |$)", qn) and any(x in qn for x in ("خوبی", "خوبید", "حالت چطوره", "چطوری", "چه خبر")):
        return simple("🌸 خوش‌آمدید", "😊 ممنون، خوبم و آماده‌ام کمکتان کنم! شما چه کمکی درباره خدمات داورایران لازم دارید؟", "smalltalk", DEFAULT_CHIPS)

    # --- سلام و تشکر ---
    if (qn in {normalize(g) for g in GREETINGS} or greeting_compact in {normalize(g) for g in GREETINGS}
            or qn in {"سلاوم", "سلاام", "سلااام", "سلاااام", "سلاممم", "سلااااام", "شلام"}
            or (len(qn.split()) <= 3 and any(greeting_compact.startswith(normalize(g)) for g in ("سلام", "درود"))
                and not tokenize(qn))):
        return simple("⚖️ پشتیبانی هوشمند داورایران",
                      "👋 **سلام و وقت بخیر!**\nدر خدمت شما هستیم؛ پرسش خود را درباره **عضویت، دوره‌ها، گواهینامه، کارت عضویت** "
                      "یا مسائل داوری بفرمایید.", "greeting", DEFAULT_CHIPS)
    if re.fullmatch(r"(تو )?خوبی|خوبی شما|حالت چطوره|چطوری", qn):
        return simple("🌸 خوش‌آمدید", "😊 ممنون، خوبم و آماده‌ام کمکتان کنم! شما چه کمکی درباره خدمات داورایران لازم دارید؟", "smalltalk", DEFAULT_CHIPS)
    if any(t in qn for t in THANKS) and len(qn.split()) <= 5 and not tokenize(qn.replace("ممنون", "").replace("مرسی", "")):
        return simple("🌸 با تشکر", "🙏 **خواهش می‌کنیم.** در صورت نیاز به راهنمایی بیشتر در خدمتیم.", "thanks")

    # جمله‌های اصلاحی: «نه، منظورم این نبود» باید نیت تازه را جایگزین نیت قبلی کند.
    correction = any(x in qn for x in ("نه", "منظورم", "گفتم", "اشتباه فهمیدی", "نه اینکه", "نه این که", "نمیخواهم", "نمیخوام", "نمی خواهم", "نمی خوام"))
    mentions_get = any(x in qn for x in ("داور میخواهم", "داور می خواهم", "داور میخام", "داور خواهم", "داور میخوام", "داور برای", "داور پرونده", "داور پیدا", "نیاز به داور", "انتخاب داور", "درخواست داور"))
    mentions_become = any(x in qn for x in ("داور بشم", "داور بشوم", "داور شوم", "داور شدن", "خودم داور", "میخواهم داور شوم", "خواهم داور شدن"))
    if correction and mentions_get and mentions_become:
        # اگر کاربر «نه، می‌خواهم خودم داور شوم نه داور پیدا کنم» گفته، نیت داور شدن غالب است.
        if re.search(r"(?:میخواهم|خواهم|میخوام|میخام)\s+داور\s+(?:بشم|بشوم|شوم|شدن)", qn) or "خودم داور" in qn:
            if any(x in qn for x in ("نه داور پیدا", "نه اینکه داور پیدا", "نه اینکه داور بخواهم", "نه داور میخواهم", "نه داور میخوام")):
                if "become_arbitrator" in engine.by_slug:
                    return build_reply(engine.by_slug["become_arbitrator"], 0.0)
        if "get_arbitrator" in engine.by_slug:
            res = build_reply(engine.by_slug["get_arbitrator"], 0.0)
            sessions.update(session_id, last_topic=res["topic"], last_title=res["subject"])
            return res
    if correction and mentions_become and not mentions_get:
        if "become_arbitrator" in engine.by_slug:
            res = build_reply(engine.by_slug["become_arbitrator"], 0.0)
            sessions.update(session_id, last_topic=res["topic"], last_title=res["subject"])
            return res

    # نیت «ثبت مدرک جدید» را از سؤال «چرا مدرکم نمایش داده نمی‌شود؟» جدا کن.
    if ("مدرک" in qn and any(x in qn for x in ("ثبت", "بارگذاری", "اپلود", "اعمال", "اضافه"))
            and any(x in qn for x in ("جدید", "کارشناسی", "مدرکم", "مدرک من"))
            and not any(x in qn for x in ("چرا نمایش", "نمایش داده نمی", "نمایش نمیشه", "نمایش نمی شود"))):
        return simple("🎓 ثبت مدرک تحصیلی جدید",
                      "برای ثبت مدرک تحصیلی جدید، وارد حساب کاربری و صفحه شخصی خود شوید و بخش اطلاعات تحصیلی/مدارک را بررسی کنید. مدرک معتبر را از مسیر مربوط بارگذاری کنید؛ بارگذاری به معنی تأیید فوری نیست و ممکن است به بررسی سامانه نیاز داشته باشد. من به حساب شما دسترسی ندارم؛ اگر گزینه بارگذاری را پیدا نکردید یا مدرک اعمال نشد، از «تیکت‌های من» یا [فرم تماس با ما](" + CONTACT_URL + ") پیگیری کنید.",
                      "academic_degree_upload", ["چرا آخرین مدرک تحصیلی من نمایش داده نمی‌شود؟", "تماس با پشتیبانی"], 0.0, "edu_doc")

    # «وضعیت/تأیید کارت» با «چطور کارت درخواست کنم» فرق دارد.
    if ("کارت" in qn and any(x in qn for x in ("تایید", "تأیید", "وضعیت", "درخواست دادم", "درخواست کردم", "ثبت کردم"))
            and any(x in qn for x in ("از کجا بفهمم", "چطور بفهمم", "تأیید شده", "تایید شده", "بررسی شده", "پیگیری", "وضعیت"))):
        return simple("🔎 پیگیری تأیید درخواست کارت عضویت",
                      "من به وضعیت زنده حساب شما دسترسی ندارم و نمی‌توانم تأیید درخواست کارت را مستقیماً بررسی کنم. پس از ورود، صفحه شخصی و بخش درخواست کارت/پیام‌های حساب را بررسی کنید. اگر وضعیت تأیید روشن نیست، از «تیکت‌های من» یا [فرم تماس با ما](" + CONTACT_URL + ") پیگیری کنید. ثبت درخواست به‌تنهایی به معنی تأیید نیست.",
                      "membership_card_status", ["مدت زمان صدور کارت عضویت", "تماس با پشتیبانی"], 0.0, "card")

    # پس از سه تلاش ناموفق، مسیر پاسخ باید با سؤال واقعی هماهنگ باشد.
    if ("آزمون" in qn or "امتحان" in qn or "ازمون" in qn) and any(x in qn for x in ("سه بار", "3 بار", "هر سه بار", "سه دفعه")) and any(x in qn for x in ("رد", "مردود", "قبول نشدم", "افتادم", "قبول نشدن")):
        return simple("📝 پس از سه بار مردودی در آزمون چه کنم؟",
                      "طبق FAQ داورایران، برای هر دوره حداکثر سه بار شرکت در آزمون ذکر شده است. در اطلاعات تأییدشده من، امکان تلاش چهارم به‌عنوان قاعده عمومی تأیید نشده؛ بنابراین آن را تضمین نمی‌کنم. راهنمای همان دوره و گزینه‌های موجود در «آزمون‌های من» را بررسی کنید و برای استثنا یا تلاش بیشتر از پشتیبانی استعلام بگیرید: [فرم تماس با ما](" + CONTACT_URL + ").",
                      "exam_attempts_exhausted", ["آزمون مجدد", "تماس با پشتیبانی"], 0.0, "exam")

    # --- موارد شخصی که قابل پیگیری در چت نیست ---
    if any(x in qn for x in PERSONAL_STATUS):
        return simple("🔎 پیگیری درخواست شخصی",
                      "ℹ️ من به **وضعیت زنده تیکت‌ها، پرداخت‌ها یا برنامه تماس کارشناسان** دسترسی ندارم و نمی‌توانم زمان یا وضعیت آن‌ها را تأیید کنم.\n\n"
                      "✅ لطفاً پس از ورود، از **«تیکت‌های من»** پیگیری کنید یا از "
                      f"[فرم تماس با ما]({CONTACT_URL}) استفاده نمایید.", "personal_status", ["تماس با پشتیبانی"], 0.0)

    # درخواست صریح برای سؤال خارج از اطلاعات سایت، باید به مسیر روشن‌کننده/پشتیبانی برود.
    if any(x in qn for x in ("جوابش تو سایت نیست", "پاسخش تو سایت نیست", "جواب تو سایت نیست", "توی سایت نیست", "در سایت نیست", "سایت جواب نداره")):
        return simple("💬 سؤال خارج از راهنمای سایت", "حتماً، سؤال‌تان را همین‌جا کامل بنویسید. اگر پاسخ آن در راهنماهای تأییدشده داورایران نباشد، پاسخ حدسی نمی‌سازم و مسیر پیگیری رسمی را معرفی می‌کنم. برای بررسی توسط پشتیبانی هم می‌توانید از [فرم تماس با ما](" + CONTACT_URL + ") استفاده کنید.", "support_handoff", ["تماس با پشتیبانی", "فهرست راهنماها"], 0.0, "support")

    # عبارت «داوری» به‌تنهایی موضوع کلی است؛ به‌جای fallback نامرتبط، گزینه‌های مرتبط بده.
    if qn in {"داوری", "داوریی", "داورییی"} or re.sub(r"(.)\1{1,}", r"\1", qn) == "داوری":
        return simple("⚖️ راهنمای موضوعات داوری", "منظورتان کدام موضوع داوری است؟", "ambiguous", ["چگونه داور شوم", "انتخاب داور", "ابطال رأی داور", "هزینه داوری"], 0.0, "general")

    # --- اصلاحات هدفمند بر اساس تست مکالمه ---
    # پرسش تماس با نام سایت نیز باید مستقیم پاسخ بگیرد، نه اینکه وارد حلقه ابهام شود.
    if any(k in qn for k in ("چطور با داورایران تماس", "چطوری با داورایران تماس", "چگونه با داورایران تماس", "تماس با داورایران", "راه ارتباط با داورایران")):
        return simple("📞 راه‌های تماس با پشتیبانی", "برای ارتباط با داورایران می‌توانید از [فرم تماس با ما](" + CONTACT_URL + ") استفاده کنید. شماره‌های درج‌شده در اطلاعات رسمی پایگاه دانش: **۰۲۱۸۸۹۶۷۹۴۶** و **۰۲۱۹۱۰۹۶۴۹۴**؛ ایمیل: **info@davariran.com**. برای پیگیری درخواست‌های مربوط به حساب، پس از ورود بخش «تیکت‌های من» را هم بررسی کنید. اگر اطلاعات تماس تغییر کرده باشد، صفحه رسمی تماس ملاک نهایی است.", "contact", ["اطلاعات تماس رسمی داورایران", "تماس با پشتیبانی"], 0.0, "support")

    # وقتی کاربر صریحاً می‌گوید منظورش هزینه عضویت اولیه است، پاسخ روشن بده.
    if ("عضویت اولیه" in qn and any(k in qn for k in ("هزینه", "پول", "مبلغ", "پرداخت", "منظورم"))):
        return simple("💳 هزینه عضویت اولیه", "طبق شرایط عضویت داورایران، **عضویت اولیه رایگان است**. این موضوع را از هزینه‌های احتمالی صدور کارت عضویت یا نمایش عمومی به‌عنوان داور فعال جدا بدانید؛ این خدمات یکسان نیستند. برای شرایط جاری، [صفحه رسمی شرایط عضویت](https://davariran.com/Home/Editors/MembershipRules) را بررسی کنید.", "membership_initial_fee", ["شرایط عضویت", "هزینه کارت عضویت", "هزینه نمایش سالیانه"], 0.0, "payment")

    # تحویل فردا را تضمین نکن؛ زمان تقریبی و راه پیگیری را بیان کن.
    if "کارت" in qn and any(k in qn for k in ("تضمین", "حتما فردا", "حتماً فردا", "فردا میرسه", "فردا می رسه", "فردا میاد", "فردا به دستم")):
        return simple("🪪 زمان رسیدن کارت عضویت", "خیر؛ نمی‌توانم رسیدن کارت تا فردا را تضمین کنم. طبق FAQ داورایران، تأیید و صدور کارت در صورت تکمیل اطلاعات و بارگذاری عکس مناسب حدود یک ماه زمان می‌برد و پس از صدور با پست ارسال می‌شود؛ این زمان تقریبی است، نه تعهد به تاریخ مشخص. برای وضعیت درخواست خود، از [فرم تماس با ما](" + CONTACT_URL + ") یا بخش «تیکت‌های من» پیگیری کنید.", "card_delivery_no_guarantee", ["مدت زمان صدور کارت عضویت", "تماس با پشتیبانی"], 0.0, "card")

    # درخواست حکم حقوقی قطعی بدون بررسی منبع، باید صریحاً محدود شود.
    if "شرایط قانونی" in qn and "داور" in qn and any(k in qn for k in ("بدون بررسی", "قطعی بگو", "بدون سایت", "بررسی سایت نکن")):
        return simple("⚖️ شرایط قانونی داور شدن", "نمی‌توانم بدون بررسی مقررات جاری، شرایط قانونی داور شدن را قطعی اعلام کنم؛ پاسخ ممکن است به نوع داوری، موضوع اختلاف و مقررات ویژه مربوط باشد. برای اطلاعات عمومی، [راهنمای چگونه داور شوم](https://davariran.com/Home/Editors/HowCanBeAnArbitrator) را ببینید؛ برای تصمیم حقوقی مشخص، متن مقررات جاری یا مشاور حقوقی صلاحیت‌دار را مبنا قرار دهید.", "legal_requirements_need_source", ["چگونه داور شوم", "شرایط عضویت", "تماس با پشتیبانی"], 0.0, "legal_info")

    # تعداد دفعات آزمون را مستقیم پاسخ بده و عنوان را با سؤال هماهنگ نگه دار.
    if any(k in qn for k in ("چند بار میتونم ازمون بدم", "چند بار می تونم ازمون بدم", "چند بار می توانم ازمون بدهم", "چند بار میتونم آزمون بدم", "حداکثر چند بار آزمون", "چند دفعه آزمون بدم")):
        return simple("📝 حداکثر دفعات شرکت در آزمون", "طبق FAQ داورایران، برای هر دوره حداکثر **سه بار** امکان شرکت در آزمون ذکر شده است. شرکت در آزمون مجدد ممکن است هزینه داشته باشد؛ برای اقدام، وارد حساب شوید و بخش «آزمون‌های من» ← «نتایج» را بررسی کنید. اگر مقررات دوره تغییر کرده باشد، راهنمای همان دوره ملاک است.", "exam_attempt_limit", ["آزمون مجدد", "گواهینامه دوره", "تماس با پشتیبانی"], 0.0, "exam")

    # درخواست اعمال مدرک تحصیلی با عبارت اسمی را به FAQ مربوطه هدایت کن.
    if any(k in qn for k in ("اعمال اخرین مدرک تحصیلی", "اعمال مدرک تحصیلی", "مدرک تحصیلی جدیدم", "ثبت اخرین مدرک تحصیلی")):
        entry = engine.by_slug.get("faq_profile_latest_degree")
        if entry:
            return build_reply(entry, 0.0)
        return simple("🎓 اعمال آخرین مدرک تحصیلی", "وارد صفحه شخصی شوید و مدرک معتبر جدید را از بخش مربوط به اطلاعات تحصیلی بارگذاری کنید. بارگذاری به معنی تأیید فوری نیست؛ اگر مدرک اعمال نشد، از «تیکت‌های من» یا [فرم تماس با ما](" + CONTACT_URL + ") پیگیری کنید.", "faq_profile_latest_degree", ["چرا آخرین مدرک تحصیلی من نمایش داده نمی‌شود؟", "تماس با پشتیبانی"], 0.0, "edu_doc")

    # سؤال درباره قیمت کتاب بدون نام کتاب، نام محصول نیست؛ عنوان را روشن کن.
    if any(k in qn for k in ("هزینه این کتاب", "هزینه کتاب چقدره", "هزینه کتاب چقدر", "این کتاب حتما موجود", "این کتاب موجوده")) and ctx.get("last_topic") != "book":
        return simple("📚 قیمت و موجودی کتاب", "برای بررسی محصول درست، لطفاً **عنوان دقیق کتاب** را بفرستید یا آن را در [فهرست رسمی کتاب‌های داورایران](https://www.davariran.com/ProductFrns) انتخاب کنید. من بدون شناسایی محصول نمی‌توانم قیمت یا موجودی فعلی را تأیید کنم.", "book_title_clarification", ["فهرست کتاب‌ها", "تماس با پشتیبانی"], 0.0, "book")


    # --- عبارت‌های مبهم ---
    if qn in {normalize(a) for a in AMBIGUOUS}:
        return simple("🤝 انتخاب موضوع",
                      "📌 لطفاً مشخص فرمایید در چه زمینه‌ای نیاز به راهنمایی دارید:\n\n"
                      "• 👨‍⚖️ **عضویت و داور شدن**\n• 🪪 **کارت عضویت**\n• 🎓 **گواهینامه و آزمون**\n"
                      "• 📚 **دوره‌ها و دانلود فایل**\n• 🔑 **ورود و رمز عبور**\n• ⚖️ **ابطال رأی و انتخاب داور**",
                      "ambiguous", DEFAULT_CHIPS, 0.0)

    # «کارت عضویت» به‌تنهایی یک موضوع شناخته‌شده است؛ بلافاصله گزینه‌های عملی را نشان بده.
    if qn in {"کارت عضویت", "کارت عضویتم", "کارت عضویت داورایران"}:
        return simple("🪪 راهنمای کارت عضویت", "برای راهنمایی دقیق‌تر، کدام مورد را می‌خواهید؟", "clarify_membership_card", ["درخواست یا پیگیری کارت", "تمدید یا مفقودی کارت", "مدت زمان صدور کارت", "هزینه کارت عضویت"], 0.0, "card")

    # پاسخ‌های کوتاه وابسته به موضوع قبلی؛ پیش از جست‌وجوی عمومی بررسی می‌شوند تا زمینه از دست نرود.
    short_yes_no = {"رایگانه", "رایگان است", "پس رایگانه", "یعنی رایگانه", "رایگانمیشه", "رایگان میشه", "مجانیه", "مجانی است", "پولیه", "پولی است"}
    if qn in short_yes_no and ctx.get("last_topic") in {"payment", "membership", "display", "exam", "card", "course", "certificate"}:
        prior = normalize(ctx.get("last_title", ""))
        if "عضویت" in prior or ctx.get("last_topic") == "membership":
            return simple("💳 رایگان بودن عضویت", "طبق شرایط رسمی داورایران، **عضویت اولیه رایگان است**؛ اما نمایش عمومی به‌عنوان داور فعال و درخواست کارت عضویت خدمات جداگانه‌اند و ممکن است هزینه داشته باشند. مبلغ جاری را از صفحه رسمی همان خدمت بررسی کنید: [شرایط عضویت](https://davariran.com/Home/Editors/MembershipRules).", "membership_fee_followup", ["عضویت اولیه", "هزینه کارت عضویت", "هزینه نمایش سالیانه"], 0.0, "payment")
        if "آزمون" in prior or ctx.get("last_topic") == "exam":
            return simple("💳 هزینه آزمون مجدد", "طبق FAQ داورایران، آزمون مجدد ممکن است مستلزم پرداخت هزینه باشد؛ مبلغ دقیق را از گزینه «ثبت‌نام در آزمون مجدد» در بخش «آزمون‌های من» بررسی کنید. عدد ثابت و به‌روز در اطلاعات من تأیید نشده است.", "exam_retake_fee", ["آزمون مجدد", "تماس با پشتیبانی"], 0.0, "exam")
        if "کارت" in prior or ctx.get("last_topic") == "card":
            return simple("💳 هزینه کارت عضویت", "درخواست کارت عضویت در FAQ سایت به‌عنوان خدمت دارای فرایند و هزینه صدور معرفی شده، اما مبلغ جاری را از اطلاعات ثابت نمی‌توانم تأیید کنم. مبلغ را در صفحه درخواست کارت یا از [پشتیبانی](https://davariran.com/ContactUs/Create) بررسی کنید.", "membership_card_fee", ["درخواست کارت عضویت", "تماس با پشتیبانی"], 0.0, "card")
        if ctx.get("last_topic") == "display":
            return simple("💳 هزینه نمایش داور فعال", "عضویت اولیه رایگان است؛ اما نمایش عمومی مشخصات به‌عنوان داور فعال خدمت جداگانه‌ای است و ممکن است حق عضویت سالیانه داشته باشد. مبلغ جاری را از [شرایط رسمی عضویت](https://davariran.com/Home/Editors/MembershipRules) استعلام کنید.", "display_fee", ["شرایط عضویت", "چگونه داور شوم"], 0.0, "display")

    # --- مسیریابی قطعی به مدخل‌های منتخب ---
    slug = None

    # پرسش‌های مرتبط با احراز شرایط قانونی: بدون منبع دقیق، پاسخ قطعی حقوقی نساز.
    if "مدرک حقوق" in qn and any(k in qn for k in ("بدون", "ندارم", "لازم", "میتونم", "می توانم", "میشه", "می شود")) and "داور" in qn:
        return simple("⚖️ شرایط داور شدن بدون مدرک حقوق", "از اطلاعات تأییدشده‌ای که در اختیار دارم، نمی‌توانم یک حکم قطعی و یکسان برای همه انواع داوری اعلام کنم. شرایط ممکن است به نوع اختلاف، توافق طرفین و مقررات قابل اعمال بستگی داشته باشد. راهنمای [چگونه داور شوم](https://davariran.com/Home/Editors/HowCanBeAnArbitrator) را بررسی کنید و برای مورد مشخص از پشتیبانی یا مشاور حقوقی صلاحیت‌دار استعلام بگیرید.", "arbitrator_legal_eligibility_uncertain", ["چگونه داور شوم", "شرایط عضویت", "تماس با پشتیبانی"], 0.0, "legal_info")

    if any(k in qn for k in ("چطور بفهمم درخواست داور", "درخواست داور شدنم تایید", "درخواست داوری من تایید", "وضعیت درخواست داور شدن", "تایید شده درخواست داور")):
        return simple("🔎 پیگیری وضعیت درخواست داور شدن", "من به وضعیت زنده حساب یا درخواست شما دسترسی ندارم و نمی‌توانم تأیید شدن آن را بررسی کنم. وارد صفحه شخصی داورایران شوید و وضعیت درخواست یا پیام‌های حساب را بررسی کنید؛ اگر وضعیت مشخص نبود، از [فرم تماس با ما](" + CONTACT_URL + ") یا بخش «تیکت‌های من» پیگیری کنید. ثبت درخواست به‌تنهایی به معنی تأیید نیست.", "arbitrator_application_status", ["چگونه داور شوم", "تماس با پشتیبانی"], 0.0, "display")

    if any(k in qn for k in ("فقط عضو بشم", "فقط عضو شوم", "داور فعال نشم", "داور فعال نشوم", "نمایش داور فعال نشم", "نمایش داور فعال نشوم")):
        return simple("💳 عضویت بدون نمایش داور فعال", "عضویت اولیه با نمایش عمومی به‌عنوان داور فعال دو خدمت متفاوت‌اند. طبق شرایط عضویت داورایران، عضویت اولیه رایگان است؛ اگر فقط عضو شوید و مراحل جداگانه نمایش عمومی داور فعال را انجام ندهید، نباید فرض کنید مشخصات شما به‌طور خودکار در فهرست داوران فعال نمایش داده می‌شود. شرایط جاری را در [صفحه رسمی عضویت](https://davariran.com/Home/Editors/MembershipRules) بررسی کنید.", "membership_without_public_display", ["عضویت اولیه", "هزینه نمایش سالیانه", "شرایط عضویت"], 0.0, "membership")

    if any(k in qn for k in ("پاسخت اشتباهه", "پاسخت اشتباه است", "جوابت اشتباهه", "جوابت اشتباه است", "از کجا مطمئن", "چطور مطمئن بشم", "چطور مطمئن شوم")):
        return simple("🔎 بررسی و گزارش پاسخ", "حق دارید پاسخ مهم را بررسی کنید. پاسخ ربات را با راهنمای رسمی همان موضوع در سایت داورایران تطبیق دهید؛ اگر اختلافی دیدید، عنوان صفحه و متن پاسخ ربات را از طریق [فرم تماس با ما](" + CONTACT_URL + ") برای پشتیبانی بفرستید. من نباید اطلاعات تأییدنشده را قطعی جلوه بدهم.", "answer_verification", ["فهرست راهنماها", "تماس با پشتیبانی"], 0.0, "support")

    if any(k in qn for k in ("چطوری با پشتیبانی تماس", "چطور با پشتیبانی تماس", "راه تماس با پشتیبانی", "ارتباط با پشتیبانی چطور", "با پشتیبانی تماس بگیرم")):
        return simple("📞 راه‌های تماس با پشتیبانی", "برای ارتباط با داورایران می‌توانید از [فرم تماس با ما](" + CONTACT_URL + ") استفاده کنید. اگر حساب کاربری دارید، بخش «تیکت‌های من» هم برای پیگیری درخواست‌های مربوط به حساب مناسب است. اطلاعات تماس درج‌شده در سایت را در صفحه رسمی بررسی کنید تا از به‌روز بودن آن مطمئن شوید.", "contact", ["اطلاعات تماس رسمی داورایران", "تماس با پشتیبانی"], 0.0, "support")

    if any(k in qn for k in ("قبول شدم ولی گواهینامه", "قبول شدم اما گواهینامه", "قبول شدم و گواهینامه ندارم", "گواهینامه ام نیومده", "گواهینامه ام نیامده", "گواهینامه دوره ام کجا", "گواهینامه دوره کجا")):
        return simple("🎓 پیگیری گواهینامه پس از قبولی", "اگر آزمون را قبول شده‌اید اما گواهینامه را نمی‌بینید، وارد حساب داورایران شوید و بخش مربوط به دوره، آزمون‌ها یا گواهینامه‌های حساب را بررسی کنید. من وضعیت صدور شخصی شما را نمی‌بینم و نمی‌توانم زمان قطعی اعلام کنم. اگر گواهینامه نمایش داده نمی‌شود، از [فرم تماس با ما](" + CONTACT_URL + ") یا «تیکت‌های من» با ذکر نام دوره پیگیری کنید.", "certificate_after_pass_missing", ["گواهینامه دوره", "تماس با پشتیبانی"], 0.0, "certificate")

    # کتاب/خرید همیشه قبل از مسیر «داور شدن» بررسی می‌شود تا نیت‌ها با هم قاطی نشوند.
    # دنبال‌کردن «این کتاب» و «قیمتش» باید از عنوان محصول قبلی استفاده کند، نه اینکه کل جمله را نام کتاب فرض کند.
    book_followup = any(k in qn for k in ("این کتاب", "قیمتش", "قیمت این", "قیمت کتاب", "موجوده", "موجود است", "موجودی", "حتما موجود"))
    if book_followup and ctx.get("last_topic") == "book":
        prior_book = str(ctx.get("last_title") or ctx.get("last_query") or "").strip()
        known_product = any(k in prior_book for k in ("شرط و موافقتنامه داوری", "مجموعه قوانین و قواعد", "اسامی داوران"))
        if known_product:
            product_url = "https://www.davariran.com/ProductFrns"
            if "شرط" in prior_book or "موافقت" in prior_book:
                product_url = "https://www.davariran.com/ProductFrns/Details/f98e1600-4a7b-4eb2-a4ed-50f906978299"
            elif "مجموعه قوانین" in prior_book or "قواعد" in prior_book:
                product_url = "https://www.davariran.com/ProductFrns/Details/7414ad4a-0a8c-4594-8009-57d660facc90"
            return simple("📚 بررسی قیمت و موجودی کتاب", "منظورتان کتاب «" + prior_book.removeprefix("کتاب ") + "» است. قیمت و موجودی لحظه‌ای را از داده ثابت نمی‌توانم تأیید کنم؛ لطفاً صفحه رسمی محصول را باز کنید و قیمت و وضعیت موجودی فعلی را بررسی کنید: [مشاهده صفحه محصول](" + product_url + ").", "book_context_followup", ["فهرست کتاب‌ها", "تماس با پشتیبانی"], 0.0, "book")
        return simple("📚 بررسی قیمت و موجودی کتاب", "برای این گفت‌وگو عنوان کتاب قبلی را دارم، اما موجودی و قیمت فعلی را نمی‌توانم از اطلاعات ثابت تأیید کنم. لطفاً عنوان دقیق را در [فهرست رسمی محصولات داورایران](https://www.davariran.com/ProductFrns) جست‌وجو کنید یا عنوان را دوباره بفرستید تا مسیر مرتبط را راهنمایی کنم.", "book_context_followup", ["فهرست کتاب‌ها", "تماس با پشتیبانی"], 0.0, "book")

    if any(k in qn for k in ("برای خرید کتاب باید عضو", "برای خرید کتاب عضویت", "خرید کتاب باید عضو", "برای خریدش باید عضو")):
        return simple("📚 آیا برای خرید کتاب باید عضو باشم؟", "بله؛ طبق راهنمای فروشگاه داورایران، برای خرید محصولات باید عضو سامانه باشید. سپس صفحه محصول را باز کنید و قیمت و وضعیت موجودی همان صفحه را بررسی کنید؛ قیمت و موجودی را نباید از داده قدیمی قطعی دانست. [فهرست رسمی محصولات](https://www.davariran.com/ProductFrns).", "book_store_membership_required", ["فهرست کتاب‌ها", "تماس با پشتیبانی"], 0.0, "book")

    has_book = any(k in qn for k in ("کتاب", "کتابها", "کتاب ها", "خرید کتاب", "سفارش کتاب"))
    if has_book and any(k in qn for k in ("راهنمایی", "راهنمای خرید", "هنوز اسم", "اسم کتاب رو انتخاب نکردم", "اسم کتاب را انتخاب نکردم", "نمی دونم چه کتاب", "نمیدونم چه کتاب", "کدوم کتاب", "کدام کتاب", "پیشنهاد کتاب")):
        return simple("📚 راهنمای انتخاب کتاب",
                      "حتماً؛ می‌توانید [فهرست رسمی کتاب‌های داورایران](https://www.davariran.com/ProductFrns) را ببینید. دنبال کتابی درباره چه موضوعی هستید؛ مثلاً قوانین و قواعد داوری، شرط و موافقت‌نامه داوری یا فهرست اسامی داوران؟ وقتی موضوع را مشخص کنید، می‌توانم محصول مرتبط موجود در پایگاه دانش را معرفی کنم. قیمت و موجودی روز را باید در صفحه فعلی محصول بررسی کنید.",
                      "book_selection_help", ["فهرست کتاب‌ها", "شرط و موافقت‌نامه داوری", "مجموعه قوانین و قواعد مرتبط با داوری"], 0.0, "book")
    if has_book:
        if any(k in qn for k in ("اسامی داور", "فهرست داور", "لیست داور")):
            slug = "arbitrator_book"
        elif any(k in qn for k in ("شرط داوری", "موافقتنامه داوری", "موافقت نامه داوری", "قرارداد داوری")):
            slug = "book_arbitration_agreement"
        elif any(k in qn for k in ("مجموعه قوانین", "قوانین داوری", "قواعد داوری", "قانون داوری")):
            slug = "book_arbitration_rules"
        elif any(k in qn for k in ("شرایط داوری", "شرایط مربوط به داوری")):
            slug = "book_arbitration_topic_ambiguous"
        elif any(k in qn for k in ("شروع داوری", "فرایند داوری", "فرآیند داوری")):
            slug = "book_arbitration_process"
        elif any(k in qn for k in ("حقوق داوری", "آشنایی با داوری")):
            slug = "book_intro_arbitration_law"
        elif any(k in qn for k in ("آرای داور", "رای داور", "رأی داور", "نمونه رای", "نمونه رأی")):
            slug = "book_arbitrator_decisions"
        elif "آیین دادرسی" in qn:
            slug = "book_civil_procedure"
        elif "داوری" in qn:
            slug = "book_arbitration_topic_ambiguous"
        else:
            # نام کتاب یا نویسندهٔ نامشخص را به راهنمای عمومی خرید تبدیل نکن.
            explicit_store_help = any(k in qn for k in ("خرید کتاب از سایت", "چطور کتاب بخرم", "روش خرید کتاب", "فروشگاه کتاب", "فهرست کتابها", "فهرست کتاب ها", "محصولات داورایران", "برای خرید کتاب باید عضو", "خرید کتاب باید عضو", "قیمت این کتاب", "قیمت کتاب چقدر", "قیمت کتاب چقدره", "این کتاب حتما موجود", "این کتاب موجوده"))
            if not explicit_store_help:
                sessions.update(session_id, last_topic="book", last_title=query, last_query=query)
                return simple("🔎 بررسی عنوان کتاب", "عنوان «" + query + "» را در اطلاعات تأییدشده فروشگاه داورایران پیدا نکردم؛ نمی‌توانم موجود بودن آن را تأیید کنم. لطفاً [فهرست رسمی محصولات](https://www.davariran.com/ProductFrns) را بررسی کنید یا عنوان دقیق را برای پشتیبانی بفرستید.", "book_title_not_found", ["فهرست کتاب‌ها", "تماس با پشتیبانی"], 0.0, "book")
            slug = "book_store"

    # سؤال درباره مدارک داور شدن باید پاسخ مستقیم بگیرد، نه تکرار کل مراحل داور شدن.
    document_markers = ("چه مدارکی", "چه مدرکی", "مدارک لازم", "مدرک لازم", "مدارک مورد نیاز", "مدارک موردنیاز", "چه چیزهایی لازمه", "چی باید ارائه کنم")
    asks_documents = any(x in qn for x in document_markers) and any(x in qn for x in ("داور", "عضویت", "ثبت نام", "ثبتنام", "گواهینامه"))
    if asks_documents and not any(x in qn for x in ("مدرک تحصیلی", "بارگذاری گواهینامه", "اصالت مدرک")):
        return simple("📄 مدارک لازم برای داور شدن", "برای اینکه فهرست اشتباه ندهم: در اطلاعات تأییدشده‌ای که در اختیار دارم، فهرست کامل و یکسانی از مدارک لازم برای همه مسیرهای داوری مشخص نیست. شرایط می‌تواند به نوع عضویت، دوره یا درخواست نمایش به‌عنوان داور فعال بستگی داشته باشد. راهنمای رسمی [چگونه داور شوم](https://davariran.com/Home/Editors/HowCanBeAnArbitrator) و [شرایط عضویت](https://davariran.com/Home/Editors/MembershipRules) را بررسی کنید؛ اگر بگویید منظورتان ثبت‌نام اولیه، شرکت در دوره یا نمایش داور فعال است، مسیر دقیق‌تر را جدا می‌کنم.", "arbitrator_documents", ["چگونه داور شوم", "شرایط عضویت", "تماس با پشتیبانی"], 0.0, "display")

    # پیگیری روشنِ نوبت قبل: «پس برای عضویت اولیه پولی نمی‌دم؟»
    if (ctx.get("last_topic") in {"payment", "membership"}
            and "عضویت" in normalize(ctx.get("last_title", ""))
            and "عضویت اولیه" in qn
            and any(x in qn for x in ("پولی نمی", "پول نمی", "هزینه نمی", "پرداخت نمی", "پول بدم", "هزینه داره", "باید پول"))):
        return simple("💳 تأیید رایگان بودن عضویت اولیه", "بله؛ طبق شرایط رسمی داورایران، **عضویت اولیه رایگان است**. فقط توجه کنید که کارت عضویت و نمایش عمومی مشخصات به‌عنوان داور فعال خدمات جداگانه‌اند و ممکن است هزینه داشته باشند. مبلغ هر خدمت را از صفحه رسمی همان خدمت بررسی کنید: [شرایط عضویت](https://davariran.com/Home/Editors/MembershipRules).", "membership_fee_followup", ["عضویت اولیه", "هزینه کارت عضویت", "هزینه نمایش سالیانه"], 0.0, "payment")
    # نیت‌های دقیق‌تر FAQ؛ این قواعد قبل از تطبیق احتمالی اجرا می‌شوند تا گزینه نزدیک ولی نامرتبط برنده نشود.
    if not slug:
        if "کارت" in qn and any(k in qn for k in ("چه مدارکی", "مدارک لازم", "چه مدرکی", "مدارک لازمه")):
            return simple("🪪 مدارک لازم برای کارت عضویت", "برای جلوگیری از اعلام فهرست نادرست، مدارک لازم را از بخش «درخواست کارت عضویت» در صفحه شخصی و راهنمای رسمی سایت بررسی کنید؛ شرایط دقیق را نمی‌توانم برای همه حساب‌ها یکسان تأیید کنم. اگر بخش مربوط را پیدا نکردید، از [فرم تماس با ما](" + CONTACT_URL + ") استعلام بگیرید.", "card_required_documents", ["درخواست کارت عضویت", "مدت زمان صدور کارت", "تماس با پشتیبانی"], 0.0, "card")
        elif "عکس" in qn and "کارت" in qn and any(k in qn for k in ("بارگذاری", "آپلود", "کجا", "بفرستم", "ثبت کنم")):
            return simple("🪪 بارگذاری عکس کارت عضویت", "طبق راهنمای کارت عضویت، عکس پرسنلی باکیفیت برای صدور کارت لازم است؛ محل دقیق بارگذاری را از صفحه شخصی و گزینه «درخواست کارت عضویت» بررسی کنید. اگر این گزینه را نمی‌بینید، از [فرم تماس با ما](" + CONTACT_URL + ") راهنمایی بگیرید.", "card_photo_upload", ["درخواست کارت عضویت", "مدت زمان صدور کارت", "تماس با پشتیبانی"], 0.0, "card")
        elif any(k in qn for k in ("کارت عضویت اجباری", "کارت نگیرم", "بدون کارت عضویت", "داشتن کارت لازمه", "کارت عضویت اختیاری")):
            slug = "faq_member_card_optional"
        elif any(k in qn for k in ("کارت عضویت مجوز", "کارت داورایران پروانه", "کارت عضویت ارزش قانونی", "کارت عضویت چه اعتباری", "کارت عضویت به چه درد")):
            slug = "faq_card_value"
        elif "کارت" in qn and any(k in qn for k in ("چطور", "چگونه", "درخواست", "بگیرم", "گرفتن", "میخوام", "خواهم", "از کجا")):
            slug = "faq_card_request_steps"
        elif any(k in qn for k in ("برای نمره بهتر", "نمره بهتر", "نمره بالاتر", "قبول شدم دوباره", "قبولی دوباره آزمون")):
            slug = "faq_passed_no_retake"
        elif any(k in qn for k in ("امتیازهای من کجا", "امتیازم کجا", "امتیاز من کجا", "جزئیات امتیاز", "امتیاز عملکردم را از کجا", "رتبه علمی خودم کجا")):
            slug = "faq_academic_points_visibility"
        elif any(k in qn for k in ("لینک دعوت کجا", "دعوت دوستان امتیاز", "چطور لینک اختصاصی", "امتیاز معرفی دوستان", "چطور امتیاز عملکرد جمع")):
            slug = "faq_performance_invite_steps"
        elif any(k in qn for k in ("شماره پشتیبانی", "تلفن داورایران", "شماره دفتر داورایران", "ایمیل داورایران", "آدرس ایمیل پشتیبانی")):
            slug = "faq_site_contact_details"
        elif any(k in qn for k in ("راهنمای تصویری", "آموزش استفاده از سایت", "فهرست راهنما", "راهنماهای سایت")):
            slug = "faq_help_topics_index"
        elif any(k in qn for k in ("اصالت مدرک", "استعلام شماره گواهینامه", "بررسی اصالت گواهینامه", "گواهینامه اصله")):
            slug = "faq_certificate_authentication"
        elif "تضمین" in qn and any(k in qn for k in ("نمایش", "داور فعال", "پرونده", "ارجاع")):
            slug = "faq_arbitrator_get_cases_realistic"
        elif any(k in qn for k in ("اسمم در لیست داوران", "اسمم تو لیست داوران", "عضو شدم اما داور فعال", "ثبت نام کردم چرا در لیست داوران", "بعد از ثبت نام اسمم", "ثبت نام به معنی نمایش")):
            slug = "faq_member_public_display_not_guaranteed"
        elif any(k in qn for k in ("پاسخ های آزمون", "جواب های آزمون", "با موبایل آزمون", "با گوشی آزمون", "آزمون با موبایل")) and any(k in qn for k in ("ثبت", "گوشی", "موبایل", "ذخیره")):
            slug = "faq_exam_mobile_answers"
        elif any(k in qn for k in ("چند روز بعد ثبت نام آزمون", "آزمون فعال میشه", "آزمون هنوز فعال", "از کی میتونم آزمون", "زمان شروع آزمون")):
            slug = "faq_course_exam_eligibility"
        elif any(k in qn for k in ("بعد قبولی مدرک کی", "چند روز بعد قبولی", "گواهینامه بعد از قبولی", "مدرکم بعد آزمون", "صدور مدرک چند روز")):
            slug = "faq_certificate_issuance_time"
        elif any(k in qn for k in ("نمایش داور فعال پرونده", "ثبت نام به معنی نمایش", "اسمم تو لیست داوران", "بعد از ثبت نام اسمم")):
            slug = "faq_member_public_display_not_guaranteed"

    if not slug:
        if qn in {"مدت زمانش چقدره", "چقدر طول میکشه", "چقدر زمان میبره", "مدت زمانش چطوره"} and ctx.get("last_topic") == "certificate":
            slug = "certificate_duration"
        elif qn in {"مدت زمانش چقدره", "چقدر طول میکشه", "چقدر زمان میبره", "مدت زمانش چطوره"} and ctx.get("last_topic") == "card":
            slug = "membership_card_duration"
        elif qn in {"درست نشد", "مشکلم حل نشده", "هنوز حل نشده", "بازم نشد", "چطور پیگیری کنم", "اگه طول کشید چطور پیگیری کنم"} and ctx.get("last_topic") == "login":
            slug = "login_help"
        elif (qn in {"چطور پیگیری کنم", "چطور پیگیری کنم؟", "اگه طول کشید چطور پیگیری کنم"} or ("تمدید" in qn and ctx.get("last_topic") == "card")) and ctx.get("last_topic") == "card":
            slug = "membership_card"
        elif "کارت" in qn and any(k in qn for k in ("کی میرسه", "کی می رسه", "کی میرسد", "نرسیده", "به دستم", "چند روز", "مدت زمان", "زمان صدور", "کی میاد", "کی می آید")):
            slug = "faq_card_duration" if "faq_card_duration" in engine.by_slug else "membership_card_duration"
        elif "عضویت" in qn and "کارت" not in qn and any(k in qn for k in ("تمدید", "تمدیدش", "تمدید کنم", "تمدید کنم")):
            return simple("🤔 منظور از تمدید عضویت چیست؟",
                          "برای اینکه راهنمایی اشتباه ندهم، منظورتان کدام مورد است؟\n\n"
                          "• **تمدید یا صدور کارت عضویت**\n"
                          "• **تمدید نمایش عمومی به‌عنوان داور فعال**\n"
                          "• **مشکل در ورود یا فعال بودن حساب کاربری**\n\n"
                          "این موارد یکسان نیستند. گزینه مربوط را در صفحه شخصی بررسی کنید یا از [پشتیبانی داورایران](" + CONTACT_URL + ") استعلام بگیرید.",
                          "clarify_membership_renewal", ["تمدید کارت عضویت", "هزینه نمایش داور فعال", "مشکل ورود"], 0.0, "membership")
        elif "کارت" in qn and any(k in qn for k in ("چطور", "چگونه", "درخواست", "بگیرم", "گرفتن", "میخوام", "خواهم", "گم", "تمدید", "صادر")):
            slug = "membership_card"
        elif any(k in qn for k in ("چه کسانی می توانند عضو", "چه کسی می تواند عضو", "چه کسانی میتونن عضو", "چه کسی میتونه عضو", "چه کسانی می توانند ثبت نام", "عضویت رایگان", "همه می توانند عضو", "ثبت نام حقیقی", "ثبت نام شرکت ها", "ثبت نام حقوقی")):
            slug = "faq_membership_types"
        elif any(k in qn for k in ("مزایای عضویت حقیقی", "مزایای عضو حقیقی", "مزایای عضویت فردی", "مزایای عضویت شخص حقیقی")):
            slug = "faq_individual_benefits_detail"
        elif any(k in qn for k in ("مزایای عضویت حقوقی", "مزایای شرکت", "مزایای عضویت شرکت", "مزایای شخص حقوقی")):
            slug = "faq_legal_entity_benefits_detail"
        elif any(k in qn for k in ("استعلام اصالت", "اصالت گواهینامه", "اعتبار گواهینامه", "استعلام مدرک")):
            slug = "faq_certificate_authentication_steps"
        elif any(k in qn for k in ("قابل ارجاع به داوری نیست", "قابل ارجاع به داوری نیستند", "چه دعاوی قابل ارجاع", "دعاوی غیرقابل داوری", "جرم را داوری", "طلاق داوری")):
            slug = "faq_arbitrable_disputes"
        elif "شرط داوری" in qn and any(k in qn for k in ("قرارداد", "متن", "نمونه", "چیست", "بنویسم")):
            slug = "faq_arbitration_clause"
        elif any(k in qn for k in ("موافقت نامه داوری", "موافقتنامه داوری", "شرایط قرارداد داوری")):
            slug = "faq_arbitration_agreement"
        elif any(k in qn for k in ("میانجیگری", "میانجی گری", "میانجیگر")) and any(k in qn for k in ("فرق", "تفاوت", "چیست", "داوری")):
            slug = "faq_arbitration_vs_mediation"
        elif any(k in qn for k in ("امتیاز عملکرد", "امتیاز علمی", "دعوت دوستان", "رتبه علمی")):
            slug = "faq_performance_score" if "عملکرد" in qn or "دعوت دوستان" in qn else "faq_academic_score"
        elif any(k in qn for k in ("دانلود می شود اما پخش", "دانلود میشه ولی پخش", "پخش نمی شود", "پخش نمیشه", "باز نمی شود فایل", "فایل txt", "پسوند فایل")):
            slug = "faq_download_mp4"
        elif any(k in qn for k in ("سایت باز نمیشه", "سایت باز نمیشود", "سایت باز نمی شود", "سایت بالا نمیاد", "سایت لود نمیشه", "سایت داور ایران باز نمیشه", "سایت داور ایران باز نمیشود", "سایت داورایران باز نمیشود")):
            slug = "site_not_loading"
        elif any(k in qn for k in ("فایل دوره", "فایل های دوره", "دانلود دوره", "دانلود فایل", "فایل آموزشی")):
            slug = "course_download"
        # سؤال هزینه آزمون مجدد نباید پاسخ عمومی «اگر قبول نشدم چه کنم؟» بگیرد.
        elif any(k in qn for k in ("هزینه", "قیمت", "پول", "مبلغ", "چقدر باید پرداخت")) and any(k in qn for k in ("آزمون مجدد", "ازمون مجدد", "آزمون دوباره", "امتحان مجدد", "امتحان دوباره", "تکرار آزمون")):
            reply = simple("💳 هزینه آزمون مجدد", "طبق راهنمای آزمون داورایران، شرکت در آزمون مجدد ممکن است مستلزم پرداخت هزینه باشد؛ اما مبلغ دقیق و به‌روز را در اطلاعات تأییدشده ندارم و نمی‌خواهم عدد حدسی اعلام کنم. وارد حساب شوید و در «آزمون‌های من» ← «نتایج»، گزینه «ثبت‌نام در آزمون مجدد» را بررسی کنید؛ هزینه قابل پرداخت باید در روند ثبت‌نام نمایش داده شود. اگر مبلغ مشخص نبود، از پشتیبانی استعلام بگیرید.", "exam_retake_fee", ["آزمون مجدد", "تماس با پشتیبانی"], 0.0, "exam")
            sessions.update(session_id, last_topic="exam", last_title="هزینه آزمون مجدد")
            return reply
        # آزمون مجدد: عبارت‌های طبیعی مثل «آزمون اول رو افتادم» را نیز تشخیص بده.
        elif any(k in qn for k in ("آزمون مجدد", "ازمون مجدد", "دوباره آزمون", "دوباره امتحان", "آزمون اول", "ازمون اول", "افتادم", "مردود شدم", "رد شدم", "دوباره امتحان بدم", "از نو امتحان")) and any(k in qn for k in ("آزمون", "ازمون", "امتحان", "افتادم", "مردود", "رد شدم")):
            slug = "faq_exam_retake" if "faq_exam_retake" in engine.by_slug else None
        # «گواهینامه بگیرم» یک درخواست مشخص برای دریافت مدرک است؛ نباید صرفاً
        # به‌خاطر نبودن عبارت «بعد از قبولی» به گزینه‌های مبهم فرستاده شود.
        elif "گواهینامه" in qn and any(k in qn for k in ("بگیرم", "دریافت", "صادر", "دانلود", "گرفتن", "میخواهم", "خواهم", "چطور", "چگونه", "از کجا")):
            slug = "faq_certificate_after_pass" if "faq_certificate_after_pass" in engine.by_slug else "certificate"
        elif "ایمیل" in qn and any(k in qn for k in ("ابلاغ", "رای", "رأی", "داور")):
            slug = "article_email_notice"
        elif any(k in qn for k in ("ابلاغ", "اجرای رای", "اجرای رأی", "اجراییه")) and any(k in qn for k in ("رای", "رأی", "داور", "داوری")):
            slug = "article_award_enforcement"
        elif "شرط" in qn and "موافقتنامه" in qn and "کتاب" in qn:
            slug = "book_arbitration_agreement"
        elif ((any(k in qn for k in ("نه اینکه", "نه این که", "نه این که خودم")) and "داور" in qn
               and any(k in qn for k in ("خواهم", "میخام", "میخوام", "نیاز به داور")))
              or ("داور خواهم" in qn and any(k in qn for k in ("نمیخواهم داور شدن", "نمیخواهم داور بشم", "نمیخواهم داور شوم")))):
            slug = "get_arbitrator"
        elif ("داور" in qn and any(k in qn for k in ("پیدا کنم", "برای اختلاف", "بین دو نفر", "داور خواهم", "خواهم داور"))
              and not any(k in qn for k in ("داور شدن", "داور بشم", "داور شوم", "خودم داور"))):
            slug = "get_arbitrator"
        elif any(k in qn for k in ("هزینه عضویت", "قیمت عضویت", "حق عضویت", "هزینه عضو شدن", "عضویت چقدره", "عضویت چقدر است")):
            reply = simple("💳 هزینه عضویت داورایران", "هزینه به نوع عضویت و خدمت موردنظر بستگی دارد؛ عضویت اولیه، کارت عضویت و نمایش عمومی به‌عنوان داور فعال را نباید یکی دانست. مبلغ جاری را بدون تأیید صفحه رسمی اعلام نمی‌کنم. لطفاً نوع موردنظر را مشخص کنید یا شرایط و تعرفه‌های رسمی را بررسی کنید: [شرایط عضویت](https://davariran.com/Home/Editors/MembershipRules) و [مزایای عضویت](https://davariran.com/Home/Editors/ContactMembershipBenefits).", "clarify_membership_fee", ["هزینه کارت عضویت", "هزینه نمایش سالیانه", "شرایط عضویت"], 0.0, "payment")
            sessions.update(session_id, last_topic="payment", last_title="هزینه عضویت داورایران")
            return reply
        elif qn in {"رایگانه", "رایگان است", "پس رایگانه", "یعنی رایگانه", "رایگانمیشه", "رایگان میشه"} and ctx.get("last_topic") == "payment":
            if "عضویت" in ctx.get("last_title", ""):
                return simple("💳 رایگان بودن عضویت", "طبق شرایط عضویت داورایران، **عضویت اولیه رایگان است**؛ اما صدور یا تمدید کارت و نمایش عمومی مشخصات به‌عنوان داور فعال ممکن است هزینه جداگانه داشته باشد. برای مبلغ جاری، صفحه رسمی همان خدمت را بررسی کنید: [شرایط عضویت](https://davariran.com/Home/Editors/MembershipRules).", "membership_fee_followup", ["عضویت اولیه", "هزینه کارت عضویت", "هزینه نمایش سالیانه"], 0.0, "payment")
            return simple("💳 روشن‌کردن هزینه", "منظورتان کدام خدمت است؟ هزینه آزمون مجدد، کارت عضویت و نمایش سالیانه شرایط متفاوتی دارند. اگر منظورتان همان خدمت قبلی است، نام آن را بگویید تا دقیق‌تر راهنمایی کنم.", "clarify_fee", ["هزینه آزمون مجدد", "هزینه کارت عضویت", "هزینه نمایش سالیانه"], 0.0, "payment")
        elif "هزینه" in qn and "کارت" in qn:
            return simple("هزینه صدور کارت عضویت", "مبلغ دقیق و به‌روز صدور یا تمدید کارت را در اطلاعات عمومی تأییدشده ندارم و نمی‌خواهم مبلغ حدسی اعلام کنم. لطفاً صفحه شخصی و گزینه‌های مربوط به کارت را بررسی کنید یا از [پشتیبانی داورایران](" + CONTACT_URL + ") استعلام بگیرید.", "membership_card_fee", ["کارت عضویت", "پیگیری کارت عضویت", "تماس با پشتیبانی"], 0.0, "card")
        elif any(k in qn for k in ("مقالات حقوقی", "فهرست مقالات", "مقالات داورایران")):
            slug = "legal_articles"
        elif any(k in qn for k in ("قیمت کتاب", "کتاب های داورایران", "فروشگاه داورایران", "خرید کتاب", "کتاب ناموجود")):
            slug = "book_store"
        elif any(k in qn for k in ("هزینه اش", "هزینش", "هزینه چقدره", "قیمتش چقدره")) and not any(k in qn for k in ("کارت", "عضویت", "کتاب", "دوره", "گواهینامه", "نمایش")) and not ctx.get("last_topic"):
            return simple("💳 مشخص کردن هزینه", "منظورتان هزینه کدام خدمت است؟ مثلاً هزینه دوره، کارت عضویت یا نمایش سالیانه به‌عنوان داور؟ برای جلوگیری از اعلام مبلغ اشتباه، لطفاً خدمت موردنظر را مشخص کنید.", "clarify_fee", ["هزینه دوره", "هزینه کارت عضویت", "هزینه نمایش سالیانه"], 0.0, "payment")
        elif any(k in qn for k in ("زنگ بزنه", "زنگ بزند", "با من تماس بگیر", "یه نفر بهم زنگ", "کارشناس تماس")):
            slug = "contact"
        elif any(k in qn for k in ANNUL_MARKERS):
            slug = "annulment"
        elif "پروانه" in qn or "مجوز داوری" in qn:
            slug = "no_license"
        # اصلاح خطای مهم نیت: اگر کاربر صریحاً می‌گوید «داور می‌خواهم، نه اینکه
        # خودم داور شوم»، نیتِ پیدا کردن/گرفتن داور بر نیتِ داور شدن مقدم است.
        elif (any(k in qn for k in ("نه اینکه", "نه این که", "نه این که خودم"))
              and any(k in qn for k in ("داور خواهم", "داور می خواهم", "داور میخام", "داور میخوام", "نیاز به داور", "داور برای", "داور پرونده"))):
            slug = "get_arbitrator"
        # درخواست «می‌خواهم داور شوم» را از «داور می‌خواهم» جدا می‌کنیم.
        elif any(k in qn for k in ("خواهم داور شدن", "خواهم داور بشوم", "خواهم داور شوم", "میخواهم داور شدن", "می خواهم داور شدن")):
            slug = "become_arbitrator"
        elif (any(k in qn for k in ("نه اینکه", "نه این که", "نه این که خودم"))
              and "داور" in qn and any(k in qn for k in ("میخواهم", "می خواهم", "میخام", "میخوام", "نیاز به داور"))):
            slug = "get_arbitrator"
        elif (any(k in qn for k in ("داور میخواهم", "داور می خواهم", "داور میخام", "داور میخوام", "داور خواهم"))
              and not any(k in qn for k in ("داور بشم", "داور شوم", "داور شدن", "خودم داور"))):
            slug = "get_arbitrator"
        elif any(k in qn for k in BECOME_MARKERS):
            slug = "become_arbitrator"
        elif any(k in qn for k in GET_MARKERS) or re.search(r"داور\s+خواهم|خواهم\s+داور", qn) or "داور حقوقی در شهر" in qn:
            slug = "get_arbitrator"
        elif re.search(r"(?:باطل|لغو|انصراف|ابطال)", qn) and re.search(r"(?:کارت|عضویت|ثبتنام)", qn):
            slug = "refund_policy"
        elif "هزینه نمایش" in qn or "نمایش سالیانه" in qn:
            slug = "display_fee"
        elif re.search(r"(?:ورود|وارد|رمز|عبور|لاگین|پسوورد)", qn) and re.search(r"(?:نتوانم|نمیشود|نمیشم|نمیشه|نمی شم|فراموش|مشکل|نمیاد|نمی آید|خطا|یادم رفته|یادم نیست|یادم نیس|یادم نی|یام نیست|یادم نیس)", qn):
            slug = "login_help"
        elif any(k in qn for k in ("تمدید کارت", "کارت را تمدید", "کارت عضویت تمدید")):
            slug = "membership_card"
        elif any(k in qn for k in ("مدت زمان کارت", "کارت چند روز", "چند روزه به دستم", "زمان صدور کارت")):
            slug = "membership_card_duration"
        elif any(k in qn for k in ("گم شده", "گم کردم", "کارتم گم")) and "کارت" in qn:
            slug = "membership_card"
        elif len(qn.split()) <= 4 and any(k in qn for k in CONTACT_MARKERS):
            slug = "contact"
    if slug and slug in engine.by_slug:
        res = build_reply(engine.by_slug[slug], 0.0)
        saved_topic = "book" if str(slug).startswith("book_") or slug == "arbitrator_book" else res["topic"]
        sessions.update(session_id, last_topic=saved_topic, last_title=engine.by_slug[slug]["title"], last_query=query if saved_topic == "book" else "")
        return res

    # تک‌واژه‌های نامشخص را به پاسخ نامرتبطِ بازیابی‌شده تبدیل نکن.
    if len(tokenize(qn)) == 1 and len(qn.split()) == 1 and len(qn) <= 6:
        return simple("🤝 راهنمایی و پشتیبانی", "این عبارت برای تشخیص موضوع کافی نیست. لطفاً سؤال را کامل‌تر بنویسید؛ مثلاً درباره عضویت، آزمون، کتاب یا ورود به حساب.", "fallback", ["کارت عضویت", "آزمون", "ورود و رمز عبور"], 0.0)

    # --- جست‌وجوی BM25 ---
    hits = engine.search(query, topic_hint=ctx.get("last_topic"), top_k=3)
    if hits:
        best, score, cov = hits[0]
        n_tok = len(set(tokenize(query)))
        second_score = hits[1][1] if len(hits) > 1 else 0.0
        # پاسخ مستقیم نیازمند پوشش خوب و فاصله از گزینه بعدی است؛ وگرنه فقط شفاف‌سازی می‌کنیم.
        strong = score >= (2.8 if n_tok >= 2 else 3.6) and cov >= 0.72 and (len(hits) == 1 or score >= second_score * 1.12)
        if strong:
            conf = 0.0  # امتیاز بازیابی، احتمال صحت پاسخ نیست؛ عدد اطمینان نمایشی نمی‌دهیم
            sessions.update(session_id, last_topic=best["topic"], last_title=best["title"])
            return build_reply(best, conf)
        # نیمه‌مطمئن: چند گزینه پیشنهاد بده
        opts = []
        for e, _, _ in hits:
            if e["title"] and e["title"] not in opts:
                opts.append(e["title"])
        if opts:
            return simple("🤔 منظور شما کدام است؟",
                          "🔍 پاسخ دقیقی پیدا نکردم؛ آیا یکی از موضوعات زیر مدنظر شماست؟\n\n"
                          + "\n".join(f"• **{o}**" for o in opts[:3]) +
                          "\n\n✍️ لطفاً پرسش خود را کمی دقیق‌تر بنویسید.", "did_you_mean", opts[:3], 0.0)

    return simple("🤝 راهنمایی و پشتیبانی",
                  "😔 برای این پرسش پاسخ مطمئنی در اطلاعات موجود پیدا نکردم.\n\n"
                  "💡 لطفاً موضوع را دقیق‌تر بنویسید؛ مثلاً: **کارت عضویت، گواهینامه، آزمون، دانلود دوره، ورود و رمز عبور**.\n\n"
                  f"🔔 برای پیگیری رسمی از **«تیکت‌های من»** یا [فرم تماس با ما]({CONTACT_URL}) استفاده کنید.\n"
                  "🔒 رمز عبور یا کد ورود خود را در چت ارسال نکنید.",
                  "fallback", ["تماس با پشتیبانی"] + DEFAULT_CHIPS[:3], 0.0)


# ==========================================
# ۶. رابط کاربری
# ==========================================
HTML_PAGE = r"""<!DOCTYPE html>
<html lang="fa" dir="rtl">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>سامانه جامع داوری ایران</title>
<link href="https://cdn.jsdelivr.net/gh/rastikerdar/vazirmatn@v33.003/Vazirmatn-font-face.css" rel="stylesheet">
<style>
:root{--bg:linear-gradient(135deg,#f8fafc,#e2e8f0);--chat:#fff;--body:#f8fafc;--bd:#e2e8f0;--tx:#1e293b;--sub:#64748b;
--head:linear-gradient(135deg,#1e3a8a,#2563eb);--bot:#fff;--chip:#f1f5f9;--chipx:#334155;--inp:#fff;--inpx:#0f172a;--inpb:#cbd5e1;
--sug:#fff;--sugh:#f1f5f9;--sh:0 20px 40px rgba(0,0,0,.16);--dot:#2563eb;--acc:#2563eb;--link:#1d4ed8}
body.dark{--bg:linear-gradient(135deg,#0f172a,#1e293b);--chat:#1e293b;--body:#0f172a;--bd:#334155;--tx:#f1f5f9;--sub:#94a3b8;
--head:linear-gradient(135deg,#0f172a,#1e3a8a);--bot:#1e293b;--chip:#1e293b;--chipx:#cbd5e1;--inp:#1e293b;--inpx:#f8fafc;--inpb:#475569;
--sug:#1e293b;--sugh:#334155;--sh:0 20px 40px rgba(0,0,0,.55);--dot:#60a5fa;--link:#93c5fd}
*{box-sizing:border-box;margin:0;padding:0;font-family:'Vazirmatn',Tahoma,sans-serif}
body{background:var(--bg);min-height:100vh;overflow:hidden;transition:background .3s}
.landing{display:flex;flex-direction:column;align-items:center;justify-content:center;height:100vh;color:var(--sub);text-align:center;padding:20px}
.landing h1{font-size:1.8rem;color:var(--tx);margin-bottom:8px}
.widget{position:fixed;bottom:25px;right:25px;z-index:9999;display:flex;flex-direction:column;align-items:flex-end}
.prompt{background:var(--chat);color:var(--tx);padding:12px 18px;border-radius:18px;border-bottom-right-radius:4px;box-shadow:0 10px 25px -5px rgba(0,0,0,.15);
border:1px solid var(--bd);margin-bottom:12px;cursor:pointer;display:flex;align-items:center;gap:10px;font-size:.88rem}
.prompt.hide{display:none}.prompt-x{color:#94a3b8;font-size:1.1rem}.prompt-x:hover{color:#ef4444}
.launch{width:62px;height:62px;border-radius:50%;background:linear-gradient(135deg,#2563eb,#1d4ed8);color:#fff;border:none;box-shadow:0 8px 24px rgba(37,99,235,.35);
cursor:pointer;font-size:1.8rem;position:relative;transition:transform .3s}.launch:hover{transform:scale(1.08)}
.ring{position:absolute;inset:0;border-radius:50%;border:2px solid #3b82f6;animation:rp 2.2s infinite ease-out;pointer-events:none}
@keyframes rp{0%{transform:scale(1);opacity:.85}100%{transform:scale(1.55);opacity:0}}
.box{position:fixed;bottom:98px;right:25px;width:410px;height:600px;max-height:calc(100vh - 120px);background:var(--chat);border-radius:24px;box-shadow:var(--sh);
border:1px solid var(--bd);display:flex;flex-direction:column;overflow:hidden;z-index:10000;opacity:0;pointer-events:none;transform:translateY(30px) scale(.92);
transition:all .35s cubic-bezier(.16,1,.3,1)}
.box.open{opacity:1;pointer-events:auto;transform:none}
.head{background:var(--head);color:#fff;padding:12px 18px;display:flex;justify-content:space-between;align-items:center}
.hi{display:flex;align-items:center;gap:10px}.av{width:38px;height:38px;background:rgba(255,255,255,.2);border-radius:50%;display:flex;align-items:center;justify-content:center;font-size:1.2rem}
.ht h3{font-size:.95rem}.ht span{font-size:.72rem;opacity:.85}
.hb{background:rgba(255,255,255,.12);border:none;color:#fff;border-radius:8px;width:30px;height:30px;cursor:pointer;font-size:1rem;margin-right:4px}.hb:hover{background:rgba(255,255,255,.25)}
.body{flex:1;overflow-y:auto;padding:14px;display:flex;flex-direction:column;gap:12px;background:var(--body)}
.msg{max-width:90%;padding:10px 14px;border-radius:14px;font-size:.88rem;line-height:1.85;word-break:break-word}
.user{align-self:flex-start;background:var(--acc);color:#fff;border-bottom-right-radius:3px}
.bot{align-self:flex-end;background:var(--bot);color:var(--tx);border:1px solid var(--bd);border-bottom-left-radius:3px;box-shadow:0 2px 4px rgba(0,0,0,.04)}
.subj{font-weight:700;color:#3b82f6;margin-bottom:6px;font-size:.9rem;border-bottom:1px solid var(--bd);padding-bottom:5px}
.bot b{color:var(--tx);font-weight:700}.bot a{color:var(--link);text-decoration:underline;word-break:break-all}
.bot .sep{border:none;border-top:1px dashed var(--bd);margin:8px 0}
.conf{font-size:.7rem;background:rgba(59,130,246,.15);color:#3b82f6;padding:2px 8px;border-radius:8px;display:inline-block;margin-top:6px}
.typing{display:flex;gap:5px;padding:12px 16px;background:var(--bot);border:1px solid var(--bd);border-radius:14px;align-self:flex-end;width:fit-content}
.dot{width:7px;height:7px;background:var(--dot);border-radius:50%;animation:tb 1.4s infinite ease-in-out both}
.dot:nth-child(1){animation-delay:-.32s}.dot:nth-child(2){animation-delay:-.16s}
@keyframes tb{0%,80%,100%{transform:scale(.6);opacity:.4}40%{transform:scale(1.15);opacity:1}}
.quick{display:flex;gap:6px;overflow-x:auto;padding:8px 12px;background:var(--chat);border-top:1px solid var(--bd);white-space:nowrap}
.chip,.fu{background:var(--chip);color:var(--chipx);border:1px solid var(--bd);padding:5px 10px;border-radius:10px;font-size:.75rem;cursor:pointer;transition:.2s}
.chip:hover{background:#3b82f6;color:#fff;border-color:#3b82f6}
.fubox{display:flex;gap:5px;flex-wrap:wrap;margin-top:8px;padding-top:7px;border-top:1px dashed var(--bd)}
.fu{background:rgba(37,99,235,.1);color:#3b82f6;border-color:rgba(37,99,235,.25)}.fu:hover{background:rgba(37,99,235,.22)}
.iw{position:relative;background:var(--chat);border-top:1px solid var(--bd)}
.sp{position:absolute;bottom:calc(100% + 4px);left:12px;right:12px;background:var(--sug);border:1px solid var(--bd);border-radius:14px;box-shadow:0 10px 25px rgba(0,0,0,.18);max-height:190px;overflow-y:auto;z-index:10005;display:none}
.sp.show{display:block}.si{padding:9px 12px;font-size:.82rem;color:var(--tx);cursor:pointer;border-bottom:1px solid var(--bd)}.si:last-child{border:none}.si:hover{background:var(--sugh);color:#3b82f6}
.ia{padding:10px 12px;display:flex;gap:8px}
.inp{flex:1;background:var(--inp);color:var(--inpx);border:1px solid var(--inpb);border-radius:10px;padding:8px 12px;font-size:.86rem;outline:none}.inp:focus{border-color:var(--acc)}
.send{background:var(--acc);color:#fff;border:none;border-radius:10px;padding:8px 16px;font-size:.85rem;font-weight:600;cursor:pointer}.send:disabled{background:#94a3b8;cursor:not-allowed}
@media(max-width:480px){.box{width:calc(100vw - 30px);right:15px;bottom:85px;height:75vh}.widget{right:15px;bottom:15px}}
</style>
</head>
<body>
<div class="landing"><h1>⚖️ سامانه جامع داوری ایران</h1><p>مرکز تخصصی داوری، آموزش و حل و فصل اختلافات حقوقی کشور</p></div>

<div class="widget">
  <div class="prompt" id="prompt"><span>💬 سوالی دارید؟ ۲۴ ساعته در خدمت شما هستم</span><span class="prompt-x" id="promptX">×</span></div>
  <button class="launch" id="launch" title="دستیار هوشمند داورایران"><div class="ring"></div><span>⚖️</span></button>
</div>

<div class="box" id="box">
  <div class="head">
    <div class="hi"><div class="av">⚖️</div><div class="ht"><h3>دستیار هوشمند داورایران</h3><span>🟢 پاسخگوی آنلاین ۲۴ ساعته</span></div></div>
    <div><button class="hb" id="theme" title="تغییر تم">🌙</button><button class="hb" id="closeBtn" title="بستن">×</button></div>
  </div>
  <div class="body" id="chat">
    <div class="msg bot"><div class="subj">🌸 خوش آمدید</div>
      <div>👋 سلام! چطور می‌توانم در خصوص <b>عضویت و داور شدن</b>، <b>کارت عضویت</b>، <b>گواهینامه و آزمون</b>، <b>دوره‌ها</b> یا <b>ورود به سامانه</b> راهنمایی‌تان کنم؟</div></div>
  </div>
  <div class="quick" id="quick"></div>
  <div class="iw">
    <div class="sp" id="sp"></div>
    <form class="ia" id="form"><input type="text" id="inp" class="inp" maxlength="500" placeholder="پرسش خود را بنویسید..." autocomplete="off"><button type="submit" id="btn" class="send">ارسال</button></form>
  </div>
</div>

<script>
const $=id=>document.getElementById(id);
const chat=$('chat'),inp=$('inp'),btn=$('btn'),sp=$('sp'),box=$('box'),prompt_=$('prompt');
const CHIPS=[["👨‍⚖️ داور شدن","چگونه داور شوم"],["🪪 کارت عضویت","کارت عضویت"],["🎓 گواهینامه","گواهینامه"],["📝 آزمون","آزمون"],
 ["📚 دانلود دوره","دانلود فایل دوره"],["🔑 مشکل ورود","مشکل ورود به سامانه"],["📄 ابطال رأی","ابطال رأی داور"],["📞 تماس","تماس با پشتیبانی"]];
const SUGG=[["چگونه داور شوم و در سامانه نمایش داده شوم؟",["داور","نمایش","عضویت","ثبت"]],["مدت زمان صدور کارت عضویت",["کارت","صدور","پست"]],
 ["مدت زمان صدور گواهینامه دوره",["گواهینامه","گواهی","صدور"]],["شرایط شرکت در آزمون دوره",["آزمون","امتحان","نمره"]],
 ["مشکل دانلود فایل دوره",["دانلود","فایل","دوره"]],["فراموشی رمز عبور و مشکل ورود",["رمز","ورود","پیامک"]],
 ["عودت وجه پرداختی",["عودت","هزینه","پرداخت","پول"]],["امتیاز علمی و بارگذاری مدارک",["امتیاز","مدرک","بارگذاری"]],
 ["ابطال رأی داور چگونه است؟",["ابطال","رای","اعتراض"]],["راه‌های تماس با پشتیبانی",["تماس","پشتیبانی","تلفن"]]];

let sid='s_'+Math.random().toString(36).slice(2,11);
try{const st=localStorage.getItem('davar_sid');if(st)sid=st;else localStorage.setItem('davar_sid',sid)}catch(e){}

function applyTheme(){try{if(localStorage.getItem('davar_theme')==='dark'){document.body.classList.add('dark');$('theme').textContent='☀️'}}catch(e){}}
applyTheme();
$('theme').onclick=()=>{const d=document.body.classList.toggle('dark');$('theme').textContent=d?'☀️':'🌙';try{localStorage.setItem('davar_theme',d?'dark':'light')}catch(e){}};
function openChat(){box.classList.add('open');prompt_.classList.add('hide');setTimeout(()=>inp.focus(),250)}
$('launch').onclick=()=>{box.classList.contains('open')?box.classList.remove('open'):openChat()};
$('closeBtn').onclick=()=>box.classList.remove('open');
prompt_.onclick=openChat;$('promptX').onclick=e=>{e.stopPropagation();prompt_.classList.add('hide')};

const esc=t=>(t||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;').replace(/'/g,'&#39;');
function fmt(t){
  let h=esc(t);
  h=h.replace(/\[([^\]]+)\]\((https?:\/\/[^\s)]+)\)/g,'<a href="$2" target="_blank" rel="noopener noreferrer">$1</a>');
  h=h.replace(/(^|[\s>(])(https?:\/\/[^\s<)]+[^\s<.,;)])/g,'$1<a href="$2" target="_blank" rel="noopener noreferrer">$2</a>');
  h=h.replace(/\*\*(.+?)\*\*/g,'<b>$1</b>').replace(/━{3,}/g,'<hr class="sep">').replace(/\n/g,'<br>');
  return h;
}
function addMsg(text,isUser,subject,conf,sugg){
  const d=document.createElement('div');d.className='msg '+(isUser?'user':'bot');
  if(subject){const s=document.createElement('div');s.className='subj';s.textContent=subject;d.appendChild(s)}
  const c=document.createElement('div');c.innerHTML=isUser?esc(text):fmt(text);d.appendChild(c);
  if(!isUser&&conf>0){const b=document.createElement('div');b.className='conf';b.textContent='🎯 '+conf+'٪ تطبیق';d.appendChild(b)}
  if(!isUser&&sugg&&sugg.length){const f=document.createElement('div');f.className='fubox';
    sugg.forEach(q=>{const b=document.createElement('button');b.type='button';b.className='fu';b.textContent='💬 '+q;b.onclick=()=>ask(q);f.appendChild(b)});d.appendChild(f)}
  chat.appendChild(d);chat.scrollTop=chat.scrollHeight;
}
function typing(on){const e=$('typ');if(on&&!e){const t=document.createElement('div');t.id='typ';t.className='typing';t.innerHTML='<div class="dot"></div><div class="dot"></div><div class="dot"></div>';chat.appendChild(t);chat.scrollTop=chat.scrollHeight}else if(!on&&e)e.remove()}

CHIPS.forEach(([l,q])=>{const b=document.createElement('button');b.className='chip';b.textContent=l;b.onclick=()=>ask(q);$('quick').appendChild(b)});

inp.addEventListener('input',()=>{
  const v=inp.value.trim();sp.innerHTML='';
  if(v.length<2){sp.classList.remove('show');return}
  const m=SUGG.filter(([q,k])=>q.includes(v)||k.some(x=>x.includes(v)||v.includes(x))).slice(0,4);
  m.forEach(([q])=>{const i=document.createElement('div');i.className='si';i.textContent='🔍 '+q;i.onclick=()=>ask(q);sp.appendChild(i)});
  sp.classList.toggle('show',m.length>0);
});
document.addEventListener('click',e=>{if(!inp.contains(e.target)&&!sp.contains(e.target))sp.classList.remove('show')});

async function ask(text){
  text=(text||'').trim();if(!text)return;
  sp.classList.remove('show');addMsg(text,true);inp.value='';inp.disabled=true;btn.disabled=true;typing(true);
  try{
    const r=await fetch('/api/ask',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({q:text,sid:sid})});
    const d=await r.json();await new Promise(x=>setTimeout(x,350));typing(false);
    addMsg(d.answer,false,d.subject,d.confidence,d.suggestions);
  }catch(e){typing(false);addMsg('❌ خطا در برقراری ارتباط با سرور. لطفاً دوباره تلاش کنید.',false,'خطا')}
  finally{inp.disabled=false;btn.disabled=false;inp.focus()}
}
$('form').addEventListener('submit',e=>{e.preventDefault();ask(inp.value)});
</script>
</body>
</html>
"""


# ==========================================
# ۷. وب‌سرور
# ==========================================
class RateLimiter:
    """محدودکننده ساده درون‌حافظه‌ای؛ برای چند سرور از محدودکننده در reverse proxy استفاده کنید."""
    def __init__(self, limit=60, window_seconds=60, max_keys=10000):
        self.limit = limit
        self.window_seconds = window_seconds
        self.max_keys = max_keys
        self.hits = defaultdict(list)
        self.lock = threading.Lock()

    def allow(self, key, now=None):
        now = time.time() if now is None else now
        with self.lock:
            if len(self.hits) > self.max_keys:
                cutoff = now - self.window_seconds
                for k in list(self.hits):
                    self.hits[k] = [t for t in self.hits[k] if t > cutoff]
                    if not self.hits[k]:
                        self.hits.pop(k, None)
            recent = [t for t in self.hits[key] if t > now - self.window_seconds]
            if len(recent) >= self.limit:
                self.hits[key] = recent
                return False
            recent.append(now)
            self.hits[key] = recent
            return True


REQUEST_LIMITER = RateLimiter(limit=int(os.environ.get("RATE_LIMIT_PER_MINUTE", "60")))


class ChatRequestHandler(SimpleHTTPRequestHandler):
    def log_message(self, fmt, *args):
        # متن پرسش‌ها و داده‌های کاربر را در لاگ پیش‌فرض ثبت نکن.
        pass

    def end_headers(self):
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Referrer-Policy", "strict-origin-when-cross-origin")
        self.send_header("Permissions-Policy", "camera=(), microphone=(), geolocation=()")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Security-Policy", "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline' https://cdn.jsdelivr.net; font-src 'self' https://cdn.jsdelivr.net data:; connect-src 'self'; img-src 'self' data:; base-uri 'self'; form-action 'self'; frame-ancestors 'none'")
        super().end_headers()

    def _cors(self):
        origin = self.headers.get("Origin", "")
        if ALLOWED_ORIGIN and (ALLOWED_ORIGIN == "*" or origin == ALLOWED_ORIGIN):
            self.send_header("Access-Control-Allow-Origin", ALLOWED_ORIGIN)
            self.send_header("Vary", "Origin")
            self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
            self.send_header("Access-Control-Allow-Headers", "Content-Type")

    def _json(self, payload, status=200):
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self._cors()
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_OPTIONS(self):
        self.send_response(204)
        self._cors()
        self.end_headers()

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        if parsed.path in ("/", "/index.html"):
            data = HTML_PAGE.encode("utf-8")
            self.send_response(200)
            self._cors()
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)
        elif parsed.path == "/api/ask":
            self.send_response(405)
            self.send_header("Allow", "POST, OPTIONS")
            self._cors()
            self.end_headers()
        elif parsed.path == "/api/health":
            self._json({"status": "ok", "entries": len(engine.entries)})
        else:
            self.send_error(404, "Not Found")

    def do_POST(self):
        if urllib.parse.urlparse(self.path).path != "/api/ask":
            self.send_error(404, "Not Found")
            return
        if not REQUEST_LIMITER.allow(self.client_address[0]):
            self._json({"status": "error", "error": "rate_limit", "answer": "تعداد درخواست‌ها زیاد است؛ لطفاً کمی بعد دوباره تلاش کنید."}, status=429)
            return
        try:
            raw_length = self.headers.get("Content-Length")
            if raw_length is None:
                self._json({"status": "error", "error": "content_length_required"}, status=411)
                return
            length = int(raw_length)
            if length < 0 or length > 10_000:
                self._json({"status": "error", "error": "request_too_large", "answer": "حجم درخواست بیش از حد مجاز است."}, status=413)
                return
            data = json.loads(self.rfile.read(length).decode("utf-8"))
            if not isinstance(data, dict):
                raise ValueError("JSON body must be an object")
            q = str(data.get("q", ""))[:MAX_QUERY_LEN]
            sid = str(data.get("sid", ""))[:64]
            if sid and not re.fullmatch(r"[A-Za-z0-9_-]{1,64}", sid):
                sid = ""
        except (ValueError, UnicodeDecodeError, json.JSONDecodeError):
            self._json({"status": "error", "error": "invalid_json", "answer": "درخواست نامعتبر است؛ لطفاً دوباره تلاش کنید."}, status=400)
            return
        self._reply(q, sid)

    def _reply(self, q, sid):
        try:
            if len(str(q or "")) > MAX_QUERY_LEN:
                q = str(q)[:MAX_QUERY_LEN]
            res = answer_query(q, sid)
            res["status"] = "ok"
        except Exception as exc:  # هرگز سرور را از کار نینداز
            print("خطا:", exc)
            res = simple("❌ خطای داخلی", "متأسفانه مشکلی پیش آمد. لطفاً دوباره تلاش کنید.", "error", [], 0.0)
            res["status"] = "error"
        self._json(res)


if __name__ == "__main__":
    server = ThreadingHTTPServer((HOST, PORT), ChatRequestHandler)
    print(f"🚀 سرور دستیار داورایران فعال شد: http://{HOST}:{PORT}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n👋 سرور متوقف شد.")
