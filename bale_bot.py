
# -*- coding: utf-8 -*-
"""اتصال دستیار هوشمند داورایران به ربات بله."""

import json
import os
import time
import urllib.error
import urllib.request

import chatbot

TOKEN = os.environ.get("BALE_BOT_TOKEN", "").strip()
API_BASE = f"https://tapi.bale.ai/bot{TOKEN}"

if not TOKEN:
    raise RuntimeError("متغیر محیطی BALE_BOT_TOKEN تنظیم نشده است.")


def api_call(method, payload=None, timeout=40):
    url = f"{API_BASE}/{method}"
    data = json.dumps(payload or {}).encode("utf-8")

    request = urllib.request.Request(
        url,
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )

    with urllib.request.urlopen(request, timeout=timeout) as response:
        result = json.loads(response.read().decode("utf-8"))

    if not result.get("ok"):
        raise RuntimeError(f"Bale API error: {result}")

    return result.get("result", [])


def send_text(chat_id, text):
    # متن طولانی را در چند پیام ارسال می‌کنیم.
    text = str(text or "").strip() or "لطفاً پرسش خود را دوباره ارسال کنید."

    chunks = []
    while len(text) > 4000:
        split_at = text.rfind("\n", 0, 4000)
        if split_at < 1000:
            split_at = 4000
        chunks.append(text[:split_at])
        text = text[split_at:].lstrip()

    if text:
        chunks.append(text)

    for chunk in chunks:
        api_call(
            "sendMessage",
            {"chat_id": chat_id, "text": chunk},
        )


def main():
    print("ربات داورایران در حال شروع است...")
    offset = 0

    while True:
        try:
            updates = api_call(
                "getUpdates",
                {"offset": offset, "timeout": 25},
                timeout=40,
            )

            for update in updates:
                offset = max(offset, int(update.get("update_id", 0)) + 1)

                message = update.get("message") or {}
                text = (message.get("text") or "").strip()
                chat = message.get("chat") or {}
                chat_id = chat.get("id")

                if not chat_id or not text:
                    continue

                if text == "/start":
                    send_text(
                        chat_id,
                        "⚖️ به دستیار هوشمند داورایران خوش آمدید!\n\n"
                        "پرسش خود را درباره عضویت، کارت عضویت، "
                        "گواهینامه، آزمون، دوره‌ها یا مسائل داوری بپرسید.\n\n"
                        "🔒 رمز عبور و کد ورود خود را ارسال نکنید.",
                    )
                    continue

                try:
                    session_id = f"bale_{chat_id}"
                    result = chatbot.answer_query(text, session_id)
                    answer = result.get("answer", "")

                    subject = result.get("subject", "")
                    if subject:
                        answer = f"⚖️ {subject}\n\n{answer}"

                    send_text(chat_id, answer)

                except Exception as exc:
                    print(f"خطا در پردازش پیام: {type(exc).__name__}")
                    send_text(
                        chat_id,
                        "در پردازش پیام مشکلی پیش آمد. "
                        "لطفاً کمی بعد دوباره تلاش کنید.",
                    )

        except (OSError, ValueError, RuntimeError) as exc:
            # توکن و اطلاعات حساس را در لاگ چاپ نمی‌کنیم.
            print(f"خطای ارتباط با بله: {type(exc).__name__}")
            time.sleep(5)


if __name__ == "__main__":
    main()
