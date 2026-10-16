
# -*- coding: utf-8 -*-

import os
import threading
from http.server import ThreadingHTTPServer

import chatbot
import bale_bot


def start_bot():
    bale_bot.main()


if __name__ == "__main__":
    # اجرای ربات بله در یک رشته جداگانه
    bot_thread = threading.Thread(
        target=start_bot,
        daemon=True,
    )
    bot_thread.start()

    # اجرای وب‌سرور روی پورتی که Render تعیین می‌کند
    host = "0.0.0.0"
    port = int(os.environ.get("PORT", getattr(chatbot, "PORT", 8000)))

    server = ThreadingHTTPServer(
        (host, port),
        chatbot.ChatRequestHandler,
    )

    print(f"دستیار داورایران روی پورت {port} فعال شد.")

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("سرور متوقف شد.")
    finally:
        server.server_close()
