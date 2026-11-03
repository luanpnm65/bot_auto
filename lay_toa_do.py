import pyautogui
import time

print("=== TOOL LẤY TỌA ĐỘ & MÃ MÀU ===")
print("Hãy di chuột vào vị trí cần lấy trong game. Nhấn Ctrl+C để dừng.\n")

try:
    while True:
        x, y = pyautogui.position()
        r, g, b = pyautogui.pixel(x, y)
        print(f"Tọa độ: ({x}, {y})   |   Mã màu RGB: ({r}, {g}, {b})          ", end="\r")
        time.sleep(0.2)
except KeyboardInterrupt:
    print("\nĐã dừng!")