import pyautogui
import cv2
import numpy as np
import time

print("Hãy mở màn hình game có quái lên. Sẽ chụp màn hình sau 3 giây...")
time.sleep(3)

# Chụp màn hình bằng chính Python
screenshot = pyautogui.screenshot()
screen_bgr = cv2.cvtColor(np.array(screenshot), cv2.COLOR_RGB2BGR)

# Đọc ảnh monster.png
template = cv2.imread("monster.png", cv2.IMREAD_COLOR)

if template is None:
    print("[LỖI] Không đọc được file monster.png! Kiểm tra lại tên file.")
else:
    h, w = template.shape[:2]
    res = cv2.matchTemplate(screen_bgr, template, cv2.TM_CCOEFF_NORMED)
    min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(res)

    print(f"\n==========================================")
    print(f"ĐỘ KHỚP CAO NHẤT TÌM THẤY: {max_val:.2f} (Tức {max_val*100:.0f}%)")
    print(f"==========================================\n")

    # Thử hạ mức nhận diện xuống thấp hơn chút để gom đủ 3 con quái
    test_threshold = max(0.55, max_val - 0.08)
    loc = np.where(res >= test_threshold)

    points = []
    for pt in zip(*loc[::-1]):
        cx, cy = pt[0] + w // 2, pt[1] + h // 2
        if all(abs(cx - px) > 20 or abs(cy - py) > 20 for px, py in points):
            points.append((cx, cy))
            # Vẽ khung chữ nhật màu ĐỎ quanh con quái tìm được
            cv2.rectangle(screen_bgr, pt, (pt[0] + w, pt[1] + h), (0, 0, 255), 2)

    print(f"-> Với mức CONFIDENCE = {test_threshold:.2f}, quét ra được: {len(points)} con quái!")
    
    # Lưu lại ảnh kết quả để bạn mở lên xem
    cv2.imwrite("ket_qua_quet.png", screen_bgr)
    print("-> Đã lưu ảnh 'ket_qua_quet.png' và 'man_hinh_goc.png' vào thư mục!")
    cv2.imwrite("man_hinh_goc.png", cv2.cvtColor(np.array(screenshot), cv2.COLOR_RGB2BGR))