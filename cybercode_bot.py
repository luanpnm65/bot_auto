import pyautogui
import cv2
import numpy as np
import time
import random

# Di chuột nhanh về góc trên cùng bên trái màn hình để dừng khẩn cấp
pyautogui.FAILSAFE = True

# ==========================================
# PHẦN CẤU HÌNH (ĐIỀN TỌA ĐỘ & ẢNH CỦA BẠN VÀO ĐÂY)
# ==========================================
CONFIG = {
    "MAX_RUNS": 50,                 # Giới hạn số lần đi Dungeon
    "CONFIDENCE": 0.85,              # Độ chính xác khi quét ảnh (0.8 = 80%)
    
    # Đường dẫn 8 file ảnh mẫu (Lưu cùng thư mục với file code này)
    "IMG_LOOT": "loot.png",         # Ảnh hòm đồ / loot trong phòng Boss (Chế độ 3)
    "IMG_PLAYER": "player.png", 
    "IMG_MENU_DUNGEON": "menu_dungeon.png",
    "IMG_ENTER_DUNGEON": "enter_dungeon.png",
    "IMG_EXIT_DUNGEON": "exit_dungeon.png",
    "IMG_CONFIRM_YES": "confirm_yes.png",   # [MỚI] Ảnh nút "Yes" ở pop-up xác nhận thoát
    "IMG_MONSTER": "monster.png",
    "IMG_DOOR_WHITE": "door_white.png",
    "IMG_DOOR_GREY": "door_grey.png",

    # Tọa độ trên THANH MÁU CỦA BẠN
    "COORD_HP_START": (1256, 859),   # Điểm ĐẦU thanh máu (sát mép trái): Kiểm tra còn trong trận hay quái đã chết
    "COORD_HP_Z": (1477, 861),       # Tọa độ Z trên thanh máu: Kiểm tra tụt máu trước mỗi phát bắn
    "COLOR_HP_RED": (223, 28, 79),  # Mã màu Đỏ của thanh máu

    # Tọa độ & Màu sắc chiến đấu / nhặt đồ
    "COORD_SHIELD": (1261, 237),     # Tọa độ kiểm tra giáp ảo của quái
    "COLOR_SHIELD": (218, 218, 218),  # Mã màu RGB khi quái có giáp ảo
    "COORD_GUN_X": (1535, 1013),      # Tọa độ x: Súng bắn khi CÓ giáp
    "COORD_GUN_Y": (1777, 1006),      # Tọa độ y: Súng bắn khi KHÔNG giáp
    "COORD_HEAL_A": (1536, 909),     # Tọa độ a: Đồ hồi máu
    "COORD_LOOT_B": (1347, 932),     # Tọa độ b: Click khi quái rơi đồ
        # Tọa độ chọn loại Dungeon ở Bước 2 (Normal / Co-op / Gang)
    "COORD_DUNGEON_NORMAL": (1503, 273),  # Tọa độ 1: Nút chọn Normal Dungeon
    "COORD_DUNGEON_COOP": (1473, 532),    # Tọa độ 2: Nút chọn Co-op Dungeon
    "COORD_DUNGEON_GANG": (1454, 839),    # Tọa độ 3: Nút chọn Gang Dungeon

    "COLOR_TOLERANCE": 30           # Sai số màu sắc cho phép
}
import os
import json
import math
import threading
import ctypes
from ctypes import wintypes
import winsound

class RestartBotException(Exception):
    """Ngoại lệ dùng để ngắt ngay lập tức luồng hiện tại khi bấm F9"""
    pass


class CyberCodeDungeonBot:
    OPPOSITE_DIR = {
        "TOP": "BOTTOM",
        "BOTTOM": "TOP",
        "LEFT": "RIGHT",
        "RIGHT": "LEFT",
    }
    DIR_DELTA = {
        "TOP": (0, -1),
        "BOTTOM": (0, 1),
        "LEFT": (-1, 0),
        "RIGHT": (1, 0),
    }

    def __init__(self, config):
        self.cfg = config
        self.mode = 1
        self.dungeon_type = 1
        self.reselect_mode_next_run = False

        # Trạng thái điều khiển phím nóng
        self.paused = False
        self.restart_requested = False

        # Tọa độ nhân vật ước tính trên màn hình
        self.player_pos = None

        # Theo dõi hướng cửa & hình học của phòng để không đi lùi về phòng cũ
        self.room_center = None
        self.room_pos = (0, 0)
        self.last_exit_dir = None
        self.last_exit_coord = None
        self.edge_visits = {}

        # Cấu hình khung cửa sổ (F2)
        self.window_config_file = "window_config.json"
        self.base_rect = None
        self.current_rect = None
        self.load_window_config()

        # Khởi chạy luồng lắng nghe phím nóng F1, F2, F8, F9
        self.hotkey_thread = threading.Thread(target=self._hotkey_listener, daemon=True)
        self.hotkey_thread.start()

    # ==========================================
    # HỆ THỐNG PHÍM NÓNG (F1, F2, F8, F9) & CỬA SỔ
    # ==========================================
    def _hotkey_listener(self):
        VK_F1 = 0x70
        VK_F2 = 0x71
        VK_F8 = 0x77
        VK_F9 = 0x78

        f1_prev = f2_prev = f8_prev = f9_prev = False

        while True:
            # F1: Chọn lại chế độ ở lượt sau
            f1_curr = bool(ctypes.windll.user32.GetAsyncKeyState(VK_F1) & 0x8000)
            if f1_curr and not f1_prev:
                self.reselect_mode_next_run = True
                print("\n[🔔 HOTKEY F1] Đã đăng ký đổi Chế độ vào lượt Dungeon tiếp theo!")
            f1_prev = f1_curr

            # F2: Đồng bộ / Khóa tỷ lệ cửa sổ
            f2_curr = bool(ctypes.windll.user32.GetAsyncKeyState(VK_F2) & 0x8000)
            if f2_curr and not f2_prev:
                self.calibrate_or_sync_window()
            f2_prev = f2_curr

            # F8: Tạm dừng / Tiếp tục (để giải mini-game)
            f8_curr = bool(ctypes.windll.user32.GetAsyncKeyState(VK_F8) & 0x8000)
            if f8_curr and not f8_prev:
                self.paused = not self.paused
                if self.paused:
                    print("\n[⏸️ HOTKEY F8] ĐÃ TẠM DỪNG BOT! Bạn có thể tự giải mini-game. Bấm F8 lần nữa để tiếp tục...")
                else:
                    print("\n[▶️ HOTKEY F8] TIẾP TỤC CHẠY BOT!")
            f8_prev = f8_curr

            # F9: Khởi động lại luồng bot ngay lập tức
            f9_curr = bool(ctypes.windll.user32.GetAsyncKeyState(VK_F9) & 0x8000)
            if f9_curr and not f9_prev:
                self.paused = False
                self.restart_requested = True
                print("\n[🔄 HOTKEY F9] Đang khởi động lại chu trình Bot ngay lập tức...")
            f9_prev = f9_curr

            time.sleep(0.05)

    def check_control_state(self):
        """Kiểm tra trạng thái Tạm dừng (F8) hoặc Khởi động lại (F9)"""
        if self.restart_requested:
            self.restart_requested = False
            raise RestartBotException()

        while self.paused:
            if self.restart_requested:
                self.restart_requested = False
                raise RestartBotException()
            time.sleep(0.2)

    def sleep(self, seconds):
        """Hàm sleep có kiểm tra F8/F9 liên tục để phản hồi tức thì"""
        end_time = time.time() + seconds
        while time.time() < end_time:
            self.check_control_state()
            time.sleep(min(0.1, max(0.01, end_time - time.time())))

    def get_active_window_rect(self):
        hwnd = ctypes.windll.user32.GetForegroundWindow()
        if not hwnd:
            return None
        rect = ctypes.wintypes.RECT()
        if ctypes.windll.user32.GetWindowRect(hwnd, ctypes.byref(rect)):
            w = rect.right - rect.left
            h = rect.bottom - rect.top
            if w > 100 and h > 100:
                return (rect.left, rect.top, w, h)
        return None

    def load_window_config(self):
        if os.path.exists(self.window_config_file):
            try:
                with open(self.window_config_file, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    self.base_rect = tuple(data.get("base_rect"))
                    self.current_rect = tuple(data.get("current_rect", self.base_rect))
                    print(f"[+] Đã tải cấu hình khung cửa sổ gốc: {self.base_rect}")
            except Exception as e:
                print(f"[!] Lỗi đọc {self.window_config_file}: {e}")

    def calibrate_or_sync_window(self):
        rect = self.get_active_window_rect()
        if not rect:
            print("[!] Không lấy được kích thước cửa sổ hiện tại!")
            return

        if self.base_rect is None:
            self.base_rect = rect
            self.current_rect = rect
            print(f"\n[📐 HOTKEY F2] Đã LƯU KHUNG CỬA SỔ GỐC: {self.base_rect}")
        else:
            self.current_rect = rect
            print(f"\n[📐 HOTKEY F2] Đã ĐỒNG BỘ KHUNG CỬA SỔ MỚI: {self.current_rect} (Gốc: {self.base_rect})")

        try:
            with open(self.window_config_file, "w", encoding="utf-8") as f:
                json.dump(
                    {"base_rect": self.base_rect, "current_rect": self.current_rect},
                    f,
                    indent=2,
                )
        except Exception as e:
            print(f"[!] Không thể lưu {self.window_config_file}: {e}")

    def get_coord(self, key):
        raw_x, raw_y = self.cfg[key]
        if not self.base_rect or not self.current_rect:
            return (raw_x, raw_y)

        bx, by, bw, bh = self.base_rect
        cx, cy, cw, ch = self.current_rect
        if bw <= 0 or bh <= 0:
            return (raw_x, raw_y)

        rel_x = (raw_x - bx) / float(bw)
        rel_y = (raw_y - by) / float(bh)

        new_x = int(round(cx + rel_x * cw))
        new_y = int(round(cy + rel_y * ch))
        return (new_x, new_y)

    # ==========================================
    # CHỌN CHẾ ĐỘ CHẠY (1, 2, 3, 4)
    # ==========================================
    def select_mode(self):
        print("\n" + "=" * 65)
        print("            CÀI ĐẶT CHẾ ĐỘ CHẠY BOT CYBERCODE")
        print("=" * 65)
        print("BƯỚC 1 - CHỌN LOẠI DUNGEON:")
        print("  [1] Dungeon Thường (Normal)")
        print("  [2] Dungeon Co-op")
        print("  [3] Dungeon Gang")
        print("-" * 65)

        while True:
            d_choice = input("👉 Nhập loại Dungeon (1, 2 hoặc 3): ").strip()
            if d_choice in ["1", "2", "3"]:
                self.dungeon_type = int(d_choice)
                break
            print("[!] Lựa chọn không hợp lệ! Vui lòng nhập 1, 2 hoặc 3.")

        print("\n" + "-" * 65)
        print("BƯỚC 2 - CHỌN CHẾ ĐỘ ĐÁNH DUNGEON & PHÒNG BOSS (> 4 quái):")
        print("  [1] Chế độ 1: Clear hết quái trong phòng Boss rồi Thoát.")
        print("  [2] Chế độ 2: Chỉ giết Boss (quái bắn > 6 phát), nhặt đồ rồi Thoát luôn.")
        print("  [3] Chế độ 3: Clear hết quái phòng Boss + Mở hết hòm đồ (loot.png) rồi Thoát.")
        print("  [4] Chế độ 4 (FARM NHANH): Luôn bắn súng Y (oneshot, bỏ qua giáp) & Thoát khi clear phòng Boss.")
        print("=" * 65)

        while True:
            choice = input("👉 Nhập chế độ bạn muốn chạy (1, 2, 3 hoặc 4): ").strip()
            if choice in ["1", "2", "3", "4"]:
                self.mode = int(choice)
                d_names = {1: "Thường (Normal)", 2: "Co-op", 3: "Gang"}
                print(
                    f"[+] Đã chọn: Dungeon {d_names[self.dungeon_type]} | Chế độ {self.mode}\n"
                )
                self.reselect_mode_next_run = False
                break
            print("[!] Lựa chọn không hợp lệ! Vui lòng nhập 1, 2, 3 hoặc 4.")

    # ==========================================
    # CÁC HÀM XỬ LÝ HÌNH ẢNH & MÀU SẮC
    # ==========================================
    def capture_screen(self):
        screenshot = pyautogui.screenshot()
        return cv2.cvtColor(np.array(screenshot), cv2.COLOR_RGB2BGR)

    def find_all_objects(self, template_path, confidence=None, screen_bgr=None):
        if confidence is None:
            confidence = self.cfg["CONFIDENCE"]

        if not os.path.exists(template_path):
            return []

        if screen_bgr is None:
            screen_bgr = self.capture_screen()

        template = cv2.imread(template_path, cv2.IMREAD_COLOR)
        if template is None:
            return []

        orig_h, orig_w = template.shape[:2]
        screen_h, screen_w = screen_bgr.shape[:2]

        # Quét ở nhiều tỷ lệ đồng nhất (không làm méo ảnh trên Web)
        scales = [1.0, 0.9, 1.1, 0.8, 1.2]
        candidates = []  # Lưu (độ_chính_xác, cx, cy)

        for s in scales:
            th = max(5, int(round(orig_h * s)))
            tw = max(5, int(round(orig_w * s)))
            if th >= screen_h or tw >= screen_w:
                continue

            if s == 1.0:
                scaled_tpl = template
            else:
                interp = cv2.INTER_AREA if s < 1.0 else cv2.INTER_LINEAR
                scaled_tpl = cv2.resize(template, (tw, th), interpolation=interp)

            result = cv2.matchTemplate(screen_bgr, scaled_tpl, cv2.TM_CCOEFF_NORMED)
            ys, xs = np.where(result >= confidence)

            for y, x in zip(ys, xs):
                score = float(result[y, x])
                cx = int(x + tw // 2)
                cy = int(y + th // 2)
                candidates.append((score, cx, cy))

            if s == 1.0 and len(candidates) > 0:
                break

        if not candidates:
            return []

        # Ưu tiên giữ lại điểm có độ khớp cao nhất và lọc bỏ các điểm trùng trong bán kính 20px
        candidates.sort(key=lambda item: item[0], reverse=True)
        centers = []
        for _, cx, cy in candidates:
            if not any(math.hypot(cx - ex, cy - ey) < 20 for (ex, ey) in centers):
                centers.append((cx, cy))

        return centers

    def find_single_object(self, template_path, confidence=None):
        matches = self.find_all_objects(template_path, confidence)
        return matches[0] if matches else None

    def click(self, coord, delay=0.5):
        self.check_control_state()
        if coord is not None:
            pyautogui.click(coord[0], coord[1])
            self.sleep(delay)

    def wait_and_click(self, template_path, timeout=10, delay=0.8):
        start_time = time.time()
        while time.time() - start_time < timeout:
            self.check_control_state()
            pos = self.find_single_object(template_path)
            if pos:
                self.click(pos, delay=delay)
                return True
            self.sleep(0.4)
        print(f"[!] Quá thời gian chờ ảnh: {template_path}")
        return False

    def get_pixel_rgb(self, coord):
        x, y = int(coord[0]), int(coord[1])
        bgr = self.capture_screen()[y, x]
        return (int(bgr[2]), int(bgr[1]), int(bgr[0]))

    def check_pixel_color(self, coord, target_rgb, tolerance=None):
        if tolerance is None:
            tolerance = self.cfg["COLOR_TOLERANCE"]
        r, g, b = self.get_pixel_rgb(coord)
        tr, tg, tb = target_rgb
        return (
            abs(r - tr) <= tolerance
            and abs(g - tg) <= tolerance
            and abs(b - tb) <= tolerance
        )

    # ==========================================
    # KIỂM TRA MÁU, GIÁP & DI CHUYỂN
    # ==========================================
    def is_hp_bar_visible(self):
        hp_start = self.get_coord("COORD_HP_START")
        return self.check_pixel_color(hp_start, self.cfg["COLOR_HP_RED"], tolerance=45)

    def need_healing(self):
        """
        Kiểm tra điểm Z trên thanh máu có còn màu đỏ hay không.
        Quét 3 điểm lân cận ngang để tránh chữ đè lên thanh máu.
        """
        zx, zy = self.get_coord("COORD_HP_Z")
        start_rgb = self.get_pixel_rgb(self.get_coord("COORD_HP_START"))
        target_red = self.cfg["COLOR_HP_RED"]

        for dx in (0, -3, 3):
            r, g, b = self.get_pixel_rgb((zx + dx, zy))
            # Nếu sắc đỏ nổi bật
            if r > 100 and (r > g + 40) and (r > b + 40):
                return False
            # Hoặc giống màu tại điểm đầu thanh máu
            if (
                abs(r - start_rgb[0]) <= 45
                and abs(g - start_rgb[1]) <= 45
                and abs(b - start_rgb[2]) <= 45
            ):
                return False
            # Hoặc khớp với COLOR_HP_RED
            if (
                abs(r - target_red[0]) <= 45
                and abs(g - target_red[1]) <= 45
                and abs(b - target_red[2]) <= 45
            ):
                return False

        return True

    def has_shield(self):
        shield_coord = self.get_coord("COORD_SHIELD")
        return self.check_pixel_color(shield_coord, self.cfg["COLOR_SHIELD"])

    def has_character_moved(self, screen_before, screen_after, diff_threshold=1500):
        gray1 = cv2.cvtColor(screen_before, cv2.COLOR_BGR2GRAY)
        gray2 = cv2.cvtColor(screen_after, cv2.COLOR_BGR2GRAY)
        diff = cv2.absdiff(gray1, gray2)
        _, thresh = cv2.threshold(diff, 25, 255, cv2.THRESH_BINARY)
        changed_pixels = cv2.countNonZero(thresh)
        return changed_pixels > diff_threshold

    def get_player_position(self, screen_bgr=None):
        if os.path.exists(self.cfg["IMG_PLAYER"]):
            pos = self.find_single_object(self.cfg["IMG_PLAYER"], confidence=0.75)
            if pos:
                self.player_pos = pos
                return pos

        if self.player_pos is not None:
            return self.player_pos

        if screen_bgr is None:
            screen_bgr = self.capture_screen()
        h, w = screen_bgr.shape[:2]
        return (w // 2, h // 2)

    def sort_by_distance_to_player(self, points, screen_bgr=None):
        if not points:
            return []
        px, py = self.get_player_position(screen_bgr)
        return sorted(points, key=lambda pt: math.hypot(pt[0] - px, pt[1] - py))

    # ==========================================
    # PHÂN LOẠI CỬA TRẮNG / XÁM & ĐỊNH HƯỚNG PHÒNG
    # ==========================================
    def classify_doors(self, screen_bgr=None):
        if screen_bgr is None:
            screen_bgr = self.capture_screen()

        candidates = []
        # Hạ ngưỡng xuống 0.68 để không bỏ sót cửa xám mờ khi phòng đã hết quái
        for img_key in ("IMG_DOOR_WHITE", "IMG_DOOR_GREY"):
            path = self.cfg[img_key]
            if os.path.exists(path):
                pts = self.find_all_objects(path, confidence=0.68, screen_bgr=screen_bgr)
                for pt in pts:
                    if not any(math.hypot(pt[0] - cx, pt[1] - cy) < 25 for (cx, cy) in candidates):
                        candidates.append(pt)

        if not candidates:
            return [], []

        w_tpl = cv2.imread(self.cfg["IMG_DOOR_WHITE"], cv2.IMREAD_GRAYSCALE)
        g_tpl = cv2.imread(self.cfg["IMG_DOOR_GREY"], cv2.IMREAD_GRAYSCALE)

        if w_tpl is not None and g_tpl is not None:
            w_mean = float(np.mean(w_tpl))
            g_mean = float(np.mean(g_tpl))
            brightness_threshold = (w_mean + g_mean) / 2.0
            ph, pw = w_tpl.shape[:2]
        else:
            brightness_threshold = 125.0
            ph, pw = 24, 24

        gray_screen = cv2.cvtColor(screen_bgr, cv2.COLOR_BGR2GRAY)
        sh, sw = gray_screen.shape[:2]

        white_doors = []
        grey_doors = []

        for (cx, cy) in candidates:
            x1 = max(0, cx - pw // 2)
            y1 = max(0, cy - ph // 2)
            x2 = min(sw, cx + pw // 2)
            y2 = min(sh, cy + ph // 2)
            patch = gray_screen[y1:y2, x1:x2]
            if patch.size == 0:
                continue

            patch_brightness = float(np.mean(patch))
            if patch_brightness >= brightness_threshold:
                white_doors.append((cx, cy))
            else:
                grey_doors.append((cx, cy))

        return white_doors, grey_doors

    def update_room_geometry(self, white_doors, grey_doors, monsters):
        """Ước tính tâm của khung bản đồ phòng để xác định hướng TOP/BOTTOM/LEFT/RIGHT"""
        all_doors = white_doors + grey_doors

        # Nếu vừa đi qua 1 cửa sang phòng mới và phòng mới có đúng 1 cửa xám (cửa vào)
        if self.last_exit_coord is not None and len(grey_doors) == 1:
            gx, gy = grey_doors[0]
            lx, ly = self.last_exit_coord
            if math.hypot(gx - lx, gy - ly) > 80:
                self.room_center = ((gx + lx) / 2.0, (gy + ly) / 2.0)
                return

        if len(all_doors) >= 2:
            xs = [p[0] for p in all_doors]
            ys = [p[1] for p in all_doors]
            span_x = max(xs) - min(xs)
            span_y = max(ys) - min(ys)

            cx, cy = (
                self.room_center
                if self.room_center is not None
                else (sum(xs) / len(xs), sum(ys) / len(ys))
            )
            if span_x > 160:
                cx = (min(xs) + max(xs)) / 2.0
            if span_y > 160:
                cy = (min(ys) + max(ys)) / 2.0
            self.room_center = (cx, cy)
            return

        if self.room_center is None:
            pts = all_doors + monsters
            if pts:
                xs = [p[0] for p in pts]
                ys = [p[1] for p in pts]
                self.room_center = (sum(xs) / len(xs), sum(ys) / len(ys))
            else:
                screen = self.capture_screen()
                h, w = screen.shape[:2]
                self.room_center = (w / 2.0, h / 2.0)

    def get_door_direction(self, door_coord):
        if self.room_center is None:
            screen = self.capture_screen()
            h, w = screen.shape[:2]
            cx, cy = w / 2.0, h / 2.0
        else:
            cx, cy = self.room_center

        dx = door_coord[0] - cx
        dy = door_coord[1] - cy
        if abs(dx) > abs(dy):
            return "RIGHT" if dx > 0 else "LEFT"
        else:
            return "BOTTOM" if dy > 0 else "TOP"

    def get_opposite_coord(self, coord):
        if self.room_center is None or coord is None:
            return coord
        cx, cy = self.room_center
        return (int(round(2 * cx - coord[0])), int(round(2 * cy - coord[1])))

    def record_door_transition(self, chosen_door):
        direction = self.get_door_direction(chosen_door)
        rx, ry = self.room_pos
        edge_key = (rx, ry, direction)
        self.edge_visits[edge_key] = self.edge_visits.get(edge_key, 0) + 1

        dx, dy = self.DIR_DELTA[direction]
        self.room_pos = (rx + dx, ry + dy)
        self.last_exit_dir = direction
        self.last_exit_coord = chosen_door
        self.player_pos = self.get_opposite_coord(chosen_door)

    def choose_best_grey_door(self, grey_doors):
        """
        Chọn cửa xám tối ưu:
        - Nếu chỉ có 1 cửa xám (ngõ cụt): đi qua cửa đó để quay lại.
        - Nếu có >= 2 cửa xám: Loại bỏ cửa nằm ở HƯỚNG NGƯỢC LẠI với cửa vừa đi ra ở phòng trước
          (vì cửa ngược hướng chính là cửa dẫn lùi về phòng vừa đứng).
        - Cho phép đi thẳng qua cửa xám trùng tọa độ/cùng hướng với cửa phòng trước.
        """
        if not grey_doors:
            return None
        if len(grey_doors) == 1:
            return grey_doors[0]

        came_from_dir = self.OPPOSITE_DIR.get(self.last_exit_dir) if self.last_exit_dir else None
        expected_back_coord = (
            self.get_opposite_coord(self.last_exit_coord) if self.last_exit_coord else None
        )

        candidates = []
        for d in grey_doors:
            d_dir = self.get_door_direction(d)
            if came_from_dir and d_dir == came_from_dir:
                continue
            if expected_back_coord and math.hypot(d[0] - expected_back_coord[0], d[1] - expected_back_coord[1]) < 65:
                continue
            candidates.append(d)

        # Fallback nếu lọc quá tay: loại bỏ cửa xa nhất so với cửa vừa bước ra (tức là cửa đối diện)
        if not candidates and self.last_exit_coord is not None:
            farthest_door = max(
                grey_doors,
                key=lambda d: math.hypot(d[0] - self.last_exit_coord[0], d[1] - self.last_exit_coord[1]),
            )
            candidates = [d for d in grey_doors if d != farthest_door]

        if not candidates:
            candidates = list(grey_doors)

        rx, ry = self.room_pos
        candidates.sort(
            key=lambda d: self.edge_visits.get((rx, ry, self.get_door_direction(d)), 0)
        )
        return candidates[0]

    # ==========================================
    # CHIẾN ĐẤU & NHẶT ĐỒ SAU TRẬN
    # ==========================================
    

    def combat_loop(self):
        print("    [⚔️] Bắt đầu giao chiến...")
        shots_fired = 0
        shot_cooldown = self.cfg.get("SHOT_COOLDOWN", 2.2)  # Thời gian giữa 2 phát bắn thực tế

        while self.is_hp_bar_visible():
            self.check_control_state()

            # 1. Kiểm tra điểm Z trên thanh máu trước mỗi phát bắn
            if self.need_healing():
                print("    [❤️] Máu tụt dưới điểm Z! Bấm hồi máu tại A...")
                self.click(self.get_coord("COORD_HEAL_A"), delay=0.8)
                continue

            # 2. Chọn súng và bắn
            if self.mode == 4:
                # Chế độ 4 (Farm oneshot): Bỏ qua kiểm tra giáp, luôn bắn súng Y
                print(f"    [🔫] (Farm Mode 4) Bắn súng Y (Phát thứ {shots_fired + 1})")
                self.click(self.get_coord("COORD_GUN_Y"), delay=0.2)
            else:
                # Chế độ 1, 2, 3: Kiểm tra giáp để chọn súng X hoặc Y
                if self.has_shield():
                    print(f"    [🛡️] Quái CÓ GIÁP -> Bắn súng X (Phát thứ {shots_fired + 1})")
                    self.click(self.get_coord("COORD_GUN_X"), delay=0.2)
                else:
                    print(f"    [🎯] Quái KHÔNG GIÁP -> Bắn súng Y (Phát thứ {shots_fired + 1})")
                    self.click(self.get_coord("COORD_GUN_Y"), delay=0.2)

            shots_fired += 1

            # 3. Chờ animation đòn bắn (tối thiểu 1.0s đầu cho đòn đánh thực thi)
            self.sleep(1.0)

            # Trong phần thời gian hồi chiêu còn lại, nếu quái đã chết (thanh máu tắt) thì thoát ngay
            wait_end = time.time() + max(0.2, shot_cooldown - 1.0)
            while time.time() < wait_end:
                self.check_control_state()
                if not self.is_hp_bar_visible():
                    break
                self.sleep(0.2)

        print(f"    [✓] Quái đã chết sau {shots_fired} phát bắn!")
        self.handle_post_combat_loot()
        return shots_fired

    # ==========================================
    # DỌN PHÒNG, MỞ HÒM LOOT & THOÁT DUNGEON
    # ==========================================
    def is_room_map_visible(self, screen_bgr=None):
        """Kiểm tra xem bản đồ phòng (quái, cửa trắng/xám, hoặc hòm loot) đã hiện ra chưa"""
        if screen_bgr is None:
            screen_bgr = self.capture_screen()

        monsters = self.find_all_objects(self.cfg["IMG_MONSTER"], screen_bgr=screen_bgr)
        if len(monsters) > 0:
            return True

        white_doors, grey_doors = self.classify_doors(screen_bgr=screen_bgr)
        if len(white_doors) > 0 or len(grey_doors) > 0:
            return True

        if os.path.exists(self.cfg["IMG_LOOT"]):
            loots = self.find_all_objects(self.cfg["IMG_LOOT"], screen_bgr=screen_bgr)
            if len(loots) > 0:
                return True

        return False

    def handle_post_combat_loot(self):
        """
        Sau khi quái chết:
        - Chờ 1.2s cho hiệu ứng chuyển cảnh kết thúc hoàn toàn.
        - Kiểm tra 2 lần liên tiếp (cách nhau 0.4s): nếu cả 2 lần đều không thấy bản đồ phòng
          (tức là bảng Loot thực sự đang che màn hình) thì mới bấm COORD_LOOT_B.
        """
        self.sleep(1.2)

        for _ in range(4):
            self.check_control_state()

            # Nếu đã thấy cửa hoặc quái trên bản đồ -> Không có bảng Loot, thoát ngay
            if self.is_room_map_visible():
                break

            # Chờ thêm 0.4s và kiểm tra lại lần 2 để tránh nhầm lúc màn hình đang chớp chuyển cảnh
            self.sleep(0.4)
            if self.is_room_map_visible():
                break

            print("    [🎁] Phát hiện bảng Loot đang che màn hình -> Bấm nhặt đồ (COORD_LOOT_B)...")
            self.click(self.get_coord("COORD_LOOT_B"), delay=0.7)

    def wait_for_room_loaded(self, timeout=6.0):
        start_time = time.time()
        while time.time() - start_time < timeout:
            self.check_control_state()
            if self.is_hp_bar_visible():
                return True

            if self.is_room_map_visible():
                self.sleep(0.4)
                return True

            self.sleep(0.3)
        return False
    def loot_all_in_boss_room(self):
        """Dành cho Chế độ 3: Đi mở toàn bộ các biểu tượng loot.png trong phòng Boss"""
        if not os.path.exists(self.cfg["IMG_LOOT"]):
            print(f"[!] Không tìm thấy file ảnh {self.cfg['IMG_LOOT']}, bỏ qua bước mở hòm.")
            return

        visited_loots = []

        while True:
            self.check_control_state()
            screen = self.capture_screen()
            loots = self.find_all_objects(self.cfg["IMG_LOOT"], screen_bgr=screen)
            loots = self.sort_by_distance_to_player(loots, screen_bgr=screen)

            # Lọc bỏ các hòm rỗng đã kiểm tra
            available_loots = [
                l for l in loots
                if not any(math.hypot(l[0] - vx, l[1] - vy) < 25 for (vx, vy) in visited_loots)
            ]

            if not available_loots:
                break

            target_loot = available_loots[0]
            print(f"    [📦] Tiến tới kiểm tra Loot tại {target_loot}...")
            self.click(target_loot, delay=1.2)
            self.player_pos = target_loot

            # Kiểm tra xem có bảng nhặt đồ hiện lên che mất cửa không
            check_screen = self.capture_screen()
            w_doors, g_doors = self.classify_doors(screen_bgr=check_screen)
            monsters = self.find_all_objects(self.cfg["IMG_MONSTER"], screen_bgr=check_screen)

            if len(w_doors) == 0 and len(g_doors) == 0 and len(monsters) == 0:
                print("    [✨] Hòm có đồ! Bấm nhặt tại COORD_LOOT_B...")
                self.click(self.get_coord("COORD_LOOT_B"), delay=0.6)
            else:
                print("    [💨] Hòm rỗng, đánh dấu bỏ qua.")
                visited_loots.append(target_loot)

    def exit_dungeon(self):
        print("[🚪] Đang bấm Thoát Dungeon (exit_dungeon.png)...")
        if self.wait_and_click(self.cfg["IMG_EXIT_DUNGEON"], timeout=8, delay=0.8):
            print("[✓] Đang chờ bảng xác nhận (confirm_yes.png)...")
            self.wait_and_click(self.cfg["IMG_CONFIRM_YES"], timeout=8, delay=1.2)
            print("[🎉] Đã thoát Dungeon thành công!")
        else:
            print("[!] Không tìm thấy nút Thoát Dungeon!")

    def is_inside_dungeon(self):
        if self.is_hp_bar_visible():
            return True
        screen = self.capture_screen()
        if self.find_all_objects(self.cfg["IMG_EXIT_DUNGEON"], screen_bgr=screen):
            return True
        w_doors, g_doors = self.classify_doors(screen_bgr=screen)
        if w_doors or g_doors:
            return True
        if self.find_all_objects(self.cfg["IMG_MONSTER"], screen_bgr=screen):
            return True
        return False

    def enter_dungeon(self):
        # Nếu đang ở sẵn trong Dungeon (ví dụ bấm F9 khởi động lại giữa chừng) thì bỏ qua Bước 1-3
        if self.is_inside_dungeon():
            print("[⚡] Phát hiện nhân vật đang ở sẵn trong Dungeon! Bắt đầu dọn phòng ngay...")
            return True

        print("[1] Mở menu Dungeon...")
        if not self.wait_and_click(self.cfg["IMG_MENU_DUNGEON"], timeout=10, delay=0.8):
            return False

        # Chọn loại Dungeon theo tọa độ đã cấu hình
        coord_map = {
            1: "COORD_DUNGEON_NORMAL",
            2: "COORD_DUNGEON_COOP",
            3: "COORD_DUNGEON_GANG",
        }
        d_coord_key = coord_map.get(self.dungeon_type, "COORD_DUNGEON_NORMAL")
        print(f"[2] Chọn loại Dungeon ({d_coord_key})...")
        self.click(self.get_coord(d_coord_key), delay=0.8)

        print("[3] Bấm nút Vào Dungeon (enter_dungeon.png)...")
        if not self.wait_and_click(self.cfg["IMG_ENTER_DUNGEON"], timeout=10, delay=1.5):
            return False

        return True
    def clear_dungeon(self):
        """Hàm chính khám phá các phòng, bắn quái và xử lý phòng Boss theo Chế độ 1, 2, 3, 4"""
        self.player_pos = None
        self.room_center = None
        self.room_pos = (0, 0)
        self.last_exit_dir = None
        self.last_exit_coord = None
        self.edge_visits = {}

        is_boss_room = False
        blocked_monsters = []

        self.wait_for_room_loaded(timeout=6.0)

        while True:
            self.check_control_state()

            # Nếu đang ở sẵn trong màn hình giao chiến thì đánh luôn
            if self.is_hp_bar_visible():
                shots = self.combat_loop()
                blocked_monsters.clear()
                if is_boss_room and self.mode == 2 and shots > 6:
                    print("[👑] (Chế độ 2) Đã tiêu diệt Boss (> 6 phát)! Thoát Dungeon ngay...")
                    self.exit_dungeon()
                    return
                self.wait_for_room_loaded(timeout=5.0)
                continue

            screen = self.capture_screen()
            monsters = self.find_all_objects(self.cfg["IMG_MONSTER"], screen_bgr=screen)
            white_doors, grey_doors = self.classify_doors(screen_bgr=screen)
            self.update_room_geometry(white_doors, grey_doors, monsters)

            # Kiểm tra phòng Boss (> 4 quái)
            if len(monsters) > 4 and not is_boss_room:
                is_boss_room = True
                print(f"[🔥 BOSS ROOM] Phát hiện {len(monsters)} quái (> 4) -> Đây là PHÒNG BOSS!")

            # ----------------------------------------------------
            # TRƯỜNG HỢP A: CÒN QUÁI TRONG PHÒNG
            # ----------------------------------------------------
            if len(monsters) > 0:
                sorted_monsters = self.sort_by_distance_to_player(monsters, screen_bgr=screen)

                # Lọc những con quái chưa bị đánh dấu kẹt đường/địa hình (bán kính 40px)
                available_monsters = [
                    m for m in sorted_monsters
                    if not any(math.hypot(m[0] - bx, m[1] - by) < 40 for (bx, by) in blocked_monsters)
                ]

                # Nếu tất cả quái đều đã thử mà vẫn kẹt, giữ lại con vừa kẹt gần nhất để đổi sang con khác
                if not available_monsters:
                    if len(blocked_monsters) > 0 and len(sorted_monsters) > 1:
                        last_blocked = blocked_monsters[-1]
                        blocked_monsters = [last_blocked]
                        available_monsters = [
                            m for m in sorted_monsters
                            if math.hypot(m[0] - last_blocked[0], m[1] - last_blocked[1]) >= 40
                        ]
                    if not available_monsters:
                        blocked_monsters.clear()
                        available_monsters = sorted_monsters

                target_monster = available_monsters[0]
                print(
                    f"[+] Phòng có {len(monsters)} quái. Tấn công quái gần nhất tại {target_monster}..."
                )

                screen_prev = screen
                self.click(target_monster, delay=0.6)

                # Chờ nhân vật chạy tới quái và vào trận
                entered_combat = False
                still_count = 0

                for step in range(20):
                    self.check_control_state()
                    if self.is_hp_bar_visible():
                        entered_combat = True
                        break

                    screen_now = self.capture_screen()
                    if self.has_character_moved(screen_prev, screen_now):
                        # Nhân vật vẫn đang di chuyển -> reset đếm đứng yên
                        still_count = 0
                        screen_prev = screen_now
                    else:
                        still_count += 1
                        # Nếu nhân vật đã dừng lại hẳn (2 nhịp liên tiếp không đổi hình) mà chưa vào trận -> bị kẹt
                        if still_count >= 2:
                            break

                    self.sleep(0.5)
                    if self.is_hp_bar_visible():
                        entered_combat = True
                        break

                if entered_combat or self.is_hp_bar_visible():
                    # Đã vào trận thành công -> cập nhật vị trí và xóa danh sách quái kẹt
                    self.player_pos = target_monster
                    blocked_monsters.clear()
                    shots = self.combat_loop()

                    # Nếu ở Chế độ 2 (Chỉ săn Boss > 6 phát bắn) trong phòng Boss
                    if is_boss_room and self.mode == 2 and shots > 6:
                        print("[👑] (Chế độ 2) Đã hạ gục Boss (> 6 phát bắn) và nhặt đồ! Thoát Dungeon ngay...")
                        self.exit_dungeon()
                        return

                    self.wait_for_room_loaded(timeout=5.0)
                else:
                    # Không vào được trận (do kẹt địa hình hoặc bị quái khác chắn) -> Khóa con quái này lại!
                    print(
                        f"    [⚠️] Không đi tới được quái tại {target_monster} (kẹt địa hình/bị chắn)! Chuyển sang quái khác..."
                    )
                    blocked_monsters.append(target_monster)

                continue

            # ----------------------------------------------------
            # TRƯỜNG HỢP B: ĐÃ HẾT QUÁI TRONG PHÒNG
            # ----------------------------------------------------
            if is_boss_room:
                if self.mode in (1, 4):
                    print(f"[🏆] (Chế độ {self.mode}) Đã dọn sạch phòng Boss! Tiến hành thoát Dungeon...")
                    self.exit_dungeon()
                    return
                elif self.mode == 3:
                    print("[🏆] (Chế độ 3) Đã dọn sạch quái phòng Boss! Bắt đầu đi mở toàn bộ Loot...")
                    self.loot_all_in_boss_room()
                    print("[🏆] (Chế độ 3) Đã mở xong toàn bộ Loot! Tiến hành thoát Dungeon...")
                    self.exit_dungeon()
                    return
                elif self.mode == 2:
                    print("[🏆] (Chế độ 2) Đã dọn sạch phòng Boss! Tiến hành thoát Dungeon...")
                    self.exit_dungeon()
                    return

            # ----------------------------------------------------
            # TRƯỜNG HỢP C: PHÒNG THƯỜNG ĐÃ SẠCH QUÁI -> ĐI QUA CỬA
            # ----------------------------------------------------
            if len(white_doors) > 0:
                white_doors = self.sort_by_distance_to_player(white_doors, screen_bgr=screen)
                chosen_door = white_doors[0]
                d_dir = self.get_door_direction(chosen_door)
                print(f"[➡️] Đi qua CỬA TRẮNG ({d_dir}) tại {chosen_door}...")
                self.record_door_transition(chosen_door)
                self.click(chosen_door, delay=1.0)
                is_boss_room = False
                blocked_monsters.clear()
                self.wait_for_room_loaded(timeout=6.0)

            elif len(grey_doors) > 0:
                chosen_door = self.choose_best_grey_door(grey_doors)
                d_dir = self.get_door_direction(chosen_door)
                print(f"[↩️] Không còn cửa trắng. Đi qua CỬA XÁM ({d_dir}) tại {chosen_door}...")
                self.record_door_transition(chosen_door)
                self.click(chosen_door, delay=1.0)
                is_boss_room = False
                blocked_monsters.clear()
                self.wait_for_room_loaded(timeout=6.0)

            else:
                print("[?] Không thấy quái và cũng không thấy cửa, chờ 1s rồi quét lại...")
                self.sleep(1.0)
    # Bí danh để tương thích nếu bạn gọi explore_and_clear_dungeon
    def explore_and_clear_dungeon(self):
        return self.clear_dungeon()

    # ==========================================
    # VÒNG LẶP CHÍNH (CHẠY NHIỀU LƯỢT)
    # ==========================================
    def run(self):
        self.select_mode()
        print("=================================================================")
        print(" PHÍM NÓNG HỖ TRỢ TRONG KHI CHẠY:")
        print("  • [F1] : Chọn lại Loại Dungeon & Chế độ (1/2/3/4) ở lượt kế tiếp")
        print("  • [F2] : Khóa / Đồng bộ tỷ lệ khung cửa sổ game hiện tại")
        print("  • [F8] : Tạm dừng / Tiếp tục Bot (để tự giải mini-game)")
        print("  • [F9] : Khởi động lại chu trình Bot ngay lập tức")
        print("=================================================================")
        print("[*] Bot sẽ bắt đầu sau 3 giây... Hãy chuyển sang cửa sổ game!")
        time.sleep(3)

        run_count = 0
        while run_count < self.cfg["MAX_RUNS"]:
            try:
                if self.reselect_mode_next_run:
                    self.select_mode()

                print(f"\n================ BẮT ĐẦU LƯỢT {run_count + 1} / {self.cfg['MAX_RUNS']} ================")
                if self.enter_dungeon():
                    self.clear_dungeon()
                    run_count += 1
                else:
                    print("[!] Không thể vào Dungeon, thử lại sau 3 giây...")
                    self.sleep(3)

            except RestartBotException:
                print("[🔄] Đã nhận lệnh F9! Bắt đầu lại chu trình mới...")
                continue
            except KeyboardInterrupt:
                print("\n[!] Đã dừng Bot theo yêu cầu người dùng (Ctrl+C).")
                break


if __name__ == "__main__":
    bot = CyberCodeDungeonBot(CONFIG)
    bot.run()