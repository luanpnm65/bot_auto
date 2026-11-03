import pyautogui
import cv2
import numpy as np
import time
import random
import os
import json
import math
import threading
import ctypes
from ctypes import wintypes
import winsound
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
class RestartBotException(Exception):
    """Ngoại lệ dùng để ngắt ngay lập tức mọi thao tác và Restart lại Bot"""
    pass


# Bảng tra cứu hướng cửa ĐỐI DIỆN và vector di chuyển trên bản đồ phòng
OPPOSITE_DIR = {
    "TOP": "BOTTOM",
    "BOTTOM": "TOP",
    "LEFT": "RIGHT",
    "RIGHT": "LEFT"
}

DIR_DELTA = {
    "TOP": (0, -1),
    "BOTTOM": (0, 1),
    "LEFT": (-1, 0),
    "RIGHT": (1, 0)
}


class CyberCodeDungeonBot:
    def __init__(self, config):
        self.cfg = config
        self.run_count = 0
        self.paused = False
        self.restart_requested = False
        
        # Quản lý Loại Dungeon (1: Normal, 2: Co-op, 3: Gang) & Chế độ Boss (1, 2, 3)
        self.dungeon_type = 1
        self.mode = 1
        self.reselect_mode_next_run = False
        self.player_pos = None

        # Bộ nhớ định hướng bản đồ phòng (Chống đi ngược vào cửa đối diện)
        self.room_center = None             # Tâm bản đồ phòng (Cx, Cy)
        self.map_points_history = []        # Lưu các điểm cửa/quái để tính tâm phòng chuẩn
        self.last_exit_dir = None           # Hướng cửa vừa đi ra ở phòng trước ('TOP', 'BOTTOM', 'LEFT', 'RIGHT')
        self.last_exit_coord = None         # Tọa độ cửa vừa click ở phòng trước
        self.room_pos = (0, 0)              # Tọa độ phòng hiện tại trên lưới (rx, ry)
        self.edge_visits = {}               # Đếm số lần đi qua từng cánh cửa ở mỗi phòng

        # ==========================================================
        # HỆ THỐNG QUẢN LÝ TỈ LỆ KHUNG HÌNH (RELATIVE RATIO SYSTEM)
        # ==========================================================
        screen_w, screen_h = pyautogui.size()
        self.calib_file = "window_config.json"
        
        self.base_rect = self.cfg.get("BASE_WINDOW_RECT", (0, 0, screen_w, screen_h))
        self.current_rect = self.base_rect
        self.game_hwnd = None

        self._load_window_calibration()

        # Khởi động luồng lắng nghe phím nóng F1, F2, F8, F9
        listener_thread = threading.Thread(target=self._hotkey_listener, daemon=True)
        listener_thread.start()

    # ==========================================================
    # CÁC HÀM XỬ LÝ TỌA ĐỘ TỈ LỆ & CỬA SỔ GAME (F2)
    # ==========================================================
    def _get_active_window_rect(self):
        try:
            hwnd = ctypes.windll.user32.GetForegroundWindow()
            rect = wintypes.RECT()
            ctypes.windll.user32.GetWindowRect(hwnd, ctypes.byref(rect))
            w = rect.right - rect.left
            h = rect.bottom - rect.top
            if w > 200 and h > 200:
                return hwnd, (rect.left, rect.top, w, h)
        except Exception:
            pass
        sw, sh = pyautogui.size()
        return None, (0, 0, sw, sh)

    def _load_window_calibration(self):
        if os.path.exists(self.calib_file):
            try:
                with open(self.calib_file, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    self.base_rect = tuple(data["base_rect"])
                    self.current_rect = tuple(data.get("current_rect", self.base_rect))
                print(f"[*] Đã tải cấu hình tỉ lệ cửa sổ chuẩn: {self.base_rect}")
            except Exception:
                pass

    def calibrate_or_sync_window(self):
        hwnd, rect = self._get_active_window_rect()
        self.game_hwnd = hwnd

        if not os.path.exists(self.calib_file):
            self.base_rect = rect
            self.current_rect = rect
            with open(self.calib_file, "w", encoding="utf-8") as f:
                json.dump({"base_rect": self.base_rect, "current_rect": self.current_rect}, f, indent=4)
            print("\n========================================================")
            print(f"[📐 ĐÃ LƯU KHUNG CỬA SỔ CHUẨN (F2)]: {self.base_rect}")
            print("-> Mọi tọa độ của bạn đã được khóa theo TỈ LỆ của cửa sổ này!")
            self.print_relative_ratios()
            print("========================================================\n")
        else:
            self.current_rect = rect
            with open(self.calib_file, "w", encoding="utf-8") as f:
                json.dump({"base_rect": self.base_rect, "current_rect": self.current_rect}, f, indent=4)
            scale_w = self.current_rect[2] / self.base_rect[2]
            scale_h = self.current_rect[3] / self.base_rect[3]
            print("\n========================================================")
            print(f"[📐 ĐÃ ĐỒNG BỘ VỊ TRÍ CỬA SỔ MỚI (F2)]: {self.current_rect}")
            print(f"-> Tỉ lệ co giãn so với chuẩn: Ngang {scale_w:.2f}x | Dọc {scale_h:.2f}x")
            print("========================================================\n")

    def auto_refresh_window_rect(self):
        if self.game_hwnd:
            try:
                rect = wintypes.RECT()
                if ctypes.windll.user32.GetWindowRect(self.game_hwnd, ctypes.byref(rect)):
                    w = rect.right - rect.left
                    h = rect.bottom - rect.top
                    if w > 200 and h > 200 and rect.left > -10000:
                        self.current_rect = (rect.left, rect.top, w, h)
            except Exception:
                pass

    def get_coord(self, key):
        """Chuyển đổi tọa độ trong CONFIG sang tọa độ thực tế dựa theo TỈ LỆ cửa sổ"""
        self.auto_refresh_window_rect()
        raw_x, raw_y = self.cfg[key]
        base_l, base_t, base_w, base_h = self.base_rect
        cur_l, cur_t, cur_w, cur_h = self.current_rect

        if isinstance(raw_x, float) and isinstance(raw_y, float) and raw_x <= 1.0 and raw_y <= 1.0:
            ratio_x, ratio_y = raw_x, raw_y
        else:
            ratio_x = (raw_x - base_l) / float(base_w)
            ratio_y = (raw_y - base_t) / float(base_h)

        real_x = int(cur_l + ratio_x * cur_w)
        real_y = int(cur_t + ratio_y * cur_h)
        return (real_x, real_y)

    def print_relative_ratios(self):
        base_l, base_t, base_w, base_h = self.base_rect
        print("--- BẢNG TỌA ĐỘ TỈ LỆ TƯƠNG ĐỐI CỦA BẠN ---")
        coord_keys = [
            "COORD_DUNGEON_NORMAL", "COORD_DUNGEON_COOP", "COORD_DUNGEON_GANG",
            "COORD_HP_START", "COORD_HP_Z", "COORD_SHIELD",
            "COORD_GUN_X", "COORD_GUN_Y", "COORD_HEAL_A", "COORD_LOOT_B"
        ]
        for k in coord_keys:
            if k in self.cfg:
                rx, ry = self.cfg[k]
                if rx > 1.0 or ry > 1.0:
                    rx = round((rx - base_l) / float(base_w), 4)
                    ry = round((ry - base_t) / float(base_h), 4)
                print(f'    "{k}": ({rx}, {ry}),')

    # ==========================================================
    # HỆ THỐNG ĐỊNH HƯỚNG CỬA & TÍNH TỌA ĐỘ ĐỐI DIỆN
    # ==========================================================
    def update_room_geometry(self, white_doors, grey_doors, monsters):
        """
        Tự động xác định Tâm Bản Đồ Phòng (Cx, Cy) từ vị trí các cánh cửa và quái vật.
        Đặc biệt: Khi vừa đi từ Cửa Trắng phòng trước sang phòng mới (chỉ có 1 Cửa Xám đối diện),
        trung điểm của 2 cửa đó chính là Tâm Phòng chính xác tuyệt đối!
        """
        all_doors = white_doors + grey_doors
        for pt in all_doors + monsters:
            self.map_points_history.append(pt)

        # Trường hợp chuẩn xác 100%: Vừa đi qua 1 cửa ở phòng cũ và phòng mới chỉ có đúng 1 Cửa Xám (cửa vừa bước vào)
        if self.last_exit_coord is not None and len(grey_doors) == 1:
            g_door = grey_doors[0]
            dist = math.hypot(g_door[0] - self.last_exit_coord[0], g_door[1] - self.last_exit_coord[1])
            if dist > 80:  # Hai cửa nằm ở 2 bức tường đối diện nhau
                cx = (self.last_exit_coord[0] + g_door[0]) // 2
                cy = (self.last_exit_coord[1] + g_door[1]) // 2
                self.room_center = (cx, cy)
                return

        # Trường hợp tìm thấy 2 cửa đối diện nhau theo trục dọc (TOP - BOTTOM) hoặc trục ngang (LEFT - RIGHT)
        doors_history = [p for p in self.map_points_history]
        if len(all_doors) >= 2:
            for i in range(len(all_doors)):
                for j in range(i + 1, len(all_doors)):
                    d1, d2 = all_doors[i], all_doors[j]
                    # Cùng trục X (lệch nhau < 45px), cách xa nhau theo trục Y (> 120px) -> Cặp cửa TRÊN - DƯỚI
                    if abs(d1[0] - d2[0]) < 45 and abs(d1[1] - d2[1]) > 120:
                        self.room_center = ((d1[0] + d2[0]) // 2, (d1[1] + d2[1]) // 2)
                        return
                    # Cùng trục Y (lệch nhau < 45px), cách xa nhau theo trục X (> 120px) -> Cặp cửa TRÁI - PHẢI
                    if abs(d1[1] - d2[1]) < 45 and abs(d1[0] - d2[0]) > 120:
                        self.room_center = ((d1[0] + d2[0]) // 2, (d1[1] + d2[1]) // 2)
                        return

        # Dự phòng: Tính tâm từ khung bao (Bounding Box) của tất cả các cửa và quái đã thấy
        if self.room_center is None and self.map_points_history:
            xs = [p[0] for p in self.map_points_history]
            ys = [p[1] for p in self.map_points_history]
            self.room_center = ((min(xs) + max(xs)) // 2, (min(ys) + max(ys)) // 2)

    def get_door_direction(self, door_coord):
        """Xác định cánh cửa nằm ở hướng nào ('TOP', 'BOTTOM', 'LEFT', 'RIGHT') so với tâm phòng"""
        if self.room_center is None:
            self.auto_refresh_window_rect()
            l, t, w, h = self.current_rect
            cx, cy = l + w // 2, t + h // 2
        else:
            cx, cy = self.room_center

        dx = door_coord[0] - cx
        dy = door_coord[1] - cy

        if abs(dx) > abs(dy):
            return "RIGHT" if dx > 0 else "LEFT"
        else:
            return "BOTTOM" if dy > 0 else "TOP"

    def get_opposite_coord(self, door_coord):
        """Tính tọa độ cửa đối diện (nơi nhân vật xuất hiện khi bước sang phòng mới)"""
        if self.room_center is None:
            return door_coord
        cx, cy = self.room_center
        return (int(2 * cx - door_coord[0]), int(2 * cy - door_coord[1]))

    def record_door_transition(self, chosen_door):
        """Ghi nhớ hướng cửa vừa bước vào để sang phòng sau biết cửa ĐỐI DIỆN là cửa vừa chui ra"""
        direction = self.get_door_direction(chosen_door)
        
        # Ghi nhận số lần đi qua cánh cửa này tại phòng hiện tại
        edge_key = (self.room_pos[0], self.room_pos[1], direction)
        self.edge_visits[edge_key] = self.edge_visits.get(edge_key, 0) + 1

        # Cập nhật tọa độ phòng mới trên lưới
        dx, dy = DIR_DELTA[direction]
        self.room_pos = (self.room_pos[0] + dx, self.room_pos[1] + dy)

        # Lưu lại hướng và tọa độ cửa vừa đi
        self.last_exit_dir = direction
        self.last_exit_coord = chosen_door

        # Khi sang phòng mới, nhân vật sẽ đứng ở CỬA ĐỐI DIỆN với cửa vừa bấm!
        self.player_pos = self.get_opposite_coord(chosen_door)
        return direction

    def choose_best_grey_door(self, grey_doors):
        """
        Chọn Cửa Xám thông minh khi phòng không còn Cửa Trắng:
        1. Nếu chỉ có 1 Cửa Xám (phòng cụt) -> Bắt buộc đi cửa đó để quay lại.
        2. Nếu có >= 2 Cửa Xám -> LOẠI BỎ CỬA ĐỐI DIỆN với cửa vừa đi ở phòng trước
           (vì cửa đối diện chính là cửa dẫn ngược về phòng vừa mới rời đi!).
        3. Lưu ý: Nếu phòng mới có cửa xám nằm TRÙNG TỌA ĐỘ (cùng hướng) với cửa phòng cũ,
           nó là cửa đi thẳng sang phòng tiếp theo nên ĐƯỢC PHÉP ĐI!
        """
        if len(grey_doors) == 1:
            only_door = grey_doors[0]
            d_dir = self.get_door_direction(only_door)
            print(f"   [*] Phòng cụt (chỉ có 1 Cửa Xám ở hướng {d_dir}) -> Đi ngược lại đường cũ.")
            return only_door

        # Hướng cửa mà nhân vật vừa bước ra khi vào phòng này chính là HƯỚNG ĐỐI DIỆN với hướng đi ở phòng trước
        came_from_dir = OPPOSITE_DIR.get(self.last_exit_dir) if self.last_exit_dir else None
        expected_back_coord = self.get_opposite_coord(self.last_exit_coord) if self.last_exit_coord else None

        candidates = []
        for d in grey_doors:
            d_dir = self.get_door_direction(d)
            
            # Kiểm tra xem cửa này có phải là cửa ĐỐI DIỆN (cửa vừa bước vào phòng) hay không
            is_opposite_direction = (came_from_dir is not None and d_dir == came_from_dir)
            
            # Kiểm tra khoảng cách tới tọa độ đối xứng qua tâm phòng
            is_near_opposite_coord = (
                expected_back_coord is not None and
                math.hypot(d[0] - expected_back_coord[0], d[1] - expected_back_coord[1]) < 65
            )

            # Kiểm tra phụ: Cửa vừa bước ra luôn là cửa nằm XA NHẤT so với tọa độ cửa vừa click ở phòng cũ
            if is_opposite_direction or is_near_opposite_coord:
                print(f"   [Né cửa] Bỏ qua Cửa Xám tại {d} (Hướng {d_dir}) vì đây là cửa ĐỐI DIỆN dẫn ngược về phòng cũ!")
                continue

            candidates.append(d)

        # Dự phòng nếu chưa có tâm phòng chuẩn làm lọc hết hoặc chưa lọc được:
        # Cửa dẫn ngược về phòng cũ luôn là cửa có khoảng cách XA NHẤT so với last_exit_coord!
        if len(candidates) == len(grey_doors) and self.last_exit_coord is not None:
            farthest_door = max(
                grey_doors,
                key=lambda d: math.hypot(d[0] - self.last_exit_coord[0], d[1] - self.last_exit_coord[1])
            )
            candidates = [d for d in grey_doors if d != farthest_door]
            print(f"   [Né cửa] Đã loại bỏ cửa đối diện xa nhất {farthest_door} để không quay lại phòng cũ!")

        if not candidates:
            candidates = grey_doors

        # Nếu vẫn còn nhiều hơn 1 cửa xám hợp lệ (ngã 3, ngã 4), ưu tiên chọn cửa ÍT ĐI QUA NHẤT
        def door_priority(d):
            d_dir = self.get_door_direction(d)
            visits = self.edge_visits.get((self.room_pos[0], self.room_pos[1], d_dir), 0)
            return visits

        candidates.sort(key=door_priority)
        chosen = candidates[0]
        print(f"   [Chọn hướng] Quyết định đi Cửa Xám hướng [{self.get_door_direction(chosen)}] tại {chosen}.")
        return chosen

    # ==========================================================
    # LUỒNG PHÍM NÓNG (F1, F2, F8, F9)
    # ==========================================================
    def _hotkey_listener(self):
        VK_F1 = 0x70
        VK_F2 = 0x71
        VK_F8 = 0x77
        VK_F9 = 0x78
        while True:
            if ctypes.windll.user32.GetAsyncKeyState(VK_F1) & 0x8000:
                self.reselect_mode_next_run = True
                winsound.Beep(900, 200)
                print("\n[🔔 ĐÃ NHẤN F1] Sẽ hiển thị bảng chọn lại Loại Dungeon & Chế Độ ở lượt kế tiếp!\n")
                time.sleep(0.5)

            if ctypes.windll.user32.GetAsyncKeyState(VK_F2) & 0x8000:
                winsound.Beep(1100, 200)
                self.calibrate_or_sync_window()
                time.sleep(0.5)

            if ctypes.windll.user32.GetAsyncKeyState(VK_F8) & 0x8000:
                self.paused = not self.paused
                if self.paused:
                    winsound.Beep(600, 300)
                    print("\n========================================================")
                    print("[⏸ TẠM DỪNG AUTO] Đã nhả chuột để bạn giải Mini-game!")
                    print("-> [F8]: Tiếp tục | [F9]: Restart | [F1]: Đổi Mode | [F2]: Đồng bộ cửa sổ")
                    print("========================================================\n")
                else:
                    winsound.Beep(1000, 150)
                    winsound.Beep(1200, 150)
                    print("\n[▶ TIẾP TỤC AUTO] Bot đang hoạt động trở lại!\n")
                time.sleep(0.5)

            if ctypes.windll.user32.GetAsyncKeyState(VK_F9) & 0x8000:
                winsound.Beep(800, 150)
                winsound.Beep(1000, 150)
                winsound.Beep(1400, 200)
                print("\n[🔄 RESTART AUTO] Đang khởi động lại chu trình Auto...\n")
                self.paused = False
                self.restart_requested = True
                time.sleep(0.5)

            time.sleep(0.05)

    def select_mode(self):
        print("\n========================================================")
        print("        BƯỚC A: CHỌN LOẠI DUNGEON (NORMAL / CO-OP / GANG)")
        print("========================================================")
        print(" [1] Normal Dungeon (Click tọa độ 1: COORD_DUNGEON_NORMAL)")
        print(" [2] Co-op Dungeon  (Click tọa độ 2: COORD_DUNGEON_COOP)")
        print(" [3] Gang Dungeon   (Click tọa độ 3: COORD_DUNGEON_GANG)")
        print("========================================================")
        while True:
            d_choice = input("-> Nhập Loại Dungeon muốn đi (1, 2 hoặc 3) rồi nhấn Enter: ").strip()
            if d_choice in ["1", "2", "3"]:
                self.dungeon_type = int(d_choice)
                break
            print("   [!] Vui lòng chỉ nhập 1, 2 hoặc 3.")

        print("\n========================================================")
        print("        BƯỚC B: CHỌN CHẾ ĐỘ ĐÁNH PHÒNG BOSS (1 / 2 / 3) ")
        print("========================================================")
        print(" [1] Chế độ 1: Clear sạch quái phòng Boss (> 4 quái) rồi thoát.")
        print(" [2] Chế độ 2: Chỉ Kill Boss (Quái bắn > 6 phát mới chết) rồi thoát ngay.")
        print(" [3] Chế độ 3: Clear sạch quái phòng Boss + Loot hết đồ (loot.png) rồi thoát.")
        print("========================================================")
        while True:
            m_choice = input("-> Nhập Chế độ đánh Boss (1, 2 hoặc 3) rồi nhấn Enter: ").strip()
            if m_choice in ["1", "2", "3"]:
                self.mode = int(m_choice)
                self.reselect_mode_next_run = False
                break
            print("   [!] Vui lòng chỉ nhập 1, 2 hoặc 3.")

        dungeon_names = {1: "NORMAL", 2: "CO-OP", 3: "GANG"}
        print(f"\n[✔] Đã chọn: Dungeon [{dungeon_names[self.dungeon_type]}] - Chế độ Boss [{self.mode}]!")
        print("-> Hãy CLICK VÀO CỬA SỔ GAME trong 3 giây tới...")
        time.sleep(3)
        hwnd, _ = self._get_active_window_rect()
        if hwnd and os.path.exists(self.calib_file):
            self.game_hwnd = hwnd
            self.auto_refresh_window_rect()

    def click_selected_dungeon_type(self):
        type_map = {
            1: ("NORMAL", "COORD_DUNGEON_NORMAL"),
            2: ("CO-OP", "COORD_DUNGEON_COOP"),
            3: ("GANG", "COORD_DUNGEON_GANG")
        }
        d_name, coord_key = type_map.get(self.dungeon_type, ("NORMAL", "COORD_DUNGEON_NORMAL"))
        
        if coord_key not in self.cfg:
            print(f"[Lỗi] Bạn chưa khai báo '{coord_key}' trong phần CONFIG!")
            return False

        target_coord = self.get_coord(coord_key)
        print(f"[Bước 2] Chọn loại Dungeon [{d_name}] -> Click tọa độ {target_coord}...")
        self.safe_click(*target_coord)
        self.random_delay(0.8, 1.4)
        return True

    def check_control_state(self):
        if self.restart_requested:
            raise RestartBotException()
        while self.paused:
            if self.restart_requested:
                raise RestartBotException()
            time.sleep(0.2)

    def random_delay(self, min_sec=0.5, max_sec=1.5):
        total_delay = random.uniform(min_sec, max_sec)
        elapsed = 0.0
        while elapsed < total_delay:
            self.check_control_state()
            time.sleep(0.1)
            elapsed += 0.1

    def safe_click(self, x, y):
        self.check_control_state()
        offset_x = random.randint(-3, 3)
        offset_y = random.randint(-3, 3)
        pyautogui.moveTo(int(x) + offset_x, int(y) + offset_y, duration=random.uniform(0.1, 0.25))
        self.check_control_state()
        pyautogui.click()

    def get_screen_bgr(self):
        screenshot = pyautogui.screenshot()
        return cv2.cvtColor(np.array(screenshot), cv2.COLOR_RGB2BGR)

    def check_pixel_color(self, coord, target_rgb):
        try:
            current_rgb = pyautogui.pixel(int(coord[0]), int(coord[1]))
            tol = self.cfg["COLOR_TOLERANCE"]
            return all(abs(current_rgb[i] - target_rgb[i]) <= tol for i in range(3))
        except Exception as e:
            print(f"[Lỗi đọc Pixel] {e}")
            return False

    def is_red_hp_at(self, coord):
        try:
            x, y = int(coord[0]), int(coord[1])
            target_r, target_g, target_b = self.cfg["COLOR_HP_RED"]
            tol = self.cfg["COLOR_TOLERANCE"]

            for dx in [0, -3, 3]:
                r, g, b = pyautogui.pixel(x + dx, y)
                match_config = (abs(r - target_r) <= tol and abs(g - target_g) <= tol and abs(b - target_b) <= tol)
                is_red_dominant = (r > 100 and r > g + 40 and r > b + 40)
                if match_config or is_red_dominant:
                    return True
            return False
        except Exception:
            return False

    def is_hp_bar_visible(self):
        return self.is_red_hp_at(self.get_coord("COORD_HP_START"))

    def is_hp_above_z(self):
        coord_z = self.get_coord("COORD_HP_Z")
        coord_start = self.get_coord("COORD_HP_START")
        if self.is_red_hp_at(coord_z):
            return True
        try:
            start_rgb = pyautogui.pixel(*coord_start)
            z_rgb = pyautogui.pixel(*coord_z)
            tol = self.cfg["COLOR_TOLERANCE"]
            if all(abs(start_rgb[i] - z_rgb[i]) <= tol for i in range(3)):
                return True
        except Exception:
            pass
        return False

    def has_character_moved(self, screen_before, screen_after, threshold=1500):
        diff = cv2.absdiff(screen_before, screen_after)
        gray_diff = cv2.cvtColor(diff, cv2.COLOR_BGR2GRAY)
        _, thresh = cv2.threshold(gray_diff, 30, 255, cv2.THRESH_BINARY)
        changed_pixels = np.count_nonzero(thresh)
        return changed_pixels > threshold

    def find_all_objects(self, image_path, return_best_score=False):
        try:
            if not os.path.exists(image_path):
                return ([], 0.0) if return_best_score else []

            base_template = cv2.imread(image_path, cv2.IMREAD_COLOR)
            if base_template is None:
                return ([], 0.0) if return_best_score else []

            screen_bgr = self.get_screen_bgr()
            best_max_val = 0.0
            points = []

            for scale in [1.0, 0.9, 1.1, 0.8, 1.2]:
                if scale == 1.0:
                    tpl = base_template
                else:
                    new_w = max(8, int(base_template.shape[1] * scale))
                    new_h = max(8, int(base_template.shape[0] * scale))
                    tpl = cv2.resize(base_template, (new_w, new_h), interpolation=cv2.INTER_LINEAR)

                h, w = tpl.shape[:2]
                if h >= screen_bgr.shape[0] or w >= screen_bgr.shape[1]:
                    continue

                res = cv2.matchTemplate(screen_bgr, tpl, cv2.TM_CCOEFF_NORMED)
                _, max_val, _, _ = cv2.minMaxLoc(res)
                if max_val > best_max_val:
                    best_max_val = max_val

                loc = np.where(res >= self.cfg["CONFIDENCE"])
                for pt in zip(*loc[::-1]):
                    cx, cy = int(pt[0] + w // 2), int(pt[1] + h // 2)
                    if all(abs(cx - px) > 20 or abs(cy - py) > 20 for px, py in points):
                        points.append((cx, cy))

                if points:
                    break

            if return_best_score:
                return points, best_max_val
            return points
        except Exception as e:
            print(f"[Lỗi quét ảnh {image_path}] {e}")
            return ([], 0.0) if return_best_score else []

    def update_player_position(self):
        player_img = self.cfg.get("IMG_PLAYER", "player.png")
        if os.path.exists(player_img):
            pts = self.find_all_objects(player_img)
            if pts:
                self.player_pos = pts[0]
                return self.player_pos

        if self.player_pos is None:
            if self.room_center is not None:
                self.player_pos = self.room_center
            else:
                self.auto_refresh_window_rect()
                l, t, w, h = self.current_rect
                self.player_pos = (l + w // 2, t + h // 2)
        return self.player_pos

    def sort_targets_by_closest(self, targets):
        if not targets:
            return []
        px, py = self.update_player_position()
        return sorted(targets, key=lambda pt: math.hypot(pt[0] - px, pt[1] - py))

    def classify_doors(self):
        screen_bgr = self.get_screen_bgr()
        tpl_white = cv2.imread(self.cfg["IMG_DOOR_WHITE"], cv2.IMREAD_COLOR)
        tpl_grey = cv2.imread(self.cfg["IMG_DOOR_GREY"], cv2.IMREAD_COLOR)

        if tpl_white is None or tpl_grey is None:
            return [], []

        white_brightness = float(np.mean(tpl_white))
        grey_brightness = float(np.mean(tpl_grey))
        mid_brightness = (white_brightness + grey_brightness) / 2.0

        raw_doors = self.find_all_objects(self.cfg["IMG_DOOR_WHITE"])
        for gd in self.find_all_objects(self.cfg["IMG_DOOR_GREY"]):
            if all(abs(gd[0] - d[0]) > 25 or abs(gd[1] - d[1]) > 25 for d in raw_doors):
                raw_doors.append(gd)

        h, w = tpl_white.shape[:2]
        white_doors, grey_doors = [], []

        for (cx, cy) in raw_doors:
            y1, y2 = max(0, cy - h // 2), min(screen_bgr.shape[0], cy + h // 2)
            x1, x2 = max(0, cx - w // 2), min(screen_bgr.shape[1], cx + w // 2)
            door_patch = screen_bgr[y1:y2, x1:x2]
            patch_brightness = float(np.mean(door_patch))

            if white_brightness >= grey_brightness:
                if patch_brightness >= mid_brightness:
                    white_doors.append((cx, cy))
                else:
                    grey_doors.append((cx, cy))
            else:
                if patch_brightness <= mid_brightness:
                    white_doors.append((cx, cy))
                else:
                    grey_doors.append((cx, cy))

        return white_doors, grey_doors

    def is_room_map_visible(self):
        monsters = self.find_all_objects(self.cfg["IMG_MONSTER"])
        white_doors, grey_doors = self.classify_doors()
        exit_btn = self.find_all_objects(self.cfg["IMG_EXIT_DUNGEON"])
        return bool(monsters or white_doors or grey_doors or exit_btn)

    def is_already_in_dungeon(self):
        if self.is_hp_bar_visible():
            return True
        if self.is_room_map_visible():
            return True
        return False

    def handle_post_combat_loot(self):
        self.random_delay(0.7, 1.1)
        
        for attempt in range(5):
            self.check_control_state()
            monsters = self.find_all_objects(self.cfg["IMG_MONSTER"])
            doors_white, doors_grey = self.classify_doors()

            if monsters or doors_white or doors_grey:
                if attempt == 0:
                    print("   [-] Không có bảng rơi đồ. Đã ở màn hình phòng.")
                else:
                    print("   [+] Đã nhận đồ tại tọa độ B xong!")
                return

            print(f"   [$] Không thấy cửa/quái -> Có RƠI ĐỒ (Lần {attempt + 1}) -> Click tọa độ B!")
            self.safe_click(*self.get_coord("COORD_LOOT_B"))
            self.random_delay(0.8, 1.3)

    def loot_all_in_boss_room(self):
        loot_img = self.cfg.get("IMG_LOOT", "loot.png")
        if not os.path.exists(loot_img):
            print(f"[Cảnh báo] Bạn chưa có file ảnh '{loot_img}' trong thư mục để chạy Chế độ 3!")
            return

        print("\n[Chế độ 3] Bắt đầu quét và nhặt toàn bộ Loot (loot.png) trong phòng Boss...")
        visited_empty_loots = []

        while True:
            self.check_control_state()
            self.wait_for_room_loaded(timeout=4)

            all_loots = self.find_all_objects(loot_img)
            loots = [
                pt for pt in all_loots
                if all(abs(pt[0] - v[0]) > 25 or abs(pt[1] - v[1]) > 25 for v in visited_empty_loots)
            ]

            if not loots:
                print("[Chế độ 3] Đã kiểm tra và nhặt hết toàn bộ Loot trong phòng Boss!")
                break

            loots = self.sort_targets_by_closest(loots)
            target_loot = loots[0]
            print(f"-> Phát hiện {len(loots)} điểm Loot. Di chuyển tới Loot gần nhất tại {target_loot}...")

            screen_before = self.get_screen_bgr()
            self.safe_click(*target_loot)
            self.random_delay(0.8, 1.2)

            for _ in range(10):
                self.check_control_state()
                monsters = self.find_all_objects(self.cfg["IMG_MONSTER"])
                doors_w, doors_g = self.classify_doors()
                
                if not monsters and not doors_w and not doors_g:
                    break
                
                screen_now = self.get_screen_bgr()
                if not self.has_character_moved(screen_before, screen_now):
                    break
                screen_before = screen_now
                time.sleep(0.5)

            monsters = self.find_all_objects(self.cfg["IMG_MONSTER"])
            doors_w, doors_g = self.classify_doors()

            if not monsters and not doors_w and not doors_g:
                print("   [$] Không thấy cửa/quái -> Xác nhận CÓ LOOT! Click tọa độ B để nhận...")
                self.handle_post_combat_loot()
                self.player_pos = target_loot
            else:
                print("   [-] Vẫn thấy cửa/quái -> Điểm này không có Loot.")
                visited_empty_loots.append(target_loot)
                self.player_pos = target_loot

    def wait_and_click_image(self, image_path, timeout=10):
        start_time = time.time()
        best_score = 0.0
        while time.time() - start_time < timeout:
            self.check_control_state()
            points, score = self.find_all_objects(image_path, return_best_score=True)
            if score > best_score:
                best_score = score
            if points:
                self.safe_click(*points[0])
                self.random_delay(0.5, 1.2)
                return True
            time.sleep(0.5)
        print(f"[Timeout] Không tìm thấy '{image_path}' (Độ khớp cao nhất: {best_score:.2f} / Cần: {self.cfg['CONFIDENCE']})")
        return False

    def exit_dungeon_with_confirm(self):
        print("-> Đang bấm nút Thoát Dungeon...")
        if self.wait_and_click_image(self.cfg["IMG_EXIT_DUNGEON"], timeout=5):
            print("-> Chờ Pop-up xác nhận và ấn nút 'Yes'...")
            if self.wait_and_click_image(self.cfg["IMG_CONFIRM_YES"], timeout=5):
                print("   [+] Đã ấn 'Yes' thoát khỏi Dungeon thành công!")
                self.random_delay(1.0, 1.8)
                return True
            else:
                print("   [!] Không tìm thấy nút 'Yes' trên Pop-up!")
        else:
            print("   [!] Không tìm thấy nút Thoát Dungeon!")
        return False

    def wait_for_room_loaded(self, timeout=6):
        print("   [...] Đang chờ phòng tải xong bản đồ...")
        start_time = time.time()
        clicked_loot_backup = False

        while time.time() - start_time < timeout:
            self.check_control_state()
            monsters = self.find_all_objects(self.cfg["IMG_MONSTER"])
            white_doors, grey_doors = self.classify_doors()
            
            if monsters or white_doors or grey_doors:
                time.sleep(0.5)
                return True

            if (time.time() - start_time > 2.5) and not clicked_loot_backup and not self.is_hp_bar_visible():
                print("   [!] Chưa thấy cửa/quái, thử click tọa độ B phòng trường hợp còn bảng Rơi Đồ...")
                self.safe_click(*self.get_coord("COORD_LOOT_B"))
                clicked_loot_backup = True

            time.sleep(0.4)
        print("   [Cảnh báo] Quá thời gian chờ tải phòng!")
        return False

    # ==========================================
    # GIAI ĐOẠN 3 & 4: TIẾP CẬN, ĐÁNH QUÁI & ĐẾM SỐ PHÁT BẮN
    # ==========================================
    def combat_loop(self):
        print("   [⚔] Đang ở màn hình chiến đấu! Bắt đầu xả đạn...")
        combat_active = True
        shots_fired = 0
        
        while combat_active:
            self.check_control_state()

            if not self.is_hp_bar_visible():
                print(f"   [+] Thanh máu biến mất -> QUÁI ĐÃ CHẾT sau {shots_fired} phát bắn!")
                combat_active = False
                break

            if not self.is_hp_above_z():
                z_rgb = pyautogui.pixel(*self.get_coord("COORD_HP_Z"))
                start_rgb = pyautogui.pixel(*self.get_coord("COORD_HP_START"))
                print(f"   [Hồi máu] Máu tại Z {z_rgb} khác đầu thanh máu {start_rgb} -> Bấm hồi máu tại A!")
                self.safe_click(*self.get_coord("COORD_HEAL_A"))
                self.random_delay(0.5, 0.9)

            shots_fired += 1
            has_shield = self.check_pixel_color(self.get_coord("COORD_SHIELD"), self.cfg["COLOR_SHIELD"])
            if has_shield:
                print(f"   [Bắn phát {shots_fired}] Quái CÓ giáp ảo -> Click súng tọa độ X.")
                self.safe_click(*self.get_coord("COORD_GUN_X"))
            else:
                print(f"   [Bắn phát {shots_fired}] Quái KHÔNG giáp -> Click súng tọa độ Y.")
                self.safe_click(*self.get_coord("COORD_GUN_Y"))

            self.random_delay(0.8, 1.4)

        self.handle_post_combat_loot()
        return shots_fired

    def try_engage_and_kill_monster(self, monster_coord):
        self.check_control_state()
        print(f"-> Thử tiếp cận quái gần nhất tại ({int(monster_coord[0])}, {int(monster_coord[1])})...")
        screen_before = self.get_screen_bgr()
        
        self.safe_click(*monster_coord)
        self.random_delay(0.7, 1.0)
        
        screen_after = self.get_screen_bgr()

        if not self.is_hp_bar_visible():
            if not self.has_character_moved(screen_before, screen_after):
                print("   [!] Nhân vật KHÔNG di chuyển (Quái này bị chặn đường)! Đổi sang quái gần tiếp theo...")
                return False, 0
            
            print("   [...] Nhân vật đang đi tới quái & tải trận, đang chờ vào trận...")
            entered_combat = False
            
            for _ in range(20):
                self.check_control_state()
                if self.is_hp_bar_visible():
                    entered_combat = True
                    break
                time.sleep(0.6)
                
            if not entered_combat:
                print("   [!] Đã chờ hết thời gian nhưng chưa thấy Thanh Máu xuất hiện!")
                return False, 0

        self.player_pos = monster_coord
        shots = self.combat_loop()
        return True, shots

    # ==========================================
    # GIAI ĐOẠN 2 & 5: QUÉT PHÒNG, CHẾ ĐỘ BOSS & QUA CỬA
    # ==========================================
    def explore_dungeon(self):
        in_dungeon = True
        self.last_exit_dir = None
        self.last_exit_coord = None
        self.room_pos = (0, 0)
        self.edge_visits = {}
        self.player_pos = None
        
        while in_dungeon:
            self.check_control_state()

            if self.is_hp_bar_visible():
                print("[*] Phát hiện nhân vật đang ở sẵn trong trận đánh! Tiếp tục chiến đấu...")
                self.combat_loop()

            self.wait_for_room_loaded(timeout=6)
            
            monsters = self.find_all_objects(self.cfg["IMG_MONSTER"])
            white_doors, grey_doors = self.classify_doors()
            
            # Tự động cập nhật Tâm Phòng (Cx, Cy) ngay khi vào phòng để phân biệt 4 hướng cửa
            self.update_room_geometry(white_doors, grey_doors, monsters)

            monster_count = len(monsters)
            print(f"\n[Phòng {self.room_pos}] Phát hiện {monster_count} quái vật. (Đang chạy Chế độ {self.mode})")

            is_boss_room = False
            if monster_count > 4:
                is_boss_room = True
                print(f"[🔥 PHÒNG BOSS] Phát hiện phòng có {monster_count} quái (> 4 quái)! Áp dụng logic Chế độ {self.mode}.")

            boss_killed_early_exit = False

            while len(monsters) > 0:
                self.check_control_state()
                killed_any = False
                
                monsters = self.sort_targets_by_closest(monsters)
                
                for idx, m_coord in enumerate(monsters):
                    self.check_control_state()
                    print(f"   -> Ưu tiên quái gần nhất số {idx + 1}/{len(monsters)}")
                    killed, shots_fired = self.try_engage_and_kill_monster(m_coord)
                    
                    if killed:
                        killed_any = True
                        if self.mode == 2 and shots_fired > 6:
                            print(f"\n[🎯 ĐÃ DIỆT BOSS] Quái vừa rồi cần tới {shots_fired} phát bắn (> 6 phát)!")
                            print("-> Theo Chế độ 2 (Chỉ Kill Boss): Lập tức rút lui khỏi Dungeon ngay!")
                            boss_killed_early_exit = True
                        break
                
                if boss_killed_early_exit:
                    break

                if self.is_hp_bar_visible():
                    print("   [!] Phát hiện đang ở trong trận đánh muộn, tiếp tục chiến đấu...")
                    shots_fired = self.combat_loop()
                    killed_any = True
                    if self.mode == 2 and shots_fired > 6:
                        print(f"\n[🎯 ĐÃ DIỆT BOSS] Quái vừa rồi cần tới {shots_fired} phát bắn (> 6 phát)!")
                        boss_killed_early_exit = True
                        break

                self.wait_for_room_loaded(timeout=5)
                monsters = self.find_all_objects(self.cfg["IMG_MONSTER"])
                
                if not killed_any and len(monsters) > 0:
                    print("[Cảnh báo] Chưa tiếp cận được quái! Chờ 1s rồi quét lại...")
                    time.sleep(1.0)

            if boss_killed_early_exit:
                self.exit_dungeon_with_confirm()
                in_dungeon = False
                break

            print(f"[Phòng {self.room_pos}] Đã clear hết quái trong phòng!")

            if is_boss_room:
                if self.mode == 3:
                    self.loot_all_in_boss_room()
                
                print(f"-> Hoàn thành nhiệm vụ Phòng Boss (Chế độ {self.mode}). Thực hiện thoát Dungeon...")
                self.exit_dungeon_with_confirm()
                in_dungeon = False
                break

            # Quét lại cửa sau khi đã dọn sạch quái
            white_doors, grey_doors = self.classify_doors()
            self.update_room_geometry(white_doors, grey_doors, [])
            print(f"[Quét Cửa] Tìm thấy: {len(white_doors)} Cửa Trắng | {len(grey_doors)} Cửa Xám.")

            # ƯU TIÊN 1: Còn Cửa Trắng là BẮT BUỘC đi Cửa Trắng (Ưu tiên cửa trắng gần nhân vật nhất)
            if white_doors:
                white_doors = self.sort_targets_by_closest(white_doors)
                chosen_white = white_doors[0]
                out_dir = self.record_door_transition(chosen_white)
                print(f"-> Đi vào CỬA TRẮNG hướng [{out_dir}] tại {chosen_white} (Sang phòng {self.room_pos})...")
                self.safe_click(*chosen_white)
                self.random_delay(1.2, 2.0)
                continue

            # ƯU TIÊN 2: Hết Cửa Trắng -> Chọn Cửa Xám (Né CỬA ĐỐI DIỆN vừa bước ra)
            if grey_doors:
                chosen_grey = self.choose_best_grey_door(grey_doors)
                out_dir = self.record_door_transition(chosen_grey)
                print(f"-> Hết cửa trắng. Đi vào CỬA XÁM hướng [{out_dir}] tại {chosen_grey} (Sang phòng {self.room_pos})...")
                self.safe_click(*chosen_grey)
                self.random_delay(1.2, 2.0)
                continue

            print("-> Không còn cửa nào trên màn hình. Thoát hoặc hoàn thành Dungeon!")
            self.exit_dungeon_with_confirm()
            in_dungeon = False

    def start(self):
        print("=== BẮT ĐẦU AUTO DUNGEON CYBERCODE ONLINE ===")
        print("💡 Phím [F1]: Chọn lại Loại Dungeon & Chế độ (1/2/3) ở lượt kế tiếp.")
        print("💡 Phím [F2]: Khóa Tỉ Lệ Cửa Sổ Game / Đồng bộ khi dời cửa sổ game.")
        print("💡 Phím [F8]: TẠM DỪNG / TIẾP TỤC (Để giải Mini-game).")
        print("💡 Phím [F9]: RESTART AUTO ngay lập tức.")
        print("💡 Hất mạnh chuột về góc trên bên trái màn hình để DỪNG HẲN.")

        self.select_mode()

        try:
            while self.run_count < self.cfg["MAX_RUNS"]:
                try:
                    self.restart_requested = False
                    self.check_control_state()

                    if self.reselect_mode_next_run:
                        self.select_mode()

                    if self.is_already_in_dungeon():
                        print("\n========================================================")
                        print(f"[*] Phát hiện ĐANG Ở SẴN TRONG DUNGEON! (Chế độ {self.mode})")
                        print("-> Bắt đầu dọn phòng ngay lập tức...")
                        print("========================================================")
                        self.explore_dungeon()
                        self.random_delay(1.5, 3.0)
                        continue

                    self.run_count += 1
                    print(f"\n================ LƯỢT DUNGEON {self.run_count}/{self.cfg['MAX_RUNS']} (CHẾ ĐỘ {self.mode}) ================")

                    if not self.wait_and_click_image(self.cfg["IMG_MENU_DUNGEON"], timeout=5):
                        if self.is_already_in_dungeon():
                            continue
                        time.sleep(2)
                        continue

                    if not self.click_selected_dungeon_type():
                        continue

                    if not self.wait_and_click_image(self.cfg["IMG_ENTER_DUNGEON"]):
                        continue

                    self.explore_dungeon()
                    self.random_delay(1.5, 3.0)

                except RestartBotException:
                    print("[🔄] Đã nhận lệnh Restart (F9)! Đang kiểm tra lại màn hình hiện tại...")
                    if self.reselect_mode_next_run:
                        self.select_mode()
                    time.sleep(1.0)
                    continue

            print("\n=== ĐÃ HOÀN THÀNH ĐỦ SỐ LƯỢT CHẠY! ===")
        except pyautogui.FailSafeException:
            print("\n[DỪNG KHẨN CẤP] Đã ngắt Bot an toàn.")
        except KeyboardInterrupt:
            print("\n[DỪNG] Người dùng nhấn Ctrl+C.")


if __name__ == "__main__":
    bot = CyberCodeDungeonBot(CONFIG)
    bot.start()