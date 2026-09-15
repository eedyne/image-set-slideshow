from __future__ import annotations

import ctypes
import queue
import random
import re
import sys
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

from PIL import Image, ImageOps, ImageTk


APP_TITLE = "묶음 이미지 슬라이드"
SUPPORTED_EXTENSIONS = {
    ".jpg",
    ".jpeg",
    ".png",
    ".webp",
    ".bmp",
    ".gif",
    ".tif",
    ".tiff",
}
GROUP_PATTERN = re.compile(r"^(?P<group>.+?)\s*\((?P<number>\d+)\)\s*$")
BACKGROUND = "#111214"
PANEL = "#1b1d21"
TEXT = "#f2f3f5"
MUTED = "#a6abb4"
ACCENT = "#62a8ff"


@dataclass(frozen=True)
class Slide:
    group_name: str
    number: int
    path: Path


@dataclass(frozen=True)
class ImageGroup:
    name: str
    slides: tuple[Slide, ...]


def parse_groups(folder: Path) -> tuple[list[ImageGroup], list[str]]:
    """Read one folder and group images by the '(number)' suffix in the stem."""
    grouped: dict[str, dict[int, Path]] = {}
    display_names: dict[str, str] = {}
    issues: list[str] = []

    try:
        entries = sorted(
            (entry for entry in folder.iterdir() if entry.is_file()),
            key=lambda path: path.name.casefold(),
        )
    except OSError as exc:
        return [], [f"폴더를 읽을 수 없습니다: {exc}"]

    for path in entries:
        if path.suffix.casefold() not in SUPPORTED_EXTENSIONS:
            continue

        match = GROUP_PATTERN.match(path.stem)
        if not match:
            issues.append(f"파일명 형식이 달라 제외: {path.name}")
            continue

        group_name = match.group("group").strip()
        number = int(match.group("number"))
        key = group_name.casefold()
        display_names.setdefault(key, group_name)
        slots = grouped.setdefault(key, {})

        if number in slots:
            issues.append(
                f"같은 묶음 번호가 중복되어 제외: {path.name} "
                f"(이미 {slots[number].name} 사용 중)"
            )
            continue
        slots[number] = path

    groups: list[ImageGroup] = []
    for key in sorted(grouped, key=lambda item: display_names[item].casefold()):
        numbered_paths = grouped[key]
        name = display_names[key]
        numbers = sorted(numbered_paths)

        if not 3 <= len(numbers) <= 5:
            issues.append(
                f"'{name}' 묶음 제외: 이미지가 {len(numbers)}장입니다 (3~5장 필요)"
            )
            continue

        expected = list(range(1, len(numbers) + 1))
        if numbers != expected:
            found = ", ".join(map(str, numbers))
            issues.append(
                f"'{name}' 묶음 제외: 번호가 1부터 연속되지 않습니다 (발견: {found})"
            )
            continue

        slides = tuple(
            Slide(name, number, numbered_paths[number]) for number in numbers
        )
        groups.append(ImageGroup(name, slides))

    return groups, issues


def shuffled_groups(
    groups: list[ImageGroup], previous_last: str | None = None
) -> list[ImageGroup]:
    order = list(groups)
    random.shuffle(order)

    # Avoid repeating the final group of the previous cycle at the boundary.
    if len(order) > 1 and previous_last and order[0].name == previous_last:
        swap_index = random.randrange(1, len(order))
        order[0], order[swap_index] = order[swap_index], order[0]
    return order


def load_scaled_image(path: Path, target_width: int, target_height: int) -> Image.Image:
    """Decode and scale in a worker thread; never retains the full-size source."""
    with Image.open(path) as source:
        source.seek(0)
        image = ImageOps.exif_transpose(source).convert("RGBA")
        image.thumbnail(
            (max(1, target_width), max(1, target_height)),
            Image.Resampling.LANCZOS,
            reducing_gap=3.0,
        )
        background = Image.new("RGB", image.size, BACKGROUND)
        background.paste(image, mask=image.getchannel("A"))
        return background


class SlideshowApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("1180x760")
        self.root.minsize(720, 480)
        self.root.configure(bg=BACKGROUND)

        self.groups: list[ImageGroup] = []
        self.group_order: list[ImageGroup] = []
        self.playlist: list[Slide] = []
        self.slide_index = -1
        self.playing = False
        self.fullscreen = False
        self.timer_id: str | None = None
        self.resize_id: str | None = None
        self.current_image_key: tuple[str, int, int] | None = None
        self.photo: ImageTk.PhotoImage | None = None
        self.current_canvas_item: int | None = None
        self.last_folder: Path | None = None
        self.issues: list[str] = []

        self.executor = ThreadPoolExecutor(max_workers=2, thread_name_prefix="image-loader")
        self.results: queue.Queue = queue.Queue()
        self.pending: set[tuple[str, int, int]] = set()
        self.cache: OrderedDict[tuple[str, int, int], Image.Image] = OrderedDict()
        self.cache_limit = 3

        self.interval_var = tk.StringVar(value="3.0")
        self.folder_var = tk.StringVar(value="폴더를 선택하세요")
        self.status_var = tk.StringVar(value="이미지 폴더를 불러오면 자동으로 재생합니다")
        self.detail_var = tk.StringVar(value="")

        self._build_style()
        self._build_ui()
        self._bind_keys()
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.after(30, self._poll_results)

    def _build_style(self) -> None:
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure("Panel.TFrame", background=PANEL)
        style.configure("Panel.TLabel", background=PANEL, foreground=TEXT)
        style.configure("Muted.TLabel", background=PANEL, foreground=MUTED)
        style.configure(
            "Accent.TButton",
            background=ACCENT,
            foreground="#08111c",
            borderwidth=0,
            padding=(14, 8),
            font=("맑은 고딕", 10, "bold"),
        )
        style.map("Accent.TButton", background=[("active", "#87bdff")])
        style.configure(
            "Dark.TButton",
            background="#2a2d33",
            foreground=TEXT,
            borderwidth=0,
            padding=(12, 8),
            font=("맑은 고딕", 10),
        )
        style.map("Dark.TButton", background=[("active", "#3a3e46")])
        style.configure(
            "Dark.TSpinbox",
            fieldbackground="#292c32",
            foreground=TEXT,
            arrowcolor=TEXT,
            bordercolor="#42464f",
            insertcolor=TEXT,
            padding=5,
        )

    def _build_ui(self) -> None:
        top = ttk.Frame(self.root, style="Panel.TFrame", padding=(14, 10))
        top.pack(side="top", fill="x")

        ttk.Button(
            top,
            text="이미지 폴더 열기",
            command=self.choose_folder,
            style="Accent.TButton",
        ).pack(side="left")

        ttk.Label(
            top,
            textvariable=self.folder_var,
            style="Muted.TLabel",
            font=("맑은 고딕", 9),
        ).pack(side="left", padx=(12, 20), fill="x", expand=True)

        ttk.Label(top, text="장당", style="Panel.TLabel").pack(side="left")
        self.interval_spinbox = ttk.Spinbox(
            top,
            from_=0.1,
            to=3600.0,
            increment=0.1,
            width=7,
            textvariable=self.interval_var,
            style="Dark.TSpinbox",
            command=self.apply_interval,
        )
        self.interval_spinbox.pack(side="left", padx=(7, 4))
        self.interval_spinbox.bind("<Return>", self.apply_interval)
        self.interval_spinbox.bind("<FocusOut>", self.apply_interval)
        ttk.Label(top, text="초", style="Panel.TLabel").pack(side="left", padx=(0, 12))

        self.play_button = ttk.Button(
            top, text="재생", command=self.toggle_play, style="Dark.TButton"
        )
        self.play_button.pack(side="left", padx=(0, 8))
        ttk.Button(
            top, text="전체화면", command=self.toggle_fullscreen, style="Dark.TButton"
        ).pack(side="left")

        self.canvas = tk.Canvas(
            self.root,
            background=BACKGROUND,
            highlightthickness=0,
            bd=0,
        )
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", self._on_canvas_resize)

        bottom = ttk.Frame(self.root, style="Panel.TFrame", padding=(14, 9))
        bottom.pack(side="bottom", fill="x")
        ttk.Label(
            bottom,
            textvariable=self.status_var,
            style="Panel.TLabel",
            font=("맑은 고딕", 10, "bold"),
        ).pack(side="left")
        ttk.Label(
            bottom,
            textvariable=self.detail_var,
            style="Muted.TLabel",
            font=("맑은 고딕", 9),
        ).pack(side="right")

        self._draw_message(
            "이미지 폴더를 선택하세요",
            "예: fh23g1 (1).png  ·  fh23g1 (2).jpg  ·  fh23g1 (3).png",
        )

    def _bind_keys(self) -> None:
        self.root.bind_all("<space>", self._on_space)
        self.root.bind_all("<Right>", lambda _event: self.next_slide(manual=True))
        self.root.bind_all("<Left>", lambda _event: self.previous_slide())
        self.root.bind_all("<F11>", lambda _event: self.toggle_fullscreen())
        self.root.bind_all("<Escape>", self._on_escape)
        self.root.bind_all("<Control-o>", lambda _event: self.choose_folder())
        # Space always means play/pause, even if a button or the time field has focus.
        self.root.bind_class("TButton", "<space>", self._on_space)
        self.root.bind_class("TSpinbox", "<space>", self._on_space)

    def choose_folder(self) -> None:
        folder = filedialog.askdirectory(
            title="이미지가 들어 있는 폴더 선택",
            initialdir=str(self.last_folder) if self.last_folder else None,
        )
        if folder:
            self.load_folder(Path(folder))

    def load_folder(self, folder: Path) -> None:
        groups, issues = parse_groups(folder)
        if not groups:
            detail = "\n".join(issues[:12]) if issues else "지원되는 이미지가 없습니다."
            messagebox.showerror(
                "재생할 묶음이 없습니다",
                "3~5장으로 구성되고 번호가 1부터 이어지는 묶음을 찾지 못했습니다.\n\n"
                + detail,
            )
            return

        self._cancel_timer()
        self.groups = groups
        self.issues = issues
        self.last_folder = folder
        self.folder_var.set(str(folder))
        self.cache.clear()
        self.pending.clear()
        self._start_new_cycle()
        self.slide_index = 0
        self.playing = True
        self._sync_play_button()
        self.show_current_slide()
        self.canvas.focus_set()

        image_count = sum(len(group.slides) for group in groups)
        self.detail_var.set(f"{len(groups)}묶음 · {image_count}장")
        if issues:
            self.root.after(150, self._show_scan_issues)

    def _show_scan_issues(self) -> None:
        if not self.issues:
            return
        shown = "\n".join(f"• {item}" for item in self.issues[:15])
        remaining = len(self.issues) - 15
        if remaining > 0:
            shown += f"\n• 그 외 {remaining}개"
        messagebox.showwarning(
            "일부 파일을 제외했습니다",
            "정상 묶음은 그대로 재생합니다.\n\n" + shown,
        )

    def _start_new_cycle(self) -> None:
        previous_last = self.group_order[-1].name if self.group_order else None
        self.group_order = shuffled_groups(self.groups, previous_last)
        self.playlist = [slide for group in self.group_order for slide in group.slides]

    def show_current_slide(self) -> None:
        if not self.playlist or self.slide_index < 0:
            return

        slide = self.playlist[self.slide_index]
        group_position = next(
            i for i, group in enumerate(self.group_order, start=1) if group.name == slide.group_name
        )
        self.status_var.set(
            f"{slide.group_name}  ·  {slide.number}/{self._group_size(slide.group_name)}"
        )
        self.detail_var.set(
            f"묶음 {group_position}/{len(self.group_order)}  ·  "
            f"이미지 {self.slide_index + 1}/{len(self.playlist)}"
        )
        self._request_image(slide.path)
        self._schedule_timer()

    def _group_size(self, group_name: str) -> int:
        for group in self.group_order:
            if group.name == group_name:
                return len(group.slides)
        return 0

    def _request_image(self, path: Path) -> None:
        width = max(1, self.canvas.winfo_width())
        height = max(1, self.canvas.winfo_height())
        key = (str(path), width, height)
        self.current_image_key = key

        cached = self.cache.get(key)
        if cached is not None:
            self.cache.move_to_end(key)
            self._display_pil(cached)
        else:
            self._queue_load(path, width, height)

        if self.slide_index + 1 < len(self.playlist):
            next_path = self.playlist[self.slide_index + 1].path
            self._queue_load(next_path, width, height)

    def _queue_load(self, path: Path, width: int, height: int) -> None:
        key = (str(path), width, height)
        if key in self.cache or key in self.pending:
            return
        self.pending.add(key)

        future = self.executor.submit(load_scaled_image, path, width, height)

        def done(completed) -> None:
            try:
                self.results.put((key, completed.result(), None))
            except Exception as exc:  # corrupt or unreadable source file
                self.results.put((key, None, str(exc)))

        future.add_done_callback(done)

    def _poll_results(self) -> None:
        try:
            while True:
                key, image, error = self.results.get_nowait()
                self.pending.discard(key)
                if image is not None:
                    self.cache[key] = image
                    self.cache.move_to_end(key)
                    while len(self.cache) > self.cache_limit:
                        self.cache.popitem(last=False)

                if key == self.current_image_key:
                    if error:
                        self._draw_message("이미지를 열 수 없습니다", Path(key[0]).name)
                    elif image is not None:
                        self._display_pil(image)
        except queue.Empty:
            pass
        if self.root.winfo_exists():
            self.root.after(30, self._poll_results)

    def _display_pil(self, image: Image.Image) -> None:
        self.photo = ImageTk.PhotoImage(image)
        self.canvas.delete("all")
        x = self.canvas.winfo_width() // 2
        y = self.canvas.winfo_height() // 2
        self.current_canvas_item = self.canvas.create_image(x, y, image=self.photo, anchor="center")

    def _draw_message(self, title: str, subtitle: str) -> None:
        self.canvas.delete("all")
        width = max(self.canvas.winfo_width(), 720)
        height = max(self.canvas.winfo_height(), 400)
        self.canvas.create_text(
            width // 2,
            height // 2 - 18,
            text=title,
            fill=TEXT,
            font=("맑은 고딕", 18, "bold"),
        )
        self.canvas.create_text(
            width // 2,
            height // 2 + 22,
            text=subtitle,
            fill=MUTED,
            font=("맑은 고딕", 10),
        )

    def next_slide(self, manual: bool = False) -> None:
        if not self.playlist:
            return
        if self.slide_index >= len(self.playlist) - 1:
            self._start_new_cycle()
            self.slide_index = 0
        else:
            self.slide_index += 1
        self.show_current_slide()
        if manual and not self.playing:
            self._cancel_timer()

    def previous_slide(self) -> None:
        if not self.playlist or self.slide_index <= 0:
            return
        self.slide_index -= 1
        self.show_current_slide()
        if not self.playing:
            self._cancel_timer()

    def toggle_play(self) -> None:
        if not self.playlist:
            self.choose_folder()
            return
        self.playing = not self.playing
        self._sync_play_button()
        if self.playing:
            self._schedule_timer()
        else:
            self._cancel_timer()

    def _sync_play_button(self) -> None:
        self.play_button.configure(text="일시정지" if self.playing else "재생")

    def _on_space(self, event) -> str:
        self.toggle_play()
        return "break"

    def apply_interval(self, _event=None) -> str:
        try:
            seconds = float(self.interval_var.get().replace(",", "."))
        except ValueError:
            seconds = 3.0
        seconds = min(3600.0, max(0.1, seconds))
        formatted = f"{seconds:.1f}".rstrip("0").rstrip(".")
        self.interval_var.set(formatted)
        self.canvas.focus_set()
        if self.playing and self.playlist:
            self._schedule_timer()
        return "break"

    def _interval_ms(self) -> int:
        try:
            seconds = float(self.interval_var.get().replace(",", "."))
        except ValueError:
            seconds = 3.0
        return max(100, int(min(3600.0, max(0.1, seconds)) * 1000))

    def _schedule_timer(self) -> None:
        self._cancel_timer()
        if self.playing and self.playlist:
            self.timer_id = self.root.after(self._interval_ms(), self.next_slide)

    def _cancel_timer(self) -> None:
        if self.timer_id is not None:
            try:
                self.root.after_cancel(self.timer_id)
            except tk.TclError:
                pass
            self.timer_id = None

    def _on_canvas_resize(self, _event) -> None:
        if self.resize_id is not None:
            self.root.after_cancel(self.resize_id)
        self.resize_id = self.root.after(120, self._redraw_after_resize)

    def _redraw_after_resize(self) -> None:
        self.resize_id = None
        if self.playlist and self.slide_index >= 0:
            self._request_image(self.playlist[self.slide_index].path)

    def toggle_fullscreen(self) -> None:
        self.fullscreen = not self.fullscreen
        self.root.attributes("-fullscreen", self.fullscreen)

    def _on_escape(self, _event) -> None:
        if self.fullscreen:
            self.fullscreen = False
            self.root.attributes("-fullscreen", False)

    def close(self) -> None:
        self._cancel_timer()
        self.executor.shutdown(wait=False, cancel_futures=True)
        self.root.destroy()


def enable_windows_high_dpi() -> None:
    if sys.platform != "win32":
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass


def main() -> None:
    enable_windows_high_dpi()
    root = tk.Tk()
    SlideshowApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
