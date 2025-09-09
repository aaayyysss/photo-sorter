# gui_reference_labeler.py
# Verion 6.5 dated 20250909
# Photo Sorter - Reference Labeling (single-file, working layout)
# Adds:
#   • Bottom black scrollable log console (dual: GUI + stdout)
#   • DB Health Check button (purges dead reference paths)
#   • Match Review Panel for _unmatched images (post-sorting)
#   • Reference handling enhancements:
#       - Select/unselect reference photos in reference grid
#       - Delete Selected reference photos (with confirmation) + rebuild embeddings
#       - Delete entire label (with confirmation) + rebuild embeddings
#       - Add selected main-grid photos to currently selected label + rebuild embeddings
#   • Sorting rules note under match mode radios
#   • Default mode = Best, then Multi, then Manual
#   • Settings menu → Preferences dialog (persisted in app_settings.json):
#       - Default sorting mode
#       - Main/Reference selection color & thickness

import os
import json
import uuid
import shutil
import threading
import tkinter as tk
import sys, subprocess
from tkinter import ttk, filedialog, messagebox, simpledialog, colorchooser
from concurrent.futures import ThreadPoolExecutor, as_completed
import queue
import itertools
import gc
from types import SimpleNamespace

from PIL import Image, ImageTk
from collections import OrderedDict

from reference_db import (
    init_db,
    insert_reference,
    get_all_references,
    delete_reference,
    set_threshold_for_label,
    get_threshold_for_label,
    get_all_labels,      # keep if you want; we won’t rely on it for the dropdown
    delete_label,
    insert_or_update_label,   # ⬅️ add this
)


# ---- Config (persisted) -----------------------------------------

SETTINGS_DEFAULT = {
    "main_grid_sel_color": "#3399ff",
    "main_grid_sel_border": 6,
    "ref_grid_sel_color":  "#3399ff",
    "ref_grid_sel_border": 6,
    "default_mode":        "best",   # best | multi | manual
    "reference_root":      os.path.join(os.getcwd(), "references"),   # ⬅️ NEW
}

#---------------UndoStack ----------------------------
class UndoStack:
    def __init__(self, limit: int = 50):
        self._stack = []
        self._limit = limit
    def push(self, action: dict):
        self._stack.append(action)
        if len(self._stack) > self._limit:
            self._stack.pop(0)
    def pop(self):
        return self._stack.pop() if self._stack else None
    def clear(self):
        self._stack.clear()

# --------------------------------------------------------

import os
import shutil
import time
from pathlib import Path

try:
    from send2trash import send2trash  # pip install Send2Trash
except Exception:
    send2trash = None


def _ensure_dir(p: Path) -> None:
    p.mkdir(parents=True, exist_ok=True)


def _unique_path(dest_dir: Path, name: str) -> Path:
    """
    Make a unique destination path by suffixing -1, -2, ... if needed.
    """
    candidate = dest_dir / name
    if not candidate.exists():
        return candidate
    stem = candidate.stem
    suffix = candidate.suffix
    i = 1
    while True:
        alt = dest_dir / f"{stem}-{i}{suffix}"
        if not alt.exists():
            return alt
        i += 1


def _module_trash_root() -> Path:
    """
    A per-app trash folder (used when Send2Trash is unavailable).
    Placed next to the script as `.trash`.
    """
    here = Path(__file__).resolve().parent
    t = here / ".trash"
    _ensure_dir(t)
    return t


def _trash_move_file(file_path: str) -> tuple[bool, str | None]:
    """
    Try to delete (prefer sending to OS recycle bin). Return (ok, detail).
    `detail` is either a message ('recycle') or the fallback dest path.
    """
    p = Path(file_path)
    if not p.exists():
        return False, "not-found"
    try:
        if send2trash is not None:
            send2trash(str(p))
            return True, "recycle"
        # Fallback: move into app-local .trash
        trash_root = _module_trash_root()
        dest = _unique_path(trash_root, p.name)
        shutil.move(str(p), str(dest))
        return True, str(dest)
    except Exception as e:
        return False, f"error: {e!s}"


def _trash_move_label_folder(label_dir: str) -> tuple[bool, str | None]:
    """
    Delete an entire label folder. Same behavior as files.
    """
    d = Path(label_dir)
    if not d.exists():
        return False, "not-found"
    try:
        if send2trash is not None:
            send2trash(str(d))
            return True, "recycle"
        trash_root = _module_trash_root()
        dest = _unique_path(trash_root, d.name)
        shutil.move(str(d), str(dest))
        return True, str(dest)
    except Exception as e:
        return False, f"error: {e!s}"


def _settings_path():
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), "app_settings.json")

def load_settings():
    try:
        with open(_settings_path(), "r", encoding="utf-8") as f:
            data = json.load(f)
        return {**SETTINGS_DEFAULT, **data}
    except Exception:
        return dict(SETTINGS_DEFAULT)

def save_settings(settings: dict):
    try:
        with open(_settings_path(), "w", encoding="utf-8") as f:
            json.dump(settings, f, indent=2)
        return True
    except Exception:
        return False

SETTINGS = load_settings()

# ---- DB / Backend ---------------------------------------------

try:
    from reference_db import purge_missing_references
except Exception:  # pragma: no cover
    def purge_missing_references() -> int:
        return 0

from photo_sorter import (
    build_reference_embeddings_from_db,
    sort_photos_with_embeddings_from_folder_using_db
)

# ---- Constants ----------------------------------------------

THUMBNAIL_SIZE = (100, 100)
DB_PATH = "reference_data.db"

# ---- Utilities -----------------------------------------------

def ensure_dir(path: str):
    os.makedirs(path, exist_ok=True)

#-----------------------------
# --- Global thumbnail cache (LRU) ---
_THUMB_CACHE = {}
_THUMB_CACHE_ORDER = []
_THUMB_CACHE_MAX = 400  # adjust to your RAM; ~400 * small images

def _thumbcache_get(key):
    if key in _THUMB_CACHE:
        # refresh order (move to end)
        if key in _THUMB_CACHE_ORDER:
            _THUMB_CACHE_ORDER.remove(key)
        _THUMB_CACHE_ORDER.append(key)
        return _THUMB_CACHE[key]
    return None

def _thumbcache_put(key, value):
    _THUMB_CACHE[key] = value
    _THUMB_CACHE_ORDER.append(key)
    while len(_THUMB_CACHE_ORDER) > _THUMB_CACHE_MAX:
        old = _THUMB_CACHE_ORDER.pop(0)
        try:
            del _THUMB_CACHE[old]
        except Exception:
            pass

#-----------------------------

def unique_copy_or_move(src: str, dst_folder: str, keep_original=False) -> str:
    """Copy (or move) file to dst_folder with a short unique prefix; returns destination path."""
    ensure_dir(dst_folder)
    base = os.path.basename(src)
    unique = f"{uuid.uuid4().hex[:8]}_{base}"
    dst = os.path.join(dst_folder, unique)
    if keep_original:
        shutil.copy2(src, dst)
    else:
        shutil.move(src, dst)
    return dst

def _labels_from_entries() -> list[str]:
    """Return sorted unique labels present in reference_entries table."""
    try:
        rows = get_all_references()  # [(id, label, path), ...]
        labels = sorted({lbl for (_id, lbl, _path) in rows})
        return labels
    except Exception:
        return []
        
def get_reference_root():
    # prefer user setting; else default to ./References under the current app folder
    root = SETTINGS.get("reference_root") or os.path.join(os.getcwd(), "References")
    root = os.path.normpath(root)

    # if this is clearly from another user profile or not writable, migrate
    needs_migrate = False
    try:
        os.makedirs(root, exist_ok=True)
    except PermissionError:
        needs_migrate = True

    # also migrate if it contains the other machine's username explicitly
    if ("C:\\Users\\ASUS" in root) or ("/Users/ASUS" in root):
        needs_migrate = True

    if needs_migrate:
        fallback = os.path.join(os.getcwd(), "References")
        try:
            os.makedirs(fallback, exist_ok=True)
            root = fallback
            SETTINGS["reference_root"] = root
            save_settings(SETTINGS)
        except Exception:
            # last resort: current working dir
            root = os.getcwd()

    return root

    

def get_label_folder_path(label: str) -> str:
    folder = os.path.join(get_reference_root(), label)
    os.makedirs(folder, exist_ok=True)
    return folder

def _safe_copy_to_label_folder(src_path: str, label: str, keep_original_name: bool = True) -> str:
    """
    Copy src_path into ReferenceRoot/<label>/ collision-safely; return destination path.
    """
    folder = get_label_folder_path(label)
    base = os.path.basename(src_path)
    if keep_original_name:
        name, ext = os.path.splitext(base)
        candidate = os.path.join(folder, base)
        if not os.path.exists(candidate):
            shutil.copy2(src_path, candidate)
            return candidate
        i = 2
        while True:
            candidate = os.path.join(folder, f"{name}_{i}{ext}")
            if not os.path.exists(candidate):
                shutil.copy2(src_path, candidate)
                return candidate
            i += 1
    else:
        dst = os.path.join(folder, f"{uuid.uuid4().hex[:8]}_{base}")
        shutil.copy2(src_path, dst)
        return dst

def _write_or_refresh_metadata(label: str, threshold: float | None = None):
    """
    Create/refresh metadata.json in ReferenceRoot/<label>/ with:
      { "label": <label>, "threshold": <threshold or stored>, "files": [ ... ] }
    """
    folder = get_label_folder_path(label)
    meta_path = os.path.join(folder, "metadata.json")

    # List current image files
    files = sorted([
        f for f in os.listdir(folder)
        if f.lower().endswith((".jpg", ".jpeg", ".png", ".bmp", ".webp"))
    ])

    # If threshold is not provided, try DB; else 0.3 default.
    try:
        thr = threshold if threshold is not None else get_threshold_for_label(label)
    except Exception:
        thr = 0.3

    data = {"label": label, "threshold": thr, "files": files}
    try:
        with open(meta_path, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
    except Exception:
        pass  # non-fatal


# ---- Visual Logger --------------------------------------------

class BottomLogFrame(tk.Frame):
    def __init__(self, parent):
        super().__init__(parent)
        self.text = tk.Text(
            self, height=8, bg="black", fg="white", insertbackground="white",
            wrap="word"
        )
        self.scroll = tk.Scrollbar(self, command=self.text.yview)
        self.text.configure(yscrollcommand=self.scroll.set)
        self.text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.scroll.pack(side=tk.RIGHT, fill=tk.Y)

    def log(self, msg):
        try:
            self.text.insert(tk.END, msg + "\n")
            self.text.see(tk.END)
        except Exception:
            self.text.insert(tk.END, "[log error]\n")
            self.text.see(tk.END)

def make_gui_logger(log_widget):
    def gui_log(msg):
        print(msg)
        if log_widget:
            log_widget.log(msg)
    return gui_log

# ---- Mouse wheel helpers ---------------------------------------

def _bind_vertical_mousewheel(canvas: tk.Canvas):
    def _on_mousewheel(event):
        delta = 0
        if hasattr(event, "delta") and event.delta:
            delta = 1 if event.delta > 0 else -1
        elif getattr(event, "num", None) == 4:
            delta = 1
        elif getattr(event, "num", None) == 5:
            delta = -1
        if delta:
            canvas.yview_scroll(-delta, "units")
        return "break"
    canvas.bind("<MouseWheel>", _on_mousewheel)
    canvas.bind("<Button-4>", _on_mousewheel)
    canvas.bind("<Button-5>", _on_mousewheel)

def _bind_horizontal_mousewheel(canvas: tk.Canvas):
    def _on_mousewheel(event):
        delta = 0
        if hasattr(event, "delta") and event.delta:
            delta = 1 if event.delta > 0 else -1
        elif getattr(event, "num", None) == 4:
            delta = 1
        elif getattr(event, "num", None) == 5:
            delta = -1
        if delta:
            canvas.xview_scroll(-delta, "units")
        return "break"
    canvas.bind("<MouseWheel>", _on_mousewheel)
    canvas.bind("<Button-4>", _on_mousewheel)
    canvas.bind("<Button-5>", _on_mousewheel)

# ---- DB init -----------------------------------------------

init_db()

# ---- Reference Browser (top strip) ---------------------------
class ReferenceBrowser(ttk.Frame):
    """
    Shows reference thumbnails for the currently selected label.
    - Click a thumbnail to select/unselect (highlight).
    - Delete Selected removes only selected reference entries (with Undo support via trash).
    - Delete Label removes all entries for the chosen label (with Undo support via trash).
    """
    def __init__(self, master, gui_log, rebuild_embeddings_async, undo_push=None, *args, **kwargs):
        super().__init__(master, *args, **kwargs)
        self.gui_log = gui_log
        self.rebuild_embeddings_async = rebuild_embeddings_async
        self.undo_push = undo_push  # callback provided by ImageRangerGUI.undo.push

        self.label_filter = tk.StringVar()
        self.selected_paths = set()
        self.thumb_widgets = {}

        # --- UI: scrollable horizontal strip of thumbs ---
        self.canvas = tk.Canvas(self, height=130)
        self.scroll_x = ttk.Scrollbar(self, orient='horizontal', command=self.canvas.xview)
        self.inner_frame = ttk.Frame(self.canvas)

        self.canvas.create_window((0, 0), window=self.inner_frame, anchor='nw')
        self.canvas.configure(xscrollcommand=self.scroll_x.set)

        self.canvas.pack(fill=tk.X, expand=True, side=tk.TOP)
        _bind_horizontal_mousewheel(self.canvas)
        self.scroll_x.pack(fill=tk.X, side=tk.BOTTOM)

        self.inner_frame.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind_all("<Shift-MouseWheel>", self._on_mousewheel)

        # --- controls ---
        controls = ttk.Frame(self)
        controls.pack(fill=tk.X, pady=5)

        self.label_menu = ttk.Combobox(controls, textvariable=self.label_filter,
                                       values=_labels_from_entries(), state="readonly")
        self.label_menu.pack(side=tk.LEFT)
        self.label_menu.bind("<<ComboboxSelected>>", lambda e: self.load_images())

        ttk.Button(controls, text="🔄 Reload", command=self.load_images).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Button(controls, text="🧭 Open Folder", command=self.open_label_folder).pack(side=tk.LEFT, padx=6)
        ttk.Button(controls, text="🎚️ Threshold…", command=self.edit_threshold).pack(side=tk.LEFT, padx=6)
        ttk.Button(controls, text="❌ Delete Selected", command=self.delete_selected_refs).pack(side=tk.LEFT, padx=6)
        ttk.Button(controls, text="🗑️ Delete Label", command=self.delete_label_all).pack(side=tk.LEFT, padx=6)
        ttk.Button(controls, text="✏️ Rename Label", command=self.rename_label).pack(side=tk.LEFT, padx=6)

    # ---------------- internals ----------------
    def _on_mousewheel(self, event):
        self.canvas.xview_scroll(-1 * int(event.delta / 120), "units")

    def _toggle_select(self, path):
        frame = self.thumb_widgets.get(path)
        if not frame:
            return
        if path in self.selected_paths:
            self.selected_paths.remove(path)
            frame.configure(style="TFrame")
        else:
            self.selected_paths.add(path)
            frame.configure(style="RefSelected.TFrame")

    def clear_selection(self):
        for p in list(self.selected_paths):
            f = self.thumb_widgets.get(p)
            if f:
                f.configure(style="TFrame")
        self.selected_paths.clear()

    # ---------------- data/UI refresh ----------------
    def refresh_label_list(self, auto_select=True):
        labels = _labels_from_entries()
        self.label_menu.configure(values=labels)
        if auto_select:
            current = self.label_filter.get()
            if not current and labels:
                self.label_filter.set(labels[0])
                self.load_images()

    def load_images(self):
        for w in self.inner_frame.winfo_children():
            w.destroy()
        self.thumb_widgets.clear()
        self.clear_selection()

        label = self.label_filter.get()
        if not label:
            self.gui_log("⚠️ No label selected in Reference Browser.")
            return

        entries = get_all_references()
        filtered = [e for e in entries if e[1] == label]

        shown = 0
        self._thumbs_internal_refs = []
        for idx, (_id, lbl, path) in enumerate(filtered):
            if not os.path.exists(path):
                continue
            try:
                with Image.open(path) as im:
                    im = im.convert("RGB")
                    im.thumbnail(THUMBNAIL_SIZE)
                    thumb = ImageTk.PhotoImage(im)
                self._thumbs_internal_refs.append(thumb)

                frame = ttk.Frame(self.inner_frame, borderwidth=2, relief="solid", style="TFrame")
                frame.grid(row=0, column=idx, padx=2, pady=2)

                label_widget = ttk.Label(frame, image=thumb)
                label_widget.image = thumb
                label_widget.pack()
                label_widget.bind("<Button-1>", lambda e, p=path: self._toggle_select(p))

                self.thumb_widgets[path] = frame
                shown += 1
            except Exception as e:
                self.gui_log(f"[Thumbnail error] {path}: {e}")

        if shown == 0:
            self.gui_log(f"⚠️ No existing references found for label '{label}'")

    # ---------------- destructive actions with Undo ----------------
    def delete_selected_refs(self):
        label = self.label_filter.get()
        if not label:
            messagebox.showwarning("No Label", "Select a label first.")
            return
        if not self.selected_paths:
            messagebox.showwarning("No Selection", "Select reference photos to delete.")
            return

        confirm = messagebox.askyesno(
            "Delete Selected",
            f"Delete {len(self.selected_paths)} reference photo(s) from label '{label}'?"
        )
        if not confirm:
            return

        entries = get_all_references()
        targets = set(self.selected_paths)

        deleted = 0
        undo_items = []  # each: {"trashed": path}

        for (_id, lbl, path) in entries:
            if lbl == label and path in targets:
                try:
                    # 1) move file to trash for safe undo
                    restore_hint = None
                    if os.path.isfile(path):
                        ok, detail = _trash_move_file(path)   # ← pass only the file path
                        if ok and detail not in (None, "recycle"):
                            restore_hint = detail  # path inside .trash fallback; can be used for undo

                    # 2) remove DB entry
                    delete_reference(path)
                    deleted += 1

                    # record undo info if we have a concrete backup path
                    if restore_hint:
                        undo_items.append({"backup_path": restore_hint, "original_path": path})
                        
                except Exception as e:
                    self.gui_log(f"⚠️ Could not delete '{path}': {e}")

        # metadata refresh (optional)
        try:
            _write_or_refresh_metadata(label)
        except Exception:
            pass

        # push undo
        if self.undo_push and undo_items:
            self.undo_push({
                "type": "delete_refs",
                "data": {"label": label, "items": undo_items}
            })

        self.gui_log(f"🗑️ Deleted {deleted} reference(s) from '{label}'. Rebuilding embeddings…")
        self.load_images()
        self.schedule_rebuild_embeddings(only_label=label)

    def delete_label_all(self):
        label = self.label_filter.get()
        if not label:
            messagebox.showwarning("No Label", "Select a label to delete.")
            return

        confirm = messagebox.askyesno(
            "Delete Label",
            f"Delete ALL references for label '{label}'?"
        )
        if not confirm:
            return

        # move entire label folder to trash so we can undo
        trashed_folder = None
        try:
            label_dir = get_label_folder_path(label)     # ← resolve the actual folder
            ok, detail = _trash_move_label_folder(label_dir)
            if ok:
                trashed_folder = detail  # "recycle" or backup path in .trash
            else:
                self.gui_log(f"⚠️ Could not move label folder to trash: {detail}")
        except Exception as e:
            self.gui_log(f"⚠️ Could not move label folder to trash: {e}")


        # delete DB rows for that label
        entries = get_all_references()
        deleted = 0
        for (_id, lbl, path) in entries:
            if lbl == label:
                try:
                    delete_reference(path)
                    deleted += 1
                except Exception as e:
                    self.gui_log(f"⚠️ Could not drop DB row {path}: {e}")

        # stash threshold then remove label metadata
        thr = None
        try:
            thr = get_threshold_for_label(label)
        except Exception:
            pass
        try:
            delete_label(label)
        except Exception:
            pass

        # push undo payload
        if self.undo_push:
            self.undo_push({
                "type": "delete_label",
                "data": {"label": label, "trashed_folder": trashed_folder, "threshold": thr if thr is not None else 0.3}
            })

        self.gui_log(f"🗑️ Deleted label '{label}' ({deleted} item(s)). Rebuilding embeddings…")

        self.label_menu.configure(values=get_all_labels())
        self.refresh_label_list(auto_select=False)
        self.label_filter.set("")
        self.load_images()
        self.schedule_rebuild_embeddings(only_label=label)

    # ---------------- rename ----------------
    def rename_label(self):
        current = self.label_filter.get()
        if not current:
            return
        new_label = simpledialog.askstring("Rename Label", f"Rename label '{current}' to:")
        if not new_label or new_label == current:
            return

        entries = get_all_references()
        moved = 0

        old_folder = get_label_folder_path(current)
        new_folder = get_label_folder_path(new_label)
        os.makedirs(new_folder, exist_ok=True)

        for (_id, lbl, path) in entries:
            if lbl == current:
                new_path = path
                try:
                    # move file if it lives inside the old folder
                    if os.path.commonpath([os.path.abspath(path), os.path.abspath(old_folder)]) == os.path.abspath(old_folder):
                        base = os.path.basename(path)
                        name, ext = os.path.splitext(base)
                        candidate = os.path.join(new_folder, base)
                        if os.path.exists(candidate):
                            i = 2
                            while True:
                                candidate = os.path.join(new_folder, f"{name}_{i}{ext}")
                                if not os.path.exists(candidate):
                                    break
                                i += 1
                        shutil.move(path, candidate)
                        new_path = candidate
                except Exception:
                    pass
                insert_reference(new_path, new_label)
                moved += 1

        thr = get_threshold_for_label(current)
        set_threshold_for_label(new_label, thr)
        insert_or_update_label(new_label, new_folder, thr)

        try:
            if os.path.isdir(old_folder) and not os.listdir(old_folder):
                shutil.rmtree(old_folder)
        except Exception:
            pass

        self.label_filter.set(new_label)
        self.refresh_label_list(auto_select=False)
        self.load_images()
        self.gui_log(f"✏️ Renamed/moved {moved} items to '{new_label}'. Rebuilding embeddings…")
        self.rebuild_embeddings_async(only_label=new_label)
        _write_or_refresh_metadata(new_label, thr)

    # ---------------- helpers ----------------
    def open_label_folder(self):
        label = self.label_filter.get()
        if not label:
            self.gui_log("⚠️ No label selected.")
            return
        folder = get_label_folder_path(label)
        try:
            if os.name == "nt":
                os.startfile(folder)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", folder])
            else:
                subprocess.Popen(["xdg-open", folder])
        except Exception as e:
            self.gui_log(f"⚠️ Could not open folder: {e}")

    def edit_threshold(self):
        label = self.label_filter.get()
        if not label:
            messagebox.showwarning("No Label", "Select a label first.")
            return
        try:
            current = get_threshold_for_label(label)
        except Exception:
            current = 0.3
        val = simpledialog.askstring("Threshold", f"Threshold for '{label}' (0.0–1.0):", initialvalue=f"{current:.3f}")
        if val is None:
            return
        try:
            thr = float(val)
            if not (0.0 <= thr <= 1.0):
                raise ValueError
            set_threshold_for_label(label, thr)
            _write_or_refresh_metadata(label, thr)
            self.gui_log(f"🎚️ Threshold for '{label}' set to {thr:.3f}.")
            self.schedule_rebuild_embeddings(only_label=label)
        except Exception:
            messagebox.showerror("Invalid", "Threshold must be a number between 0.0 and 1.0.")


# ---- Match Review Panel (post-sorting) ----------------------------

class MatchReviewPanel(tk.Toplevel):
    def __init__(self, master, unmatched_dir, output_dir, gui_log, *args, **kwargs):
        super().__init__(master, *args, **kwargs)
        self.title("Review Unmatched Photos")
        self.geometry("1100x700")
        self.unmatched_dir = unmatched_dir
        self.output_dir = output_dir
        self.gui_log = gui_log

        self._thumbs = []
        self._checks = []   # (var, path, label_var)

        top = ttk.Frame(self)
        top.pack(fill=tk.X, padx=10, pady=6)
        ttk.Label(top, text=f"Unmatched Folder: {self.unmatched_dir}").pack(side=tk.LEFT)
        ttk.Button(top, text="Open Folder", command=self.open_folder).pack(side=tk.LEFT, padx=10)

        ttk.Separator(self, orient=tk.HORIZONTAL).pack(fill=tk.X, padx=10)

        toolbar = ttk.Frame(self)
        toolbar.pack(fill=tk.X, padx=10, pady=6)

        labels_now = _labels_from_entries()
        
        default_label = (labels_now[0] if labels_now else "Unknown")
        self.assign_label_var = tk.StringVar(value=default_label)
        self.keep_original = tk.BooleanVar(value=False)
        ttk.Label(toolbar, text="Assign to:").pack(side=tk.LEFT)
        self.assign_combo = ttk.Combobox(
            toolbar,
            textvariable=self.assign_label_var,
            values=labels_now,
            state="readonly",
            width=20
        )
        
        self.assign_combo.pack(side=tk.LEFT, padx=5)
        ttk.Button(toolbar, text="✅ Assign Selected to Label", command=self.assign_selected).pack(side=tk.LEFT, padx=8)
        ttk.Button(toolbar, text="➕ Add Selected as Reference", command=self.add_selected_as_reference).pack(side=tk.LEFT, padx=8)
        ttk.Checkbutton(toolbar, text="Copy (don’t move)", variable=self.keep_original).pack(side=tk.LEFT, padx=8)

        ttk.Separator(self, orient=tk.HORIZONTAL).pack(fill=tk.X, padx=10)

        mid = ttk.Frame(self)
        mid.pack(fill=tk.BOTH, expand=True, padx=10, pady=6)
        self.canvas = tk.Canvas(mid, bg="#ffffff")
        self.vsb = ttk.Scrollbar(mid, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.grid_frame = ttk.Frame(self.canvas)
        self.canvas.create_window((0, 0), window=self.grid_frame, anchor='nw')
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.vsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.grid_frame.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))

        self.load_unmatched()

    def open_folder(self):
        try:
            os.startfile(self.unmatched_dir)  # Windows
        except Exception:
            self.gui_log(f"📁 Open this folder manually: {self.unmatched_dir}")

    def load_unmatched(self):
        for w in self.grid_frame.winfo_children():
            w.destroy()
        self._thumbs.clear()
        self._checks.clear()

        paths = []
        for sub, _, files in os.walk(self.unmatched_dir):
            for f in files:
                if f.lower().endswith((".jpg", ".jpeg", ".png", ".bmp", ".webp")):
                    paths.append(os.path.join(sub, f))

        if not paths:
            self.gui_log("ℹ️ No images in unmatched folder.")
            ttk.Label(self.grid_frame, text="No unmatched images found.").grid(row=0, column=0, padx=6, pady=6)
            return

        self.gui_log(f"🖼️ Review: found {len(paths)} unmatched images.")
        cols = 6
        TH = (100, 100)
        for i, p in enumerate(paths):
            try:
                with Image.open(p) as im:
                    im = im.convert("RGB")
                    im.thumbnail(TH)
                    th = ImageTk.PhotoImage(im)
                self._thumbs.append(th)

                cell = ttk.Frame(self.grid_frame, borderwidth=1, relief="solid")
                cell.grid(row=i // cols, column=i % cols, padx=6, pady=6)

                lbl = ttk.Label(cell, image=th)
                lbl.image = th
                lbl.pack()

                base = os.path.basename(p)
                ttk.Label(cell, text=base, width=18, anchor="center").pack()

                row = ttk.Frame(cell)
                row.pack(pady=3)

                var = tk.BooleanVar(value=False)
                ttk.Checkbutton(row, variable=var).pack(side=tk.LEFT)

                lblv = tk.StringVar(value=self.assign_label_var.get())
                              
                combo = ttk.Combobox(row, textvariable=lblv, values=_labels_from_entries(), state="readonly", width=12)
                combo.pack(side=tk.LEFT, padx=4)

                self._checks.append((var, p, lblv))
            except Exception as e:
                self.gui_log(f"⚠️ Skip {p}: {e}")

    def _selected_items(self):
        return [(p, lblv.get()) for var, p, lblv in self._checks if var.get()]

    def assign_selected(self):
        items = self._selected_items()
        if not items:
            messagebox.showinfo("Assign", "No images selected.")
            return

        moved = 0
        for p, label in items:
            try:
                dst = os.path.join(self.output_dir, label)
                unique_copy_or_move(p, dst, keep_original=self.keep_original.get())
                moved += 1
            except Exception as e:
                self.gui_log(f"❌ Assign failed for {p}: {e}")
        self.gui_log(f"✅ Assigned {moved} image(s) to labels in output folder.")
        self.load_unmatched()

    def add_selected_as_reference(self):
        items = self._selected_items()
        if not items:
            messagebox.showinfo("Add as Reference", "No images selected.")
            return

        added = 0
        for p, label in items:
            try:
                insert_reference(p, label)
                added += 1
            except Exception as e:
                self.gui_log(f"❌ Add reference failed for {p}: {e}")
        self.gui_log(f"✅ Added {added} image(s) as references.")
        messagebox.showinfo("References", f"Added {added} reference(s).")

# ---- Settings Dialog ---------------------------------------------

class SettingsDialog(tk.Toplevel):
    def __init__(self, master, current_settings: dict, on_save_callback, *args, **kwargs):
        super().__init__(master, *args, **kwargs)
        self.title("Preferences")
        self.resizable(False, False)
        self.transient(master)
        self.grab_set()

        self.on_save_callback = on_save_callback
        self.values = dict(current_settings)

        frm = ttk.Frame(self, padding=12)
        frm.pack(fill=tk.BOTH, expand=True)

        mframe = ttk.LabelFrame(frm, text="Default Sorting Mode")
        mframe.grid(row=0, column=0, sticky="we", padx=5, pady=5)
        self.mode_var = tk.StringVar(value=self.values.get("default_mode", "best"))
        modes = [("Best", "best"), ("Multi", "multi"), ("Manual", "manual")]
        for i, (label, val) in enumerate(modes):
            ttk.Radiobutton(mframe, text=label, value=val, variable=self.mode_var).grid(row=0, column=i, padx=6, pady=4)

        gframe = ttk.LabelFrame(frm, text="Main Grid Selection Style")
        gframe.grid(row=1, column=0, sticky="we", padx=5, pady=5)
        ttk.Label(gframe, text="Color:").grid(row=0, column=0, sticky="w")
        self.main_color = tk.StringVar(value=self.values["main_grid_sel_color"])
        self.main_border = tk.IntVar(value=int(self.values["main_grid_sel_border"]))
        
# -------------------- Reference Root --------------------------------
        rroot = ttk.LabelFrame(frm, text="Reference Storage")
        rroot.grid(row=3, column=0, sticky="we", padx=5, pady=5)

        self.ref_root_var = tk.StringVar(
            value=self.values.get("reference_root", SETTINGS_DEFAULT["reference_root"])
        )

        def pick_ref_root():
            folder = filedialog.askdirectory(title="Choose Reference Root")
            if folder:
                self.ref_root_var.set(folder)

        ttk.Label(rroot, text="Reference Root:").grid(row=0, column=0, sticky="w")
        ttk.Entry(rroot, textvariable=self.ref_root_var, width=48).grid(
            row=0, column=1, sticky="we", padx=6
        )
        ttk.Button(rroot, text="Browse", command=pick_ref_root).grid(
            row=0, column=2, sticky="w"
        )

        # allow the entry to stretch
        rroot.columnconfigure(1, weight=1)
# ------------------------------------------------------
        self._main_color_btn = ttk.Button(gframe, text=self.main_color.get(), command=self.pick_main_color)
        self._main_color_btn.grid(row=0, column=1, sticky="w", padx=6)
        ttk.Label(gframe, text="Border px:").grid(row=0, column=2, sticky="e")
        ttk.Spinbox(gframe, from_=1, to=12, textvariable=self.main_border, width=5).grid(row=0, column=3, sticky="w", padx=6)

        rframe = ttk.LabelFrame(frm, text="Reference Grid Selection Style")
        rframe.grid(row=2, column=0, sticky="we", padx=5, pady=5)
        ttk.Label(rframe, text="Color:").grid(row=0, column=0, sticky="w")
        self.ref_color = tk.StringVar(value=self.values["ref_grid_sel_color"])
        self.ref_border = tk.IntVar(value=int(self.values["ref_grid_sel_border"]))
        self._ref_color_btn = ttk.Button(rframe, text=self.ref_color.get(), command=self.pick_ref_color)
        self._ref_color_btn.grid(row=0, column=1, sticky="w", padx=6)
        ttk.Label(rframe, text="Border px:").grid(row=0, column=2, sticky="e")
        ttk.Spinbox(rframe, from_=1, to=12, textvariable=self.ref_border, width=5).grid(row=0, column=3, sticky="w", padx=6)

        bframe = ttk.Frame(frm)
        bframe.grid(row=4, column=0, sticky="e", pady=(8, 0))   # ← move buttons to row=4
        ttk.Button(bframe, text="Restore Defaults", command=self.restore_defaults).grid(row=0, column=0, padx=6)
        ttk.Button(bframe, text="Cancel", command=self.destroy).grid(row=0, column=1, padx=6)
        ttk.Button(bframe, text="Save", command=self.save).grid(row=0, column=2, padx=6)

        self.columnconfigure(0, weight=1)
        frm.columnconfigure(0, weight=1)

    def pick_main_color(self):
        _, hexcolor = colorchooser.askcolor(color=self.main_color.get(), title="Select Main Grid Selection Color")
        if hexcolor:
            self.main_color.set(hexcolor)
            self._main_color_btn.config(text=hexcolor)

    def pick_ref_color(self):
        _, hexcolor = colorchooser.askcolor(color=self.ref_color.get(), title="Select Reference Grid Selection Color")
        if hexcolor:
            self.ref_color.set(hexcolor)
            self._ref_color_btn.config(text=hexcolor)

    def restore_defaults(self):
        self.mode_var.set(SETTINGS_DEFAULT["default_mode"])
        self.main_color.set(SETTINGS_DEFAULT["main_grid_sel_color"])
        self.main_border.set(SETTINGS_DEFAULT["main_grid_sel_border"])
        self.ref_color.set(SETTINGS_DEFAULT["ref_grid_sel_color"])
        self.ref_border.set(SETTINGS_DEFAULT["ref_grid_sel_border"])
        self._main_color_btn.config(text=self.main_color.get())
        self._ref_color_btn.config(text=self.ref_color.get())

    def save(self):
        try:
            mb = int(self.main_border.get())
            rb = int(self.ref_border.get())
            if mb < 1 or rb < 1:
                raise ValueError
        except Exception:
            messagebox.showerror("Invalid Input", "Border thickness must be an integer ≥ 1.")
            return
     
        new_values = {
            "default_mode":        self.mode_var.get(),
            "main_grid_sel_color": self.main_color.get(),
            "main_grid_sel_border": int(self.main_border.get()),
            "ref_grid_sel_color":  self.ref_color.get(),
            "ref_grid_sel_border": int(self.ref_border.get()),
            "reference_root":      self.ref_root_var.get(),   # ⬅️ NEW
        }
        self.on_save_callback(new_values)
        self.destroy()
        
# ----------------Modal Progress Dialog (for long tasks)----------
class _ModalProgress:
    def __init__(self, parent, title="Working…", message="Please wait…"):
        self.top = tk.Toplevel(parent)
        self.top.title(title)
        self.top.resizable(False, False)
        self.top.transient(parent)
        self.top.grab_set()

        frm = ttk.Frame(self.top, padding=12)
        frm.pack(fill=tk.BOTH, expand=True)

        ttk.Label(frm, text=message, wraplength=360).pack(pady=(0,6))
        self.pb = ttk.Progressbar(frm, mode="indeterminate", length=300)
        self.pb.pack(pady=(0,4))
        self.pb.start(10)

        # center on the screen (not just over parent)
        self.top.update_idletasks()
        sw = self.top.winfo_screenwidth()
        sh = self.top.winfo_screenheight()
        ww = self.top.winfo_reqwidth()
        wh = self.top.winfo_reqheight()
        xpos = (sw // 2) - (ww // 2)
        ypos = (sh // 2) - (wh // 2)
        self.top.geometry(f"+{xpos}+{ypos}")

    def close(self):
        try:
            self.pb.stop()
        except Exception:
            pass
        try:
            self.top.grab_release()
        except Exception:
            pass
        self.top.destroy()
        
# ------------------ CreateLabelDialog ------------------

class CreateLabelDialog(tk.Toplevel):
    """One-shot dialog to collect label name + threshold together."""
    def __init__(self, master, initial_name="", initial_threshold=0.3):
        super().__init__(master)
        self.title("Create Label")
        self.resizable(False, False)
        self.transient(master)
        self.grab_set()
        # Center over parent
        self.update_idletasks()
        if master:
            x = master.winfo_rootx()
            y = master.winfo_rooty()
            w = master.winfo_width()
            h = master.winfo_height()
            ww = self.winfo_reqwidth()
            wh = self.winfo_reqheight()
            xpos = x + (w // 2) - (ww // 2)
            ypos = y + (h // 2) - (wh // 2)
            self.geometry(f"+{xpos}+{ypos}")

        self.result = None  # (label:str, threshold:float)

        frm = ttk.Frame(self, padding=12)
        frm.pack(fill=tk.BOTH, expand=True)

        # Label name
        ttk.Label(frm, text="Label name:").grid(row=0, column=0, sticky="e", padx=(0,8), pady=4)
        self.name_var = tk.StringVar(value=initial_name)
        self.name_entry = ttk.Entry(frm, textvariable=self.name_var, width=28)
        self.name_entry.grid(row=0, column=1, sticky="we", pady=4)

        # Threshold
        ttk.Label(frm, text="Threshold (0.0–1.0):").grid(row=1, column=0, sticky="e", padx=(0,8), pady=4)
        self.thr_var = tk.StringVar(value=f"{float(initial_threshold):.3f}")
        self.thr_entry = ttk.Entry(frm, textvariable=self.thr_var, width=10)
        self.thr_entry.grid(row=1, column=1, sticky="w", pady=4)

        # Buttons
        btns = ttk.Frame(frm)
        btns.grid(row=2, column=0, columnspan=2, sticky="e", pady=(10,0))
        ttk.Button(btns, text="Cancel", command=self._cancel).grid(row=0, column=0, padx=6)
        ttk.Button(btns, text="Create", command=self._ok).grid(row=0, column=1, padx=6)

        frm.columnconfigure(1, weight=1)
        self.name_entry.focus_set()

        # Enter/Esc shortcuts
        self.bind("<Return>", lambda e: self._ok())
        self.bind("<Escape>", lambda e: self._cancel())

    def _ok(self):
        name = (self.name_var.get() or "").strip()
        if not name:
            messagebox.showerror("Invalid", "Please enter a label name.")
            return
        try:
            thr = float(self.thr_var.get())
            if not (0.0 <= thr <= 1.0):
                raise ValueError
        except Exception:
            messagebox.showerror("Invalid", "Threshold must be a number between 0.0 and 1.0.")
            return
        self.result = (name, thr)
        self.destroy()

    def _cancel(self):
        self.result = None
        self.destroy()

# ---- Main IGUI -----------------------------------------------------
class ImageRangerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Photo Sorter - Reference Labeling")

    # ===== Excire-style UI state =====
        self.zoom_min, self.zoom_max = 80, 360        
        self.zoom_value = tk.IntVar(value=160)     # shared slider position        
        self.main_thumb_size = tk.IntVar(value=160)        
        self.ref_thumb_size  = tk.IntVar(value=96)        
        self.active_zoom_target = tk.StringVar(value="main")  # 'main' or 'ref'
        
        self.grid_gutter = 10
        self.selected_indices = set()              # selection in main grid
        self.current_images = []                   # files shown in main grid
        self._thumb_cache = {}                     # ((path,size) -> PhotoImage)
        # ---- thumbnail cache (LRU with soft limits) ----
        self._thumb_cache = OrderedDict()   # (path, size_px) -> (PhotoImage, est_bytes)
        self._thumb_cache_est_bytes = 0
        self._thumb_cache_items_limit = 2000            # ~ how many thumbs to keep
        self._thumb_cache_bytes_limit = 256 * 1024 * 1024  # ~256 MB cap

        self.root.bind("<Control-n>", lambda e: self.create_label_from_selection())

        # remember last zooms to decide when to purge a lot
        self._last_main_zoom = int(self.main_thumb_size.get())
        self._last_ref_zoom  = int(self.ref_thumb_size.get())
        
        # ---- busy/spinner state ----
        self._is_busy = False
        self._buttons_to_disable = []


        # workers/cancel (if you have background tasks)
        self._cancel_event = threading.Event()
        self._workers = []

    # graceful close
        self._is_closing = False
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        
        # styles + sorting state
        self.style = ttk.Style()
        self.sorting = False
        self.sort_thread = None
        self.sort_stop_event = None

        # button styles (ttk not used for sort button anymore, but keep for future)
        self.style.configure("SortGreen.TButton", foreground="white", background="#22aa22")
        self.style.map("SortGreen.TButton", background=[("active", "#1c8f1c")])
        self.style.configure("SortRed.TButton", foreground="white", background="#cc3333")
        self.style.map("SortRed.TButton", background=[("active", "#a62828")])

        # menu + logger
        self._build_menu()
        self.log = BottomLogFrame(self.root)
        self.log.pack(side=tk.BOTTOM, fill=tk.X)
        self.gui_log = make_gui_logger(self.log)

        # data state
        self.selected_folder = tk.StringVar()
        self.image_paths = []
        self.thumbnails = []
        self.selected_images = set()
        self.multi_face_mode = tk.StringVar(value=SETTINGS["default_mode"])
        self.last_unmatched_dir = None
        self.last_output_dir = None

        self._rebuild_after_id = None   # Tk 'after' handle for debounce
        self._rebuild_last_label = None

        # async/undo helpers
        self._rebuild_pending = None
        self.undo = UndoStack()

        # visuals
        self.apply_styles()
        self.build_layout()
        # self.reference_browser.refresh_label_list(auto_select=True)
        # refresh label list for the new reference strip UI
        labels = self.get_all_label_names()
        try:
            self.ref_label_menu.configure(values=labels)
        except Exception:
            pass
        if labels:
            self.active_label.set(labels[0])
            self.render_reference_strip(labels[0])

        
        self.set_zoom_target("main")   # initial active grid highlights

        # Legacy compatibility shim (now UI elements exist)
        self.reference_browser = SimpleNamespace(
            refresh_label_list=lambda auto_select=False: self._rb_refresh_label_list(auto_select),
            delete_label_all=lambda label: self.delete_label_all(label),
        )

        # Now it's safe to refresh the label list (Combobox is built)
        self._rb_refresh_label_list(auto_select=True)

        self.gui_log("✅ GUI initialized.")
        self.undo_stack = []


    def _build_menu(self):
        menubar = tk.Menu(self.root)
        settings_menu = tk.Menu(menubar, tearoff=0)
        settings_menu.add_command(label="Preferences…", command=self.open_settings_dialog)
        menubar.add_cascade(label="Settings", menu=settings_menu)

        tools = tk.Menu(menubar, tearoff=0)
        tools.add_command(label="Rebuild Embeddings", command=self.rebuild_embeddings_async)
        tools.add_command(label="Open Reference Root", command=self.open_reference_root)
        tools.add_separator()
        tools.add_command(label="Export Match Audit (CSV)…", command=self.export_match_audit_csv)
        menubar.add_cascade(label="Tools", menu=tools)

        self.root.config(menu=menubar)

    # -----------------------------------------
    def _rb_refresh_label_list(self, auto_select: bool = False):
        labels = []
        try:
            labels = self.get_all_label_names()
        except Exception:
            pass
        try:
            self.ref_label_menu.configure(values=labels)
        except Exception:
            pass
        if auto_select and labels:
            self.active_label.set(labels[0])
            self.render_reference_strip(labels[0])
    
    def delete_label_all(self, label: str):
        if not label:
            return
        try:
            from reference_db import get_all_references, delete_reference, set_threshold_for_label
            refs = [r["path"] for r in get_all_references() if r["label"] == label]
            for p in refs:
                try:
                    delete_reference(p)
                except Exception:
                    pass
            try:
                set_threshold_for_label(label, None)
            except Exception:
                pass
        except Exception:
            pass
        # refresh UI
        try:
            labels = self.get_all_label_names()
            self.ref_label_menu.configure(values=labels)
        except Exception:
            pass
        if self.active_label.get() == label:
            self.active_label.set("")
            self.render_reference_strip("")

    def on_close(self):
        if getattr(self, "_is_closing", False): return
        self._is_closing = True
        self.set_status_left("Shutting down…")
        try: self._cancel_event.set()
        except Exception: pass
        try:
            for t in getattr(self, "_workers", []):
                if t and t.is_alive(): t.join(timeout=3.0)
        except Exception: pass
        # DB close (optional)
        try:
            from reference_db import close_db
            try: close_db()
            except Exception: pass
        except Exception: pass
        # Release ML resources (optional)
        try:
            from photo_sorter import release_resources
            try: release_resources()
            except Exception: pass
        except Exception: pass
        # Clear caches
        try: self._thumb_cache.clear()
        except Exception: pass
        try:
            import gc; gc.collect()
        except Exception: pass
        try: self.root.destroy()
        except Exception: pass
        try:
            import sys; sys.exit(0)
        except Exception: pass

# -----------------------------------------
    def apply_styles(self):
        if not hasattr(self, "style"):
            self.style = ttk.Style()
        # main-grid style
        self.style.configure(
            "Selected.TFrame",
            background=SETTINGS["main_grid_sel_color"],
            borderwidth=int(SETTINGS["main_grid_sel_border"]),
            relief="solid",
        )
        # ref-grid style
        self.style.configure(
            "RefSelected.TFrame",
            background=SETTINGS["ref_grid_sel_color"],
            borderwidth=int(SETTINGS["ref_grid_sel_border"]),
            relief="solid",
        )

    # ---------------- background thumbnail loader ----------------
    def _cancel_thumb_job(self):
        self._thumb_stop = True

    def _start_thumb_job(self, paths):
        self._cancel_thumb_job()
        self._thumb_stop = False
        self._thumb_executor = getattr(self, "_thumb_executor", None) or ThreadPoolExecutor(max_workers=4)
        self._thumb_queue = queue.Queue(maxsize=256)

        def producer():
            for p in paths:
                if self._thumb_stop:
                    break
                cached = _thumbcache_get(p)
                if cached is not None:
                    self._thumb_queue.put(("ok", p, cached))
                    continue
                try:
                    with Image.open(p) as im:
                        im = im.convert("RGB")
                        im.thumbnail(THUMBNAIL_SIZE)
                        bio = im.tobytes()
                        size = im.size
                    self._thumb_queue.put(("raw", p, (bio, size)))
                except Exception as e:
                    self._thumb_queue.put(("err", p, str(e)))
            self._thumb_queue.put(("done", None, None))

        threading.Thread(target=producer, daemon=True).start()
        self._consume_thumbs_batch()

    def _consume_thumbs_batch(self):
        BATCH = 24
        consumed = 0
        while consumed < BATCH:
            try:
                kind, path, payload = self._thumb_queue.get_nowait()
            except queue.Empty:
                break
            if kind == "done":
                gc.collect()
                return
            if self._thumb_stop:
                continue
            if kind == "ok":
                thumb = payload
                self._add_thumbnail_widget(path, thumb)
            elif kind == "raw":
                raw, size = payload
                try:
                    im = Image.frombytes("RGB", size, raw)
                    tkimg = ImageTk.PhotoImage(im)
                    _thumbcache_put(path, tkimg)
                    self._add_thumbnail_widget(path, tkimg)
                except Exception as e:
                    self.gui_log(f"[Thumb build error] {path}: {e}")
            else:
                self.gui_log(f"[Thumbnail error] {path}: {payload}")
            consumed += 1
        if not self._thumb_stop:
            self.root.after(10, self._consume_thumbs_batch)

    def _add_thumbnail_widget(self, img_path, tkimg):
        idx = len(self.thumbnails)
        self.thumbnails.append(tkimg)
        frame = ttk.Frame(self.scrollable_frame, borderwidth=2, relief="solid", style="TFrame")
        frame.grid(row=idx // 6, column=idx % 6, padx=5, pady=5)
        label = ttk.Label(frame, image=tkimg)
        label.image = tkimg
        label.pack()
        def toggle_selection(p=img_path, f=frame):
            if p in self.selected_images:
                self.selected_images.remove(p)
                f.configure(style="TFrame")
            else:
                self.selected_images.add(p)
                f.configure(style="Selected.TFrame")
        label.bind("<Button-1>", lambda e, path=img_path, fr=frame: toggle_selection(path, fr))

    # ---------------- settings ----------------
    def _on_settings_saved(self, values: dict):
        SETTINGS.update(values)
        save_settings(SETTINGS)
        self.apply_styles()
        self.multi_face_mode.set(SETTINGS["default_mode"])
        self.reference_browser.refresh_label_list(auto_select=False)
        self.gui_log("⚙️ Preferences saved and applied.")

    def open_settings_dialog(self):
        SettingsDialog(self.root, SETTINGS, self._on_settings_saved)

    # ---------------- embeddings rebuild (debounced + threaded) ----------------

    #def rebuild_embeddings_async(self, only_label=None):
    #    """Threaded rebuild + spinner + button disable."""
    #    if getattr(self, "_cancel_event", None) and self._cancel_event.is_set():
    #        return
    #
    #    self.begin_busy("Rebuilding embeddings…")
    
    #    def _job():
    #        err = None
    #        try:
    #            from photo_sorter import build_reference_embeddings_from_db
    #            build_reference_embeddings_from_db(only_label=only_label)
    #        except Exception as e:
    #            err = e
    #        # back to UI thread
    #        def _done():
    #            if err:
    #                self.end_busy(f"Rebuild failed: {err}")
    #            else:
    #                self.end_busy("✅ Embeddings rebuilt.")
    #        try:
    #            self.root.after(0, _done)
    #        except Exception:
    #            pass
    #
    #    t = threading.Thread(target=_job, daemon=True)
    #    t.start()
    #    try:
    #        self._workers.append(t)
    #    except Exception:
    #        pass

# ------------------------Debounce multiple rebuild requests into one."--------------------------
    # ---- Debounce state (keep if you already have it) ----
    # self._rebuild_after_id = None
    # self._rebuild_last_label = None
    
    def schedule_rebuild_embeddings(self, only_label=None, delay_ms=400):
        """Debounce multiple rebuild requests into one; accepts label but will ignore it if backend doesn't support it."""
        self._rebuild_last_label = (only_label or "").strip() or None
        if self._rebuild_after_id is not None:
            try: self.root.after_cancel(self._rebuild_after_id)
            except Exception: pass
        self._rebuild_after_id = self.root.after(delay_ms, self._run_rebuild_coalesced)
    
    def _run_rebuild_coalesced(self):
        self._rebuild_after_id = None
        label = self._rebuild_last_label
        self._rebuild_last_label = None
        self.rebuild_embeddings_async(only_label=label)
    
    def rebuild_embeddings_async(self, only_label=None):
        """Threaded rebuild + spinner; auto-detects whether backend supports 'only_label'."""
        if getattr(self, "_cancel_event", None) and self._cancel_event.is_set():
            return
    
        self.begin_busy("Rebuilding embeddings…")
    
        def _job():
            import inspect
            err = None
            try:
                from photo_sorter import build_reference_embeddings_from_db
                # detect if function accepts 'only_label'
                sig = None
                try:
                    sig = inspect.signature(build_reference_embeddings_from_db)
                except Exception:
                    sig = None
    
                if sig and "only_label" in sig.parameters and only_label:
                    build_reference_embeddings_from_db(only_label=only_label)
                else:
                    # fallback: call without kwarg
                    build_reference_embeddings_from_db()
            except Exception as e:
                err = e
    
            def _done():
                if err:
                    self.end_busy(f"Rebuild failed: {err}")
                else:
                    self.end_busy("✅ Embeddings rebuilt.")
            try:
                self.root.after(0, _done)
            except Exception:
                pass
    
        import threading
        t = threading.Thread(target=_job, daemon=True)
        t.start()
        try: self._workers.append(t)
        except Exception: pass

# --------------------------------------------------------------------
    def _rebuild_do(self, only_label: str | None):
        self._rebuild_pending = None
        def _runner(label=only_label):
            model_dir = os.path.join(os.path.dirname(__file__), "buffalo_l")
            try:
                if label:
                    from photo_sorter import build_reference_embeddings_for_labels
                    self.gui_log(f"⚙️ Rebuilding embeddings for '{label}'…")
                    build_reference_embeddings_for_labels(DB_PATH, model_dir, [label], self.gui_log)
                else:
                    from photo_sorter import build_reference_embeddings_from_db
                    self.gui_log("⚙️ Rebuilding reference embeddings…")
                    build_reference_embeddings_from_db(DB_PATH, model_dir, self.gui_log)
                self.gui_log("✅ Embeddings rebuilt.")
            except Exception as e:
                self.gui_log(f"❌ Embedding rebuild failed: {e}")
        threading.Thread(target=_runner, daemon=True).start()

    # ---------------- layout ----------------
    def build_layout(self):
        # ====== Paned root: sidebar | right ======
        self.main_pane = tk.PanedWindow(self.root, orient=tk.HORIZONTAL, sashwidth=6, bg="#222")
        self.main_pane.pack(fill=tk.BOTH, expand=True)
    
        # Sidebar
        self.sidebar = tk.Frame(self.main_pane, width=260, bg="#1f1f1f")
        self.main_pane.add(self.sidebar)
    
        # Right
        self.right_panel = tk.Frame(self.main_pane, bg="#111")
        self.main_pane.add(self.right_panel)
    
        # ====== Top toolbar ======
        topbar = tk.Frame(self.right_panel, height=40, bg="#111")
        topbar.pack(side=tk.TOP, fill=tk.X)
    
        self.status_left = tk.Label(topbar, text="No tasks at the moment", fg="#bbb", bg="#111")
        self.status_left.pack(side=tk.LEFT, padx=10)
    
        # Shared zoom slider
        self.zoom = ttk.Scale(
            topbar, from_=self.zoom_min, to=self.zoom_max,
            orient=tk.HORIZONTAL, variable=self.zoom_value,
            command=lambda v: self.on_zoom_change(int(float(v))), length=220
        )
        self.zoom.pack(side=tk.LEFT, padx=12)
    
        self.status_right = tk.Label(topbar, text="Photos in view: 0   Selected: 0", fg="#bbb", bg="#111")
        self.status_right.pack(side=tk.RIGHT, padx=10)
    
        # quick placeholders (swap later with icons)
        btnbar = tk.Frame(topbar, bg="#111"); btnbar.pack(side=tk.RIGHT, padx=8)
        for txt, cb in [("🗂", self.action_toggle_view), ("↕", self.action_sort_menu),
                        ("⭐", self.action_flag_selected), ("⚙", self.action_settings)]:
            ttk.Button(btnbar, text=txt, width=2, command=cb).pack(side=tk.LEFT, padx=2)
        
        # ---------------------------------------------------------
        # spinner (hidden by default)
        self.busy = ttk.Progressbar(topbar, mode="indeterminate", length=90)
        # pack it on demand in begin_busy()
        
        # ... when creating quick buttons and the "📂 Open" button:
        # keep references so we can disable/enable while busy
        # Example:
        # open button
        open_btn = ttk.Button(btnbar, text="📂 Open", command=self.choose_folder)
        open_btn.pack(side=tk.LEFT, padx=2)
        
        # add your existing buttons (🗂, ↕, ⭐, ⚙) and collect them:
        btn_toggle = ttk.Button(btnbar, text="🗂", width=2, command=self.action_toggle_view); btn_toggle.pack(side=tk.LEFT, padx=2)
        btn_sort   = ttk.Button(btnbar, text="↕",  width=2, command=self.action_sort_menu);  btn_sort.pack(side=tk.LEFT, padx=2)
        btn_flag   = ttk.Button(btnbar, text="⭐",  width=2, command=self.action_flag_selected); btn_flag.pack(side=tk.LEFT, padx=2)
        btn_sett   = ttk.Button(btnbar, text="⚙",  width=2, command=self.action_settings);   btn_sett.pack(side=tk.LEFT, padx=2)
        
        # register all toolbar buttons we want to disable while busy
        self._buttons_to_disable.extend([open_btn, btn_toggle, btn_sort, btn_flag, btn_sett])

        # quick “free memory” button in the toolbar
        btn_clear = ttk.Button(btnbar, text="🧹", width=2, command=self.clear_thumb_cache)
        btn_clear.pack(side=tk.LEFT, padx=2)
        self._buttons_to_disable.append(btn_clear)


        # ====== Vertical split: reference strip | main grid ======
        self.right_split = tk.PanedWindow(self.right_panel, orient=tk.VERTICAL, sashwidth=6, bg="#111")
        self.right_split.pack(fill=tk.BOTH, expand=True)
    
        # Reference strip (top)
        self.ref_frame = tk.Frame(self.right_split, bg="#141414", height=160,
                                  highlightthickness=1, highlightbackground="#2a2a2a")
        self.right_split.add(self.ref_frame)
    
        # Main grid (bottom)
        self.grid_container = tk.Frame(self.right_split, bg="#111",
                                       highlightthickness=2, highlightbackground="#69a7ff")
        self.right_split.add(self.grid_container)
    
        # Sidebar + Reference strip contents
        self.build_sidebar_contents()
        self.build_reference_strip()
    
        # ====== Main grid (scrollable) ======
        self.canvas = tk.Canvas(self.grid_container, bg="#171717", highlightthickness=0)
        self.vbar = ttk.Scrollbar(self.grid_container, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vbar.set)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.vbar.pack(side=tk.RIGHT, fill=tk.Y)
    
        self.inner = tk.Frame(self.canvas, bg="#171717")
        self.canvas_window = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
    
        self.inner.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", self.on_canvas_resize)
    
        # Make grids activate the shared zoom slider
        self.canvas.bind("<Button-1>", lambda e: self.set_zoom_target("main"))
        self.inner.bind("<Button-1>",  lambda e: self.set_zoom_target("main"))
        self.ref_canvas.bind("<Button-1>", lambda e: self.set_zoom_target("ref"))
        self.ref_inner.bind("<Button-1>",  lambda e: self.set_zoom_target("ref"))

    # ----------------- Sidebar scaffolding -----------
    def build_sidebar_contents(self): 
        tabs = tk.Frame(self.sidebar, bg="#1f1f1f"); tabs.pack(fill=tk.X, pady=(8,4))
        for name in ("Folders", "Results"):
            tk.Button(tabs, text=name, relief=tk.FLAT, bg="#2a2a2a", fg="#ddd",
                      activebackground="#3a3a3a", activeforeground="#fff").pack(side=tk.LEFT, padx=6, ipady=2)
    
        lf_results = ttk.LabelFrame(self.sidebar, text="Results"); lf_results.pack(fill=tk.X, padx=8, pady=8)
        for label in ("Last Search Results","Find Similar Photos","Find by Keyword","Find Faces",
                      "Find People","Find by GPS","Find by text prompt","Find Duplicates"):
            ttk.Button(lf_results, text=label, command=lambda L=label: self.sidebar_action(L)).pack(fill=tk.X, pady=2)
    
        lf_col = ttk.LabelFrame(self.sidebar, text="Collections"); lf_col.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        top = tk.Frame(lf_col); top.pack(fill=tk.X, pady=(0,6))
        ttk.Button(top, text="+ Collection", command=lambda: self.sidebar_action("Add Collection")).pack(side=tk.LEFT)
        ttk.Button(top, text="+ Group",      command=lambda: self.sidebar_action("Add Group")).pack(side=tk.LEFT, padx=6)
        for name in ("Best of 2023", "Holidays 2020"):
            ttk.Button(lf_col, text=name, command=lambda N=name: self.sidebar_action(N)).pack(fill=tk.X, pady=2)
    
    def sidebar_action(self, name): self.set_status_left(f"{name} clicked")

    # ------Reference strip (controls + filmstrip)-----------------------------
    def build_reference_strip(self):
        # controls
        bar = tk.Frame(self.ref_frame, bg="#141414"); bar.pack(side=tk.TOP, fill=tk.X)
        tk.Label(bar, text="Label:", bg="#141414", fg="#ddd").pack(side=tk.LEFT, padx=(8,4))
    
        self.active_label = tk.StringVar(value="")
        self.ref_label_menu = ttk.Combobox(
            bar,
            textvariable=self.active_label,
            values=self.get_all_label_names(),
            width=18,
            state="normal"   # ← allow typing a new label name
        )
        self.ref_label_menu.bind("<Return>", lambda e: self.create_label_from_text())

        self.ref_label_menu.pack(side=tk.LEFT, padx=(0,6))
        self.ref_label_menu.bind("<<ComboboxSelected>>", lambda e: self.on_change_active_label())
        
        # + New Label button
        btn_new_label = ttk.Button(bar, text="+", width=3, command=self.create_label_from_selection)
        btn_new_label.pack(side=tk.LEFT, padx=(0,8))
        
        # (optional) remember to disable it during busy mode
        if not hasattr(self, "_buttons_to_disable"):
            self._buttons_to_disable = []
        self._buttons_to_disable.append(btn_new_label)
    
        tk.Label(bar, text="Threshold", bg="#141414", fg="#aaa").pack(side=tk.LEFT, padx=(8,4))
        self.ref_thr = tk.DoubleVar(value=0.30)
        ttk.Scale(bar, from_=0.05, to=0.90, orient=tk.HORIZONTAL, variable=self.ref_thr,
                  command=lambda v: self.on_change_threshold(float(v)), length=160).pack(side=tk.LEFT, padx=(0,10))
        self.lbl_thr_val = tk.Label(bar, text="0.30", bg="#141414", fg="#aaa"); self.lbl_thr_val.pack(side=tk.LEFT)
    
        # ---- Buttons (assign to variables!) ----
        btns = tk.Frame(bar, bg="#141414"); btns.pack(side=tk.RIGHT, padx=8)
        btn_add     = ttk.Button(btns, text="Add from Selection", command=self.add_selected_to_label)
        btn_remove  = ttk.Button(btns, text="Remove Selected",    command=self.remove_selected_refs)
        btn_rebuild = ttk.Button(btns, text="Rebuild",            command=lambda: self.schedule_rebuild_embeddings(only_label=self.active_label.get()))
        btn_delete  = ttk.Button(btns, text="Delete Label",       command=self.delete_active_label)
    
        btn_add.pack(side=tk.LEFT, padx=4)
        btn_remove.pack(side=tk.LEFT, padx=4)
        btn_rebuild.pack(side=tk.LEFT, padx=4)
        btn_delete.pack(side=tk.LEFT, padx=4)
    
        # make sure the disable-list exists, then register buttons for busy-mode
        if not hasattr(self, "_buttons_to_disable"):
            self._buttons_to_disable = []
        self._buttons_to_disable.extend([btn_add, btn_remove, btn_rebuild, btn_delete])
    
        # filmstrip (horizontal scroll)
        strip = tk.Frame(self.ref_frame, bg="#141414"); strip.pack(fill=tk.BOTH, expand=True)
        self.ref_canvas = tk.Canvas(strip, bg="#141414", height=110, highlightthickness=0)
        self.ref_hbar = ttk.Scrollbar(strip, orient=tk.HORIZONTAL, command=self.ref_canvas.xview)
        self.ref_canvas.configure(xscrollcommand=self.ref_hbar.set)
        self.ref_canvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        self.ref_hbar.pack(side=tk.BOTTOM, fill=tk.X)
    
        self.ref_inner = tk.Frame(self.ref_canvas, bg="#141414")
        self.ref_canvas_window = self.ref_canvas.create_window((0,0), window=self.ref_inner, anchor="nw")
        self.ref_inner.bind("<Configure>", lambda e: self.ref_canvas.configure(scrollregion=self.ref_canvas.bbox("all")))

    # ---------Clear Thumb Cache------------------------
    def clear_thumb_cache(self):
        try:
            self._thumb_cache.clear()
            self._thumb_cache_est_bytes = 0
            self.set_status_left("Thumbnail cache cleared.")
        except Exception:
            pass

    # -----------------------------------------------
    def create_label_from_text(self):
        label = self._sanitize_label(self.active_label.get())
        if not label:
            return
        self._ensure_label_registered(label)
        self._refresh_label_list_and_select(label)
        self.render_reference_strip(label)
        self.set_status_left(f"Label '{label}' ready. Select photos and click 'Add from Selection'.")

    #------------------------------------------------
    def render_reference_strip(self, label=None):
        for w in self.ref_inner.winfo_children(): w.destroy()
        label = label or self.active_label.get()
        if not label: return
    
        try:
            from reference_db import get_all_references
            refs = [r["path"] for r in get_all_references() if r["label"] == label]
        except Exception:
            refs = []
    
        size = int(self.ref_thumb_size.get())
        gutter = 8
        self._ref_thumbs = []
    
        for i, p in enumerate(refs):
            f = tk.Frame(self.ref_inner, width=size, height=size, bg="#1c1c1c",
                         highlightthickness=2, highlightbackground="#2a2a2a")
            f.pack(side=tk.LEFT, padx=(gutter,0), pady=6); f.pack_propagate(False)
            ph = self.load_thumb(p, size)
            if ph:
                lbl = tk.Label(f, image=ph, bg="#1c1c1c"); lbl.image = ph
                lbl.pack(fill=tk.BOTH, expand=True)
    
            def on_click(e, frame=f):
                bg = frame.cget("highlightbackground")
                frame.config(highlightbackground="#69a7ff" if bg != "#69a7ff" else "#2a2a2a")
            f.bind("<Button-1>", on_click)
            for w in f.winfo_children(): w.bind("<Button-1>", on_click)
    
            self._ref_thumbs.append((f, p))
    
        # adjust height to size
        try:
            self.ref_canvas.config(height=max(110, size + 14))
        except Exception: pass
    
        self.ref_inner.update_idletasks()
        bbox = self.ref_canvas.bbox(self.ref_canvas_window)
        if bbox:
            width = bbox[2] - bbox[0]
            self.ref_canvas.configure(scrollregion=(0,0,width,max(110, size+14)))
    # -----------------------------------------------
    def begin_busy(self, msg="Working…"):
        if self._is_busy:
            return
        self._is_busy = True
        self.set_status_left(msg)
        # show spinner
        try:
            self.busy.pack(side=tk.LEFT, padx=8)
            self.busy.start(10)  # ms per step
        except Exception:
            pass
        # disable buttons
        for b in self._buttons_to_disable:
            try: b.configure(state=tk.DISABLED)
            except Exception: pass
    
    def end_busy(self, msg="Done."):
        # allow multiple end calls safely
        if not self._is_busy:
            return
        self._is_busy = False
        self.set_status_left(msg)
        # hide spinner
        try:
            self.busy.stop()
            self.busy.pack_forget()
        except Exception:
            pass
        # enable buttons
        for b in self._buttons_to_disable:
            try: b.configure(state=tk.NORMAL)
            except Exception: pass

    #----------------------------------------------
    def _sanitize_label(self, s: str) -> str:
        s = (s or "").strip()
        # simple cleanup; adjust to your rules if needed
        bad = '<>:"/\\|?*'
        for ch in bad:
            s = s.replace(ch, "_")
        return s
    
    def _ensure_label_registered(self, label: str):
        """Optional: set default threshold so the label appears in lists, even if your DB doesn't have a 'labels' table."""
        try:
            from reference_db import set_threshold_for_label
            set_threshold_for_label(label, 0.30)
        except Exception:
            # fine if unsupported
            pass
    
    def _refresh_label_list_and_select(self, label: str):
        try:
            labels = self.get_all_label_names()
            if label not in labels:
                labels = labels + [label]
            self.ref_label_menu.configure(values=labels)
            self.active_label.set(label)
        except Exception:
            self.active_label.set(label)
    
    def create_label_from_selection(self):
        """
        Create (or select) a label. If there are selected images in the main grid,
        offer to add them immediately as references.
        """
        from tkinter import simpledialog, messagebox
        current = self.active_label.get().strip()
        prompt_default = current if current else ""
        name = simpledialog.askstring("New label", "Enter label name:", initialvalue=prompt_default)
        if not name:
            return
        label = self._sanitize_label(name)
        if not label:
            messagebox.showwarning("Invalid", "Label name is empty.")
            return
    
        # register default threshold so label is visible (if supported)
        self._ensure_label_registered(label)
        self._refresh_label_list_and_select(label)
    
        # if user has selected photos in the main grid, ask to add them now
        if self.selected_indices:
            if messagebox.askyesno("Add references", f"Add {len(self.selected_indices)} selected photo(s) to '{label}'?"):
                try:
                    from reference_db import insert_reference
                    to_add = [self.current_images[i] for i in sorted(self.selected_indices) if 0 <= i < len(self.current_images)]
                    added = 0
                    for p in to_add:
                        try:
                            insert_reference(p, label)
                            added += 1
                        except Exception:
                            pass
                    self.set_status_left(f"Added {added} reference(s) to '{label}'. Rebuilding…")
                    self.render_reference_strip(label)
                    self.schedule_rebuild_embeddings(only_label=label)
                except Exception as e:
                    self.set_status_left(f"Add failed: {e}")
        else:
            self.set_status_left(f"Label '{label}' created. Select photos and click 'Add from Selection'.")
            self.render_reference_strip(label)


    
    # ----------------------------------------------
    def choose_folder(self):
        from tkinter import filedialog, messagebox
        folder = filedialog.askdirectory(title="Select a folder with photos")
        if not folder:
            return
        self.load_images_from_folder(folder)
    
    def load_images_from_folder(self, folder: str):
        self.begin_busy("Scanning folder…")
        def _scan():
            exts = {".jpg",".jpeg",".png",".webp",".bmp",".gif",".tif",".tiff"}
            paths = []
            err = None
            try:
                for root, dirs, files in os.walk(folder):
                    for fn in files:
                        if os.path.splitext(fn)[1].lower() in exts:
                            paths.append(os.path.join(root, fn))
                paths.sort()
            except Exception as e:
                err = e
    
            def _done():
                if err:
                    self.end_busy(f"Scan failed: {err}")
                    return
                self.selected_indices.clear()
                self.render_grid(paths)
                self.end_busy(f"Loaded {len(paths)} photos from: {folder}")
            self.root.after(0, _done)
    
        t = threading.Thread(target=_scan, daemon=True)
        t.start()
        try: self._workers.append(t)
        except Exception: pass

    # -----------------------------------------------
    def get_all_label_names(self):
        try:
            from reference_db import get_all_labels
            return get_all_labels()
        except Exception:
            return []
    
    def on_change_active_label(self):
        label = self.active_label.get()
        try:
            from reference_db import get_threshold_for_label
            t = get_threshold_for_label(label) or 0.30
            self.ref_thr.set(float(t)); self.lbl_thr_val.config(text=f"{float(t):.2f}")
        except Exception:
            pass
        self.render_reference_strip(label)
    
    def on_change_threshold(self, v):
        self.lbl_thr_val.config(text=f"{float(v):.2f}")
        label = self.active_label.get()
        if not label: return
        try:
            from reference_db import set_threshold_for_label
            set_threshold_for_label(label, float(v))
        except Exception:
            pass
    # --------------Main grid (zoomable + multi-select)--------------------------------
    def on_canvas_resize(self, event):
        self.render_grid()
    
    def render_grid(self, images=None):
        if images is not None:
            self.current_images = images
    
        for w in self.inner.winfo_children(): w.destroy()
    
        if not self.current_images:
            self.set_status_right(0, len(self.selected_indices)); return
    
        gutter = self.grid_gutter
        size = int(self.main_thumb_size.get())
        cell = size + gutter
    
        avail_w = self.canvas.winfo_width() or self.canvas.winfo_reqwidth()
        cols = max(1, avail_w // cell)
    
        self.thumb_buttons = []
        for idx, path in enumerate(self.current_images):
            r, c = divmod(idx, cols)
            frame = tk.Frame(self.inner, width=size, height=size, bg="#202020", highlightthickness=2)
            frame.grid(row=r, column=c, padx=gutter//2, pady=gutter//2); frame.grid_propagate(False)
    
            ph = self.load_thumb(path, size)
            if ph:
                lbl = tk.Label(frame, image=ph, bg="#202020"); 
                lbl.image = ph
                lbl.pack(fill=tk.BOTH, expand=True)
            else:
                # fallback visual for unreadable images
                tk.Label(frame, text="(no preview)", fg="#aaa", bg="#202020").pack(expand=True, fill=tk.BOTH)
                
            frame.config(highlightbackground="#69a7ff" if idx in self.selected_indices else "#2a2a2a")
    
            def on_click(e, i=idx): self.toggle_select(i)
            def on_ctrl_click(e, i=idx): self.toggle_select(i)
            frame.bind("<Button-1>", on_click)
            frame.bind("<Control-Button-1>", on_ctrl_click)
            for w in frame.winfo_children():
                w.bind("<Button-1>", on_click)
                w.bind("<Control-Button-1>", on_ctrl_click)
    
            self.thumb_buttons.append(frame)
    
        self.set_status_right(len(self.current_images), len(self.selected_indices))
        self.inner.update_idletasks()
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))
    # ------------------------------------------------
    def _estimate_thumb_bytes(self, size_px: int) -> int:
        # rough RGBA estimate; Tk PhotoImage is platform-dependent, but this is a safe upper bound
        return int(size_px) * int(size_px) * 4
    
    def _evict_cache_if_needed(self):
        # Evict by size first, then by count; pop oldest first (LRU)
        while self._thumb_cache_est_bytes > self._thumb_cache_bytes_limit and self._thumb_cache:
            (k_path, k_size), (img, est) = self._thumb_cache.popitem(last=False)
            self._thumb_cache_est_bytes -= est
        while len(self._thumb_cache) > self._thumb_cache_items_limit and self._thumb_cache:
            (k_path, k_size), (img, est) = self._thumb_cache.popitem(last=False)
            self._thumb_cache_est_bytes -= est
    
    def load_thumb(self, path: str, size: int):
        key = (path, int(size))
        if key in self._thumb_cache:
            # touch: move to end (most recently used)
            img, est = self._thumb_cache.pop(key)
            self._thumb_cache[key] = (img, est)
            return img
        try:
            im = Image.open(path)
            if im.mode not in ("RGB", "RGBA"):
                im = im.convert("RGB")
            im.thumbnail((int(size), int(size)))
            ph = ImageTk.PhotoImage(im)
            est = self._estimate_thumb_bytes(int(size))
            # insert and evict if necessary
            self._thumb_cache[key] = (ph, est)
            self._thumb_cache_est_bytes += est
            self._evict_cache_if_needed()
            return ph
        except Exception:
            return None
    # ------------------------------------------------
    def _maybe_purge_cache_on_zoom(self, target: str, old_size: int, new_size: int):
        """
        If zoom jumps big (>= 48px or >= 25%), purge most of the cache so memory doesn't balloon.
        Strategy:
          - purge entries not matching the new_size (keeps a small slice if sizes are close)
        """
        try:
            if old_size <= 0:
                old_size = new_size
            jump_px = abs(int(new_size) - int(old_size))
            jump_pct = (jump_px / max(1, old_size))
            big_jump = (jump_px >= 48) or (jump_pct >= 0.25)
            if not big_jump or not self._thumb_cache:
                return
    
            # rebuild cache keeping only thumbs of the new size
            keep = OrderedDict()
            est_bytes = 0
            for (p, sz), (img, est) in self._thumb_cache.items():
                if sz == int(new_size):
                    keep[(p, sz)] = (img, est)
                    est_bytes += est
            self._thumb_cache = keep
            self._thumb_cache_est_bytes = est_bytes
        except Exception:
            pass

    # ------------------------------------------------
    def toggle_select(self, idx: int):
        if idx in self.selected_indices: self.selected_indices.remove(idx)
        else: self.selected_indices.add(idx)
        try:
            frame = self.thumb_buttons[idx]
            frame.config(highlightbackground="#69a7ff" if idx in self.selected_indices else "#2a2a2a")
        except Exception:
            pass
        self.set_status_right(len(self.current_images), len(self.selected_indices))

    # ----------------One slider → active grid-------------------------------
    def set_zoom_target(self, target: str):
        if target not in ("main","ref"): return
        self.active_zoom_target.set(target)
        self.zoom_value.set(self.main_thumb_size.get() if target=="main" else self.ref_thumb_size.get())
    
        # visual cue (blue outline on active)
        try:
            self.grid_container.config(highlightthickness=2 if target=="main" else 1,
                                       highlightbackground="#69a7ff" if target=="main" else "#2a2a2a")
            self.ref_frame.config(highlightthickness=2 if target=="ref" else 1,
                                  highlightbackground="#69a7ff" if target=="ref" else "#2a2a2a")
        except Exception:
            pass
    
        self.set_status_left(f"Zoom target: {'Main Grid' if target=='main' else 'Reference Strip'}")
    
    def on_zoom_change(self, value: int):
        value = max(self.zoom_min, min(self.zoom_max, int(value)))
        if self.active_zoom_target.get() == "main":
            old = self._last_main_zoom
            if value != self.main_thumb_size.get():
                self.main_thumb_size.set(value)
                self._maybe_purge_cache_on_zoom("main", old, value)
                self._last_main_zoom = value
                self.render_grid()
        else:
            old = self._last_ref_zoom
            if value != self.ref_thumb_size.get():
                self.ref_thumb_size.set(value)
                self._maybe_purge_cache_on_zoom("ref", old, value)
                self._last_ref_zoom = value
                self.render_reference_strip()

    # ----------------Reference actions (hook to your DB + rebuild)---------------
    def add_selected_to_label(self):
        label = self.active_label.get().strip()
        if not label:
            self.set_status_left("Choose a label first.")
            return
        if not self.selected_indices:
            self.set_status_left("Select images in the main grid first.")
            return
    
        to_add = [self.current_images[i] for i in sorted(self.selected_indices) if 0 <= i < len(self.current_images)]
        try:
            from reference_db import insert_reference
            added = 0
            for p in to_add:
                try:
                    insert_reference(p, label)
                    added += 1
                except Exception:
                    pass
    
            self.set_status_left(f"Added {added} reference(s) to '{label}'. Rebuilding embeddings…")
            self.schedule_rebuild_embeddings(only_label=label)
            self.render_reference_strip(label)
        except Exception as e:
            self.set_status_left(f"Add failed: {e}")

    
    def remove_selected_refs(self):
        label = self.active_label.get().strip()
        if not label:
            self.set_status_left("Choose a label.")
            return
    
        to_remove = [path for frame, path in getattr(self, "_ref_thumbs", [])
                     if frame.cget("highlightbackground") == "#69a7ff"]
        if not to_remove:
            self.set_status_left("Select references in the strip to remove.")
            return
    
        try:
            from reference_db import delete_reference
            rem = 0
            for p in to_remove:
                try:
                    delete_reference(p)
                    rem += 1
                except Exception:
                    pass
    
            self.set_status_left(f"Removed {rem} from '{label}'. Rebuilding embeddings…")
            self.schedule_rebuild_embeddings(only_label=label)
            self.render_reference_strip(label)
        except Exception as e:
            self.set_status_left(f"Remove failed: {e}")


    # -----------------------------------------------
    def set_status_left(self, msg):
        try: self.status_left.config(text=msg)
        except Exception: pass
    
    def set_status_right(self, in_view: int, selected: int):
        try: self.status_right.config(text=f"Photos in view: {in_view}   Selected: {selected}")
        except Exception: pass
    
    def action_toggle_view(self): pass
    def action_sort_menu(self): pass
    def action_flag_selected(self): pass
    def action_settings(self): pass

    #------------------------------------------------

    def delete_active_label(self):
        label = self.active_label.get().strip()
        if not label:
            self.set_status_left("No active label.")
            return
        self.delete_label_all(label)
        # refresh UI
        self.active_label.set("")
        try:
            self.ref_label_menu.configure(values=self.get_all_label_names())
        except Exception:
            pass
        self.render_reference_strip("")
        self.set_status_left(f"Deleted label '{label}'.")

    def delete_label_all(self, label: str):
        if not label:
            return
        try:
            # remove all references of this label from DB
            from reference_db import get_all_references, delete_reference
            refs = [r["path"] for r in get_all_references() if r["label"] == label]
            for p in refs:
                try:
                   delete_reference(p)
                except Exception:
                   pass
            # optional: clear threshold if your DB supports it
            try:
                from reference_db import set_threshold_for_label
                set_threshold_for_label(label, None)
            except Exception:
                pass
        except Exception:
            pass

    # ----------------------------------------------

    
    
    # ---------------- modal confirm ----------------
    def _confirm_modal(self, title: str, message: str) -> bool:
        dlg = tk.Toplevel(self.root)
        dlg.title(title)
        dlg.resizable(False, False)
        dlg.transient(self.root)
        dlg.grab_set()
        frm = ttk.Frame(dlg, padding=12)
        frm.pack(fill=tk.BOTH, expand=True)
        ttk.Label(frm, text=message, wraplength=380, justify="left").grid(row=0, column=0, columnspan=2, pady=(0, 10))
        result = {"ok": False}
        def on_yes():
            result["ok"] = True
            dlg.destroy()
        def on_no():
            result["ok"] = False
            dlg.destroy()
        ttk.Button(frm, text="Cancel", command=on_no).grid(row=1, column=0, sticky="e", padx=(0, 6))
        ttk.Button(frm, text="Stop", command=on_yes).grid(row=1, column=1, sticky="w")
        dlg.bind("<Return>", lambda e: on_yes())
        dlg.bind("<Escape>", lambda e: on_no())
        dlg.update_idletasks()
        x = self.root.winfo_rootx(); y = self.root.winfo_rooty()
        w = self.root.winfo_width(); h = self.root.winfo_height()
        ww = dlg.winfo_reqwidth(); wh = dlg.winfo_reqheight()
        dlg.geometry(f"+{x + (w//2 - ww//2)}+{y + (h//2 - wh//2)}")
        self.root.wait_window(dlg)
        return result["ok"]
    
    # --------------- inside class ImageRangerGUI ----------------

    def undo_last(self, event=None):
        """Undo the last destructive action (delete_refs / delete_label) or callables."""
        try:
            # Prefer the structured stack
            item = None
            if isinstance(getattr(self, "undo", None), UndoStack):
                item = self.undo.pop()
            elif getattr(self, "undo_stack", None):
                item = self.undo_stack.pop()

            if not item:
                self.gui_log("Nothing to undo.")
                return

            # 1) Direct callable support
            if callable(item):
                item()
                return

            # 2) Dict payloads
            if isinstance(item, dict):
                t = item.get("type")
                data = item.get("data", {})

                # ---- Undo: Delete Selected References ----
                if t == "delete_refs":
                    label = data.get("label")
                    entries = data.get("items", [])
                    restored = 0
                    for e in entries:
                        # accept both legacy {"trashed": "..."} and new {"backup_path": "...", "original_path": "..."}
                        backup = e.get("backup_path") or e.get("trashed")
                        orig = e.get("original_path")
                        if not backup or not orig:
                            continue
                        try:
                            os.makedirs(os.path.dirname(orig), exist_ok=True)
                            if os.path.exists(backup):
                                shutil.move(backup, orig)
                                if label:
                                    try:
                                        insert_reference(orig, label)
                                    except Exception:
                                        pass
                                restored += 1
                        except Exception as ex:
                            self.gui_log(f"Undo restore failed for {orig}: {ex}")

                    if label:
                        try:
                            _write_or_refresh_metadata(label)
                        except Exception:
                            pass
                        # Refresh the UI + rebuild just this label's embeddings
                        self.reference_browser.refresh_label_list(auto_select=False)
                        if self.reference_browser.label_filter.get() == label:
                            self.reference_browser.load_images()
                        self.schedule_rebuild_embeddings(only_label=label)

                    self.gui_log(f"↩ Restored {restored} reference(s) to '{label}'.")
                    return

                # ---- Undo: Delete Entire Label ----
                if t == "delete_label":
                    label = data.get("label")
                    trashed_folder = data.get("trashed_folder")
                    thr = float(data.get("threshold", 0.3))

                    if not label:
                        self.gui_log("Undo failed: missing label.")
                        return

                    # If deletion went to OS recycle bin we can’t auto-restore.
                    if not trashed_folder or trashed_folder == "recycle":
                        self.gui_log("Cannot auto-undo: label was sent to the system Recycle Bin.")
                        return

                    dest_folder = get_label_folder_path(label)  # ensures folder exists
                    try:
                        # If an empty folder was recreated, remove it before restoring
                        try:
                            if os.path.isdir(dest_folder) and not os.listdir(dest_folder):
                                os.rmdir(dest_folder)
                        except Exception:
                            pass

                        os.makedirs(os.path.dirname(dest_folder), exist_ok=True)
                        shutil.move(trashed_folder, dest_folder)

                        # Reinsert entries to DB
                        restored = 0
                        for root_dir, _, files in os.walk(dest_folder):
                            for f in files:
                                if f.lower().endswith((".jpg", ".jpeg", ".png", ".bmp", ".webp")):
                                    full = os.path.join(root_dir, f)
                                    try:
                                        insert_reference(full, label)
                                        restored += 1
                                    except Exception:
                                        pass

                        # restore label metadata / threshold
                        try:
                            set_threshold_for_label(label, thr)
                            insert_or_update_label(label, dest_folder, thr)
                            _write_or_refresh_metadata(label, thr)
                        except Exception:
                            pass

                        # UI & embeddings
                        self.reference_browser.refresh_label_list(auto_select=False)
                        self.reference_browser.label_filter.set(label)
                        self.reference_browser.load_images()
                        self.schedule_rebuild_embeddings(only_label=label)
                        self.gui_log(f"↩ Restored label '{label}' ({restored} items).")
                    except Exception as ex:
                        self.gui_log(f"Undo restore of label failed: {ex}")
                    return

            # Fallback (not a recognized shape)
            self.gui_log(f"Undo item format not recognized: {item!r}")

        except Exception as e:
            self.gui_log(f"Undo failed: {e}")

  
    # ---------------- health/review/browse ----------------
    def db_health_check(self):
        try:
            removed = purge_missing_references()
            self.gui_log(f"🧹 DB Health Check: removed {removed} dead reference entries.")
            messagebox.showinfo("DB Health Check", f"Removed {removed} dead reference entries.")
            self.reference_browser.refresh_label_list(auto_select=False)
            if removed:
                self.rebuild_embeddings_async()
        except Exception as e:
            self.gui_log(f"⚠️ DB Health Check failed: {e}")
            messagebox.showerror("DB Health Check", f"Failed: {e}")

    def open_review(self):
        if not (self.last_unmatched_dir and os.path.isdir(self.last_unmatched_dir)):
            messagebox.showinfo("Review", "No unmatched folder to review yet.")
            return
        MatchReviewPanel(self.root, self.last_unmatched_dir, self.last_output_dir, self.gui_log)

    def browse_folder(self):
        folder = filedialog.askdirectory()
        if folder:
            self.selected_folder.set(folder)
            self.gui_log(f"📂 Folder selected: {folder}")
            self._cancel_thumb_job()
            self.load_images_recursive(folder)
            candidate = os.path.join(folder, "_unmatched")
            if os.path.isdir(candidate):
                self.last_unmatched_dir = candidate
                self.last_output_dir = folder
                try:
                    self.btn_review.configure(state="normal")
                except Exception:
                    pass

    # ---------------- image grid ----------------
    def load_images_recursive(self, folder):
        self.image_paths = []
        exts = (".jpg", ".jpeg", ".png", ".bmp", ".webp")
        for root_dir, _, files in os.walk(folder):
            for f in files:
                if f.lower().endswith(exts):
                    self.image_paths.append(os.path.join(root_dir, f))
        self.gui_log(f"🖼️ Found {len(self.image_paths)} images. Rendering grid…")
        self.display_thumbnails()

    def display_thumbnails(self):
        for widget in self.scrollable_frame.winfo_children():
            widget.destroy()
        self.thumbnails.clear()
        gc.collect()
        self._start_thumb_job(self.image_paths)
        # (the old eager loader is left out intentionally)

    # ---------------- label flows ----------------
    def label_selected(self):
        if not self.selected_images:
            messagebox.showwarning("No Selection", "Please select images to label.")
            return
        dlg = CreateLabelDialog(self.root, initial_name="", initial_threshold=0.3)
        self.root.wait_window(dlg)
        if not dlg.result:
            return
        label, threshold = dlg.result
        for path in self.selected_images:
            dst = _safe_copy_to_label_folder(path, label, keep_original_name=True)
            insert_reference(dst, label)
        set_threshold_for_label(label, threshold)
        default_folder = get_label_folder_path(label)
        os.makedirs(default_folder, exist_ok=True)
        insert_or_update_label(label, default_folder, threshold)
        _write_or_refresh_metadata(label, threshold)
        messagebox.showinfo("Saved", f"{len(self.selected_images)} images labeled as '{label}'")
        self.selected_images.clear()
        self.display_thumbnails()
        self.reference_browser.refresh_label_list()
        self.reference_browser.label_filter.set(label)
        self.reference_browser.load_images()
        self.gui_log(f"🏷️ Labeled images as '{label}' (threshold {threshold}). Rebuilding embeddings…")
        self.schedule_rebuild_embeddings(only_label=label)

    def add_selected_to_reference(self):
        if not self.selected_images:
            messagebox.showwarning("No Selection", "Select photos in the main grid first.")
            return
        current_label = self.reference_browser.label_filter.get()
        if not current_label:
            dlg = CreateLabelDialog(self.root, initial_name="", initial_threshold=0.3)
            self.root.wait_window(dlg)
            if not dlg.result:
                return
            current_label, thr = dlg.result
            default_folder = get_label_folder_path(current_label)
            os.makedirs(default_folder, exist_ok=True)
            set_threshold_for_label(current_label, thr)
            insert_or_update_label(current_label, default_folder, thr)
            _write_or_refresh_metadata(current_label, thr)
        for p in self.selected_images:
            dst = _safe_copy_to_label_folder(p, current_label, keep_original_name=True)
            insert_reference(dst, current_label)
        _write_or_refresh_metadata(current_label)
        self.gui_log(f"➕ Added {len(self.selected_images)} image(s) to reference label '{current_label}'. Rebuilding embeddings…")
        messagebox.showinfo("Reference", f"Added {len(self.selected_images)} image(s) to '{current_label}'.")
        self.selected_images.clear()
        self.display_thumbnails()
        self.reference_browser.refresh_label_list(auto_select=False)
        if self.reference_browser.label_filter.get() == current_label:
            self.reference_browser.load_images()
        self.rebuild_embeddings_async(only_label=current_label)

    # ---------------- sorting flow ----------------
    def start_sort_flow(self):
        ref_list = get_all_references()
        if not ref_list:
            messagebox.showwarning("No References", "Please label reference images first.")
            return
        model_dir = os.path.join(os.path.dirname(__file__), "buffalo_l")
        def log_callback(msg):
            self.gui_log(msg)
        self.gui_log("⚙️ Building reference embeddings…")
        try:
            build_reference_embeddings_from_db(DB_PATH, model_dir, log_callback)
        except Exception as e:
            messagebox.showerror("Embeddings", f"Failed to build embeddings: {e}")
            return
        progress = _ModalProgress(self.root, title="Building Embeddings", message="Preparing reference embeddings…")
        ok_holder = {"ok": True, "err": None}
        def _prebuild():
            try:
                self.gui_log("⚙️ Preparing reference embeddings…")
                build_reference_embeddings_from_db(DB_PATH, model_dir, log_callback)
            except Exception as e:
                ok_holder["ok"] = False
                ok_holder["err"] = e
            finally:
                self.root.after(0, progress.close)
        threading.Thread(target=_prebuild, daemon=True).start()
        self.root.wait_window(progress.top)
        if not ok_holder["ok"]:
            messagebox.showerror("Embeddings", f"Failed to build embeddings: {ok_holder['err']}")
            return
        inbox = filedialog.askdirectory(title="Select Inbox Folder to Sort")
        if not inbox:
            return
        output = filedialog.askdirectory(title="Select Output Folder for Sorted Photos")
        if not output:
            return
        unmatched = os.path.join(output, "_unmatched")
        match_mode = self.multi_face_mode.get()
        self.sort_stop_event = threading.Event()
        self._set_sort_running()
        def worker():
            try:
                self.gui_log(f"🚀 Sorting started → mode: {match_mode}")
                sort_photos_with_embeddings_from_folder_using_db(
                    inbox_dir=inbox,
                    output_dir=output,
                    unmatched_dir=unmatched,
                    db_path=DB_PATH,
                    log_callback=log_callback,
                    match_mode=match_mode,
                    move_files=True,
                    keep_original_filenames=True,
                    stop_event=self.sort_stop_event,
                    model_dir=model_dir,
                )
                if self.sort_stop_event.is_set():
                    self.gui_log("⛔ Sorting stopped by user.")
                else:
                    self.gui_log("✅ Sorting complete.")
                self.last_unmatched_dir = unmatched
                self.last_output_dir = output
                try:
                    self.btn_review.configure(state="normal")
                except Exception:
                    pass
            except Exception as e:
                self.gui_log(f"❌ Sorting error: {e}")
            finally:
                self.root.after(0, self._set_sort_idle)
        self.sort_thread = threading.Thread(target=worker, daemon=True)
        self.sort_thread.start()

    # ---------------- open/export ----------------
    def open_reference_root(self):
        folder = get_reference_root()
        try:
            if os.name == "nt":
                os.startfile(folder)
            elif sys.platform == "darwin":
                subprocess.Popen(["open", folder])
            else:
                subprocess.Popen(["xdg-open", folder])
        except Exception as e:
            self.gui_log(f"⚠️ Could not open reference root: {e}")

    def export_match_audit_csv(self):
        path = filedialog.asksaveasfilename(
            title="Export Match Audit", defaultextension=".csv",
            filetypes=[("CSV", "*.csv")]
        )
        if not path:
            return
        try:
            import csv, sqlite3
            conn = sqlite3.connect(DB_PATH)
            cur = conn.cursor()
            cur.execute("""SELECT id, filename, matched_label, confidence, match_mode, timestamp
                           FROM match_audit ORDER BY id""")
            rows = cur.fetchall()
            conn.close()
            with open(path, "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                w.writerow(["id","filename","matched_label","confidence","match_mode","timestamp"])
                w.writerows(rows)
            messagebox.showinfo("Export", f"Exported {len(rows)} rows to:\n{path}")
            self.gui_log(f"📤 Exported match audit to {path}")
        except Exception as e:
            messagebox.showerror("Export", f"Failed to export: {e}")

    # ---------------- sort button states ----------------
    def _set_sort_idle(self):
        self.sorting = False
        self.btn_sort.configure(text="▶ Sort", bg="SystemButtonFace", fg="black", relief="raised")

    def _set_sort_running(self):
        self.sorting = True
        self.btn_sort.configure(text="🟢 Sorting… (click to stop)", bg="#22aa22", fg="white", relief="sunken")

    def _set_sort_stopping(self):
        self.btn_sort.configure(text="🛑 Stop (stopping…)", bg="#cc3333", fg="white", relief="sunken")

    def toggle_sort(self):
        if not self.sorting:
            self.start_sort_flow()
        else:
            if self._confirm_modal("Stop Sorting", "Are you sure you want to stop sorting?"):
                if self.sort_stop_event:
                    self.sort_stop_event.set()
                self._set_sort_stopping()

# -----------------------------------------------------------

if __name__ == '__main__':
    root = tk.Tk()
    app = ImageRangerGUI(root)
    root.mainloop()
