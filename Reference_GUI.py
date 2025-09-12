# Reference_GUI.py
# Verion 6.7 dated 20250912
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
from tkinter import *
from tkinter import ttk, filedialog, messagebox, simpledialog, colorchooser
from concurrent.futures import ThreadPoolExecutor, as_completed
import queue
import itertools
import gc

import time
from pathlib import Path

from PIL import Image, ImageTk

from reference_db import (
    init_db,  # ✅ Add this
    get_all_labels, insert_or_update_label, delete_label,
    insert_reference, delete_reference, get_all_references,
    get_label_folder, get_threshold_for_label, set_threshold_for_label
)

from photo_sorter import build_reference_embeddings_from_db, build_reference_embeddings_for_labels

from reference_utils import get_label_folder_path, _trash_move_file, _trash_move_label_folder
from settings_manager import SettingsManager

# ---- Config (persisted) -----------------------------------------

SETTINGS_DEFAULT = {
    "main_grid_sel_color": "#3399ff",
    "main_grid_sel_border": 6,
    "ref_grid_sel_color":  "#3399ff",
    "ref_grid_sel_border": 6,
    "default_mode":        "best",   # best | multi | manual
    "reference_root":      os.path.join(os.getcwd(), "references"),   # ⬅️ NEW
}

# --------------------------------------------------------

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
        self.settings = settings           # ← store SettingsManager
    
        self.label_filter = tk.StringVar()
        self.selected_paths = set()
        self.ref_cells = {}                # path -> {"cell": tk.Frame, "border": tk.Frame}
        self.ref_thumbs = []               # keep PhotoImage refs if you use them

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

        targets = set(self.selected_paths)
        entries = get_all_references()
        deleted = 0
        undo_items = []  # will store dicts {backup_path, original_path}

        for (_id, lbl, path) in entries:
            if lbl == label and path in targets:
                try:
                    restore_hint = None
                    if os.path.isfile(path):
                        ok, detail = _trash_move_file(path)
                        if ok and detail not in (None, "recycle"):
                            restore_hint = detail

                    # Always remove DB entry regardless
                    delete_reference(path)
                    deleted += 1

                    if restore_hint:
                        undo_items.append({
                            "backup_path": restore_hint,
                            "original_path": path
                        })
                        self.gui_log(f"🗑️ Moved to trash: {path}")

                except Exception as e:
                    self.gui_log(f"⚠️ Could not delete '{path}': {e}")

        try:
            _write_or_refresh_metadata(label)
        except Exception:
            pass

        # Push to undo stack
        if self.undo_push and undo_items:
            self.undo_push({
                "type": "delete_refs",
                "data": {"label": label, "items": undo_items}
            })

        self.gui_log(f"🗑️ Deleted {deleted} reference(s) from '{label}'. Rebuilding embeddings…")
        self.load_images()
        self.rebuild_embeddings_async(only_label=label)



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

        trashed_folder = None
        try:
            label_dir = get_label_folder_path(label)
            ok, detail = _trash_move_label_folder(label_dir)
            if ok and detail not in (None, "recycle"):
                trashed_folder = detail
                self.gui_log(f"🗑️ Label folder moved to trash: {detail}")
            else:
                self.gui_log(f"⚠️ Could not move label folder to trash: {detail}")
        except Exception as e:
            self.gui_log(f"⚠️ Could not move label folder to trash: {e}")

        # Remove DB rows for label
        entries = get_all_references()
        deleted = 0
        for (_id, lbl, path) in entries:
            if lbl == label:
                try:
                    delete_reference(path)
                    deleted += 1
                except Exception as e:
                    self.gui_log(f"⚠️ Could not drop DB row {path}: {e}")

        # Store threshold before deleting metadata
        thr = None
        try:
            thr = get_threshold_for_label(label)
        except Exception:
            pass
        try:
            delete_label(label)
        except Exception:
            pass

        # Push undo payload
        if self.undo_push and trashed_folder:
            self.undo_push({
                "type": "delete_label",
                "data": {
                    "label": label,
                    "trashed_folder": trashed_folder,
                    "threshold": thr if thr is not None else 0.3
                }
            })

        self.gui_log(f"🗑️ Deleted label '{label}' ({deleted} item(s)). Rebuilding embeddings…")
        self.label_menu.configure(values=get_all_labels())
        self.refresh_label_list(auto_select=False)
        self.label_filter.set("")
        self.load_images()
        self.rebuild_embeddings_async(only_label=label)



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
        moved_files = []
    
        old_folder = get_label_folder_path(current)
        new_folder = get_label_folder_path(new_label)
        os.makedirs(new_folder, exist_ok=True)
    
        for (_id, lbl, path) in entries:
            if lbl == current:
                new_path = path
                try:
                    # Only move if inside label folder
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
                        moved_files.append((path, candidate))  # For undo
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
    
        # Push undo action
        if self.undo_push:
            self.undo_push({
                "type": "rename_label",
                "data": {
                    "old_label": old_label,
                    "new_label": new_label,
                    "threshold": old_threshold,
                    "moved_files": list(zip(new_paths, old_paths))
                }
            })

    
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
            self.rebuild_embeddings_async(only_label=label)
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
        self.destroy()# Reference_GUI.py
# Verion 6.6 dated 20250908
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
from tkinter import *
from tkinter import ttk, filedialog, messagebox, simpledialog, colorchooser
from concurrent.futures import ThreadPoolExecutor, as_completed
import queue
import itertools
import gc

from PIL import Image, ImageTk

from reference_db import (
    init_db,  # ✅ Add this
    get_all_labels, insert_or_update_label, delete_label,
    insert_reference, delete_reference, get_all_references,
    get_label_folder, get_threshold_for_label, set_threshold_for_label
)


from photo_sorter import build_reference_embeddings_from_db, build_reference_embeddings_for_labels


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
        undo_items = []
    
        for (_id, lbl, path) in entries:
            if lbl == label and path in targets:
                try:
                    # Move to trash (if file exists)
                    restore_hint = None
                    if os.path.isfile(path):
                        ok, detail = _trash_move_file(path)
                        if ok and detail not in (None, "recycle"):
                            restore_hint = detail
    
                    # Remove DB entry
                    delete_reference(path)
                    deleted += 1
    
                    # Save undo hint if backup is valid
                    if restore_hint:
                        undo_items.append({
                            "backup_path": restore_hint,
                            "original_path": path
                        })
    
                except Exception as e:
                    self.gui_log(f"⚠️ Could not delete '{path}': {e}")
    
        try:
            _write_or_refresh_metadata(label)
        except Exception:
            pass
    
        if self.undo_push:
            self.undo_push({
                "type": "delete_refs",
                "data": {
                    "label": current_label,
                    "items": [
                        {
                            "original_path": orig,
                            "backup_path": backup,
                        } for orig, backup in zip(selected_paths, backup_paths)
                    ]
                }
            })

    
        self.gui_log(f"🗑️ Deleted {deleted} reference(s) from '{label}'. Rebuilding embeddings…")
        self.load_images()
        self.rebuild_embeddings_async(only_label=label)



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
    
        trashed_folder = None
        try:
            label_dir = get_label_folder_path(label)
            ok, detail = _trash_move_label_folder(label_dir)
            if ok:
                trashed_folder = detail
            else:
                self.gui_log(f"⚠️ Could not move label folder to trash: {detail}")
        except Exception as e:
            self.gui_log(f"⚠️ Could not move label folder to trash: {e}")
    
        entries = get_all_references()
        deleted = 0
        for (_id, lbl, path) in entries:
            if lbl == label:
                try:
                    delete_reference(path)
                    deleted += 1
                except Exception as e:
                    self.gui_log(f"⚠️ Could not drop DB row {path}: {e}")
    
        thr = None
        try:
            thr = get_threshold_for_label(label)
        except Exception:
            pass
    
        try:
            delete_label(label)
        except Exception:
            pass
    
        if self.undo_push:
            self.undo_push({
                "type": "delete_label",
                "data": {
                    "label": label,
                    "trashed_folder": moved_folder,  # path to `.trash/...`
                    "threshold": threshold,
                }
            })

    
        self.gui_log(f"🗑️ Deleted label '{label}' ({deleted} item(s)). Rebuilding embeddings…")
    
        self.label_menu.configure(values=get_all_labels())
        self.refresh_label_list(auto_select=False)
        self.label_filter.set("")
        self.load_images()
        self.rebuild_embeddings_async(only_label=label)


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
        moved_files = []
    
        old_folder = get_label_folder_path(current)
        new_folder = get_label_folder_path(new_label)
        os.makedirs(new_folder, exist_ok=True)
    
        for (_id, lbl, path) in entries:
            if lbl == current:
                new_path = path
                try:
                    # Only move if inside label folder
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
                        moved_files.append((path, candidate))  # For undo
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
    
        # Push undo action
        if self.undo_push:
            self.undo_push({
                "type": "rename_label",
                "data": {
                    "old_label": old_label,
                    "new_label": new_label,
                    "threshold": old_threshold,
                    "moved_files": list(zip(new_paths, old_paths))
                }
            })

    
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
            self.rebuild_embeddings_async(only_label=label)
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

# ---- Main GUI -----------------------------------------------------
# -------------------------------------------------------------------

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
            #frame.configure(style="TFrame")
            frame.configure(style="RefSelected.TFrame" if path in self.selected_paths else "TFrame")
        else:
            self.selected_paths.add(path)
            frame.configure(style="RefSelected.TFrame")

    def clear_selection(self):
        for p in list(self.selected_paths):
            f = self.thumb_widgets.get(p)
            if f:
                f.configure(style="TFrame")
        self.selected_paths.clear()

    def apply_ref_selection_styles_after_settings(self):
        settings = SettingsManager()
        style = ttk.Style()
        style.configure(
            "RefSelected.TFrame",
            background=settings.get("ref_grid_sel_color"),
            borderwidth=int(settings.get("ref_grid_sel_border")),
            relief="solid",
        )

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
        self.rebuild_embeddings_async(only_label=label)

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
        self.rebuild_embeddings_async(only_label=label)

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
            self.rebuild_embeddings_async(only_label=label)
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


# -----------------------------------------------------------
