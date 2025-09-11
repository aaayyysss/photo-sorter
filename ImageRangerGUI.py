# ImageRanger.py
# Verion 6.6 dated 20250911
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
from tkinter import *

import sys, subprocess
from tkinter import ttk, filedialog, messagebox, simpledialog, colorchooser
from concurrent.futures import ThreadPoolExecutor, as_completed
import queue
import itertools
import gc

from PIL import Image, ImageTk

from undo_stack import UndoStack

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

from ReferenceGUI import ReferenceBrowser
from photo_sorter import sort_photos_with_embeddings_from_folder_using_db
from reference_utils import _write_or_refresh_metadata, get_label_folder_path, get_reference_root


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
#class UndoStack:
#    def __init__(self, limit: int = 50):
#        self._stack = []
#        self._limit = limit
#    def push(self, action: dict):
#        self._stack.append(action)
#        if len(self._stack) > self._limit:
#            self._stack.pop(0)
#    def pop(self):
#        return self._stack.pop() if self._stack else None
#    def clear(self):
#        self._stack.clear()

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
class ImageRangerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Photo Sorter - Reference Labeling")

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

        # async/undo helpers
        self._rebuild_pending = None
        self.undo_stack = UndoStack()

        # visuals
        self.apply_styles()
        self.build_layout()
        self.reference_browser.refresh_label_list(auto_select=True)

        self.gui_log("✅ GUI initialized.")
        #self.undo_stack = []


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
        self.ReferenceBrowser.refresh_label_list(auto_select=False)
        self.gui_log("⚙️ Preferences saved and applied.")

    def open_settings_dialog(self):
        SettingsDialog(self.root, SETTINGS, self._on_settings_saved)

    # ---------------- embeddings rebuild (debounced + threaded) ----------------
    def rebuild_embeddings_async(self, only_label: str | None = None):
        if getattr(self, "_rebuild_pending", None):
            try:
                self.root.after_cancel(self._rebuild_pending)
            except Exception:
                pass
            self._rebuild_pending = None
        self._rebuild_pending = self.root.after(200, lambda ol=only_label: self._rebuild_do(ol))

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
        top_frame = ttk.Frame(self.root)
        top_frame.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)

        ttk.Label(top_frame, text="📂 Folder:").pack(side=tk.LEFT)
        ttk.Entry(top_frame, textvariable=self.selected_folder, width=60).pack(side=tk.LEFT, padx=5)
        ttk.Button(top_frame, text="Browse", command=self.browse_folder).pack(side=tk.LEFT)
        ttk.Button(top_frame, text="🏷️ Label Selected", command=self.label_selected).pack(side=tk.LEFT, padx=10)
        ttk.Button(top_frame, text="➕ Add to Reference", command=self.add_selected_to_reference).pack(side=tk.LEFT, padx=6)
        
        ttk.Button(top_frame, text="↩ Undo", command=self.undo_last_action).pack(side=tk.LEFT, padx=6)
        
        ttk.Button(top_frame, text="🧹 DB Health Check", command=self.db_health_check).pack(side=tk.LEFT, padx=10)

        self.btn_review = ttk.Button(top_frame, text="🧭 Review Unmatched", command=self.open_review, state="disabled")
        self.btn_review.pack(side=tk.LEFT, padx=10)

        self.btn_sort = tk.Button(
            top_frame,
            text="▶ Sort",
            bg="SystemButtonFace",
            fg="black",
            command=self.toggle_sort,
            width=18,
            relief="raised"
        )
        self.btn_sort.pack(side=tk.RIGHT)

        mode_frame = ttk.LabelFrame(top_frame, text="Face Matching Mode")
        mode_frame.pack(side=tk.RIGHT, padx=10)
        ttk.Radiobutton(mode_frame, text="Best Match",  variable=self.multi_face_mode, value="best").pack(anchor=tk.W)
        ttk.Radiobutton(mode_frame, text="Multi-Match", variable=self.multi_face_mode, value="multi").pack(anchor=tk.W)
        ttk.Radiobutton(mode_frame, text="Manual",      variable=self.multi_face_mode, value="manual").pack(anchor=tk.W)
        rules = (
            "Rules:\n"
            "• Best: MOVE file to the single best label.\n"
            "• Multi: COPY to all other matched labels.\n"
            "• Manual: placeholder for now."
        )
        tk.Label(mode_frame, text=rules, justify="left", anchor="w", fg="#444", wraplength=320).pack(anchor=tk.W, pady=(6, 2))

        self.reference_browser = ReferenceBrowser(
            self.root, 
            self.gui_log, 
            self.rebuild_embeddings_async, 
            undo_push=self.undo_stack.push
        )
        self.reference_browser.pack(fill=tk.X, padx=10, pady=5)

        self.main_frame = ttk.Frame(self.root)
        self.main_frame.pack(fill=tk.BOTH, expand=True)
        self.canvas = tk.Canvas(self.main_frame, bg="#ffffff")
        self.scrollbar = ttk.Scrollbar(self.main_frame, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.scrollable_frame = ttk.Frame(self.canvas)
        self.canvas.create_window((0, 0), window=self.scrollable_frame, anchor='nw')
        self.scrollable_frame.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        _bind_vertical_mousewheel(self.canvas)
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

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

    #def undo_last_action(self, event=None):
    #    """Undo the last destructive action (delete_refs / delete_label) or callables."""
    #    try:
    #        # Prefer the structured stack
    #        item = None
    #        if isinstance(getattr(self, "undo", None), UndoStack):
    #            item = self.undo.pop()
    #        elif getattr(self, "undo_stack", None):
    #            item = self.undo_stack.pop()

    #        if not item:
    #            self.gui_log("Nothing to undo.")
    #            return

    #        # 1) Direct callable support
    #        if callable(item):
    #            item()
    #            return

    #        # 2) Dict payloads
    #        if isinstance(item, dict):
    #            t = item.get("type")
    #            data = item.get("data", {})

                # ---- Undo: Delete Selected References ----
    #            if t == "delete_refs":
    #                label = data.get("label")
    #                entries = data.get("items", [])
    #                restored = 0
    #                for e in entries:
    #                    # accept both legacy {"trashed": "..."} and new {"backup_path": "...", "original_path": "..."}
    #                    backup = e.get("backup_path") or e.get("trashed")
    #                    orig = e.get("original_path")
    #                    if not backup or not orig:
    #                        continue
    #                    try:
    #                        os.makedirs(os.path.dirname(orig), exist_ok=True)
    #                        if os.path.exists(backup):
    #                            shutil.move(backup, orig)
    #                            if label:
    #                                try:
    #                                    insert_reference(orig, label)
    #                                except Exception:
    #                                    pass
    #                            restored += 1
    #                    except Exception as ex:
    #                        self.gui_log(f"Undo restore failed for {orig}: {ex}")

    #                if label:
    #                    try:
    #                        _write_or_refresh_metadata(label)
    #                    except Exception:
    #                        pass
    #                    # Refresh the UI + rebuild just this label's embeddings
    #                    self.reference_browser.refresh_label_list(auto_select=False)
    #                    if self.reference_browser.label_filter.get() == label:
    #                        self.reference_browser.load_images()
    #                    self.rebuild_embeddings_async(only_label=label)

    #                self.gui_log(f"↩ Restored {restored} reference(s) to '{label}'.")
    #                return

                # ---- Undo: Delete Entire Label ----
    #            if t == "delete_label":
    #                label = data.get("label")
    #                trashed_folder = data.get("trashed_folder")
    #                thr = float(data.get("threshold", 0.3))

    #                if not label:
    #                    self.gui_log("Undo failed: missing label.")
    #                    return

                    # If deletion went to OS recycle bin we can’t auto-restore.
    #                if not trashed_folder or trashed_folder == "recycle":
    #                    self.gui_log("Cannot auto-undo: label was sent to the system Recycle Bin.")
    #                    return

    #                dest_folder = get_label_folder_path(label)  # ensures folder exists
    #                try:
                        # If an empty folder was recreated, remove it before restoring
    #                    try:
    #                        if os.path.isdir(dest_folder) and not os.listdir(dest_folder):
    #                            os.rmdir(dest_folder)
    #                    except Exception:
    #                        pass

    #                    os.makedirs(os.path.dirname(dest_folder), exist_ok=True)
    #                    shutil.move(trashed_folder, dest_folder)

                        # Reinsert entries to DB
    #                    restored = 0
    #                    for root_dir, _, files in os.walk(dest_folder):
    #                        for f in files:
    #                            if f.lower().endswith((".jpg", ".jpeg", ".png", ".bmp", ".webp")):
    #                                full = os.path.join(root_dir, f)
    #                                try:
    #                                    insert_reference(full, label)
    #                                    restored += 1
    #                                except Exception:
    #                                    pass

                        # restore label metadata / threshold
    #                    try:
    #                        set_threshold_for_label(label, thr)
    #                        insert_or_update_label(label, dest_folder, thr)
    #                        _write_or_refresh_metadata(label, thr)
    #                    except Exception:
    #                        pass

                        # UI & embeddings
    #                    self.reference_browser.refresh_label_list(auto_select=False)
    #                    self.reference_browser.label_filter.set(label)
    #                    self.reference_browser.load_images()
    #                    self.rebuild_embeddings_async(only_label=label)
    #                    self.gui_log(f"↩ Restored label '{label}' ({restored} items).")
    #                except Exception as ex:
    #                    self.gui_log(f"Undo restore of label failed: {ex}")
    #                return

            # Fallback (not a recognized shape)
    #        self.gui_log(f"Undo item format not recognized: {item!r}")

    #    except Exception as e:
    #        self.gui_log(f"Undo failed: {e}")


    

    
  
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

    def browse_folder(self):def undo_last_action(self, event=None):
        """Undo the last destructive action (delete_refs / delete_label / rename_label) or callables."""
        try:
            item = self.undo_stack.pop() if self.undo_stack.can_undo() else None
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
                        self.reference_browser.refresh_label_list(auto_select=False)
                        if self.reference_browser.label_filter.get() == label:
                            self.reference_browser.load_images()
                        self.rebuild_embeddings_async(only_label=label)
    
                    self.gui_log(f"↩ Restored {restored} reference(s) to '{label}'.")
                    return
    
                # ---- Undo: Delete Entire Label ----
                elif t == "delete_label":
                    label = data.get("label")
                    trashed_folder = data.get("trashed_folder")
                    thr = float(data.get("threshold", 0.3))
    
                    if not label:
                        self.gui_log("Undo failed: missing label.")
                        return
    
                    if not trashed_folder or trashed_folder == "recycle":
                        self.gui_log("Cannot auto-undo: label was sent to the system Recycle Bin.")
                        return
    
                    dest_folder = get_label_folder_path(label)
                    try:
                        try:
                            if os.path.isdir(dest_folder) and not os.listdir(dest_folder):
                                os.rmdir(dest_folder)
                        except Exception:
                            pass
    
                        os.makedirs(os.path.dirname(dest_folder), exist_ok=True)
                        shutil.move(trashed_folder, dest_folder)
    
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
    
                        try:
                            set_threshold_for_label(label, thr)
                            insert_or_update_label(label, dest_folder, thr)
                            _write_or_refresh_metadata(label, thr)
                        except Exception:
                            pass
    
                        self.reference_browser.refresh_label_list(auto_select=False)
                        self.reference_browser.label_filter.set(label)
                        self.reference_browser.load_images()
                        self.rebuild_embeddings_async(only_label=label)
                        self.gui_log(f"↩ Restored label '{label}' ({restored} items).")
                    except Exception as ex:
                        self.gui_log(f"Undo restore of label failed: {ex}")
                    return
    
                # ---- Undo: Rename Label ----
                elif t == "rename_label":
                    old = data.get("old_label")
                    new = data.get("new_label")
                    files = data.get("moved_files", [])
                    thr = data.get("threshold", 0.3)
    
                    restored = 0
                    for new_path, old_path in files:
                        try:
                            os.makedirs(os.path.dirname(old_path), exist_ok=True)
                            shutil.move(new_path, old_path)
                            insert_reference(old_path, old)
                            restored += 1
                        except Exception:
                            pass
    
                    try:
                        set_threshold_for_label(old, thr)
                        insert_or_update_label(old, get_label_folder_path(old), thr)
                        _write_or_refresh_metadata(old, thr)
                    except Exception:
                        pass
    
                    try:
                        delete_label(new)
                    except Exception:
                        pass
    
                    self.reference_browser.refresh_label_list(auto_select=False)
                    self.reference_browser.label_filter.set(old)
                    self.reference_browser.load_images()
                    self.rebuild_embeddings_async(only_label=old)
                    self.gui_log(f"↩ Undid label rename: restored '{old}' ({restored} items).")
                    return
    
            # If none of the above handled the item
            self.gui_log(f"Undo item format not recognized: {item!r}")
    
        except Exception as e:
            self.gui_log(f"Undo failed: {e}")

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
        self.rebuild_embeddings_async(only_label=label)

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
