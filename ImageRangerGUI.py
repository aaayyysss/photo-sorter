# ImageRanger.py
# Verion 6.10.3 dated 20250915
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
import time
import queue
import itertools
import gc
import sys, subprocess

import tkinter as tk

from tkinter import *
from tkinter import ttk, filedialog, messagebox, simpledialog, colorchooser
from concurrent.futures import ThreadPoolExecutor, as_completed

from PIL import Image, ImageTk
from undo_stack import UndoStack
from pathlib import Path


from reference_db import (
    init_db,
    insert_reference,
    get_all_references,
    delete_reference,
    set_threshold_for_label,
    get_threshold_for_label,
    get_all_labels,      # keep if you want; we won’t rely on it for the dropdown
    delete_label,
    insert_or_update_label,
    _trash_move_label_folder   # ⬅️ add this
)

from ReferenceGUI import ReferenceBrowser
from photo_sorter import sort_photos_with_embeddings_from_folder_using_db
from reference_utils import (
    _write_or_refresh_metadata, 
    get_label_folder_path, 
    get_reference_root,
    cleanup_trash
)

from settings_manager import SettingsManager, SettingsDialog

SETTINGS = SettingsManager()


try:
    from send2trash import send2trash  # pip install Send2Trash
except Exception:
    send2trash = None

# ---------- Global thumbnail cache for main grid
_THUMB_CACHE = {}
_THUMB_CACHE_ORDER = []
_THUMB_CACHE_MAX = 400

# ---- Constants ----------------------------------

THUMBNAIL_SIZE = (100, 100)
DB_PATH = "reference_data.db"

def _thumbcache_get(key):
    if key in _THUMB_CACHE:
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


# ---- Utilities -------------------------------------

def ensure_dir(path: str):
    os.makedirs(path, exist_ok=True)

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

# ------------------ProgressPopup-------------------------

class ProgressPopup:
    def __init__(self, master):
        self.top = tk.Toplevel(master)
        self.top.title("Loading…")
        self.top.geometry("400x180")
        
        self.top.resizable(False, False)
        self.top.transient(master)
        self.top.grab_set()

        # UI Components
        self.label = tk.Label(self.top, text="Preparing to load images...")
        self.label.pack(pady=(20, 10))

        self.progress = ttk.Progressbar(self.top, orient="horizontal", length=250, mode="determinate")
        self.progress.pack()

        self.status_label = tk.Label(self.top, text="")
        self.status_label.pack(pady=(10, 5))

        self.cancel_requested = False  # ✅ used by scan_worker()

        cancel_btn = ttk.Button(self.top, text="Cancel", command=self._cancel)
        cancel_btn.pack(pady=(5, 10))

        # Ensure visible and centered
        self._center_popup()
        self.top.update_idletasks()
        self.top.deiconify()

    def _cancel(self):
        self.cancel_requested = True
        self.label.config(text="Cancelling...")

    def set_total(self, total):
        self.progress["maximum"] = total

    def update_progress(self, value, total=None, current_path=None):
        self.progress["value"] = value
        if total:
            self.progress["maximum"] = total
        text = f"Processing {value} of {int(self.progress['maximum'])}"
        if current_path:
            filename = os.path.basename(current_path)
            text += f"\n{filename}"
        self.status_label.config(text=text)

    def close(self):
        self.top.destroy()

    def _center_popup(self):
        self.top.update_idletasks()
        w = self.top.winfo_width()
        h = self.top.winfo_height()
        parent_x = self.top.master.winfo_rootx()
        parent_y = self.top.master.winfo_rooty()
        parent_w = self.top.master.winfo_width()
        parent_h = self.top.master.winfo_height()
        x = parent_x + (parent_w // 2) - (w // 2)
        y = parent_y + (parent_h // 2) - (h // 2)
        self.top.geometry(f"+{x}+{y}")


# ---- Visual Logger -------------------------------------

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

# ---- Mouse wheel helpers ----------------------------------

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

# ---- DB init ----------------------------------------

init_db()

# ---- Match Review Panel (post-sorting) --------------

class MatchReviewPanel(tk.Toplevel):
    def __init__(self, master, unmatched_dir, output_dir, gui_log, settings, *args, **kwargs):
        super().__init__(master, *args, **kwargs)
        self.title("Review Unmatched Photos")
        self.geometry("1100x700")
        self.unmatched_dir = unmatched_dir
        self.output_dir = output_dir
        self.gui_log = gui_log
        self.settings = settings


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
        #TH = (100, 100)
        TH = self.settings.get("thumbnail_size", (120, 120))

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

      
# ------------Modal Progress Dialog (for long tasks)-------
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

# ---- LeftSideBar  ---------------------------------

class LeftSidebar(ttk.Frame):
    def __init__(self, master, on_folder_select, on_sort_change, on_filter_toggle, *args, **kwargs):
        super().__init__(master, *args, **kwargs)
        self.on_folder_select = on_folder_select
        self.on_sort_change = on_sort_change
        self.on_filter_toggle = on_filter_toggle

        self._build_ui()

    def _build_ui(self):
        # === Folder Tree Viewer ===
        folder_frame = ttk.LabelFrame(self, text="Folders")
        folder_frame.pack(fill=tk.BOTH, expand=True, padx=6, pady=(6, 3))

        self.tree = ttk.Treeview(folder_frame, show="tree")
        self.tree.pack(fill=tk.BOTH, expand=True)
        self.tree.bind("<<TreeviewSelect>>", self._on_tree_select)

        abspath = Path.home()
        root_node = self.tree.insert('', 'end', text=abspath.name, open=True, values=[str(abspath)])
        self._populate_tree(root_node, abspath)

        # === Sorting & Filter Controls ===
        control_frame = ttk.LabelFrame(self, text="Sort & Filter")
        control_frame.pack(fill=tk.X, padx=6, pady=(3, 6))

        # Sort by
        ttk.Label(control_frame, text="Sort by:").pack(anchor="w")
        self.sort_var = tk.StringVar(value="name")
        ttk.Combobox(control_frame, textvariable=self.sort_var, values=["name", "date", "size"], state="readonly", width=12).pack(fill="x", padx=2, pady=2)
        self.sort_var.trace_add("write", lambda *_,: self.on_sort_change(self.sort_var.get()))

        # Filter small images
        self.hide_small = tk.BooleanVar(value=False)
        ttk.Checkbutton(control_frame, text="Hide small images", variable=self.hide_small, command=self._trigger_filter).pack(anchor="w", pady=2)

        # Hide hidden/system
        self.hide_hidden = tk.BooleanVar(value=True)
        ttk.Checkbutton(control_frame, text="Hide hidden/system", variable=self.hide_hidden, command=self._trigger_filter).pack(anchor="w", pady=2)

    def _populate_tree(self, parent, path):
        try:
            for p in Path(path).iterdir():
                if p.is_dir() and not p.name.startswith('.'):
                    node = self.tree.insert(parent, 'end', text=p.name, open=False, values=[str(p)])
                    # Add dummy child for expandable UI
                    self.tree.insert(node, 'end')
        except PermissionError:
            pass

    def _on_tree_select(self, event):
        selected = self.tree.focus()
        path = self.tree.item(selected, "values")[0]
        if path:
            self.on_folder_select(path)

    def _trigger_filter(self):
        filters = {
            "hide_small": self.hide_small.get(),
            "hide_hidden": self.hide_hidden.get()
        }
        self.on_filter_toggle(filters)


# ---- Main GUI --------------------------------------

class ImageRangerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Photo Sorter - Reference Labeling")
    
        # styles + sorting state
        self.style = ttk.Style()
        self.sorting = False
        self.sort_thread = None
        self.sort_stop_event = None
        
        #self.thumb_cache = ThumbnailCache(
        #    use_disk_cache=self.settings.get("use_disk_cache"),
        #    cache_dir=self.settings.get("thumb_cache_dir"),
        #    #max_memory_items=self.settings.get("thumb_cache_max_items#")
        #)
        
        # button styles
        self.style.configure("SortGreen.TButton", foreground="white", background="#22aa22")
        self.style.map("SortGreen.TButton", background=[("active", "#1c8f1c")])
        self.style.configure("SortRed.TButton", foreground="white", background="#cc3333")
        self.style.map("SortRed.TButton", background=[("active", "#a62828")])
    
        # menu + logger
        self._build_menu()
        self.log = BottomLogFrame(self.root)
        self.log.pack(side=tk.BOTTOM, fill=tk.X)
        self.gui_log = make_gui_logger(self.log)

        self.selected_images = set()         # selected file paths in main grid 
        
        self.thumb_cells = {}                # path -> {"cell": tk.Frame, "border": tk.Frame}


        # ✅ initialize SettingsManager with GUI log
        self.settings = SettingsManager(log_fn=self.gui_log)
    
        # data state
        self.selected_folder = tk.StringVar()
        self.image_paths = []
        self.thumbnails = []
        
        #self.last_applied_thumb_size = None  # ✅ Fix: initialize this to avoid attribute error
        self.last_applied_thumb_size = self.settings.get("thumbnail_size", (120, 120))[0]
        
        # dynamic grid defaults
        self.dynamic_columns = 6
        self.tile_pad = 10  # outer padding per tile (px)
        
        #self.thumb_cache = {}  # {path: thumbnail_image}

        self.multi_face_mode = tk.StringVar(value=self.settings.get("default_mode"))

        self.last_unmatched_dir = None
        self.last_output_dir = None
    
        # async/undo helpers
        self._rebuild_pending = None
        self.undo_stack = UndoStack()
        self.undo = self.undo_stack  # ✅ alias so both old and new references work

    
        # visuals
        self.apply_styles()
    
        # build UI layout (reference_browser defined here)
        self.build_layout()
    
        # ✅ refresh after it's defined
        self.reference_browser.refresh_label_list(auto_select=True)
        
        #tkimg = self.settings.thumb_cache.get(image_path)
        #self.settings.thumb_cache.put(image_path, tkimg)

        # log success
        self.gui_log("✅ GUI initialized.")

    def clear_thumbnail_cache(self):
        #self.thumb_cache.clear()
        self.settings.thumb_cache.cache.clear()
        self.gui_log("🧹 Thumbnail cache cleared.")


    def _finish_scan(self, folder):
        self.gui_log("✅ Scan complete. Loading thumbnails...")

        def load_images_worker():
            images = []
            while not self.image_queue.empty():
                if self.progress_popup.cancel_requested:
                    self.gui_log("❌ Loading canceled by user.")
                    break

                path = self.image_queue.get()
                images.append(path)
                
            def on_done():
                print(f"[DEBUG] Set image_paths: {len(images)} images")

                self.image_paths = images  # ✅ Correct: now running in GUI thread
                self.load_images_recursive()
                self.progress_popup.close()

            self.root.after(0, on_done)
            
            #self.images_paths = images  # or whatever your app expects
            #self.root.after(0, lambda: self.load_images_recursive())  # ✅ Load thumbnails in GUI thread
            #self.root.after(0, self.progress_popup.close)  # ✅ Close popup after thumbnails are queued

        threading.Thread(target=load_images_worker, daemon=True).start()

   
    def open_settings_dialog(self):
        from settings_manager import SettingsDialog
        dlg = SettingsDialog(self.root, self.settings)
        self.root.wait_window(dlg)  # wait until user closes
        # Re-apply visuals with new settings
        self.apply_styles()
        self.apply_main_selection_styles_after_settings()
        if hasattr(self, "reference_browser"):
            self.reference_browser.apply_ref_selection_styles_after_settings()
        self.multi_face_mode.set(self.settings.get("default_mode"))
        self.gui_log("⚙️ Preferences applied.")
        self.gui_log(f"📐 Main selection border: {self.settings.get('main_grid_sel_border')} px, color: {self.settings.get('main_grid_sel_color')}")
        self.gui_log(f"📐 Ref selection border: {self.settings.get('ref_grid_sel_border')} px, color: {self.settings.get('ref_grid_sel_color')}")


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
        
        # ✅ define confirm_cleanup inside the method so it's in scope
        
        def confirm_cleanup():
            days = self.settings.trash_retention_days
            confirm = messagebox.askyesno(
                "Confirm Trash Cleanup",
                f"Delete items in .trash older than {days} days?"
            )
            if confirm:
                removed = self.settings.cleanup_trash(days)
                messagebox.showinfo("Trash Cleanup", f"🧹 Removed {removed} old item(s) from .trash.")
                self.gui_log(f"🧹 Cleaned .trash → {removed} item(s) deleted.")

        tools.add_command(label="Clean .trash Now", command=confirm_cleanup)
        
        menubar.add_cascade(label="Tools", menu=tools)
        
        self.root.config(menu=menubar)


    def apply_styles(self):
        if not hasattr(self, "style"):
            self.style = ttk.Style()
        # main-grid style
        self.style.configure(
            "Selected.TFrame",
            background=self.settings.get("main_grid_sel_color"),
            borderwidth=int(self.settings.get("main_grid_sel_border")),
            relief="solid",
        )
        # ref-grid style
        self.style.configure(
            "RefSelected.TFrame",
            background=self.settings.get("ref_grid_sel_color"),
            borderwidth=int(self.settings.get("ref_grid_sel_border")),
            relief="solid",
        )

    # ----------- background thumbnail loader ------------
    def _current_thumb_size(self) -> int:
        """Return the current thumbnail edge (square), and also keep last_applied_thumb_size in sync."""
        size = int(self.settings.get("thumbnail_size", (120, 120))[0])
        self.last_applied_thumb_size = size
        return size
    
    def _compute_tile_size(self) -> int:
        """Tile = thumb + inner padding for the border frame."""
        return self._current_thumb_size() + 2 * 8  # 8px inner padding left+right (and top+bottom)
    
    def _update_dynamic_columns(self):
        """Re-compute how many columns fit into the canvas area."""
        try:
            canvas_width = max(self.canvas.winfo_width(), 1)
        except Exception:
            canvas_width = 1000  # safe fallback during early layout
    
        tile_w = self._compute_tile_size()
        # Include grid padding between tiles
        step = tile_w + self.tile_pad
        cols = max(1, canvas_width // step)
        self.dynamic_columns = cols
        self.gui_log(f"[DEBUG] Canvas: {canvas_width}, Columns: {self.dynamic_columns}")
    
    def _on_canvas_resize(self, _event=None):
        """Debounced reflow on resize."""
        if hasattr(self, "_relayout_pending"):
            try:
                self.root.after_cancel(self._relayout_pending)
            except Exception:
                pass
        self._relayout_pending = self.root.after(120, self._relayout)
    
    def _relayout(self):
        self._update_dynamic_columns()
        # Fast reflow: just rebuild the grid with the same images
        self.display_thumbnails()

    
    
    def load_thumbnail_async(self, image_path, label_widget):
        def task():
            cache = self.settings.thumb_cache
            cached_thumb = cache.get(image_path)

            if cached_thumb:
                self.root.after(0, lambda: label_widget.configure(image=cached_thumb))
                return

            try:
                im = Image.open(image_path).convert("RGB")
                #im.thumbnail(self.settings.thumb_cache.thumb_size)
                                
                thumb_size = self.settings.get("thumbnail_size", (120, 120))
                im.thumbnail(thumb_size)
                tkimg = ImageTk.PhotoImage(im)
                
                # Save to cache
                cache.put(image_path, tkimg, pil_image=im)

                # Apply to UI
                self.root.after(0, lambda: label_widget.configure(image=tkimg))
            except Exception as e:
                self.gui_log(f"[Thumbnail load error] {image_path}: {e}")

        threading.Thread(target=task, daemon=True).start()

    
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
                #cached = _thumbcache_get(p)
                cached = self.settings.thumb_cache.get(p)
                if cached is not None:
                    self._thumb_queue.put(("ok", p, cached))
                    continue
                try:
                    thumb_size = self.settings.get("thumbnail_size", (120, 120))
                    with Image.open(p) as im:
                        im = im.convert("RGB")                                                                      
                        im.thumbnail(thumb_size)
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
                    #_thumbcache_put(path, tkimg)
                    self.settings.thumb_cache.put(path, tkimg)
                    self._add_thumbnail_widget(path, tkimg)
                except Exception as e:
                    self.gui_log(f"[Thumb build error] {path}: {e}")
            else:
                self.gui_log(f"[Thumbnail error] {path}: {payload}")
            consumed += 1
        if not self._thumb_stop:
            self.root.after(10, self._consume_thumbs_batch)


    def _apply_main_selection_style(self, path, selected=False):
        """Apply border color/thickness to a main-grid thumbnail cell."""
        if path not in self.thumb_cells:
            return
        border = self.thumb_cells[path]["border"]
        if selected:
            border.config(
                highlightbackground=self.settings.get("main_grid_sel_color"),
                highlightthickness=int(self.settings.get("main_grid_sel_border"))
            )
        else:
            border.config(highlightthickness=0)


    def _add_thumbnail_widget(self, img_path, tkimg):
        idx = len(self.thumbnails)
        self.thumbnails.append(tkimg)
    
        color = self.settings.get("main_grid_sel_color")
        thickness = int(self.settings.get("main_grid_sel_border"))
    
        row = idx // self.dynamic_columns
        col = idx % self.dynamic_columns
    
        tile_size = self.last_applied_thumb_size + 10  # include border space
    
        # Tile container with visible border or fixed light gray bg
        cell = tk.Frame(
            self.scrollable_frame,
            bg="#cccccc",  # light gray background to show tile edge
            width=tile_size,
            height=tile_size
        )
        cell.grid(row=row, column=col, padx=self.tile_pad, pady=self.tile_pad)
        cell.grid_propagate(False)  # prevent auto-resize
    
        # Inner padding frame to host the image and highlight selection
        border = tk.Frame(
            cell,
            bg="white",
            highlightthickness=thickness,
            highlightbackground=color
        )
        border.pack(expand=True, fill=tk.BOTH, padx=2, pady=2)
    
        label = tk.Label(border, image=tkimg, bg="white", bd=0)
        label.image = tkimg
        label.pack(expand=True)
    
        self.thumb_cells[img_path] = {"cell": cell, "border": border}
    
        def toggle_selection(event=None, p=img_path):
            if p in self.selected_images:
                self.selected_images.remove(p)
                border.config(highlightthickness=0)
            else:
                self.selected_images.add(p)
                border.config(highlightbackground=color, highlightthickness=thickness)
    
        for w in (cell, border, label):
            w.bind("<Button-1>", toggle_selection)
    
        self._apply_main_selection_style(img_path, selected=(img_path in self.selected_images))

    
    def apply_main_selection_styles_after_settings(self):
        # Re-apply (e.g. after user changes color/thickness in Preferences)
        for path, node in self.thumb_cells.items():
            self._apply_main_selection_style(path, selected=(path in self.selected_images))

    # ----- embeddings rebuild (debounced + threaded) --------
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
        # === Root Layout Container ===
        root_content = ttk.Frame(self.root)
        root_content.pack(fill=tk.BOTH, expand=True)

        # === Top Bar ===
        top_frame = ttk.Frame(root_content)
        top_frame.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)

        # ✅ Folder input and control buttons
        # --- Folder Selection ---
        ttk.Label(top_frame, text="📂 Folder:").pack(side=tk.LEFT)
        ttk.Entry(top_frame, textvariable=self.selected_folder, width=60).pack(side=tk.LEFT, padx=5)
        ttk.Button(top_frame, text="Browse", command=self.browse_folder).pack(side=tk.LEFT)

        # --- Labeling Actions ---
        ttk.Button(top_frame, text="🏷️ Label Selected", command=self.label_selected).pack(side=tk.LEFT, padx=10)
        ttk.Button(top_frame, text="➕ Add to Reference", command=self.add_selected_to_reference).pack(side=tk.LEFT, padx=6)
        ttk.Button(top_frame, text="↩ Undo", command=self.undo_last_action).pack(side=tk.LEFT, padx=6)

        # --- Tools ---
        ttk.Button(top_frame, text="🧹 DB Health Check", command=self.db_health_check).pack(side=tk.LEFT, padx=10)

        # --- Review Button (starts disabled) ---
        self.btn_review = ttk.Button(top_frame, text="🧭 Review Unmatched", command=self.open_review, state="disabled")
        self.btn_review.pack(side=tk.LEFT, padx=10)

        # --- Sort Button ---
        self.btn_sort = tk.Button(
            top_frame,
            text="▶ Sort",
            bg="SystemButtonFace",
            fg="black",
            command=self.toggle_sort,
            width=18,
            relief="raised"
        )
        self.btn_sort.pack(side=tk.RIGHT, padx=10)

        # --- Face Matching Mode ---
        mode_frame = ttk.LabelFrame(top_frame, text="Face Matching Mode")
        mode_frame.pack(side=tk.RIGHT, padx=10)
        ttk.Radiobutton(mode_frame, text="Best Match", variable=self.multi_face_mode, value="best").pack(anchor=tk.W)
        ttk.Radiobutton(mode_frame, text="Multi-Match", variable=self.multi_face_mode, value="multi").pack(anchor=tk.W)
        ttk.Radiobutton(mode_frame, text="Manual", variable=self.multi_face_mode, value="manual").pack(anchor=tk.W)

        rules = (
            "Rules:\n"
            "• Best: MOVE file to the single best label.\n"
            "• Multi: COPY to all matched labels.\n"
            "• Manual: placeholder for now."
        )
        tk.Label(mode_frame, text=rules, justify="left", anchor="w", fg="#444", wraplength=320).pack(anchor=tk.W, pady=(6, 2))

        # === Zoom Bar ===
        zoom_frame = ttk.Frame(root_content)
        zoom_frame.pack(fill=tk.X, padx=10, pady=(4, 2))

        # ... [your zoom controls here] ...
        ttk.Label(zoom_frame, text="🧐 Zoom").pack(side=tk.LEFT)
        ttk.Button(zoom_frame, text="-", width=3, command=self.zoom_out).pack(side=tk.LEFT, padx=(6, 2))

        self.zoom_slider = ttk.Scale(
            zoom_frame,
            from_=60, to=240,
            orient="horizontal",
            command=self.on_zoom_change
        )
        self.zoom_slider.set(self.settings.get("thumbnail_size", (120, 120))[0])
        self.zoom_slider.pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(zoom_frame, text="+", width=3, command=self.zoom_in).pack(side=tk.LEFT, padx=(2, 6))

        # === Main Content Frame (Sidebar + Grid Area) ===
        content_frame = ttk.Frame(root_content)
        content_frame.pack(fill=tk.BOTH, expand=True)

        # --- Left Sidebar (takes full vertical height) ---
        self.left_sidebar = LeftSidebar(
            master=content_frame,
            on_folder_select=self.browse_folder,
            on_sort_change=self.change_sort_mode,
            on_filter_toggle=self.update_filters
        )
        self.left_sidebar.pack(side=tk.LEFT, fill=tk.Y, padx=(8, 4), pady=4)

        # --- Right Grid Area ---
        grid_frame = ttk.Frame(content_frame)
        grid_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # === Right Sidebar ===
        self.right_sidebar = ttk.Frame(content_frame)
        self.right_sidebar.pack(side=tk.RIGHT, fill=tk.Y, padx=(4, 8), pady=4)

        # --- Reference Browser ---
        self.reference_browser = ReferenceBrowser(
            grid_frame,
            gui_log=self.gui_log,
            rebuild_embeddings_async=self.rebuild_embeddings_async,
            undo_push=self.undo_stack.push
        )
        self.reference_browser.settings = self.settings
        self.reference_browser.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)

        # --- Scrollable Image Grid ---
        self.main_frame = ttk.Frame(grid_frame)
        self.main_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        self.canvas = tk.Canvas(self.main_frame, bg="#ffffff")
        self.scrollbar = ttk.Scrollbar(self.main_frame, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.scrollbar.set)

        self.scrollable_frame = ttk.Frame(self.canvas)
        self.canvas.create_window((0, 0), window=self.scrollable_frame, anchor='nw')
        self.scrollable_frame.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        
        self.canvas.bind("<Configure>", self._on_canvas_resize)


        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.bind("<Configure>", lambda e: self.display_thumbnails())

        _bind_vertical_mousewheel(self.canvas)

        print("[DEBUG] ReferenceBrowser settings attached:", self.reference_browser.settings)
        self.build_right_sidebar()

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
    
    # ------------------ Right Sidebar --------------------
    def build_right_sidebar(self):
        ttk.Label(self.right_sidebar, text="🎯 Reference Tools", font=("Segoe UI", 10, "bold")).pack(anchor="w", pady=(0, 6))

        # Filter Entry
        ttk.Label(self.right_sidebar, text="🔍 Label Filter:").pack(anchor="w")
        self.ref_filter_entry = ttk.Entry(self.right_sidebar)
        self.ref_filter_entry.pack(fill=tk.X, pady=(0, 4))
        self.ref_filter_entry.bind("<Return>", lambda e: self.apply_reference_filter())

        # Apply Filter Button
        ttk.Button(self.right_sidebar, text="Apply", command=self.apply_reference_filter).pack(fill=tk.X)

        # Refresh Button
        ttk.Button(self.right_sidebar, text="🔄 Refresh Labels", command=self.reference_browser.refresh_label_list).pack(fill=tk.X, pady=(6, 0))

        # Rebuild Embeddings Button
        ttk.Button(self.right_sidebar, text="🧬 Rebuild Embeddings", command=self.rebuild_embeddings_async).pack(fill=tk.X, pady=(6, 0))

        # Batch Tools Header
        ttk.Label(self.right_sidebar, text="🧹 Batch Tools:", font=("Segoe UI", 9, "bold")).pack(anchor="w", pady=(12, 2))

        ttk.Button(self.right_sidebar, text="🗑️ Delete Empty Labels", command=self.delete_empty_labels).pack(fill=tk.X)
        ttk.Button(self.right_sidebar, text="✏️ Rename Selected Label", command=self.rename_selected_label).pack(fill=tk.X, pady=(4, 0))

    # ---------------- Right Sidebar Supporting Methods ---
    
    def apply_reference_filter(self):
        label = self.ref_filter_entry.get().strip()
        self.reference_browser.label_filter.set(label)
        self.reference_browser.load_images()
        self.gui_log(f"🔍 Filter applied: {label}")

    def delete_empty_labels(self):
        from photo_sorter import delete_empty_label_folders
        removed = delete_empty_label_folders()
        self.gui_log(f"🧹 Removed {removed} empty label folders.")
        self.reference_browser.refresh_label_list()

    def rename_selected_label(self):
        current = self.reference_browser.label_filter.get()
        if not current:
            messagebox.showinfo("Rename", "No label is currently selected.")
            return
        new_name = simpledialog.askstring("Rename Label", f"Rename '{current}' to:", initialvalue=current)
        if new_name and new_name != current:
            from photo_sorter import rename_label
            rename_label(current, new_name)
            self.reference_browser.refresh_label_list(auto_select=False)
            self.reference_browser.label_filter.set(new_name)
            self.reference_browser.load_images()
            self.gui_log(f"✏️ Renamed label '{current}' → '{new_name}'")


    # --------------- inside class ImageRangerGUI ---------
    
    def change_sort_mode(self, sort_mode: str):
        self.settings.set("sort_mode", sort_mode)
        self.gui_log(f"🔃 Sorting mode changed to: {sort_mode}")
        self.refresh_image_grid()  # or scan_folder()

    def update_filters(self, filters: dict):
        self.settings.set("filter_options", filters)
        self.gui_log(f"🔍 Filters updated: {filters}")
        self.scan_folder(self.selected_folder.get())

    
    def zoom_in(self):
        current = int(float(self.zoom_slider.get()))
        new_value = min(current + 20, 240)
        self.zoom_slider.set(new_value)
        self._apply_zoom(new_value)

    def zoom_out(self):
        current = int(float(self.zoom_slider.get()))
        new_value = max(current - 20, 60)
        self.zoom_slider.set(new_value)
        self._apply_zoom(new_value)


    def on_zoom_change(self, val):
        try:
            new_size = int(float(val))
            current_size = self.settings.get("thumbnail_size", (120, 120))[0]

            # 🛑 Stop if size hasn't changed (avoid loop)
            if new_size == current_size:
                return

            if hasattr(self, "_zoom_pending"):
                self.root.after_cancel(self._zoom_pending)

            self._zoom_pending = self.root.after(
                200,
                lambda: self._apply_zoom(new_size)
            )

        except Exception as e:
            print(f"[Zoom Error] {e}")
    


    def _apply_zoom(self, new_size):
        try:
            old_size = self.last_applied_thumb_size or self.settings.get("thumbnail_size", (120, 120))[0]
            if new_size == old_size:
                return

            self.zoom_animation_step = 0
            self._animate_zoom(old_size, new_size)

        except Exception as e:
            print(f"[Zoom Error] Failed to apply zoom: {e}")

    def _animate_zoom(self, start_size, end_size, steps=None, delay=None):
        if steps is None:
            steps = self.settings.get("zoom_animation_steps", 5)
        if delay is None:
            delay = self.settings.get("zoom_animation_delay", 30)
        """
        Smoothly transition from start_size to end_size over a few frames.
        """
        if self.zoom_animation_step >= steps:
            # Final step: apply target size and reload grid
            self.settings.set("thumbnail_size", (end_size, end_size))
            self.last_applied_thumb_size = end_size

            if hasattr(self.settings.thumb_cache, "clear"):
                self.settings.thumb_cache.clear()
                print("🧹 Thumbnail cache cleared (final).")

            self.display_thumbnails()
            return

        progress = (self.zoom_animation_step + 1) / steps
        intermediate_size = int(start_size + (end_size - start_size) * progress)

        # Update zoom slider to reflect animation (optional)
        self.zoom_slider.set(intermediate_size)

        # Set thumbnail size in settings (but don't trigger reload yet)
        self.settings.set("thumbnail_size", (intermediate_size, intermediate_size))
        self.last_applied_thumb_size = intermediate_size

        self.zoom_animation_step += 1
        self.root.after(delay, lambda: self._animate_zoom(start_size, end_size, steps, delay))
        
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
        #MatchReviewPanel(self.root, self.last_unmatched_dir, self.last_output_dir, self.gui_log)
        MatchReviewPanel(self.root, self.last_unmatched_dir, self.last_output_dir, self.gui_log, self.settings)


    
    def browse_folder(self):
        folder = filedialog.askdirectory()
        if not folder:
            return

        self.selected_folder.set(folder)
        self.gui_log(f"📂 Folder selected: {folder}")
        self._cancel_thumb_job()

        self.progress_popup = ProgressPopup(self.root)
        self.image_queue = queue.Queue()

        def scan_worker():
            all_images = []
            for root, dirs, files in os.walk(folder):
                for f in files:
                    if f.lower().endswith((".jpg", ".jpeg", ".png", ".bmp", ".webp")):
                        all_images.append(os.path.join(root, f))

            total = len(all_images)
            self.root.after(0, lambda: self.progress_popup.set_total(total))

# ------------ enhanced ----------------------
            for idx, img_path in enumerate(all_images, start=1):
                if self.progress_popup.cancel_requested:
                    print("Scan cancelled.")
                    break

                self.image_queue.put(img_path)
                self.root.after(0, lambda i=idx, t=total, p=img_path:
                            self.progress_popup.update_progress(i, t, p))
            time.sleep(0.001)  # Simulate I/O delay
# --------------------------------------------------    
            self.root.after(0, lambda: self._finish_scan(folder))

        threading.Thread(target=scan_worker, daemon=True).start()

        
    def undo_last_action(self, event=None):
        """Undo the last destructive action (delete_refs / delete_label / rename_label)."""
        try:
            # --- Prefer structured stack ---
            item = None
            if isinstance(getattr(self, "undo", None), UndoStack):
                item = self.undo.pop()
            elif getattr(self, "undo_stack", None):
                item = self.undo_stack.pop()

            if not item:
                self.gui_log("Nothing to undo.")
                return

            # --- Direct callable support ---
            if callable(item):
                item()
                self.gui_log("↩ Undid last callable action.")
                return

            # --- Dict payloads ---
            if isinstance(item, dict):
                t = item.get("type")
                data = item.get("data", {})

                # -------------------------------------------------
                # Undo: Delete Selected References
                # -------------------------------------------------
                if t == "delete_refs":
                    label = data.get("label")
                    entries = data.get("items", [])
                    restored = 0

                    for e in entries:
                        # Support both new and legacy keys
                        backup = e.get("backup_path") or e.get("trashed")
                        orig = e.get("original_path")
                        if not backup or not orig:
                            continue
                        try:
                            os.makedirs(os.path.dirname(orig), exist_ok=True)
                            if os.path.exists(backup):
                                shutil.move(backup, orig)
                                insert_reference(orig, label)
                                self.gui_log(f"✅ Restored reference: {orig}")
                                restored += 1
                        except Exception as ex:
                            self.gui_log(f"❌ Undo restore failed for {orig}: {ex}")

                    if label:
                        try:
                            _write_or_refresh_metadata(label)
                        except Exception:
                            pass

                        # Refresh UI + embeddings
                        self.reference_browser.refresh_label_list(auto_select=False)
                        if self.reference_browser.label_filter.get() == label:
                            self.reference_browser.load_images()
                        self.rebuild_embeddings_async(only_label=label)

                    self.gui_log(f"↩ Restored {restored} reference(s) to '{label}'.")
                    return

                # -------------------------------------------------
                # Undo: Delete Entire Label
                # -------------------------------------------------
                if t == "delete_label":
                    label = data.get("label")
                    trashed_folder = data.get("trashed_folder")
                    thr = float(data.get("threshold", 0.3))

                    if not label:
                        self.gui_log("❌ Undo failed: missing label.")
                        return

                    if not trashed_folder or trashed_folder == "recycle":
                        self.gui_log("⚠️ Cannot auto-undo: label was sent to the system Recycle Bin.")
                        return

                    dest_folder = get_label_folder_path(label)
                    try:
                        # remove empty placeholder folder if it exists
                        if os.path.isdir(dest_folder) and not os.listdir(dest_folder):
                            os.rmdir(dest_folder)
                    except Exception:
                        pass

                    try:
                        os.makedirs(os.path.dirname(dest_folder), exist_ok=True)
                        shutil.move(trashed_folder, dest_folder)
                    except Exception as ex:
                        self.gui_log(f"❌ Undo restore of label failed: {ex}")
                        return

                    # Reinsert DB entries
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

                    # Refresh UI + embeddings
                    self.reference_browser.refresh_label_list(auto_select=False)
                    self.reference_browser.label_filter.set(label)
                    self.reference_browser.load_images()
                    self.rebuild_embeddings_async(only_label=label)

                    self.gui_log(f"↩ Restored label '{label}' ({restored} items).")
                    return

                # -------------------------------------------------
                # Undo: Rename Label
                # -------------------------------------------------
                if t == "rename_label":
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
                            self.gui_log(f"✅ Restored file: {old_path}")
                            restored += 1
                        except Exception as e:
                            self.gui_log(f"❌ Rename undo failed: {e}")

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

                    try:
                        new_folder = get_label_folder_path(new)
                        if os.path.isdir(new_folder) and not os.listdir(new_folder):
                            shutil.rmtree(new_folder)
                    except Exception:
                        pass

                    # Refresh UI + embeddings
                    self.reference_browser.refresh_label_list(auto_select=False)
                    self.reference_browser.label_filter.set(old)
                    self.reference_browser.load_images()
                    self.rebuild_embeddings_async(only_label=old)

                    self.gui_log(f"↩ Undid label rename: restored '{old}' ({restored} items).")
                    return

            # --- If nothing matched ---
            self.gui_log(f"Undo item format not recognized: {item!r}")

        except Exception as e:
            self.gui_log(f"Undo failed: {e}")


    # ---------------- image grid ----------------
    def load_images_recursive(self):
#        self.image_paths = []
#        exts = (".jpg", ".jpeg", ".png", ".bmp", ".webp")
#        for root_dir, _, files in os.walk(folder):
#            for f in files:
#                if f.lower().endswith(exts):
#                    self.image_paths.append(os.path.join(root_dir, f))
#        self.gui_log(f"🖼️ Found {len(self.image_paths)} images. Rendering grid…")
        self.gui_log(f"🖼️ Loading {len(self.image_paths)} images into grid…")
        self.display_thumbnails()

    def display_thumbnails(self):
        if not self.image_paths:
            return
    
        # Clear previous thumbnail widgets
        for widget in self.scrollable_frame.winfo_children():
            widget.destroy()
        self.thumbnails.clear()
        self.thumb_cells.clear()
        gc.collect()

        # 🧭 Sync zoom bar and size
        zoom_size = self.settings.get("thumbnail_size", (120, 120))[0]
        self.zoom_slider.set(zoom_size)
        self.last_applied_thumb_size = int(zoom_size)
        
        # Calculate dynamic columns based on canvas width
        canvas_width = self.canvas.winfo_width()
        tile_size = self.last_applied_thumb_size + 10  # thumbnail + padding
        columns = max(1, canvas_width // tile_size)
        self.dynamic_columns = columns  # store for use in thumbnail placement
        
        print(f"[DEBUG] Canvas: {canvas_width}, Columns: {columns}")
        
        #self.last_applied_thumb_size = int(self.zoom_slider.get())

        # start background building
        self._start_thumb_job(self.image_paths)

        self.scrollable_frame.update_idletasks()


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
