# gui_reference_labeler
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

from PIL import Image, ImageTk

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

try:
    from photo_sorter import build_reference_embeddings_for_label as _build_label_embeddings
except Exception:
    _build_label_embeddings = None  # fallback to full rebuild if not available

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
def get_reference_root() -> str:
    root = SETTINGS.get("reference_root") or os.path.join(os.getcwd(), "References")
    try:
        os.makedirs(root, exist_ok=True)
    except Exception:
        # fallback to cwd if path is not permitted
        root = os.path.join(os.getcwd(), "References")
        os.makedirs(root, exist_ok=True)
    return root

def set_reference_root(path: str):
    SETTINGS["reference_root"] = path
    save_settings(SETTINGS)

def get_label_folder_path(label: str) -> str:
    return os.path.join(get_reference_root(), label)


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
        
def get_reference_root() -> str:
#    os.makedirs(root, exist_ok=True)
#    prefer user setting; else default to ./References under the current app folder
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

# ---- Simple Undo Stack ------------------------------------------------------
class UndoStack:
    def __init__(self, log_cb=None):
        self.stack = []
        self._log = log_cb or (lambda *a, **k: None)

    def push(self, action: dict):
        """
        action examples:
          {"type": "delete_ref",   "label": str, "path": str}
          {"type": "delete_label", "label": str, "paths": [str, ...], "threshold": float|None, "folder": str|None}
        """
        self.stack.append(action)

    def pop(self):
        if not self.stack:
            self._log("ℹ️ Nothing to undo.")
            return None
        return self.stack.pop()

    def clear(self):
        self.stack.clear()

# ---- Reference Browser (top strip) ---------------------------

class ReferenceBrowser(ttk.Frame):
    """
    Shows reference thumbnails for the currently selected label.
    - Click a thumbnail to select/unselect (highlight).
    - Delete Selected removes only selected reference entries.
    - Delete Label removes all entries for the chosen label.
    """
    def __init__(self, master, gui_log, rebuild_embeddings_async, push_undo, *args, **kwargs):
        super().__init__(master, *args, **kwargs)
        self.gui_log = gui_log
        self.rebuild_embeddings_async = rebuild_embeddings_async
        self.push_undo = push_undo
        
        self.label_filter = tk.StringVar()
        self.selected_paths = set()
        self.thumb_widgets = {}

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

        controls = ttk.Frame(self)
        controls.pack(fill=tk.X, pady=5)

        self.label_menu = ttk.Combobox(controls, textvariable=self.label_filter, values=_labels_from_entries(),  state="readonly")
        
        ttk.Button(controls, text="🧭 Open Folder", command=self.open_label_folder).pack(side=tk.LEFT, padx=6)
        ttk.Button(controls, text="🎚️ Threshold…", command=self.edit_threshold).pack(side=tk.LEFT, padx=6)
       
        self.label_menu.pack(side=tk.LEFT)
        self.label_menu.bind("<<ComboboxSelected>>", lambda e: self.load_images())

        ttk.Button(controls, text="🔄 Reload", command=self.load_images).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Button(controls, text="❌ Delete Selected", command=self.delete_selected_refs).pack(side=tk.LEFT, padx=6)
        ttk.Button(controls, text="🗑️ Delete Label", command=self.delete_label_all).pack(side=tk.LEFT, padx=6)
        ttk.Button(controls, text="✏️ Rename Label", command=self.rename_label).pack(side=tk.LEFT, padx=6)

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

        deleted = 0
        entries = get_all_references()
        targets = set(self.selected_paths)
        for (_id, lbl, path) in entries:
            if lbl == label and path in targets:
                # Remove file if it exists (we now copy into ReferenceRoot/<label>)
                try:
                    delete_reference(path)
                    deleted += 1
                    # push to Undo (now using self.app)
                    self.push_undo({"type": "delete_ref", "label": label, "path": path})
                except Exception as e:
                    self.gui_log(f"⚠️ Could not delete '{path}': {e}")
                    
        self.gui_log(f"🗑️ Deleted {deleted} reference(s) from '{label}'. Rebuilding embeddings…")
        self.load_images()
        # use the injected callback, not self.master
        self.rebuild_embeddings_async(only_label=label)

    def delete_label_all(self):
        label = self.label_filter.get()
        if not label:
            messagebox.showwarning("No Label", "Select a label to delete.")
            return
            
        if not messagebox.askyesno("Delete Label", f"Delete ALL references for label '{label}'?"):
            return
    
        # Gather everything BEFORE we delete (for Undo)
        try:
            entries = get_all_references()
        except Exception as e:
            messagebox.showerror("Delete Label", f"Failed to read DB: {e}")
            return
    
        paths_for_label = [path for (_id, lbl, path) in entries if lbl == label]
    
        # capture metadata for Undo
        try:
            threshold = get_threshold_for_label(label)
        except Exception:
            threshold = None
    
        try:
            # we want the intended folder path (even if missing)
            folder = get_label_folder_path(label)
        except Exception:
            folder = None
    
        # Delete references
        deleted = 0
        for (_id, lbl, path) in entries:
            if lbl == label:
                try:
                    delete_reference(path)
                    deleted += 1
                except Exception as e:
                    self.gui_log(f"⚠️ Could not delete reference '{path}': {e}")
    
        # Remove on-disk folder
        try:
            if folder and os.path.isdir(folder):
                shutil.rmtree(folder)
        except Exception as e:
            self.gui_log(f"⚠️ Could not remove folder for '{label}': {e}")
    
        # Remove label metadata
        try:
            delete_label(label)
        except Exception:
            pass
    
        # Push a single UNDO action for the whole label
        try:
            self.push_undo({
                "type": "delete_label",
                "label": label,
                "paths": paths_for_label,
                "threshold": threshold,
                "folder": folder
            })
        except Exception:
            pass
    
        # UI refresh
        self.gui_log(f"🗑️ Deleted label '{label}' ({deleted} item(s)). Rebuilding embeddings…")
        try:
            self.label_menu.configure(values=get_all_labels())
        except Exception:
            self.label_menu.configure(values=_labels_from_entries())
    
        self.label_filter.set("")
        self.load_images()
    
        # PARTIAL rebuild for just this label (flush it from memory)
       
        self.rebuild_embeddings_async(only_label=label)

    def rename_label(self):
        current = self.label_filter.get()
        if not current:
            return
        new_label = simpledialog.askstring("Rename Label", f"Rename label '{current}' to:")
        if not new_label or new_label == current:
            return

        entries = get_all_references()
        moved = 0

        # Move files on disk from old folder to new folder (if they are inside the reference root)
        old_folder = get_label_folder_path(current)
        new_folder = get_label_folder_path(new_label)
        os.makedirs(new_folder, exist_ok=True)

        for (_id, lbl, path) in entries:
            if lbl == current:
                new_path = path
                try:
                    # If file lives inside old_folder, move it to new_folder (preserve filename; handle collisions)
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
                    # If move fails, keep original path in DB
                    pass

                # Reinsert with new label + new_path (if changed)
                insert_reference(new_path, new_label)
                moved += 1

        # Update threshold & metadata
        thr = get_threshold_for_label(current)
        set_threshold_for_label(new_label, thr)
        insert_or_update_label(new_label, new_folder, thr)

        # Clean up old folder if empty
        try:
            if os.path.isdir(old_folder) and not os.listdir(old_folder):
                shutil.rmtree(old_folder)
        except Exception:
            pass

        # Refresh UI
        self.label_filter.set(new_label)
        self.refresh_label_list(auto_select=False)
        self.load_images()
        self.gui_log(f"✏️ Renamed/moved {moved} items to '{new_label}'. Rebuilding embeddings…")
        self.rebuild_embeddings_async()

        # Rewrite metadata files
        _write_or_refresh_metadata(new_label, thr)
        
    def refresh_label_list(self, auto_select=True):
        labels = _labels_from_entries()
        self.label_menu.configure(values=labels)
        if auto_select:
            # If nothing selected, pick the first label (if any) to avoid "no label selected".
            current = self.label_filter.get()
            if not current and labels:
                self.label_filter.set(labels[0])
                # Immediately load images for that label
                self.load_images()

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
        # small inline prompt using a single dialog row
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
            # optional: rebuild embeddings right away
            self.rebuild_embeddings_async()
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

class ImageRangerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Photo Sorter - Reference Labeling")

        self.style = ttk.Style()
        
        self.sorting = False
        self.sort_thread = None
        self.sort_stop_event = None  # threading.Event when running

        self.style.configure("SortGreen.TButton", foreground="white", background="#22aa22")
        self.style.map("SortGreen.TButton", background=[("active", "#1c8f1c")])

        self.style.configure("SortRed.TButton", foreground="white", background="#cc3333")
        self.style.map("SortRed.TButton", background=[("active", "#a62828")])

        self._build_menu()

        self.log = BottomLogFrame(self.root)
        self.log.pack(side=tk.BOTTOM, fill=tk.X)
        self.gui_log = make_gui_logger(self.log)

        # Undo + debounce state
        self.undo = UndoStack(self.gui_log)
        self.root.bind_all("<Control-z>", lambda e: self.undo_last())
        
        self._rebuild_pending = None
        self._rebuild_running = False
        self._rebuild_next_label = None

        self.selected_folder = tk.StringVar()
        self.image_paths = []
        self.thumbnails = []
        self.selected_images = set()

        self.multi_face_mode = tk.StringVar(value=SETTINGS["default_mode"])

        self.last_unmatched_dir = None
        self.last_output_dir = None        

        self.apply_styles()
        self.build_layout()
        
        # After building layout:
        self.reference_browser.refresh_label_list(auto_select=True)

        self.gui_log("✅ GUI initialized.")
        self._rebuild_pending = None
        self._rebuild_running = False
        self._rebuild_next_label = None
        
        self.undo = UndoStack(self.gui_log)        # <-- create it here
        self.root.bind_all("<Control-z>", lambda e: self.undo_last())  # optional hotkey


    def rebuild_embeddings_async(self, only_label: str | None = None):
        """Debounce and rebuild embeddings (optionally only for one label)."""
        # cancel any pending call
        if getattr(self, "_rebuild_pending", None):
            try:
                self.root.after_cancel(self._rebuild_pending)
            except Exception:
                pass
            self._rebuild_pending = None
    
        # slight debounce to coalesce multiple rapid calls
        self._rebuild_pending = self.root.after(
            200, lambda ol=only_label: self._rebuild_do(ol)
        )
    
    def _rebuild_do(self, only_label: str | None):
        """Worker launcher for (partial) rebuild."""
        self._rebuild_pending = None  # clear pending flag now
    
        def _work():
            model_dir = os.path.join(os.path.dirname(__file__), "buffalo_l")
            try:
                if only_label and _build_label_embeddings:
                    self.gui_log(f"⚙️ Rebuilding embeddings for '{only_label}'…")
                    _build_label_embeddings(
                        db_path=DB_PATH,
                        model_dir=model_dir,
                        label=only_label,
                        log_callback=self.gui_log
                    )
                else:
                    self.gui_log("⚙️ Rebuilding reference embeddings…")
                    build_reference_embeddings_from_db(
                        DB_PATH, model_dir, self.gui_log
                    )
                self.gui_log("✅ Embeddings rebuilt.")
            except Exception as e:
                self.gui_log(f"❌ Embedding rebuild failed: {e}")
    
        threading.Thread(target=_work, daemon=True).start()
        
# ---------------background thumbnail loader-------------------
    def _cancel_thumb_job(self):
        # signal any ongoing loader to stop
        self._thumb_stop = True

    def _start_thumb_job(self, paths):
        """
        Stream thumbnails into the grid in small bursts.
        """
        # cancel any existing job
        self._cancel_thumb_job()
        self._thumb_stop = False
        self._thumb_executor = getattr(self, "_thumb_executor", None) or ThreadPoolExecutor(max_workers=4)
        self._thumb_queue = queue.Queue(maxsize=256)

        # producer: decode PIL thumbnails in thread pool
        def producer():
            for p in paths:
                if self._thumb_stop:
                    break
                # cached?
                cached = _thumbcache_get(p)
                if cached is not None:
                    self._thumb_queue.put(("ok", p, cached))
                    continue

                try:
                    with Image.open(p) as im:
                        im = im.convert("RGB")
                        im.thumbnail(THUMBNAIL_SIZE)
                        # send raw bytes to main thread; Tk PhotoImage must be created on UI thread
                        bio = im.tobytes()
                        size = im.size
                    self._thumb_queue.put(("raw", p, (bio, size)))
                except Exception as e:
                    self._thumb_queue.put(("err", p, str(e)))
            # signal done
            self._thumb_queue.put(("done", None, None))

        threading.Thread(target=producer, daemon=True).start()
        self._consume_thumbs_batch()

    def _consume_thumbs_batch(self):
        """
        Consume a small batch from the queue on the UI thread, then reschedule self.
        """
        BATCH = 24  # tune for UI smoothness
        consumed = 0
        while consumed < BATCH:
            try:
                kind, path, payload = self._thumb_queue.get_nowait()
            except queue.Empty:
                break

            if kind == "done":
                # final GC nudge
                gc.collect()
                return
            if self._thumb_stop:
                # drain quickly
                continue
            if kind == "ok":
                # already a PhotoImage in cache
                thumb = payload
                self._add_thumbnail_widget(path, thumb)
            elif kind == "raw":
                # build PhotoImage here (UI thread)
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

        # schedule next burst
        if not self._thumb_stop:
            self.root.after(10, self._consume_thumbs_batch)

    def _add_thumbnail_widget(self, img_path, tkimg):
        """Create the thumbnail cell for a single image path."""
        idx = len(self.thumbnails)  # sequential placement
        self.thumbnails.append(tkimg)

        frame = ttk.Frame(self.scrollable_frame, borderwidth=2, relief="solid", style="TFrame")
        frame.grid(row=idx // 6, column=idx % 6, padx=5, pady=5)

        label = ttk.Label(frame, image=tkimg)
        label.image = tkimg  # keep reference
        label.pack()

        def toggle_selection(p=img_path, f=frame):
            if p in self.selected_images:
                self.selected_images.remove(p)
                f.configure(style="TFrame")
            else:
                self.selected_images.add(p)
                f.configure(style="Selected.TFrame")
        label.bind("<Button-1>", lambda e, path=img_path, fr=frame: toggle_selection(path, fr))
# -------------------------------------------------

    def _on_settings_saved(self, values: dict):
        SETTINGS.update(values)
        save_settings(SETTINGS)
        self.apply_styles()
        self.multi_face_mode.set(SETTINGS["default_mode"])
        self.reference_browser.refresh_label_list(auto_select=False)
        self.gui_log("⚙️ Preferences saved and applied.")

    def open_settings_dialog(self):
        SettingsDialog(self.root, SETTINGS, self._on_settings_saved)

    #def rebuild_embeddings_async(self, only_label: str | None = None):
    #    model_dir = os.path.join(os.path.dirname(__file__), "buffalo_l")
    #    title = "Building Embeddings"
    #    msg = "Building reference embeddings…" if not only_label else f"Rebuilding embeddings for '{only_label}'…"
    #    progress = _ModalProgress(self.root, title=title, message=msg)

    #    def _runner():
    #        try:
    #            if only_label:
    #                from photo_sorter import build_reference_embeddings_for_labels
    #                build_reference_embeddings_for_labels(DB_PATH, model_dir, [only_label], self.gui_log)
    #            else:
    #                from photo_sorter import build_reference_embeddings_from_db
    #                build_reference_embeddings_from_db(DB_PATH, model_dir, self.gui_log)
    #            self.gui_log("✅ Embeddings rebuilt.")
    #        except Exception as e:
    #            self.gui_log(f"❌ Embedding rebuild failed: {e}")
    #            self.root.after(0, lambda: messagebox.showerror("Embeddings", str(e)))
    #        finally:
    #            self.root.after(0, progress.close)
    #
    #    threading.Thread(target=_runner, daemon=True).start()

    def build_layout(self):
        top_frame = ttk.Frame(self.root)
        top_frame.pack(side=tk.TOP, fill=tk.X, padx=10, pady=5)

        ttk.Label(top_frame, text="📂 Folder:").pack(side=tk.LEFT)
        ttk.Entry(top_frame, textvariable=self.selected_folder, width=60).pack(side=tk.LEFT, padx=5)

        ttk.Button(top_frame, text="Browse", command=self.browse_folder).pack(side=tk.LEFT)
        ttk.Button(top_frame, text="🏷️ Label Selected", command=self.label_selected).pack(side=tk.LEFT, padx=10)
        ttk.Button(top_frame, text="➕ Add to Reference", command=self.add_selected_to_reference).pack(side=tk.LEFT, padx=6)

        ttk.Button(top_frame, text="🧹 DB Health Check", command=self.db_health_check).pack(side=tk.LEFT, padx=10)
        ttk.Button(top_frame, text="↩ Undo", command=self.undo_last).pack(side=tk.LEFT, padx=6)

        self.btn_review = ttk.Button(top_frame, text="🧭 Review Unmatched", command=self.open_review, state="disabled")
        self.btn_review.pack(side=tk.LEFT, padx=10)
        
        self.btn_sort = tk.Button(
            top_frame,
            text="▶ Sort",
            bg="SystemButtonFace",   # default system color
            fg="black",
            command=self.toggle_sort,
            width=18,                # adjust width so text fits nicely
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
            self.rebuild_embeddings_async,  # pass method
            self.undo.push,                 # pass Undo push function
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
        
# ---------------- Implement undo_last ---------------------
    def undo_last(self):
        action = self.undo.pop()
        if not action:
            return
    
        t = action.get("type")
    
        if t == "delete_ref":
            lbl = action.get("label")
            pth = action.get("path")
            try:
                insert_reference(pth, lbl)
                self.reference_browser.refresh_label_list(auto_select=False)
                if self.reference_browser.label_filter.get() == lbl:
                    self.reference_browser.load_images()
                self.rebuild_embeddings_async(only_label=lbl)
                self.gui_log(f"↩ Restored reference to '{lbl}': {pth}")
            except Exception as e:
                self.gui_log(f"Undo failed (delete_ref): {e}")
    
        elif t == "delete_label":
            lbl       = action.get("label")
            paths     = action.get("paths", [])
            threshold = action.get("threshold", 0.3)
            folder    = action.get("folder")
    
            try:
                # ensure folder exists (prefer previously stored folder, else default under Reference Root)
                if not folder or not isinstance(folder, str) or not folder.strip():
                    folder = os.path.join(get_reference_root(), lbl)
                try:
                    os.makedirs(folder, exist_ok=True)
                except Exception:
                    pass
                # restore label metadata (folder + threshold)
                try:
                    insert_or_update_label(lbl, folder, threshold)
                except Exception:
                    pass
                # restore all references
                restored = 0
                for p in paths:
                    try:
                        insert_reference(p, lbl)
                        restored += 1
                    except Exception:
                        pass
                # UI refresh
                self.reference_browser.refresh_label_list(auto_select=False)
                self.reference_browser.label_filter.set(lbl)
                self.reference_browser.load_images()

                # partial rebuild for restored label
                self.rebuild_embeddings_async(only_label=lbl)

                self.gui_log(f"↩ Restored label '{lbl}' with {restored} reference(s).")
            except Exception as e:
                self.gui_log(f"Undo failed (delete_label): {e}")
    
        else:
            self.gui_log(f"ℹ️ Unknown undo type: {t}")

# ---------------------------------------------------    
    def _confirm_modal(self, title: str, message: str) -> bool:
        """Blocking, truly modal Yes/No dialog centered over the main window."""
        dlg = tk.Toplevel(self.root)
        dlg.title(title)
        dlg.resizable(False, False)
        dlg.transient(self.root)     # stay on top of parent
        dlg.grab_set()               # modal grab: block all other windows

        # --- content ---
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

        # keyboard shortcuts
        dlg.bind("<Return>", lambda e: on_yes())
        dlg.bind("<Escape>", lambda e: on_no())

        # center over parent
        dlg.update_idletasks()
        x = self.root.winfo_rootx()
        y = self.root.winfo_rooty()
        w = self.root.winfo_width()
        h = self.root.winfo_height()
        ww = dlg.winfo_reqwidth()
        wh = dlg.winfo_reqheight()
        dlg.geometry(f"+{x + (w//2 - ww//2)}+{y + (h//2 - wh//2)}")

        self.root.wait_window(dlg)   # block until closed
        return result["ok"]

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
        # clear UI frame
        for widget in self.scrollable_frame.winfo_children():
            widget.destroy()
        # release references; let GC reclaim Tk photo memory
        self.thumbnails.clear()
        gc.collect()
        # stream thumbnails instead of decoding all at once
        self._start_thumb_job(self.image_paths)
        for idx, img_path in enumerate(self.image_paths):
            try:
                with Image.open(img_path) as im:
                    im = im.convert("RGB")
                    im.thumbnail(THUMBNAIL_SIZE)
                    thumb = ImageTk.PhotoImage(im)

                frame = ttk.Frame(self.scrollable_frame, borderwidth=2, relief="solid", style="TFrame")
                frame.grid(row=idx // 6, column=idx % 6, padx=5, pady=5)

                label = ttk.Label(frame, image=thumb)
                label.image = thumb
                label.pack()

                def toggle_selection(p=img_path, f=frame):
                    if p in self.selected_images:
                        self.selected_images.remove(p)
                        f.configure(style="TFrame")
                    else:
                        self.selected_images.add(p)
                        f.configure(style="Selected.TFrame")

                label.bind("<Button-1>", lambda e, path=img_path, fr=frame: toggle_selection(path, fr))
                self.thumbnails.append(thumb)
            except Exception as e:
                self.gui_log(f"[Thumbnail error] {img_path}: {e}")

    def label_selected(self):
        if not self.selected_images:
            messagebox.showwarning("No Selection", "Please select images to label.")
            return
        # One compact dialog for name + threshold (default 0.3)
        dlg = CreateLabelDialog(self.root, initial_name="", initial_threshold=0.3)
        self.root.wait_window(dlg)
        if not dlg.result:
            return
        label, threshold = dlg.result
# --------------------------------
        for path in self.selected_images:
            # Copy to ReferenceRoot/<label>/…
            dst = _safe_copy_to_label_folder(path, label, keep_original_name=True)
            # Insert the *copied* path into DB
            insert_reference(dst, label)

        # threshold in DB (update/seed)
        set_threshold_for_label(label, threshold)

        # Ensure label metadata row exists and points to our folder
        default_folder = get_label_folder_path(label)  # creates folder too
        os.makedirs(default_folder, exist_ok=True)
        insert_or_update_label(label, default_folder, threshold)

        # Write/refresh metadata.json in the label folder
        _write_or_refresh_metadata(label, threshold)
# -------------------------------  
        messagebox.showinfo("Saved", f"{len(self.selected_images)} images labeled as '{label}'")
        self.selected_images.clear()
        self.display_thumbnails()
        
        # new:
        self.reference_browser.refresh_label_list()
        # if a specific label is current, select it again:
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
            # Let user create a new label (with threshold). We won't use threshold here,
            # but we seed metadata so it's consistent.
            dlg = CreateLabelDialog(self.root, initial_name="", initial_threshold=0.3)
            self.root.wait_window(dlg)
            if not dlg.result:
                return
            current_label, thr = dlg.result
            # Seed metadata row + folder + metadata.json
            default_folder = get_label_folder_path(current_label)
            os.makedirs(default_folder, exist_ok=True)
            set_threshold_for_label(current_label, thr)
            insert_or_update_label(current_label, default_folder, thr)
            _write_or_refresh_metadata(current_label, thr)
      
        for p in self.selected_images:
            dst = _safe_copy_to_label_folder(p, current_label, keep_original_name=True)
            insert_reference(dst, current_label)
            self.undo.push({"type":"add_ref","label": current_label,"path": p})

        # Optional: update metadata based on existing threshold
        _write_or_refresh_metadata(current_label)

        self.gui_log(f"➕ Added {len(self.selected_images)} image(s) to reference label '{current_label}'. Rebuilding embeddings…")
        messagebox.showinfo("Reference", f"Added {len(self.selected_images)} image(s) to '{current_label}'.")


        self.selected_images.clear()
        self.display_thumbnails()
        self.reference_browser.refresh_label_list(auto_select=False)
        if self.reference_browser.label_filter.get() == current_label:
            self.reference_browser.load_images()
        self.rebuild_embeddings_async(only_label=current_label)      

# ------------- old ----------------------------
#    def run_sorting_thread(self):
#        threading.Thread(target=self.start_sorting, daemon=True).start()

#    def start_sorting(self):
#        ref_list = get_all_references()
#        if not ref_list:
#            messagebox.showwarning("No References", "Please label reference images first.")
#            return

#        model_dir = os.path.join(os.path.dirname(__file__), "buffalo_l")

#       def log_callback(msg):
#            self.gui_log(msg)

#        self.gui_log("⚙️ Building reference embeddings…")
#        build_reference_embeddings_from_db(DB_PATH, model_dir, log_callback)

#        inbox = filedialog.askdirectory(title="Select Inbox Folder to Sort")
#        if not inbox:
#            return
#        output = filedialog.askdirectory(title="Select Output Folder for Sorted Photos")
#        if not output:
#            return

#        unmatched = os.path.join(output, "_unmatched")
#        match_mode = self.multi_face_mode.get()

#        self.gui_log(f"🚀 Sorting started → mode: {match_mode}")
#        sort_photos_with_embeddings_from_folder_using_db(
#            inbox_dir=inbox,
#            output_dir=output,
#            unmatched_dir=unmatched,
#            db_path=DB_PATH,
#            log_callback=log_callback,
#            match_mode=match_mode,
#            move_files=True,
#            keep_original_filenames=True
#        )
#        self.gui_log("✅ Sorting complete.")

#        self.last_unmatched_dir = unmatched
#        self.last_output_dir = output
#        try:
#            self.btn_review.configure(state="normal")
#        except Exception:
#            pass

#        if messagebox.askyesno("Review", "Open review panel for unmatched images now?"):
#            self.open_review()
#        else:
#            self.gui_log("ℹ️ You can review later via '🧭 Review Unmatched'.")

# -----------------NEW ----------------------
    def start_sort_flow(self):
        # Make sure we have references
        ref_list = get_all_references()
        if not ref_list:
            messagebox.showwarning("No References", "Please label reference images first.")
            return

        model_dir = os.path.join(os.path.dirname(__file__), "buffalo_l")

        def log_callback(msg):
            self.gui_log(msg)

        # Rebuild embeddings before sorting
        self.gui_log("⚙️ Building reference embeddings…")
        try:
            build_reference_embeddings_from_db(DB_PATH, model_dir, log_callback)
        except Exception as e:
            messagebox.showerror("Embeddings", f"Failed to build embeddings: {e}")
            return

        # Rebuild embeddings before sorting (modal progress)
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

        # Ask for folders
        inbox = filedialog.askdirectory(title="Select Inbox Folder to Sort")
        if not inbox:
            return
        output = filedialog.askdirectory(title="Select Output Folder for Sorted Photos")
        if not output:
            return

        unmatched = os.path.join(output, "_unmatched")
        match_mode = self.multi_face_mode.get()

        # Prepare stop event + thread
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
                    model_dir=model_dir,   # pass through
                )
                if self.sort_stop_event.is_set():
                    self.gui_log("⛔ Sorting stopped by user.")
                else:
                    self.gui_log("✅ Sorting complete.")
                # remember paths for review
                self.last_unmatched_dir = unmatched
                self.last_output_dir = output
                try:
                    self.btn_review.configure(state="normal")
                except Exception:
                    pass
            except Exception as e:
                self.gui_log(f"❌ Sorting error: {e}")
            finally:
                # back to idle
                self.root.after(0, self._set_sort_idle)

        self.sort_thread = threading.Thread(target=worker, daemon=True)
        self.sort_thread.start()
 
# -------------------------------------------
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

    def _set_sort_idle(self):
        self.sorting = False
        self.btn_sort.configure(
            text="▶ Sort",
            bg="SystemButtonFace",
            fg="black",
            relief="raised"
        )

    def _set_sort_running(self):
        self.sorting = True
        self.btn_sort.configure(
            text="🟢 Sorting… (click to stop)",
            bg="#22aa22",   # green background
            fg="white",     # white text
            relief="sunken"
        )

    def _set_sort_stopping(self):
        self.btn_sort.configure(
            text="🛑 Stop (stopping…)",
            bg="#cc3333",   # red background
            fg="white",
            relief="sunken"
        )

    def toggle_sort(self):
        if not self.sorting:
            # start
            self.start_sort_flow()
        else:
            # ask to stop
#            if messagebox.askyesno("Stop Sorting", "Are you sure you want to stop sorting?"):
            # NEW (truly modal, blocks interaction):
            if self._confirm_modal("Stop Sorting", "Are you sure you want to stop sorting?"):
                if self.sort_stop_event:
                    self.sort_stop_event.set()
                self._set_sort_stopping()

# -----------------------------------------------------------

if __name__ == '__main__':
    root = tk.Tk()
    app = ImageRangerGUI(root)
    root.mainloop()
