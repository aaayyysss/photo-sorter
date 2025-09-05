# components/top_controls.py

import tkinter as tk
from tkinter import filedialog, ttk
from helpers.logger import gui_log
from photo_sorter import (
    build_reference_embeddings_from_db,
    sort_photos_with_embeddings_from_folder_using_db
)
import threading


class TopControls(tk.Frame):
    def __init__(self, parent):
        super().__init__(parent)
        self.pack(fill=tk.X, padx=10)

        self.folder_path = tk.StringVar()
        self.match_mode = tk.StringVar(value="multi")

        # Folder entry + Browse
        tk.Label(self, text="📁 Folder:").pack(side=tk.LEFT, padx=(0, 5))
        self.entry = tk.Entry(self, textvariable=self.folder_path, width=60)
        self.entry.pack(side=tk.LEFT)
        tk.Button(self, text="Browse", command=self.browse).pack(side=tk.LEFT, padx=5)

        # Label Selected
        tk.Button(self, text="🖋️ Label Selected", command=self.label_selected).pack(side=tk.LEFT, padx=5)

        # Match Mode
        mode_frame = tk.LabelFrame(self, text="Face Matching Mode")
        mode_frame.pack(side=tk.RIGHT, padx=(20, 0))

        for mode in ["multi", "best", "manual"]:
            tk.Radiobutton(
                mode_frame,
                text=mode.capitalize().replace("multi", "Multi-Match").replace("best", "Best Match").replace("manual", "Manual"),
                variable=self.match_mode,
                value=mode
            ).pack(anchor=tk.W)

        tk.Button(mode_frame, text="🔍 Start Sorting", command=self.start_sorting).pack(pady=2)

    def browse(self):
        path = filedialog.askdirectory()
        if path:
            self.folder_path.set(path)
            gui_log(f"📂 Folder selected: {path}")

    def label_selected(self):
        gui_log("🖋️ Label selected placeholder (hook to reference label logic).")

    def start_sorting(self):
        folder = self.folder_path.get()
        if not folder:
            gui_log("⚠️ Please select a folder to sort.")
            return
    
        out_dir = folder + "_sorted"
        unmatched_dir = folder + "_unmatched"
    
        threading.Thread(
            target=sort_photos_with_embeddings_from_folder_using_db,
            args=(folder, out_dir, unmatched_dir, "reference_data.db", gui_log, self.match_mode.get()),
            daemon=True
        ).start()
  
    def build_embeddings(self):
        threading.Thread(
            target=build_reference_embeddings_from_db,
            args=("reference_data.db", "buffalo_l", gui_log),
            daemon=True
        ).start()

