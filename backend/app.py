import os
import shutil
import json
import string
from datetime import datetime
from flask import Flask, request, jsonify, send_from_directory
from flask_socketio import SocketIO
from photo_sorter import (
    build_reference_embeddings,
    sort_photos_with_embeddings,
    release_resources,
    save_ref_artifacts,
    set_device,
)

UPLOAD_FOLDER = "uploads"
REFS_FOLDER = os.path.join(UPLOAD_FOLDER, "references")
INBOX_FOLDER = os.path.join(UPLOAD_FOLDER, "inbox")
SORTED_FOLDER = os.path.join(UPLOAD_FOLDER, "sorted")
LOGS_FOLDER = os.path.join(UPLOAD_FOLDER, "logs")
MANIFESTS_FOLDER = os.path.join(UPLOAD_FOLDER, "manifests")

for p in (REFS_FOLDER, INBOX_FOLDER, SORTED_FOLDER, LOGS_FOLDER, MANIFESTS_FOLDER):
    os.makedirs(p, exist_ok=True)

app = Flask(__name__, static_folder=".", static_url_path="")
socketio = SocketIO(app, cors_allowed_origins="*")

_last_sorted_path = None  # for audit zips
_last_manifest_path = None

# --- logging ---
current_log_path = None
def start_run_log():
    global current_log_path
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    current_log_path = os.path.join(LOGS_FOLDER, f"run_{ts}.log")
    with open(current_log_path, "w", encoding="utf-8") as f:
        f.write(f"Run started {ts}\n")

def log_to_ui(message, level="info"):
    socketio.emit("log", {"message": message, "level": level})
    if current_log_path:
        try:
            with open(current_log_path, "a", encoding="utf-8") as f:
                f.write(f"[{level.upper()}] {message}\n")
        except Exception:
            pass

def emit_metric(value: float):
    try:
        socketio.emit("metric", {"cos": float(value)})
    except Exception:
        pass

@app.route("/")
def serve_index():
    return send_from_directory(".", "index.html")

@app.route("/manifests/<path:filename>")
def serve_manifest(filename):
    return send_from_directory(MANIFESTS_FOLDER, filename, as_attachment=True)

@app.route("/latest_artifacts")
def latest_artifacts():
    try:
        files = os.listdir(MANIFESTS_FOLDER)
        manifests = sorted([f for f in files if f.startswith("manifest_") and f.endswith(".json")])
        bats = sorted([f for f in files if f.startswith("revert_") and f.endswith(".bat")])
        shs = sorted([f for f in files if f.startswith("revert_") and f.endswith(".sh")])
        res = {}
        if manifests:
            res["manifest_url"] = f"/manifests/{manifests[-1]}"
        if bats:
            res["revert_bat_url"] = f"/manifests/{bats[-1]}"
        if shs:
            res["revert_sh_url"] = f"/manifests/{shs[-1]}"
        return jsonify(res)
    except Exception:
        return jsonify({})

# --- server-side folder browser ---
def list_roots():
    # Robust cross-platform roots
    if os.name == "nt":
        roots = []
        for d in string.ascii_uppercase:
            p = f"{d}:{os.sep}"  # avoids backslash escaping issues
            if os.path.exists(p):
                roots.append(p)
        return roots
    else:
        return ["/"]

@app.route("/roots")
def roots_route():
    return jsonify({"roots": list_roots()})

@app.route("/browse")
def browse_route():
    path = request.args.get("path", "").strip()
    if not path:
        return jsonify({"dirs": [{"name": r, "path": r} for r in list_roots()]})
    try:
        entries = []
        for name in sorted(os.listdir(path)):
            full = os.path.join(path, name)
            if os.path.isdir(full):
                entries.append({"name": name, "path": full})
        return jsonify({"dirs": entries})
    except Exception as e:
        return jsonify({"error": str(e), "dirs": []})

@app.route("/validate_paths", methods=["POST"])
def validate_paths():
    data = request.get_json(silent=True) or {}
    img_exts = {".jpg",".jpeg",".png",".bmp",".webp",".tif",".tiff"}
    def summarize(p):
        ok = bool(p) and os.path.isdir(p)
        cnt = 0
        if ok:
            for root, _, files in os.walk(p):
                for f in files:
                    if os.path.splitext(f)[1].lower() in img_exts:
                        cnt += 1
        return {"exists": ok, "count": cnt, "path": p or ""}
    refs = summarize(data.get("refs_path",""))
    inbox = summarize(data.get("inbox_path",""))
    sorted_p = summarize(data.get("sorted_path",""))
    return jsonify({"status": "success", "refs": refs, "inbox": inbox, "sorted": sorted_p})

def clear_folder(path):
    if os.path.exists(path):
        shutil.rmtree(path)
    os.makedirs(path, exist_ok=True)

def save_files_preserving_subfolders(files, base_folder):
    saved_paths = []
    for file in files:
        rel_path = os.path.normpath(file.filename).replace('\\', '/')
        if rel_path.startswith('../') or rel_path.startswith('/'):
            rel_path = rel_path.split('/')[-1]
        target_path = os.path.join(base_folder, rel_path)
        os.makedirs(os.path.dirname(target_path), exist_ok=True)
        file.save(target_path)
        saved_paths.append(target_path)
    return saved_paths

@app.route("/zip_latest_audit")
def zip_latest_audit():
    # Create a zip with the latest manifest + all crops under last sorted path
    files = os.listdir(MANIFESTS_FOLDER)
    manifests = sorted([f for f in files if f.startswith("manifest_") and f.endswith(".json")])
    if not manifests:
        return jsonify({"status": "error", "message": "No manifest found."})
    manifest_path = os.path.join(MANIFESTS_FOLDER, manifests[-1])
    try:
        with open(manifest_path, "r", encoding="utf-8") as f:
            manifest = json.load(f)
    except Exception as e:
        return jsonify({"status": "error", "message": f"Cannot read manifest: {e}"})
    summary = manifest.get("summary", {})
    sorted_base = summary.get("sorted_base_dir")
    if not sorted_base or not os.path.isdir(sorted_base):
        return jsonify({"status": "error", "message": "Sorted path not in manifest or does not exist."})
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    zip_name = f"audit_{ts}.zip"
    zip_path = os.path.join(MANIFESTS_FOLDER, zip_name)
    img_count = 0
    try:
        import zipfile
        with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as z:
            # add manifest
            z.write(manifest_path, arcname=os.path.basename(manifest_path))
            # add all crops
            for root, dirs, files in os.walk(sorted_base):
                if os.path.basename(root).lower() == "crops":
                    for f in files:
                        p = os.path.join(root, f)
                        arc = os.path.relpath(p, start=sorted_base)
                        z.write(p, arcname=arc)
                        img_count += 1
    except Exception as e:
        return jsonify({"status": "error", "message": f"ZIP failed: {e}"})
    log_to_ui(f"📦 Audit ZIP created with {img_count} crops: {zip_path}", "info")
    return jsonify({"status": "success", "url": f"/manifests/{os.path.basename(zip_path)}"})

@app.route("/reset_run", methods=["POST"])
def reset_run():
    clear_folder(INBOX_FOLDER)
    clear_folder(SORTED_FOLDER)
    log_to_ui("♻️ Reset: cleared uploads/inbox and uploads/sorted.", "info")
    return jsonify({"status": "success", "message": "Reset complete: uploads/inbox + uploads/sorted cleared"})

@app.route("/set_device", methods=["POST"])
def set_device_route():
    data = request.get_json(silent=True) or {}
    use_gpu = bool(data.get("use_gpu", False))
    os.environ["FACE_USE_GPU"] = "1" if use_gpu else "0"
    ok, msg = set_device(use_gpu=use_gpu)
    level = "success" if ok else "warning"
    log_to_ui(msg, level)
    return jsonify({"status": "success" if ok else "error", "message": msg})

@app.route("/build_references", methods=["POST"])
def build_refs():
    files = request.files.getlist("ref_files")
    if not files:
        return jsonify({"status": "error", "message": "No reference files uploaded"})
    start_run_log()
    log_to_ui("🧹 Cleaning uploads/inbox & uploads/sorted for new run...", "info")
    clear_folder(INBOX_FOLDER)
    clear_folder(SORTED_FOLDER)

    saved_paths = save_files_preserving_subfolders(files, REFS_FOLDER)
    log_to_ui(f"📥 Saved {len(saved_paths)} reference files. Building embeddings...", "info")
    build_reference_embeddings(saved_paths, log_callback=log_to_ui, refs_base_dir=REFS_FOLDER, num_workers=None)
    save_ref_artifacts(base_dir=UPLOAD_FOLDER, log_callback=log_to_ui)
    release_resources()
    log_to_ui("✅ References ready.", "success")
    log_to_ui(f"🗒 Log file: {current_log_path}", "info")
    return jsonify({"status": "success", "message": "Reference embeddings built successfully"})

@app.route("/build_references_inplace", methods=["POST"])
def build_refs_inplace():
    data = request.get_json(silent=True) or {}
    refs_path = data.get("refs_path", "").strip()
    delete_refs = bool(data.get("delete_refs", False))
    if not refs_path or not os.path.isdir(refs_path):
        return jsonify({"status": "error", "message": "Invalid refs_path"})
    start_run_log()
    log_to_ui("🧹 Cleaning uploads/inbox & uploads/sorted for new run (in-place mode)...", "info")
    clear_folder(INBOX_FOLDER)
    clear_folder(SORTED_FOLDER)
    img_exts = {".jpg",".jpeg",".png",".bmp",".webp",".tif",".tiff"}
    ref_files = []
    for root, _, files in os.walk(refs_path):
        for f in files:
            if os.path.splitext(f)[1].lower() in img_exts:
                ref_files.append(os.path.join(root, f))
    if not ref_files:
        return jsonify({"status": "error", "message": "No images found in refs_path"})
    log_to_ui(f"📥 Using {len(ref_files)} reference files from {refs_path}", "info")
    build_reference_embeddings(ref_files, log_callback=log_to_ui, refs_base_dir=refs_path, num_workers=None)
    save_ref_artifacts(base_dir=UPLOAD_FOLDER, log_callback=log_to_ui)
    if delete_refs:
        log_to_ui("🧽 Deleting ORIGINAL reference files after embedding (in-place)...", "warning")
        try:
            shutil.rmtree(refs_path); os.makedirs(refs_path, exist_ok=True)
        except Exception as e:
            log_to_ui(f"❌ Failed deleting refs_path: {e}", "error")
    release_resources()
    log_to_ui("✅ References ready (in-place).", "success")
    log_to_ui(f"🗒 Log file: {current_log_path}", "info")
    return jsonify({"status": "success", "message": "Reference embeddings built successfully (in-place)"})

@app.route("/upload_inbox", methods=["POST"])
def upload_inbox():
    files = request.files.getlist("inbox_files")
    if not files:
        return jsonify({"status": "error", "message": "No inbox files uploaded"})
    log_to_ui("🧹 Cleaning uploads/inbox before upload...", "info")
    clear_folder(INBOX_FOLDER)
    saved_paths = save_files_preserving_subfolders(files, INBOX_FOLDER)
    log_to_ui(f"📂 Loaded {len(saved_paths)} inbox photos.", "success")
    release_resources()
    return jsonify({"status": "success", "message": "Inbox loaded successfully"})

@app.route("/sort_photos", methods=["POST"])
def sort_photos():
    global _last_sorted_path, _last_manifest_path
    data = request.get_json(silent=True) or {}
    pct = int(data.get("threshold_pct", 32)); pct = max(0, min(100, pct))
    min_sim = pct / 100.0
    policy = data.get("multi_face_policy", "copy_all")
    save_crops = bool(data.get("save_crops", True))
    output_mode = data.get("output_mode", "move")
    dry_run = bool(data.get("dry_run", False))
    use_adaptive = bool(data.get("use_adaptive", False))
    adaptive_k = float(data.get("adaptive_k", 1.0))

    inplace = bool(data.get("inplace", False))
    cleanup_uploads = bool(data.get("cleanup_uploads", True))
    refs_path = data.get("refs_path") if inplace else REFS_FOLDER
    inbox_path = data.get("inbox_path") if inplace else INBOX_FOLDER
    sorted_path = data.get("sorted_path") if inplace else SORTED_FOLDER
    if inplace:
      if not refs_path or not os.path.isdir(refs_path):
          return jsonify({"status": "error", "message": "Invalid refs_path (in-place)"})
      if not inbox_path or not os.path.isdir(inbox_path):
          return jsonify({"status": "error", "message": "Invalid inbox_path (in-place)"})
      if not sorted_path: sorted_path = os.path.join(inbox_path, "sorted")
      os.makedirs(sorted_path, exist_ok=True)
      log_to_ui(f"📂 In-place mode: refs={refs_path} | inbox={inbox_path} | sorted={sorted_path}", "info")
    else:
      log_to_ui("🧹 Fresh uploads/sorted folder...", "info"); clear_folder(SORTED_FOLDER)

    img_exts = {".jpg",".jpeg",".png",".bmp",".webp",".tif",".tiff"}
    inbox_files = []
    for root, _, files in os.walk(inbox_path):
        for f in files:
            if os.path.splitext(f)[1].lower() in img_exts:
                inbox_files.append(os.path.join(root, f))
    if not inbox_files:
        return jsonify({"status": "error", "message": "Inbox is empty."})

    log_to_ui(f"🚀 Sorting {len(inbox_files)} photos (cos≥{min_sim:.2f}, policy={policy}, save_crops={save_crops}, output={output_mode}, dry_run={dry_run}, adaptive={use_adaptive}, k={adaptive_k:.1f})", "info")
    result = sort_photos_with_embeddings(
        inbox_files,
        log_callback=log_to_ui,
        min_cosine=min_sim,
        refs_base_dir=refs_path,
        sorted_base_dir=sorted_path,
        num_workers=None,
        multi_face_policy=policy,
        save_crops=save_crops,
        metric_callback=lambda v: socketio.emit("metric", {"cos": float(v)}),
        output_mode=output_mode,
        dry_run=dry_run,
        base_dir=UPLOAD_FOLDER,
        adaptive_enabled=use_adaptive,
        adaptive_k=adaptive_k
    )

    manifest = result.get("manifest", {})
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    manifest["summary"] = manifest.get("summary", {})
    manifest["summary"]["sorted_base_dir"] = sorted_path
    manifest["summary"]["refs_base_dir"] = refs_path
    manifest["summary"]["inplace"] = inplace
    manifest_path = os.path.join(MANIFESTS_FOLDER, f"manifest_{ts}.json")
    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2)
    log_to_ui(f"🗂 Manifest saved: {manifest_path}", "info")
    _last_manifest_path = manifest_path
    _last_sorted_path = sorted_path

    bat_path = os.path.join(MANIFESTS_FOLDER, f"revert_{ts}.bat")
    sh_path = os.path.join(MANIFESTS_FOLDER, f"revert_{ts}.sh")
    write_revert_scripts(manifest, bat_path, sh_path)
    log_to_ui(f"↩ Revert scripts saved: {bat_path} / {sh_path}", "info")

    # optional cleanup of uploads mirror
    if inplace and cleanup_uploads:
        try:
            if os.path.exists(REFS_FOLDER): shutil.rmtree(REFS_FOLDER)
            if os.path.exists(INBOX_FOLDER): shutil.rmtree(INBOX_FOLDER)
            if os.path.exists(SORTED_FOLDER): shutil.rmtree(SORTED_FOLDER)
            os.makedirs(REFS_FOLDER, exist_ok=True)
            os.makedirs(INBOX_FOLDER, exist_ok=True)
            os.makedirs(SORTED_FOLDER, exist_ok=True)
            log_to_ui("🧹 Cleaned uploads/ mirror (refs, inbox, sorted).", "info")
        except Exception as e:
            log_to_ui(f"⚠️ Failed to clean uploads mirror: {e}", "warning")

    release_resources()
    log_to_ui("✅ Sorting done.", "success")
    log_to_ui(f"🗒 Log file: {current_log_path}", "info")

    # Prepare dry-run preview (first 50)
    preview_rows = []
    for i, e in enumerate(manifest.get("entries", [])[:50]):
        preview_rows.append({
            "decision": e.get("decision"),
            "person": e.get("person"),
            "score": e.get("score"),
            "src": e.get("src"),
            "dst": e.get("dst"),
            "action": e.get("action")
        })

    return jsonify({
        "status": "success",
        "message": f"Sorting complete (cos≥{min_sim:.2f}, output={output_mode}, dry_run={dry_run}, inplace={inplace})",
        "manifest_url": f"/manifests/{os.path.basename(manifest_path)}",
        "revert_bat_url": f"/manifests/{os.path.basename(bat_path)}",
        "revert_sh_url": f"/manifests/{os.path.basename(sh_path)}",
        "preview": preview_rows
    })

def write_revert_scripts(manifest, bat_path, sh_path):
    with open(bat_path, "w", encoding="utf-8") as f:
        f.write("@echo off\r\n")
        f.write("echo Reverting file placements...\r\n")
        for item in manifest.get("entries", []):
            src = item["src"]; dst = item["dst"]; action = item["action"]
            if action == "move":
                f.write(f'if exist "{dst}" move /Y "{dst}" "{src}"\r\n')
            else:
                f.write(f'if exist "{dst}" del /F /Q "{dst}"\r\n')
        f.write("echo Done.\r\n")
    with open(sh_path, "w", encoding="utf-8") as f:
        f.write("#!/usr/bin/env bash\nset -e\nset -o pipefail\n\necho 'Reverting file placements...'\n")
        for item in manifest.get("entries", []):
            src = item["src"]; dst = item["dst"]; action = item["action"]
            if action == "move":
                f.write(f'if [ -e "{dst}" ]; then mkdir -p "$(dirname "{src}")"; mv -f "{dst}" "{src}"; fi\n')
            else:
                f.write(f'if [ -e "{dst}" ]; then rm -f "{dst}"; fi\n')
        f.write("echo 'Done.'\n")
    try:
        os.chmod(sh_path, 0o755)
    except Exception:
        pass

if __name__ == "__main__":
    socketio.run(app, host="127.0.0.1", port=5000, debug=True)
