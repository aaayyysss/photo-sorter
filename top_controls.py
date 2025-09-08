# File: photo_sorter.py (Updated with match_mode support)

import os
import cv2
import numpy as np
import shutil
import uuid
from insightface.app import FaceAnalysis
from sklearn.metrics.pairwise import cosine_similarity
from reference_db import (
    get_all_references,
    log_match_result,
    get_threshold_for_label,
    purge_missing_references
)

# Global cache
ref_embeddings = {}

# ---- Global model cache (loaded once per process) --------------

_MODEL_CACHE = {
    "app": None,         # cached FaceAnalysis instance
    "model_dir": None,   # path it was built from
    "providers": None,   # ORT providers used
}

def get_buffalo_model(model_dir, providers=None, log_callback=print):
    """
    Return a cached insightface.FaceAnalysis('buffalo_l') instance.
    - Detects available onnxruntime providers (CPU/GPU) if not specified.
    - Prepares once with det_size=(640,640).
    - Reuses the same object for future calls (same model_dir/providers).
    """
    global _MODEL_CACHE

    # Normalize args
    model_dir = os.path.normpath(model_dir)

    # Auto-detect providers if not given
    if providers is None:
        try:
            import onnxruntime as ort
            avail = ort.get_available_providers()
        except Exception:
            avail = ["CPUExecutionProvider"]
        providers = ["CUDAExecutionProvider"] if "CUDAExecutionProvider" in avail else ["CPUExecutionProvider"]

    # If already cached with same settings, reuse
    if (
        _MODEL_CACHE["app"] is not None and
        _MODEL_CACHE["model_dir"] == model_dir and
        _MODEL_CACHE["providers"] == tuple(providers)
    ):
        return _MODEL_CACHE["app"]

    # (Re)initialize
    app = _init_your_existing_buffalo(model_dir, providers, log_callback)
    if app is None:
        return None
    _MODEL_CACHE.update({
        "app": app,
        "model_dir": model_dir,
        "providers": tuple(providers),
    })
    return app


def _init_your_existing_buffalo(model_dir, providers, log_callback=print):
    """
    Your original loader, wrapped:
    - creates the FaceAnalysis app with providers
    - prepares once (CPU if no CUDA)
    - returns the ready-to-use app
     Initialize FaceAnalysis once with correct providers / ctx.
    Works with older InsightFace versions that don't accept `providers=`.
    """
    # FaceAnalysis accepts 'root' where the model package lives and optional 'providers'
    # Model package name is 'buffalo_l' (your current code)
    try:
        # try to pass providers (newer insightface); fall back if TypeError
        try:
            app = FaceAnalysis(name="buffalo_l", root=model_dir, providers=providers)
            used_providers = providers
        except TypeError:
            # older insightface doesn't support `providers` kwarg
            app = FaceAnalysis(name="buffalo_l", root=model_dir)
            used_providers = None  # unknown to app; we choose ctx only

        # choose CPU/GPU via ctx_id; older insightface will still honor this
        use_cuda = (isinstance(providers, (list, tuple)) and "CUDAExecutionProvider" in providers)
        ctx_id = 0 if use_cuda else -1
        app.prepare(ctx_id=ctx_id, det_size=(640, 640))
        return app
        
#        model_path = os.path.join(model_dir, "buffalo_l")
#        log_callback(f"📦 Loading model from: {model_path}")
#
#        # If CUDA is present, providers will contain 'CUDAExecutionProvider'
#        use_cuda = ("CUDAExecutionProvider" in providers)
#
#        # Newer insightface exposes 'providers' param; older versions ignore it (harmless)
#        app = FaceAnalysis(name="buffalo_l", root=model_dir, providers=providers)
#
#        # ctx_id = 0 for GPU, -1 for CPU. det_size matches your log.
#        ctx_id = 0 if use_cuda else -1
#        app.prepare(ctx_id=ctx_id, det_size=(640, 640))
#        return app
    except Exception as e:
        log_callback(f"❌ Failed to initialize FaceAnalysis: {e}")
        return None


def _build_safe_destination(out_folder, filename, keep_original_filenames=True):
    """
    Returns a destination path inside out_folder that does not overwrite existing files.
    If keep_original_filenames=True -> keep name, add _2, _3... on collision.
    Otherwise -> prefix an 8-char uuid.
    """
    os.makedirs(out_folder, exist_ok=True)
    name, ext = os.path.splitext(filename)

    if not keep_original_filenames:
        return os.path.join(out_folder, f"{uuid.uuid4().hex[:8]}_{filename}")

    candidate = os.path.join(out_folder, filename)
    if not os.path.exists(candidate):
        return candidate

    i = 2
    while True:
        candidate = os.path.join(out_folder, f"{name}_{i}{ext}")
        if not os.path.exists(candidate):
            return candidate
        i += 1


def _copy_one(src_path, dest_folder, filename, keep_original_filenames, log_callback):
    dst = _build_safe_destination(dest_folder, filename, keep_original_filenames)
    shutil.copy2(src_path, dst)
    log_callback(f"📄 Copied {os.path.basename(src_path)} → {dest_folder} as {os.path.basename(dst)}")
    return dst


def _move_one(src_path, dest_folder, filename, keep_original_filenames, log_callback):
    dst = _build_safe_destination(dest_folder, filename, keep_original_filenames)
    shutil.move(src_path, dst)
    log_callback(f"📦 Moved {os.path.basename(dst)} into {dest_folder}")
    return dst

# ------------- OLD MODAL LOADING ----------------------
#def load_model(model_dir, log_callback):
#    try:
#        model_path = os.path.join(model_dir, "buffalo_l")
#        log_callback(f"📦 Loading model from: {model_path}")
#        app = FaceAnalysis(name='buffalo_l', root=model_dir)
#        app.prepare(ctx_id=0)
#        return app
#    except Exception as e:
#        log_callback(f"❌ Failed to initialize FaceAnalysis: {e}")
#        return None

# ---------------USES CACHE -------------------------------
def load_model(model_dir, log_callback):
    # Back-compat wrapper that uses the cached model
    app = get_buffalo_model(model_dir, providers=None, log_callback=log_callback)
    return app


def build_reference_embeddings_for_labels(db_path, model_dir, labels, log_callback=print):
    """
    Rebuild embeddings only for the given label(s).
    - Updates global ref_embeddings[label] in-place.
    - Removes the label from ref_embeddings if it has no valid faces anymore.
    """
    global ref_embeddings

    # Clean dead paths (safe to run every time)
    try:
        removed = purge_missing_references()
        if removed:
            log_callback(f"🧹 Cleaned {removed} dead reference entries.")
    except Exception as e:
        log_callback(f"⚠️ DB cleanup skipped: {e}")

    app = get_buffalo_model(model_dir, log_callback=log_callback)
    if app is None:
        return

    try:
        all_refs = get_all_references()  # [(id, label, path), ...]
    except Exception as e:
        log_callback(f"❌ Failed to fetch references from DB: {e}")
        return

    target = set(labels)
    if not target:
        log_callback("⚠️ No labels requested for partial rebuild.")
        return

    # Group references by label (filter early)
    refs_by_label = {}
    for _id, lbl, path in all_refs:
        if lbl in target:
            refs_by_label.setdefault(lbl, []).append(path)

    # Recompute each requested label
    for lbl in target:
        paths = refs_by_label.get(lbl, [])
        if not paths:
            # No references → remove from embeddings if present
            if lbl in ref_embeddings:
                del ref_embeddings[lbl]
                log_callback(f"ℹ️ '{lbl}': no references left → removed from embeddings.")
            continue

        embeddings = []
        for img_path in paths:
            try:
                if not os.path.isfile(img_path):
                    log_callback(f"⚠️ Missing reference file, skipping: {img_path}")
                    continue
                img = cv2.imdecode(np.fromfile(img_path, dtype=np.uint8), cv2.IMREAD_COLOR)
                if img is None:
                    raise ValueError("Image not readable")
                faces = app.get(img)
                if not faces:
                    log_callback(f"⚠️ No face found in reference: {img_path}")
                    continue
                vecs = [f.embedding for f in faces]
                embeddings.append(np.mean(vecs, axis=0))
                log_callback(f"✔️ Embedded '{lbl}' from {img_path}")
            except Exception as e:
                log_callback(f"❌ Error processing {img_path}: {e}")

        if embeddings:
            ref_embeddings[lbl] = np.mean(embeddings, axis=0)
        else:
            if lbl in ref_embeddings:
                del ref_embeddings[lbl]
            log_callback(f"⚠️ '{lbl}': no valid embeddings after rebuild.")

def build_reference_embeddings_from_db(db_path, model_dir, log_callback):
    """
    Full rebuild for ALL labels (Tools → Rebuild Embeddings).
    """
    global ref_embeddings
    ref_embeddings.clear()

    # Clean dead paths
    try:
        removed = purge_missing_references()
        if removed:
            log_callback(f"🧹 Cleaned {removed} dead reference entries.")
    except Exception as e:
        log_callback(f"⚠️ DB cleanup skipped: {e}")

    app = get_buffalo_model(model_dir, log_callback=log_callback)
    if app is None:
        return

    try:
        references = get_all_references()
    except Exception as e:
        log_callback(f"❌ Failed to fetch references from DB: {e}")
        return

    if not references:
        log_callback("⚠️ No references found in DB. Add some in the GUI first.")
        return

    tmp = {}
    for _id, label, img_path in references:
        try:
            if not os.path.isfile(img_path):
                log_callback(f"⚠️ Missing reference file, skipping: {img_path}")
                continue
            img = cv2.imdecode(np.fromfile(img_path, dtype=np.uint8), cv2.IMREAD_COLOR)
            if img is None:
                raise ValueError("Image not readable")
            faces = app.get(img)
            if not faces:
                log_callback(f"⚠️ No face found in reference: {img_path}")
                continue
            vecs = [f.embedding for f in faces]
            tmp.setdefault(label, []).append(np.mean(vecs, axis=0))
            log_callback(f"✔️ Embedded '{label}' from {img_path}")
        except Exception as e:
            log_callback(f"❌ Error processing {img_path}: {e}")

    for label, vecs in tmp.items():
        if vecs:
            ref_embeddings[label] = np.mean(vecs, axis=0)

    if not ref_embeddings:
        log_callback("⚠️ No valid embeddings were built. Check your reference images.")



def sort_photos_with_embeddings_from_folder_using_db(
    inbox_dir, 
    output_dir, 
    unmatched_dir, 
    db_path, 
    log_callback, 
    match_mode="multi",          # "multi", "best", "manual"
    move_files=True,             # kept for compatibility; we honor your plan below
    keep_original_filenames=True,
    stop_event=None,
    model_dir=None,    
    
):
    """
    Behavior per plan:
      - BEST: always MOVE to the best label.
      - MULTI: COPY to all other matched labels, then MOVE to the BEST label.
      - MANUAL: placeholder → send to unmatched for now.
    Filenames are preserved; on collision we add _2, _3, ...
    """

    # Normalize and verify
    inbox_dir = os.path.normpath(inbox_dir)
    output_dir = os.path.normpath(output_dir)
    unmatched_dir = os.path.normpath(unmatched_dir)

    if model_dir is None:
            model_dir = os.path.join(os.path.dirname(__file__), "buffalo_l")
    app = get_buffalo_model(model_dir, log_callback=log_callback)
        
    def _should_stop():
        return (stop_event is not None) and stop_event.is_set()

    if not os.path.isdir(inbox_dir):
        log_callback(f"❌ Inbox folder does not exist: {inbox_dir}")
        return

    os.makedirs(unmatched_dir, exist_ok=True)
    os.makedirs(output_dir, exist_ok=True)

#    model_dir = os.path.join(os.path.dirname(__file__), "buffalo_l")
#    app = load_model(model_dir, log_callback)
    if app is None:
        return

    log_callback(f"🔧 Match mode: {match_mode}")
    log_callback(f"📁 Walking inbox: {inbox_dir}")

    for subdir, _, files in os.walk(inbox_dir):
        if _should_stop():
            log_callback("⛔ Stop requested. Finishing current item and exiting…")
            break
        for file in files:
            if _should_stop():
                log_callback("⛔ Stop requested. Finishing current item and exiting…")
                break
            
            if not file.lower().endswith((".jpg", ".jpeg", ".png", ".bmp", ".webp")):
                continue

            img_path = os.path.normpath(os.path.join(subdir, file))
            if not os.path.isfile(img_path):
                log_callback(f"⚠️ Skipping missing file (not found): {img_path}")
                continue
            
            # Load + detect
                      
            try:
                img = cv2.imdecode(np.fromfile(img_path, dtype=np.uint8), cv2.IMREAD_COLOR)
                if img is None:
                    raise ValueError("Image unreadable")

                faces = app.get(img)
                if not faces:
                    raise RuntimeError("No faces found")
            except Exception as e:
                log_callback(f"⚠️ Skipping {file}: {e}")
                try:
                    # move unreadable images to unmatched, keep name (use collision-safe)
                    dst = _build_safe_destination(unmatched_dir, file, keep_original_filenames)
                    shutil.move(img_path, dst)
                    log_callback(f"↪︎ Moved to unmatched: {os.path.basename(dst)}")
                except Exception as move_e:
                    log_callback(f"⚠️ Could not move to unmatched: {move_e}")
                continue

            if _should_stop():
                log_callback("⛔ Stop requested. Finishing current item and exiting…")
                break
  

            if match_mode == "manual":
                log_callback(f"🛠️ Manual match mode not implemented yet for {file}")
                try:
                    dst = _build_safe_destination(unmatched_dir, file, keep_original_filenames)
                    shutil.move(img_path, dst)
                    log_callback(f"↪︎ Moved to unmatched: {os.path.basename(dst)}")
                except Exception as move_e:
                    log_callback(f"⚠️ Could not move to unmatched: {move_e}")
                continue

            if _should_stop():
                log_callback("⛔ Stop requested. Finishing current item and exiting…")
                break
  
            # Identify
            labels_set, best_label, _scores = identify_faces(faces, file, log_callback, match_mode)

            if not labels_set:
                log_callback(f"⚠️ No good match for {file}")
                try:
                    dst = _build_safe_destination(unmatched_dir, file, keep_original_filenames)
                    shutil.move(img_path, dst)
                    log_callback(f"↪︎ Moved to unmatched: {os.path.basename(dst)}")
                except Exception as move_e:
                    log_callback(f"⚠️ Could not move to unmatched: {move_e}")
                continue

            # Distribute per requested mode:
            if match_mode == "best":
                distribute_to_labels(
                    img_path, file, labels_set, best_label, output_dir, log_callback,
                    keep_original_filenames=keep_original_filenames, mode="best"
                )
            elif match_mode == "multi":
                # COPY to all other matches, then MOVE to best
                distribute_to_labels(
                    img_path, file, labels_set, best_label, output_dir, log_callback,
                    keep_original_filenames=keep_original_filenames, mode="multi"
                )
            else:
                # Fallback: treat as best
                distribute_to_labels(
                    img_path, file, labels_set, best_label, output_dir, log_callback,
                    keep_original_filenames=keep_original_filenames, mode="best"
                )


def identify_faces(faces, file, log_callback, match_mode):
    """
    Returns:
      labels_set: set[str] of matched labels (unique)
      best_label: str|None (the label with highest score overall)
      label_scores: dict[label] -> best score (max across faces)
    """
    label_scores = {}
    matches = []  # (label, score) per-face best

    for face in faces:
        embedding = face.embedding
        best_label = None
        best_score = 0.0

        for label, ref_emb in ref_embeddings.items():
            score = cosine_similarity([embedding], [ref_emb])[0][0]
            threshold = get_threshold_for_label(label)
            if score >= threshold and score > best_score:
                best_score = score
                best_label = label

        if best_label:
            matches.append((best_label, best_score))
            # keep the max score per label
            label_scores[best_label] = max(label_scores.get(best_label, 0.0), best_score)
            log_match_result(file, best_label, best_score, match_mode=match_mode)

    if not matches:
        return set(), None, label_scores

    labels_set = set(lbl for (lbl, _) in matches)
    # overall best label by score across faces
    best_label_overall = max(label_scores.items(), key=lambda kv: kv[1])[0]
    return labels_set, best_label_overall, label_scores


def copy_to_label_dirs(img_path, filename, labels, output_dir, log_callback):
    for label in labels:
        out_folder = os.path.join(output_dir, label)
        os.makedirs(out_folder, exist_ok=True)

        unique_filename = f"{uuid.uuid4().hex[:8]}_{filename}"
        out_path = os.path.join(out_folder, unique_filename)

        try:
            shutil.copy(img_path, out_path)
            log_callback(f"📤 Copied {filename} → {label}")
        except Exception as e:
            log_callback(f"❌ Copy failed for {filename}: {e}")


def distribute_to_labels(img_path, filename, labels_set, best_label, output_dir, log_callback,
                         keep_original_filenames=True, mode="best"):
    """
    - mode == "best": move to best_label only.
    - mode == "multi": copy to every *other* label, then move original to best_label.
    """
    if not labels_set:
        return

    # safety
    if best_label is None:
        # fallback: just pick any deterministic label
        best_label = sorted(labels_set)[0]

    if mode == "best" or len(labels_set) == 1:
        # MOVE once to the best label
        dest_folder = os.path.join(output_dir, best_label)
        _move_one(img_path, dest_folder, filename, keep_original_filenames, log_callback)
        return

    # MULTI:
    # 1) Copy to all non-best labels (using the original path as source)
    others = [lbl for lbl in labels_set if lbl != best_label]
    for lbl in others:
        dest_folder = os.path.join(output_dir, lbl)
        try:
            _copy_one(img_path, dest_folder, filename, keep_original_filenames, log_callback)
        except Exception as e:
            log_callback(f"⚠️ Copy failed for {filename} → {lbl}: {e}")

    # 2) Move the original into the best label (final location)
    dest_folder = os.path.join(output_dir, best_label)
    try:
        _move_one(img_path, dest_folder, filename, keep_original_filenames, log_callback)
    except Exception as e:
        log_callback(f"❌ Move failed for {filename} → {best_label}: {e}")

