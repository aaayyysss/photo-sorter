import os
import gc
import shutil
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Tuple, Optional

import cv2
import numpy as np
from insightface.app import FaceAnalysis

def _init_face_app(use_gpu: Optional[bool] = None):
    if use_gpu is None:
        use_gpu = os.environ.get("FACE_USE_GPU", "0") in ("1","true","True")
    try:
        app = FaceAnalysis(name="buffalo_l")
        ctx_id = 0 if use_gpu else -1
        app.prepare(ctx_id=ctx_id, det_size=(640, 640))
        return app, True, f"FaceAnalysis initialized (backend={'GPU' if use_gpu else 'CPU'})"
    except Exception as e:
        app = FaceAnalysis(name="buffalo_l")
        app.prepare(ctx_id=-1, det_size=(640, 640))
        return app, False, f"FaceAnalysis initialized on CPU (fallback). Reason: {e}"

app, _ok, _msg = _init_face_app()

def set_device(use_gpu: bool):
    global app
    os.environ["FACE_USE_GPU"] = "1" if use_gpu else "0"
    app, ok, msg = _init_face_app(use_gpu=use_gpu)
    return ok, msg

reference_centroids: Dict[str, np.ndarray] = {}
person_stats: Dict[str, Dict[str, float]] = {}

def release_resources():
    gc.collect()
    try: cv2.destroyAllWindows()
    except Exception: pass

def imread_rgb(path: str):
    data = np.fromfile(path, dtype=np.uint8)
    img = cv2.imdecode(data, cv2.IMREAD_COLOR)
    if img is None: return None
    return cv2.cvtColor(img, cv2.COLOR_BGR2RGB)

def imwrite_unicode(path: str, bgr_img: np.ndarray) -> bool:
    ext = os.path.splitext(path)[1].lower()
    if ext not in (".jpg", ".jpeg", ".png"):
        ext = ".jpg"; path = path + ".jpg"
    ok, buf = cv2.imencode(ext, bgr_img)
    if not ok: return False
    try: buf.tofile(path); return True
    except Exception: return False

def _cosine(a: np.ndarray, b: np.ndarray) -> float:
    return float(np.dot(a, b))

def _person_from_ref_path(img_path: str, refs_base_dir: str) -> str:
    rel = os.path.relpath(img_path, start=refs_base_dir)
    parts = rel.split(os.sep)
    if len(parts) >= 2: return parts[-2]
    return os.path.splitext(parts[0])[0]

def _clip_bbox(bbox, w, h):
    x1, y1, x2, y2 = [int(round(v)) for v in bbox]
    x1 = max(0, min(w-1, x1)); x2 = max(0, min(w, x2))
    y1 = max(0, min(h-1, y1)); y2 = max(0, min(h, y2))
    if x2 <= x1: x2 = min(w, x1 + 1)
    if y2 <= y1: y2 = min(h, y1 + 1)
    return x1, y1, x2, y2

def _save_crop(rgb_img, bbox, out_dir, stem, tag):
    h, w = rgb_img.shape[:2]
    x1, y1, x2, y2 = _clip_bbox(bbox, w, h)
    crop_rgb = rgb_img[y1:y2, x1:x2]
    crop_bgr = cv2.cvtColor(crop_rgb, cv2.COLOR_RGB2BGR)
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, f"{stem}_{tag}.jpg")
    imwrite_unicode(out_path, crop_bgr)

def _place_file(src: str, dst: str, mode: str, log_callback):
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    if mode == "move":
        try:
            os.replace(src, dst)
        except Exception:
            try:
                shutil.copy2(src, dst); os.remove(src)
            except Exception as e:
                log_callback(f"❌ Move failed for {src} → {dst}: {e}", "error"); return False
        return True
    elif mode == "link":
        try: os.link(src, dst); return True
        except Exception:
            try: os.symlink(src, dst); return True
            except Exception:
                try: shutil.copy2(src, dst); log_callback(f"⚠️ Linking not supported; copied {src} → {dst}", "warning"); return True
                except Exception as e: log_callback(f"❌ Link/copy failed for {src} → {dst}: {e}", "error"); return False
    else:
        try: shutil.copy2(src, dst); return True
        except Exception as e: log_callback(f"❌ Copy failed for {src} → {dst}: {e}", "error"); return False

def build_reference_embeddings(image_paths: List[str], log_callback, refs_base_dir: str, num_workers: int = None):
    per_person_embs: Dict[str, List[np.ndarray]] = {}
    total = len(image_paths)
    if total == 0: log_callback("⚠️ No reference images provided.", "warning"); return
    if num_workers is None: num_workers = max(2, os.cpu_count() or 2)
    log_callback(f"🧠 Building {total} reference embeddings with {num_workers} workers...", "info")

    def worker(pth: str):
        img = imread_rgb(pth)
        if img is None: return ("warn", pth, "unreadable")
        faces = app.get(img)
        if not faces: return ("warn", pth, "no face")
        faces.sort(key=lambda f: (f.bbox[2]-f.bbox[0])*(f.bbox[3]-f.bbox[1]), reverse=True)
        emb = faces[0].normed_embedding
        person = _person_from_ref_path(pth, refs_base_dir)
        return ("ok", person, emb, os.path.basename(pth))

    processed, skipped = 0, 0
    with ThreadPoolExecutor(max_workers=num_workers) as ex:
        futures = {ex.submit(worker, p): p for p in image_paths}
        for fut in as_completed(futures):
            p = futures[fut]
            try:
                res = fut.result()
                if res[0] != "ok":
                    skipped += 1; log_callback(f"⚠️ Skipped {os.path.basename(p)}: {res[2]}", "warning"); continue
                _, person, emb, base = res
                per_person_embs.setdefault(person, []).append(emb)
                processed += 1; log_callback(f"✅ {base} → {person}", "success")
            except Exception as e:
                skipped += 1; log_callback(f"⚠️ Skipped {os.path.basename(p)}: {e}", "warning")

    reference_centroids.clear(); person_stats.clear()
    for person, embs in per_person_embs.items():
        if not embs: continue
        arr = np.vstack(embs)
        mean = arr.mean(axis=0); mean = mean / (np.linalg.norm(mean)+1e-10)
        reference_centroids[person] = mean.astype(np.float32)
        sims = (arr @ mean.astype(arr.dtype))
        mu = float(np.mean(sims)); sigma = float(np.std(sims))
        person_stats[person] = {"mu": mu, "sigma": sigma, "n": int(arr.shape[0])}

    if not reference_centroids:
        log_callback("❌ No usable reference embeddings. Add better reference images.", "error"); return

    persons = sorted(reference_centroids.keys())
    counts = {p: person_stats[p]["n"] for p in persons}
    log_callback(f"🎯 Persons: {persons}", "info")
    log_callback(f"📊 Embeddings per person: {counts}", "info")
    log_callback("📐 Stats μ/σ per person: " + ", ".join([f"{p}({person_stats[p]['mu']:.3f}/{person_stats[p]['sigma']:.3f})" for p in persons]), "info")
    log_callback(f"✅ Built {processed}/{total} embeddings (skipped {skipped}).", "success")

def save_ref_artifacts(base_dir: str, log_callback):
    out_dir = os.path.join(base_dir, "ref_artifacts"); os.makedirs(out_dir, exist_ok=True)
    if reference_centroids:
        labels = sorted(reference_centroids.keys())
        cents = np.stack([reference_centroids[p] for p in labels])
        np.save(os.path.join(out_dir, "centroids.npy"), cents)
        with open(os.path.join(out_dir, "centroids_labels.json"), "w", encoding="utf-8") as f:
            import json as _json; _json.dump(labels, f, indent=2)
    with open(os.path.join(out_dir, "person_stats.json"), "w", encoding="utf-8") as f:
        import json as _json; _json.dump(person_stats, f, indent=2)
    log_callback(f"🗂 Saved reference artifacts to {out_dir}", "info")

def sort_photos_with_embeddings(inbox_files: List[str], log_callback, min_cosine: float, refs_base_dir: str, sorted_base_dir: str, num_workers: int = None, multi_face_policy: str = "copy_all", save_crops: bool = True, metric_callback=None, output_mode: str = "move", dry_run: bool = False, base_dir: Optional[str] = None, adaptive_enabled: bool = False, adaptive_k: float = 1.0):
    if not reference_centroids:
        log_to_ui = log_callback; log_to_ui("⚠️ No references built yet.", "warning")
        return {"manifest": {"entries": [], "summary": {}}}
    if num_workers is None: num_workers = max(2, os.cpu_count() or 2)
    log_callback(f"🧮 Cosine≥{min_cosine:.2f}; workers={num_workers}; policy={multi_face_policy}; save_crops={save_crops}; output={output_mode}; dry_run={dry_run}; adaptive={adaptive_enabled}; k={adaptive_k:.1f}", "info")

    total = len(inbox_files); done = 0
    counts = {"sorted": 0, "unsorted": 0, "noface": 0}
    manifest_entries = []
    os.makedirs(os.path.join(sorted_base_dir, "unsorted"), exist_ok=True)

    def _process_one(path: str):
        file_name = os.path.basename(path); stem, _ = os.path.splitext(file_name)
        img = imread_rgb(path)
        if img is None:
            return ("warning", f"Skipping {file_name} — unreadable", [("unsorted", None, None)], None, None)
        faces = app.get(img)
        if not faces:
            return ("warning", f"No face: {file_name}", [("unsorted", None, None)], img, None)
        per_face_best = []
        for f in faces:
            emb = f.normed_embedding
            best_p, best_s = None, -1.0
            for p, c in reference_centroids.items():
                s = _cosine(emb, c)
                if s > best_s: best_s, best_p = s, p
            if metric_callback is not None:
                try: metric_callback(best_s)
                except Exception: pass
            eff_thr = min_cosine
            if adaptive_enabled and best_p in person_stats:
                mu = person_stats[best_p]["mu"]; sigma = person_stats[best_p]["sigma"]
                t_adapt = mu - adaptive_k * sigma; t_adapt = max(0.20, min(0.95, t_adapt))
                eff_thr = max(eff_thr, t_adapt)
            per_face_best.append((best_p, best_s, f.bbox, eff_thr))
        matches = [(p,s,b,thr) for (p,s,b,thr) in per_face_best if p is not None and s >= thr]
        if not matches:
            return ("warning", f"Unsorted: {file_name}", [("unsorted", None, None)], img, per_face_best)
        best_per_person = {}
        for p,s,b,thr in matches:
            if p not in best_per_person or s > best_per_person[p][0]: best_per_person[p] = (s,b,thr)
        ranked = sorted(((p,)+best_per_person[p] for p in best_per_person), key=lambda x: x[1], reverse=True)  # (p, score, bbox, thr)
        if output_mode == "move" or multi_face_policy == "best_single": ranked = ranked[:1]
        placements = [(p, s, b) for (p,s,b,thr) in ranked]
        return ("success", f"Planned: {file_name}", placements, img, per_face_best)

    from concurrent.futures import ThreadPoolExecutor, as_completed
    with ThreadPoolExecutor(max_workers=num_workers) as ex:
        futures = {ex.submit(_process_one, p): p for p in inbox_files}
        for fut in as_completed(futures):
            src_path = futures[fut]
            try:
                status, msg, placements, img_rgb, per_face_best = fut.result()
            except Exception as e:
                file_name = os.path.basename(src_path); dst_dir = os.path.join(sorted_base_dir, "unsorted"); dst_path = os.path.join(dst_dir, file_name)
                action = "plan" if dry_run else output_mode
                if not dry_run: _place_file(src_path, dst_path, output_mode, log_callback)
                manifest_entries.append({"src": src_path, "dst": dst_path, "person": "unsorted", "score": None, "decision": "unsorted", "action": action})
                counts["unsorted"] += 1; done += 1; continue

            file_name = os.path.basename(src_path); stem, _ = os.path.splitext(file_name)
            if placements and placements[0][0] != "unsorted":
                effective = placements
                for person, score, bbox in effective:
                    dst_dir = os.path.join(sorted_base_dir, person); dst_path = os.path.join(dst_dir, file_name)
                    action = "plan" if dry_run else output_mode
                    if not dry_run:
                        _place_file(src_path, dst_path, output_mode, log_callback)
                        if save_crops and bbox is not None and img_rgb is not None:
                            crops_dir = os.path.join(dst_dir, "crops"); _save_crop(img_rgb, bbox, crops_dir, stem, f"{person}_{score:.3f}")
                    manifest_entries.append({"src": src_path, "dst": dst_path, "person": person, "score": float(score) if score is not None else None, "decision": "sorted", "action": action})
                counts["sorted"] += 1; persons_str = ", ".join([f"{p}({score:.3f})" for p,score,_ in effective]); log_callback(f"Sorted: {file_name} → {persons_str}", "success")
            else:
                dst_dir = os.path.join(sorted_base_dir, "unsorted"); dst_path = os.path.join(dst_dir, file_name)
                action = "plan" if dry_run else output_mode
                if not dry_run:
                    _place_file(src_path, dst_path, output_mode, log_callback)
                    if save_crops and img_rgb is not None and per_face_best:
                        best = max(per_face_best, key=lambda x: x[1]); crops_dir = os.path.join(dst_dir, "crops"); _save_crop(img_rgb, best[2], crops_dir, stem, f"top1_{best[0]}_{best[1]:.3f}")
                manifest_entries.append({"src": src_path, "dst": dst_path, "person": "unsorted", "score": None, "decision": "unsorted", "action": action})
                if img_rgb is None: counts["noface"] += 1
                else: counts["unsorted"] += 1; log_callback(f"{msg}", "warning")

            done += 1
            if done % 10 == 0 or done == total:
                log_callback(f"⏱ Progress: {done}/{total}", "info")

    summary = {"sorted": counts["sorted"], "unsorted": counts["unsorted"], "noface": counts["noface"], "total": total, "output_mode": output_mode, "dry_run": dry_run}
    log_callback(f"📈 Summary — sorted: {counts['sorted']}, unsorted: {counts['unsorted']}, noface: {counts['noface']} / total {total}", "info")
    log_callback("🎉 Sorting complete!", "success")
    release_resources()
    return {"manifest": {"entries": manifest_entries, "summary": summary}}
