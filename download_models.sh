#!/bin/bash
set -e

echo "📥 Creating buffalo_l model directory..."
mkdir -p .insightface/models/buffalo_l
cd .insightface/models/buffalo_l

echo "📥 Downloading model files from Google Drive using gdown..."

gdown --id 1Ldp7BATcllpe_yGjJzrTBFvHHsgtSpV5 -O config.yaml
gdown --id 1Px5xAjdBzYZjvGGEsZEBm5bDi--1NU6u -O det_10g.onnx
gdown --id 1VreU-_OqA-oeiR9V583Q_LPh_1sld8Yk -O genderage.onnx
gdown --id 1EbNrHaSieVeb7Hu399WHDDwElTKcEyKD -O w600k_r50.onnx
gdown --id 1gWLXugVbjXSE57QsVCpBmN_tyJpXlsAc -O 1k3d68.onnx
gdown --id 1XrOeD77P53jFE36Qd41iPECidfcYhWqw -O 2d106det.onnx

echo "✅ All files downloaded successfully."
