set -e

echo "📥 Creating buffalo_l model directory..."
mkdir -p .insightface/models/buffalo_l

cd .insightface/models/buffalo_l

echo "📥 Downloading model files from Google Drive..."

# Replace these links with your actual direct download links
curl -L -o config.yaml 'https://drive.google.com/file/d/1Ldp7BATcllpe_yGjJzrTBFvHHsgtSpV5/view?usp=drive_link'
curl -L -o det_10g.onnx 'https://drive.google.com/file/d/1Px5xAjdBzYZjvGGEsZEBm5bDi--1NU6u/view?usp=drive_link'
curl -L -o genderage.onnx 'https://drive.google.com/file/d/1VreU-_OqA-oeiR9V583Q_LPh_1sld8Yk/view?usp=drive_link'
curl -L -o w600k_r50.onnx 'https://drive.google.com/file/d/1EbNrHaSieVeb7Hu399WHDDwElTKcEyKD/view?usp=drive_link'
curl -L -o 1k3d68.onnx 'https://drive.google.com/file/d/1gWLXugVbjXSE57QsVCpBmN_tyJpXlsAc/view?usp=drive_link'
curl -L -o 2d106det.onnx 'https://drive.google.com/file/d/1XrOeD77P53jFE36Qd41iPECidfcYhWqw/view?usp=drive_link'

echo "✅ All files downloaded successfully."
