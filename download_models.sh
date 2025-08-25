#!/bin/bash
set -e

MODEL_DIR=".insightface/models/buffalo_l"
MODEL_ZIP=".insightface/models/buffalo_l.zip"

if [ ! -d "$MODEL_DIR" ]; then
    echo "📦 buffalo_l model missing — downloading..."
    mkdir -p .insightface/models

    # TODO: Replace YOUR_FILE_ID below with your Google Drive file ID
    FILE_ID="1QCBCygyQXGPZcn_veQj2uBObHFgp-n2k"
    URL="https://drive.google.com/uc?export=download&id=${FILE_ID}"

    curl -L "$URL" -o "$MODEL_ZIP"
    unzip -o "$MODEL_ZIP" -d ".insightface/models/"
    rm "$MODEL_ZIP"
    echo "✅ buffalo_l model ready."
else
    echo "✅ buffalo_l model already exists."
fi
