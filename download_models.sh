#!/bin/bash

echo "📦 Checking buffalo_l model..."

if [ ! -d ".insightface/models/buffalo_l" ]; then
    echo "📥 Downloading buffalo_l from Google Drive..."

    mkdir -p .insightface/models/

    # Replace this with your actual folder ID
    FOLDER_ID=1RgwYMdbP1VxOPWtjmJfvOXzoAfKh4GXf

    # Install gdown if missing
    if ! command -v gdown &> /dev/null; then
        pip install gdown
    fi

    gdown --folder "https://drive.google.com/drive/folders/$FOLDER_ID" -O .insightface/models/
else
    echo "✅ buffalo_l already present"
fi
