#!/bin/zsh

# Get the current Git branch name
BRANCH_NAME=$(git rev-parse --abbrev-ref HEAD)

# Define the folder path with the branch name as prefix
FOLDER_PATH=".logs/benches/${BRANCH_NAME}"

# Check if the folder exists
if [ -d "$FOLDER_PATH" ]; then
  echo "Folder already exists."
else
  echo "Folder does not exist. Creating now."
  mkdir -p "$FOLDER_PATH"
  echo "Folder created."
fi

echo "investigate 10"

# Sirius 10 _2,5_
cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 2 \
    --fold-step-count 5 \
    --primary-circuit-k-table-size 17 \
    --json-logs > $FOLDER_PATH/sirius_2_5_10;

cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 5 \
    --fold-step-count 2 \
    --primary-circuit-k-table-size 17 \
    --json-logs > $FOLDER_PATH/sirius_5_2_10;

cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 10 \
    --fold-step-count 1 \
    --primary-circuit-k-table-size 18 \
    --json-logs > $FOLDER_PATH/sirius_10_1_10;

cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 1 \
    --fold-step-count 10 \
    --primary-circuit-k-table-size 17 \
    --json-logs > $FOLDER_PATH/sirius_1_10_10;

