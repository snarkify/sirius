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

echo "2"

## Sirius 2
cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 2 \
    --fold-step-count 1 \
    --primary-circuit-k-table-size 17 \
    --json-logs > $FOLDER_PATH/sirius_2_1_17;

## IPA 2
cargo re-ipa-merkle --repeat-count 2 > $FOLDER_PATH/halo2_ipa_2;

## KZG 2
cargo re-kzg-merkle --repeat-count 2 > $FOLDER_PATH/halo2_kzg_2;

echo "10"

# Sirius 10 (2,5)
cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 2 \
    --fold-step-count 5 \
    --primary-circuit-k-table-size 17 \
    --json-logs > $FOLDER_PATH/sirius_10;

cargo re-ipa-merkle --repeat-count 10 > $FOLDER_PATH/halo2_ipa_10;
cargo re-kzg-merkle --repeat-count 10 > $FOLDER_PATH/halo2_kzg_10;

echo "20"

# Sirius 20 (20,1)
cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 20 \
    --fold-step-count 1 \
    --primary-circuit-k-table-size 19 \
    --json-logs > $FOLDER_PATH/sirius_20;

cargo re-ipa-merkle --repeat-count 20 > $FOLDER_PATH/halo2_ipa_20;
cargo re-kzg-merkle --repeat-count 20 > $FOLDER_PATH/halo2_kzg_20;

echo "40"

# Sirius 40 (10,4)
cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 10 \
    --fold-step-count 4 \
    --primary-circuit-k-table-size 18 \
    --json-logs > $FOLDER_PATH/sirius_40;

cargo re-ipa-merkle --repeat-count 40 > $FOLDER_PATH/halo2_ipa_40;
cargo re-kzg-merkle --repeat-count 40 > $FOLDER_PATH/halo2_kzg_40;

echo "60"

# Sirius 60 (10,4)
cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 10 \
    --fold-step-count 6 \
    --primary-circuit-k-table-size 18 \
    --json-logs > $FOLDER_PATH/sirius_60;

cargo re-ipa-merkle --repeat-count 60 > $FOLDER_PATH/halo2_ipa_60;
cargo re-kzg-merkle --repeat-count 60 > $FOLDER_PATH/halo2_kzg_60;

echo "80"

# Sirius 80 (20,4)
cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 20 \
    --fold-step-count 4 \
    --primary-circuit-k-table-size 19 \
    --json-logs > $FOLDER_PATH/sirius_80;

cargo re-kzg-merkle --repeat-count 80 > $FOLDER_PATH/halo2_kzg_80;
cargo re-ipa-merkle --repeat-count 80 > $FOLDER_PATH/halo2_ipa_80;

echo "100"

# Sirius 100 (10, 10)
cargo re-cli merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 10 \
    --fold-step-count 10 \
    --primary-circuit-k-table-size 18 \
    --json-logs > $FOLDER_PATH/sirius_100;

cargo re-ipa-merkle --repeat-count 100 > $FOLDER_PATH/halo2_ipa_100;
cargo re-kzg-merkle --repeat-count 100 > $FOLDER_PATH/halo2_kzg_100;
