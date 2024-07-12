#!/bin/zsh

# Define the folder path
FOLDER_PATH="mem_usage_logs"

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
cargo re-cli-dhat merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 2 \
    --fold-step-count 1 \
    --primary-circuit-k-table-size 17 \
    --json-logs \
    > $FOLDER_PATH/dhat_sirius_2_1_17 \
    2> $FOLDER_PATH/sirius_2_1_17;

mv dhat-heap.json $FOLDER_PATH/dhat_heap_sirius_2_1_17.json;

## IPA 2
cargo re-ipa-merkle-dhat \
    --repeat-count 2 \
    > $FOLDER_PATH/halo2_ipa_2 \
    2> $FOLDER_PATH/dhat_halo2_ipa_2;

mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_ipa_2.json;

## KZG 2
cargo re-kzg-merkle-dhat \
    --repeat-count 2 \
    > $FOLDER_PATH/halo2_kzg_2 \
    2> $FOLDER_PATH/dhat_halo2_kzg_2;

mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_kzg_2.json;

echo "10"

# Sirius 10 (2,5)
cargo re-cli-dhat merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 2 \
    --fold-step-count 5 \
    --primary-circuit-k-table-size 17 \
    --json-logs \
    > $FOLDER_PATH/sirius_10 \
    2> $FOLDER_PATH/dhat_sirius_10;

mv dhat-heap.json $FOLDER_PATH/dhat_heap_sirius_10.json;

cargo re-ipa-merkle-dhat \
    --repeat-count 10 \
    2> $FOLDER_PATH/dhat_halo2_ipa_10 \
    > $FOLDER_PATH/halo2_ipa_10;

mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_ipa_10.json;

cargo re-kzg-merkle-dhat \
    --repeat-count 10 \
    2> $FOLDER_PATH/dhat_halo2_kzg_10 \
    > $FOLDER_PATH/halo2_kzg_10;

mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_kzg_10.json;

echo "20"

# Sirius 20 (20,1)
cargo re-cli-dhat merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 20 \
    --fold-step-count 1 \
    --primary-circuit-k-table-size 19 \
    --json-logs \
    > $FOLDER_PATH/sirius_20 \
    2> $FOLDER_PATH/dhat_sirius_20;
mv dhat-heap.json FOLDER_PATH/dhat_heap_sirius_20.json;

cargo re-ipa-merkle-dhat \
    --repeat-count 20 \
    2> $FOLDER_PATH/dhat_halo2_ipa_20 \
    > $FOLDER_PATH/halo2_ipa_20;

mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_ipa_20.json

cargo re-kzg-merkle-dhat \
    --repeat-count 20 \
    2> $FOLDER_PATH/dhat_halo2_kzg_20 \
    > $FOLDER_PATH/halo2_kzg_20;
mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_kzg_20.json

echo "40"

# Sirius 40 (10,4)
cargo re-cli-dhat merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 10 \
    --fold-step-count 4 \
    --primary-circuit-k-table-size 18 \
    --json-logs \
    2> $FOLDER_PATH/dhat_sirius_40 \
    > $FOLDER_PATH/sirius_40;
mv dhat-heap.json $FOLDER_PATH/dhat_heap_sirius_40.json

cargo re-ipa-merkle-dhat \
    --repeat-count 40 \
    2> $FOLDER_PATH/dhat_halo2_ipa_40 \
    > $FOLDER_PATH/halo2_ipa_40;
mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_ipa_40.json

cargo re-kzg-merkle-dhat \
    --repeat-count 40 \
    2> $FOLDER_PATH/dhat_halo2_kzg_40 \
    > $FOLDER_PATH/halo2_kzg_40;

mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_kzg_40.json

echo "60"

# Sirius 60 (10,4)
cargo re-cli-dhat merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 10 \
    --fold-step-count 6 \
    --primary-circuit-k-table-size 18 \
    --json-logs \
    2> $FOLDER_PATH/dhat_sirius_60 \
    > $FOLDER_PATH/sirius_60;
mv dhat-heap.json $FOLDER_PATH/dhat_heap_sirius_60.json

cargo re-ipa-merkle-dhat \
    --repeat-count 60 \
    2> $FOLDER_PATH/dhat_halo2_ipa_60 \
    > $FOLDER_PATH/halo2_ipa_60;
mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_ipa_60.json

cargo re-kzg-merkle-dhat \
    --repeat-count 60 \
    2> $FOLDER_PATH/dhat_halo2_kzg_60 \
    > $FOLDER_PATH/halo2_kzg_60;
mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_kzg_60.json

echo "80"

# Sirius 80 (20,4)
cargo re-cli-dhat merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 20 \
    --fold-step-count 4 \
    --primary-circuit-k-table-size 19 \
    --json-logs \
    2> $FOLDER_PATH/dhat_sirius_80\
    > $FOLDER_PATH/sirius_80;

mv dhat-heap.json $FOLDER_PATH/dhat_heap_sirius_80.json

cargo re-kzg-merkle-dhat \
    --repeat-count 80 \
    2> $FOLDER_PATH/dhat_halo2_kzg_80 \
    > $FOLDER_PATH/halo2_kzg_80;
mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_kzg_80.json

cargo re-ipa-merkle-dhat \
    --repeat-count 80 \
    2> $FOLDER_PATH/dhat_halo2_ipa_80 \
    > $FOLDER_PATH/halo2_ipa_80;
mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_ipa_80.json

echo "100"

# Sirius 100 (10, 10)
cargo re-cli-dhat merkle-tree trivial \
    --primary-commitment-key-size 27 \
    --primary-repeat-count 10 \
    --fold-step-count 10 \
    --primary-circuit-k-table-size 18 \
    --json-logs 
    2> $FOLDER_PATH/dhat_sirius_100 \
    > $FOLDER_PATH/sirius_100;
    mv dhat-heap.json_heap $FOLDER_PATH/dhat_sirius_100.json

cargo re-ipa-merkle-dhat --repeat-count 100 \
    2> $FOLDER_PATH/dhat_halo2_ipa_100 \
    > $FOLDER_PATH/halo2_ipa_100;
mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_ipa_100.json

cargo re-kzg-merkle-dhat \
    --repeat-count 100 \
    2> $FOLDER_PATH/dhat_halo2_kzg_100 \
    > $FOLDER_PATH/halo2_kzg_100;

mv dhat-heap.json $FOLDER_PATH/dhat_heap_halo2_kzg_100.json
