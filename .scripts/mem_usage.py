#!/bin/python

import os
import subprocess
import math

# Define the folder path
FOLDER_PATH = "mem_usage_logs"

# Check if the folder exists, and create it if it doesn't
if not os.path.exists(FOLDER_PATH):
    print("Folder does not exist. Creating now.")
    os.makedirs(FOLDER_PATH)
    print("Folder created.")
else:
    print("Folder already exists.")

# Constant
ROWS = 20838

# Function to calculate primary-circuit-k-table-size
def calculate_k_table_size(repeat_count):
    return max(17, math.ceil(math.log2(ROWS * repeat_count)))

# Function to run a command and handle its output
def run_command(command, stdout_file, stderr_file):
    with open(stdout_file, 'w') as out, open(stderr_file, 'w') as err:
        result = subprocess.run(command, stdout=out, stderr=err, shell=True)
    if os.path.exists("dhat-heap.json"):
        os.rename("dhat-heap.json", stdout_file.replace("dhat_", "dhat_heap_"))
    else:
        print(f"lost dhat-heap.json for {command}")
    return result.returncode == 0

# Define configurations
configurations = [
    {"type": "IPA",     "repeat_count": 2,                   "file_suffix": "halo2_ipa_2"},
    {"type": "IPA",     "repeat_count": 10,                  "file_suffix": "halo2_ipa_10"},
    {"type": "IPA",     "repeat_count": 20,                  "file_suffix": "halo2_ipa_20"},
    {"type": "IPA",     "repeat_count": 40,                  "file_suffix": "halo2_ipa_40"},
    {"type": "IPA",     "repeat_count": 60,                  "file_suffix": "halo2_ipa_60"},
    {"type": "IPA",     "repeat_count": 80,                  "file_suffix": "halo2_ipa_80"},
    {"type": "IPA",     "repeat_count": 100,                 "file_suffix": "halo2_ipa_100"},

    {"type": "KZG",     "repeat_count": 2,                   "file_suffix": "halo2_kzg_2"},
    {"type": "KZG",     "repeat_count": 10,                  "file_suffix": "halo2_kzg_10"},
    {"type": "KZG",     "repeat_count": 20,                  "file_suffix": "halo2_kzg_20"},
    {"type": "KZG",     "repeat_count": 40,                  "file_suffix": "halo2_kzg_40"},
    {"type": "KZG",     "repeat_count": 60,                  "file_suffix": "halo2_kzg_60"},
    {"type": "KZG",     "repeat_count": 80,                  "file_suffix": "halo2_kzg_80"},
    {"type": "KZG",     "repeat_count": 100,                 "file_suffix": "halo2_kzg_100"},

    {"type": "Sirius",  "repeat_count": 2,   "fold_step": 1, "file_suffix": "2"},
    {"type": "Sirius",  "repeat_count": 10,  "fold_step": 1, "file_suffix": "10"},
    {"type": "Sirius",  "repeat_count": 20,  "fold_step": 1, "file_suffix": "20"},
    {"type": "Sirius",  "repeat_count": 40,  "fold_step": 1, "file_suffix": "40"},
    {"type": "Sirius",  "repeat_count": 60,  "fold_step": 1, "file_suffix": "60"},
    {"type": "Sirius",  "repeat_count": 80,  "fold_step": 1, "file_suffix": "80"},
    {"type": "Sirius",  "repeat_count": 100, "fold_step": 1, "file_suffix": "100"},
]

# Loop through configurations and execute commands
for config in configurations:
    if config["type"] == "Sirius":
        k_table_size = calculate_k_table_size(config["repeat_count"])
        commitment_key_size = max(21, k_table_size + 3)
        max_key_size = 27
        base_command = 'cargo re-cli-dhat merkle-tree trivial'
        while commitment_key_size <= max_key_size:
            command = (
                f'{base_command} --primary-commitment-key-size {commitment_key_size} '
                f'--primary-repeat-count {config["repeat_count"]} --fold-step-count {config["fold_step"]} '
                f'--primary-circuit-k-table-size {k_table_size} --json-logs'
            )
            stdout_file = os.path.join(FOLDER_PATH, f'dhat_sirius_{config["file_suffix"]}')
            stderr_file = os.path.join(FOLDER_PATH, f'dhat_sirius_{config["file_suffix"]}')
            if run_command(command, stdout_file, stderr_file):
                print(config["file_suffix"])
                break
            else:
                commitment_key_size += 1
        else:
            print(f"Failed to find a suitable primary-commitment-key-size up to {max_key_size} for configuration: {config}")
            break
    elif config["type"] == "IPA":
        command = f'cargo re-ipa-merkle-dhat --repeat-count {config["repeat_count"]}'
        stdout_file = os.path.join(FOLDER_PATH, f'dhat_halo2_ipa_{config["file_suffix"]}')
        stderr_file = os.path.join(FOLDER_PATH, f'dhat_halo2_ipa_{config["file_suffix"]}')
        if run_command(command, stdout_file, stderr_file):
            print(config["file_suffix"])
    elif config["type"] == "KZG":
        command = f'cargo re-kzg-merkle-dhat --repeat-count {config["repeat_count"]}'
        stdout_file = os.path.join(FOLDER_PATH, f'dhat_halo2_kzg_{config["file_suffix"]}')
        stderr_file = os.path.join(FOLDER_PATH, f'dhat_halo2_kzg_{config["file_suffix"]}')
        if run_command(command, stdout_file, stderr_file):
            print(config["file_suffix"])

print("All commands executed successfully.")
