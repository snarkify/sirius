#!/bin/python

import os
import sys
import subprocess
import math

# Define the folder path
FOLDER_PATH = ".logs/mem_usage_logs"

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

# Function to generate file_suffix
def generate_file_suffix(type, repeat_count):
    return f"halo2_{type.lower()}_{repeat_count}"

# Function to run a command and handle its output
def run_command(command, stdout_file, stderr_file, dhat_file):
    with open(stdout_file, 'w') as out, open(stderr_file, 'w') as err:
        result = subprocess.run(command, stdout=out, stderr=err, shell=True)

    if result.returncode != 0:
        print(f"Command failed with exit code {result.returncode}")
    else:
        print("command running finished")

    if os.path.exists("dhat-heap.json"):
        os.rename("dhat-heap.json", dhat_file)
    else:
        raise ValueError(f"lost dhat-heap.json for {command}")

    return None

# Define configurations
configurations = [
        #{"type": "IPA",     "repeat_count": 2},
        #{"type": "IPA",     "repeat_count": 10},
        #{"type": "IPA",     "repeat_count": 20},
        #{"type": "IPA",     "repeat_count": 40},
        #{"type": "IPA",     "repeat_count": 60},
        #{"type": "IPA",     "repeat_count": 80},
        #{"type": "IPA",     "repeat_count": 100},

        #{"type": "KZG",     "repeat_count": 2},
        #{"type": "KZG",     "repeat_count": 10},
        #{"type": "KZG",     "repeat_count": 20},
        #{"type": "KZG",     "repeat_count": 40},
        #{"type": "KZG",     "repeat_count": 60},
        #{"type": "KZG",     "repeat_count": 80},
        #{"type": "KZG",     "repeat_count": 100},

    {"type": "Sirius",  "repeat_count": 2,   "fold_step": 1},
    {"type": "Sirius",  "repeat_count": 10,  "fold_step": 1},
    {"type": "Sirius",  "repeat_count": 20,  "fold_step": 1},
    {"type": "Sirius",  "repeat_count": 40,  "fold_step": 1},
    {"type": "Sirius",  "repeat_count": 60,  "fold_step": 1},
    {"type": "Sirius",  "repeat_count": 80,  "fold_step": 1},
    {"type": "Sirius",  "repeat_count": 100, "fold_step": 1},
]

# Loop through configurations and execute commands
for config in configurations:
    print(f"start processing {config}")
    file_suffix = generate_file_suffix(config["type"], config["repeat_count"])

    if config["type"] == "Sirius":
        k_table_size = calculate_k_table_size(config["repeat_count"])
        commitment_key_size = max(21, k_table_size + 4)
        max_key_size = 27
        base_command = 'cargo re-cli-dhat merkle-tree trivial'
        while commitment_key_size <= max_key_size:
            command = (
                f'{base_command} --primary-commitment-key-size {commitment_key_size} '
                f'--primary-repeat-count {config["repeat_count"]} --fold-step-count {config["fold_step"]} '
                f'--primary-circuit-k-table-size {k_table_size} --json-logs'
            )
            stdout_file = os.path.join(FOLDER_PATH, f'sirius_log_{file_suffix}')
            stderr_file = os.path.join(FOLDER_PATH, f'sirius_out_{file_suffix}')
            dhat_file = f'dhat_{file_suffix}.json'
            print(f"run command: {command}")
            if run_command(command, stdout_file, stderr_file, dhat_file) is None:
                print(file_suffix)
                break
            else:
                commitment_key_size += 1
        else:
            print(f"Failed to find a suitable primary-commitment-key-size up to {max_key_size} for configuration: {config}")
            break
    elif config["type"] == "IPA":
        command = f'cargo re-ipa-merkle-dhat --repeat-count {config["repeat_count"]}'
        stdout_file = os.path.join(FOLDER_PATH, f'halo2_ipa_log_{file_suffix}')
        stderr_file = os.path.join(FOLDER_PATH, f'halo2_ipa_out_{file_suffix}')
        dhat_file = f'dhat_{file_suffix}.json'
        print(f"run command: {command}")
        if run_command(command, stdout_file, stderr_file, dhat_file) is None:
            print(file_suffix)
        else:
            raise ValueError("WHY")
    elif config["type"] == "KZG":
        command = f'cargo re-kzg-merkle-dhat --repeat-count {config["repeat_count"]}'
        stdout_file = os.path.join(FOLDER_PATH, f'halo2_kzg_log_{file_suffix}')
        stderr_file = os.path.join(FOLDER_PATH, f'halo2_kzg_out_{file_suffix}')
        dhat_file = f'dhat_{file_suffix}.json'
        print(f"run command: {command}")
        if run_command(command, stdout_file, stderr_file, dhat_file) is None:
            print(file_suffix)
        else:
            raise ValueError("WHY")

print("All commands executed successfully.")
