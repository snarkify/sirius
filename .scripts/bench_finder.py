#!/bin/python3

import os
import subprocess
import math

def get_branch_name():
    result = subprocess.run(['git', 'rev-parse', '--abbrev-ref', 'HEAD'], capture_output=True, text=True)
    return result.stdout.strip()

def create_folder(folder_path):
    if not os.path.exists(folder_path):
        print(f"Folder does not exist. Creating now: {folder_path}")
        os.makedirs(folder_path)
        print("Folder created.")
    else:
        print("Folder already exists.")

def k(repeat_count, rows=20838):
    return max(17, math.ceil(math.log2(rows * repeat_count)))

def run_command(folder_path, repeat_count, fold_step_count, target):
    file_name = f"sirius_{repeat_count}_{fold_step_count}_{target}"
    command = [
        "cargo", "re-cli", "merkle-tree", "trivial",
        "--primary-commitment-key-size", "27",
        "--primary-repeat-count", str(repeat_count),
        "--fold-step-count", str(fold_step_count),
        "--primary-circuit-k-table-size", str(k(repeat_count)),
        "--json-logs"
    ]

    output_file = os.path.join(folder_path, file_name)
    with open(output_file, 'w') as f:
        subprocess.run(command, stdout=f)

def get_divisors(n):
    divisors = []
    for i in range(1, n + 1):
        if n % i == 0:
            divisors.append(i)
    return divisors

def main():
    target_values = [10, 20, 40, 60, 80, 100]
    branch_name = get_branch_name()
    folder_path = f".logs/benches/finder/{branch_name}"

    create_folder(folder_path)

    for target in target_values:
        divisors = get_divisors(target)
        for repeat_count in divisors:
            fold_step_count = target // repeat_count
            run_command(folder_path, repeat_count, fold_step_count, target)

if __name__ == "__main__":
    main()
