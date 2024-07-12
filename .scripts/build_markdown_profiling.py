#!/bin/python3

import json
import os
import statistics
import sys

def extract_data(json_data):
    keygen_time = None
    prove_times = []
    verify_time = None

    def traverse(node):
        nonlocal keygen_time, prove_times, verify_time

        if node['name'] == 'pp_new':
            keygen_time = node['time_busy']
        elif node['name'] == 'prove':
            prove_times.append(node['time_busy'])
        elif node['name'] == 'ivc_vefify':
            verify_time = node['time_busy']

        for child in node.get('children', []):
            traverse(child)

    for root in json_data['roots']:
        traverse(root)

    return keygen_time, statistics.mean(prove_times) if prove_times else None, verify_time

def process_json_files(json_files):
    table = "| Name | Keygen | Prove Step | Verify |\n"
    table += "|------|--------|------------|--------|\n"

    for json_file in json_files:
        with open(json_file, 'r') as f:
            data = json.load(f)
        
        keygen_time, prove_step_time, verify_time = extract_data(data)
        file_name = os.path.basename(json_file)

        table += f"| {file_name} | {keygen_time} | {prove_step_time} | {verify_time} |\n"

    return table

def main():
    if len(sys.argv) < 2:
        print("Usage: python script.py <json_file1> <json_file2> ...")
        sys.exit(1)

    json_files = sys.argv[1:]
    table = process_json_files(json_files)

    with open('output.md', 'w') as f:
        f.write(table)

if __name__ == "__main__":
    main()
