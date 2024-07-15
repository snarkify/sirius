#!/bin/python3

import json
import os
import statistics
import sys

from build_profiling import LogProcessor

def extract_data(json_data, keygen_span, prove_span, verify_span, prove_step_spans=None, prove_step_filter=None):
    keygen_times = []
    prove_times = []
    verify_times = []
    prove_step_times = []

    def traverse(node):
        if node['name'] == keygen_span:
            keygen_times.append(node['time_busy'])
        elif node['name'] == prove_span:
            if prove_step_filter is None or node.get('fields', {}).get('steps', None) is not None:
                prove_times.append(node['time_busy'])
        elif node['name'] == verify_span:
            verify_times.append(node['time_busy'])
        elif prove_step_spans and node['name'] in prove_step_spans:
            prove_step_times.append(node['time_busy'])

        for child in node.get('children', []):
            traverse(child)

    for root in json_data['roots']:
        traverse(root)

    return (
        (statistics.mean(keygen_times) if keygen_times else None, len(keygen_times)),
        (statistics.mean(prove_times) if prove_times else None, len(prove_times)),
        (statistics.mean(verify_times) if verify_times else None, len(verify_times)),
        (statistics.mean(prove_step_times) if prove_step_times else None, len(prove_step_times))
    )

def get_spans_for_file(file_name, mapping):
    for prefix, spans in mapping.items():
        if file_name.startswith(prefix):
            return spans
    return None, None, None, None, None  # Return None if no prefix matches

def process_log_files(log_files, mapping):
    table = "| Repeat Count | Name | Keygen | Prove | Verify | Prove Step |\n"
    table += "|--------------|------|--------|-------|--------|------------|\n"

    entries = []

    for log_file in log_files:
        log_processor = LogProcessor()

        with open(log_file, 'r') as f:
            log_data = f.readlines()

        for line in log_data:
            log_processor.process_log_line(line.strip())

        json_data = log_processor.span_tree.to_dict()

        file_name = os.path.basename(log_file)
        keygen_span, prove_span, verify_span, prove_step_spans, prove_step_filter = get_spans_for_file(file_name, mapping)

        if keygen_span is None:
            continue  # Skip files without a matching prefix

        try:
            base_name, repeat_count_str = file_name.rsplit('_', 1)
            repeat_count = int(repeat_count_str)
        except ValueError:
            print(f"Error: No valid postfix found in filename '{file_name}'. Skipping this file.")
            continue

        keygen_time, prove_time, verify_time, prove_step_time = extract_data(json_data, keygen_span, prove_span, verify_span, prove_step_spans, prove_step_filter)

        def format_time(time, count):
            return f"{time} (x{count})" if count > 1 else str(time)

        entry = (
            repeat_count,
            base_name,
            format_time(keygen_time[0], keygen_time[1]),
            format_time(prove_time[0], prove_time[1]),
            format_time(verify_time[0], verify_time[1]),
            format_time(prove_step_time[0], prove_step_time[1]) if prove_step_spans else ''
        )
        entries.append(entry)

    # Sort entries by repeat count
    entries.sort(key=lambda x: x[0])

    for entry in entries:
        table += f"| {entry[0]} | {entry[1]} | {entry[2]} | {entry[3]} | {entry[4]} | {entry[5]} |\n"

    return table

def main():
    if len(sys.argv) < 2:
        print("Usage: python script.py <log_file1> <log_file2> ...")
        sys.exit(1)

    log_files = sys.argv[1:]

    # Define the mapping from filename prefixes to span names
    mapping = {
        "sirius_": ("keygen", "prove", "ivc_vefify", ["ivc_new", "ivc_fold_step"], "step"),
        "halo2_": ("keygen", "prove", "verify", None, None),
    }

    table = process_log_files(log_files, mapping)

    with open('output.md', 'w') as f:
        f.write(table)
    print(table)

if __name__ == "__main__":
    main()
