#!/bin/python3

import unittest
import sys
import argparse
import json
import re

from typing import Dict, List, Optional
from datetime import timedelta, datetime


class SpanNode:
    def __init__(
        self,
        name: str,
        start: datetime,
        level: str,
        fields: Optional[Dict[str, str]] = None,
    ):
        self.name = name
        self.start = start
        self.level = level
        self.fields = fields or {}
        self.children: List["SpanNode"] = []
        self.time_busy: Optional[timedelta] = None

    def add_child(self, child: "SpanNode"):
        self.children.append(child)

    def set_time_busy(self, time_busy: timedelta):
        self.time_busy = time_busy

    def to_dict(self) -> Dict:
        return {
            "name": self.name,
            "level": self.level,
            "start": self.start,
            "fields": self.fields,
            "children": [child.to_dict() for child in self.children],
            "time_busy": self.time_busy,
        }

    def to_human_readable(
        self, time_filter: timedelta, indent: int = 0, max_length: int = 80
    ) -> List[str]:
        """
        Generates a human-readable representation of the SpanNode and its children.
        Returns a list of formatted strings.
        """

        if self.time_busy and self.time_busy < time_filter:
            return []

        start_line = "··" * indent + f"Start:  {self.name}"
        end_line = "··" * indent + f"End:    {self.name}"

        # Time busy formatting
        if self.time_busy:
            time_busy_str = f"{self.time_busy.total_seconds():.2f}s"
        else:
            time_busy_str = "unknown"

        # Align time busy
        fill_dots = max_length - len(end_line) - len(time_busy_str)
        end_line += "." * max(0, fill_dots) + time_busy_str

        result = [start_line]
        for child in self.children:
            result.extend(
                child.to_human_readable(
                    time_filter=time_filter, indent=indent + 1, max_length=max_length
                )
            )
        result.append(end_line)
        return result


class SpanTree:
    def __init__(self):
        self.roots: List[SpanNode] = []
        self.span_mapping: Dict[str, SpanNode] = {}

    def to_human_readable(self, time_filter: timedelta, max_length: int = 80) -> str:
        """
        Generates a human-readable representation of the entire SpanTree.
        """
        result = []
        for root in self.roots:
            result.extend(
                root.to_human_readable(max_length=max_length, time_filter=time_filter)
            )
        return "\n".join(result)


class LogProcessor:
    def __init__(self):
        self.span_tree = SpanTree()
        self.span_counters: Dict[str, int] = {}

    def generate_span_key(self, span_info: Dict) -> str:
        """
        Generates a key based on the span information.
        """
        return json.dumps({"span": span_info}, sort_keys=True)

    def find_unfinished_span_node(self, key: str) -> Optional[SpanNode]:
        """
        Find the most recent unfinished SpanNode with the given key.
        """
        candidates = [
            node
            for node_id, node in self.span_tree.span_mapping.items()
            if node_id == key and node.time_busy is None
        ]
        if candidates:
            # Return the node with the latest timestamp
            return sorted(candidates, key=lambda x: x.start, reverse=True)[0]
        return None

    def process_log_line(self, line: str):
        # Parse JSON line
        try:
            log = json.loads(line)
        except json.JSONDecodeError:
            return  # Ignore non-JSON lines

        start = log.get("timestamp", "")
        target = log.get("target", "")
        level = log.get("level", "")
        message = log.get("fields", {}).get("message", "")
        span_info = log.get("span", {})
        spans_info = log.get("spans", [])

        if message == "enter" and span_info:
            # Case 1: Span Enter
            span_key = self.generate_span_key(span_info)
            node_name = span_info.get("name", "")

            new_span = SpanNode(
                name=node_name,
                level=level,
                start=parse_timestamp(start),
                fields={**span_info, **{"target": target}},
            )

            # Fix for determining root node
            if len(spans_info) == 1 and spans_info[0].get("name") == node_name:
                # Root node
                self.span_tree.roots.append(new_span)
            else:
                parent_span_key = self.generate_span_key(spans_info[-2])
                parent_span = self.find_unfinished_span_node(parent_span_key)

                if parent_span:
                    parent_span.add_child(new_span)
                else:
                    raise ValueError(f"Can't find parent for {parent_span}, can't find {spans_info[-2]}")

            # Store the span node in the mapping
            self.span_tree.span_mapping[span_key] = new_span

        elif message == "close" and span_info:
            span_key = self.generate_span_key(span_info)

            span_node = self.find_unfinished_span_node(span_key)
            if span_node:
                time_busy_str = log.get("fields", {}).get("time.busy", "0s")
                time_busy_timedelta = parse_timedelta(time_busy_str)

                if time_busy_timedelta is None:
                    raise ValueError(f"Can't parse: {time_busy_str}")

                span_node.set_time_busy(time_busy_timedelta)


def parse_timedelta(time_str: str) -> Optional[timedelta]:
    """
    Parse the time.busy string into timedelta.
    Supports ns, µs, ms, s.
    """
    match = re.match(r"(\d+(\.\d+)?)([a-zµ]+)", time_str)
    if match:
        value, _, unit = match.groups()
        value = float(value)
        if unit == "ns":
            return timedelta(0)
        elif unit == "µs":
            return timedelta(microseconds=value)
        elif unit == "ms":
            return timedelta(milliseconds=value)
        elif unit == "s":
            return timedelta(seconds=value)

    return None


def parse_timestamp(timestamp_str: str) -> datetime:
    """
    Parse the timestamp string into a datetime object.
    """
    return datetime.fromisoformat(timestamp_str.replace("Z", "+00:00"))


def main():
    import sys

    log_processor = LogProcessor()
    for line in sys.stdin:
        log_processor.process_log_line(line.strip())

    import json

    print(json.dumps(log_processor.get_result_tree(), indent=2))


class TestLogProcessor(unittest.TestCase):
    def setUp(self):
        self.processor = LogProcessor()

    def test_process_log_line(self):
        log_lines = [
            '{"timestamp":"2024-05-09T17:59:30.817151Z","level":"INFO","fields":{"message":"enter"},"target":"poseidon","span":{"name":"poseidon_example"},"spans":[{"name":"poseidon_example"}]}',
            '{"timestamp":"2024-05-09T17:59:30.820519Z","level":"INFO","fields":{"message":"enter"},"target":"poseidon","span":{"k":27,"label":"bn256","name":"get_or_create_commitment_key"},"spans":[{"name":"poseidon_example"},{"k":27,"label":"bn256","name":"get_or_create_commitment_key"}]}',
            '{"timestamp":"2024-05-09T17:59:30.820544Z","level":"INFO","fields":{"message":"\\".cache/examples/bn256/27.bin\\" exists, load key"},"target":"poseidon","span":{"k":27,"label":"bn256","name":"get_or_create_commitment_key"},"spans":[{"name":"poseidon_example"},{"k":27,"label":"bn256","name":"get_or_create_commitment_key"}]}',
            '{"timestamp":"2024-05-09T17:59:34.294587Z","level":"INFO","fields":{"message":"close","time.busy":"3.47s","time.idle":"1.42µs"},"target":"poseidon","span":{"k":27,"label":"bn256","name":"get_or_create_commitment_key"},"spans":[{"name":"poseidon_example"}]}',
            '{"timestamp":"2024-05-09T17:59:34.294652Z","level":"INFO","fields":{"message":"enter"},"target":"poseidon","span":{"k":27,"label":"grumpkin","name":"get_or_create_commitment_key"},"spans":[{"name":"poseidon_example"},{"k":27,"label":"grumpkin","name":"get_or_create_commitment_key"}]}',
            '{"timestamp":"2024-05-09T17:59:34.294668Z","level":"INFO","fields":{"message":"\\".cache/examples/grumpkin/27.bin\\" exists, load key"},"target":"poseidon","span":{"k":27,"label":"grumpkin","name":"get_or_create_commitment_key"},"spans":[{"name":"poseidon_example"},{"k":27,"label":"grumpkin","name":"get_or_create_commitment_key"}]}',
            '{"timestamp":"2024-05-09T17:59:36.536003Z","level":"INFO","fields":{"message":"close","time.busy":"2.24s","time.idle":"2.09µs"},"target":"poseidon","span":{"k":27,"label":"grumpkin","name":"get_or_create_commitment_key"},"spans":[{"name":"poseidon_example"}]}',
            '{"timestamp":"2024-05-09T17:59:36.536088Z","level":"INFO","fields":{"message":"enter"},"target":"sirius::ivc::public_params","span":{"name":"pp_new"},"spans":[{"name":"poseidon_example"},{"name":"pp_new"}]}',
            '{"timestamp":"2024-05-09T17:59:36.536095Z","level":"INFO","fields":{"message":"enter"},"target":"sirius::ivc::public_params","span":{"name":"primary"},"spans":[{"name":"poseidon_example"},{"name":"pp_new"},{"name":"primary"}]}',
            '{"timestamp":"2024-05-09T17:59:36.536127Z","level":"INFO","fields":{"message":"start build constraint system metainfo with 1 custom gates"},"target":"sirius::table::constraint_system_metainfo","span":{"name":"primary"},"spans":[{"name":"poseidon_example"},{"name":"pp_new"},{"name":"primary"}]}',
            '{"timestamp":"2024-05-09T17:59:37.813017Z","level":"INFO","fields":{"message":"close","time.busy":"1.28s","time.idle":"422ns"},"target":"sirius::ivc::public_params","span":{"name":"primary"},"spans":[{"name":"poseidon_example"},{"name":"pp_new"}]}',
        ]

        for line in log_lines:
            self.processor.process_log_line(line)

        # Check the structure of the root span "poseidon_example"
        roots = self.processor.span_tree.roots
        self.assertEqual(len(roots), 1)
        root_span = roots[0]
        self.assertEqual(root_span.name, "poseidon_example")
        self.assertEqual(
            root_span.start, parse_timestamp("2024-05-09T17:59:30.817151Z")
        )
        self.assertIsNone(root_span.time_busy)

        # Check the child "get_or_create_commitment_key_bn256"
        child_bn256 = root_span.children[0]
        self.assertEqual(child_bn256.name, "get_or_create_commitment_key")
        self.assertEqual(
            child_bn256.start, parse_timestamp("2024-05-09T17:59:30.820519Z")
        )
        self.assertEqual(child_bn256.time_busy, timedelta(seconds=3.47))

        # Check the child "get_or_create_commitment_key_grumpkin"
        child_grumpkin = root_span.children[1]
        self.assertEqual(child_grumpkin.name, "get_or_create_commitment_key")
        self.assertEqual(
            child_grumpkin.start, parse_timestamp("2024-05-09T17:59:34.294652Z")
        )
        self.assertEqual(child_grumpkin.time_busy, timedelta(seconds=2.24))

        # Check the grandchild "pp_new"
        grandchild_pp_new = root_span.children[2]
        self.assertEqual(grandchild_pp_new.name, "pp_new")
        self.assertEqual(
            grandchild_pp_new.start, parse_timestamp("2024-05-09T17:59:36.536088Z")
        )
        self.assertIsNone(grandchild_pp_new.time_busy)

        # Check the grand-grandchild "primary"
        grandgrandchild_primary = grandchild_pp_new.children[0]
        self.assertEqual(grandgrandchild_primary.name, "primary")
        self.assertEqual(
            grandgrandchild_primary.start,
            parse_timestamp("2024-05-09T17:59:36.536095Z"),
        )
        self.assertEqual(grandgrandchild_primary.time_busy, timedelta(seconds=1.28))


def main():
    parser = argparse.ArgumentParser(
        description="Process log files and filter spans based on time_busy."
    )
    parser.add_argument(
        "--min-busy",
        type=str,
        default="1s",
        help="Minimum busy time to display (default: 1s)",
    )
    args = parser.parse_args()

    min_busy = parse_timedelta(args.min_busy)
    if min_busy is None:
        raise ValueError(f"Can't parse {args.min_busy} as min busy")

    log_processor = LogProcessor()
    for line in sys.stdin:
        log_processor.process_log_line(line.strip())

    print(log_processor.span_tree.to_human_readable(time_filter=min_busy))


if __name__ == "__main__":
    main()
