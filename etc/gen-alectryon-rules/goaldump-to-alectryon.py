#!/usr/bin/env python3
# Copyright © 2025 Ali Caglayan
# SPDX-License-Identifier: MIT
"""Convert fcc goaldump JSON to alectryon JSON format.

Usage:
    python goaldump-to-alectryon.py file.v > file.v.alectryon.json

Or with explicit goaldump path:
    python goaldump-to-alectryon.py file.v --goaldump file.v.json.goaldump

The output can be used with alectryon's json frontend:
    alectryon --frontend coq.json file.v.alectryon.json -o file.html
"""

import argparse
import json
import sys
from pathlib import Path
from typing import List, Optional


def parse_goaldump(goaldump_path: Path) -> List[dict]:
    """Parse the goaldump JSON file.

    The file contains multiple JSON objects concatenated together.
    We use json.JSONDecoder.raw_decode() to correctly handle strings
    containing braces.
    """
    content = goaldump_path.read_text()
    decoder = json.JSONDecoder()
    objects = []
    idx = 0
    length = len(content)

    while idx < length:
        # Skip whitespace
        while idx < length and content[idx].isspace():
            idx += 1
        if idx >= length:
            break
        try:
            obj, end_idx = decoder.raw_decode(content, idx)
            objects.append(obj)
            idx = end_idx
        except json.JSONDecodeError as e:
            print(f"Warning: Skipping malformed JSON at position {idx}: {e}",
                  file=sys.stderr)
            # Skip to next '{' to try to recover
            idx += 1
            while idx < length and content[idx] != '{':
                idx += 1

    return objects


def decode_hyp(hyp: dict) -> dict:
    """Decode a hypothesis from goaldump JSON to alectryon format."""
    names = hyp.get("names", [])
    # Names can be strings or ["Id", "name"] pairs
    decoded_names = []
    for n in names:
        if isinstance(n, list) and len(n) == 2 and n[0] == "Id":
            decoded_names.append(n[1])
        else:
            decoded_names.append(str(n))

    return {
        "_type": "hypothesis",
        "names": decoded_names,
        "body": hyp.get("def"),  # Can be None
        "type": hyp.get("ty", "")
    }


def decode_goal(goal: dict) -> dict:
    """Decode a goal from goaldump JSON to alectryon format."""
    info = goal.get("info", {})
    name = info.get("name")
    if isinstance(name, list) and len(name) == 2 and name[0] == "Id":
        name = name[1]
    elif name:
        name = str(name)
    else:
        name = None

    return {
        "_type": "goal",
        "name": name,
        "conclusion": goal.get("ty", ""),
        "hypotheses": [decode_hyp(h) for h in goal.get("hyps", [])]
    }


def decode_goals(goals_obj: Optional[dict]) -> List[dict]:
    """Decode goals from goaldump JSON to alectryon format."""
    if not goals_obj:
        return []
    goals_list = goals_obj.get("goals", [])
    return [decode_goal(g) for g in goals_list]


def compute_lines(source: str) -> List[str]:
    """Split source into lines, preserving line structure."""
    return source.split('\n')


def compute_offsets(source: str) -> List[int]:
    """Compute beginning-of-line character offsets for the source text."""
    offsets = [0]
    for i, char in enumerate(source):
        if char == '\n':
            offsets.append(i + 1)
    return offsets


def utf16_to_char_offset(line_text: str, utf16_col: int) -> int:
    """Convert a UTF-16 code unit offset to a Python character offset.

    fcc (coq-lsp) uses UTF-16 code units for column positions (the LSP
    default). Python strings are indexed by Unicode code points (UTF-32).
    Characters outside the Basic Multilingual Plane (e.g. 𝕊 U+1D54A) take
    2 UTF-16 code units but 1 Python character, so we need to convert.
    """
    utf16_units = 0
    for i, ch in enumerate(line_text):
        if utf16_units >= utf16_col:
            return i
        # Characters outside BMP take 2 UTF-16 code units
        utf16_units += 2 if ord(ch) > 0xFFFF else 1
    return len(line_text)


def lc_to_offset(bol_offsets: List[int], lines: List[str],
                 line: int, col: int) -> int:
    """Convert 0-based line and UTF-16 column to character offset."""
    if line < len(bol_offsets):
        line_text = lines[line] if line < len(lines) else ""
        return bol_offsets[line] + utf16_to_char_offset(line_text, col)
    return bol_offsets[-1] if bol_offsets else 0


def convert_goaldump_to_alectryon(source_path: Path, goaldump_path: Path) -> List[List[dict]]:
    """Convert goaldump JSON to alectryon JSON format."""
    source = source_path.read_text()
    lines = compute_lines(source)
    bol_offsets = compute_offsets(source)

    objects = parse_goaldump(goaldump_path)

    fragments = []
    last_end = 0

    for i, obj in enumerate(objects):
        if not isinstance(obj, dict):
            print(f"Warning: Skipping non-object entry at index {i}",
                  file=sys.stderr)
            continue

        raw = obj.get("raw", "")
        if not raw:
            continue

        rng = obj.get("range")
        if not isinstance(rng, dict):
            print(f"Warning: Skipping entry at index {i} with missing/invalid range",
                  file=sys.stderr)
            continue

        start = rng.get("start", {})
        end = rng.get("end", {})

        # Convert line/character (UTF-16) to character offsets
        start_line = start.get("line", 0)
        start_char = start.get("character", 0)
        end_line = end.get("line", 0)
        end_char = end.get("character", 0)

        beg = lc_to_offset(bol_offsets, lines, start_line, start_char)
        end_offset = lc_to_offset(bol_offsets, lines, end_line, end_char)

        if beg > len(source) or end_offset > len(source):
            print(f"Warning: Skipping entry at index {i} with out-of-bounds range "
                  f"(line {start_line}:{start_char} to {end_line}:{end_char})",
                  file=sys.stderr)
            continue

        if end_offset <= beg:
            print(f"Warning: Skipping entry at index {i} with empty/inverted range",
                  file=sys.stderr)
            continue

        # Add text fragment for any gap
        if beg > last_end:
            text_content = source[last_end:beg]
            if text_content:
                fragments.append({
                    "_type": "text",
                    "contents": text_content
                })

        # Add sentence fragment
        content = source[beg:end_offset]
        goals = decode_goals(obj.get("goals"))

        fragments.append({
            "_type": "sentence",
            "contents": content,
            "messages": [],  # goaldump doesn't include messages
            "goals": goals
        })

        last_end = end_offset

    # Add trailing text
    if last_end < len(source):
        trailing = source[last_end:]
        if trailing:
            fragments.append({
                "_type": "text",
                "contents": trailing
            })

    # Alectryon expects a list of chunks, each chunk is a list of fragments
    # For a single file, we have one chunk
    return [fragments]


def main():
    parser = argparse.ArgumentParser(
        description="Convert fcc goaldump JSON to alectryon JSON format"
    )
    parser.add_argument("source", type=Path, help="Source .v file")
    parser.add_argument("--goaldump", type=Path,
                       help="Path to .json.goaldump file (default: source.json.goaldump)")
    parser.add_argument("-o", "--output", type=Path,
                       help="Output file (default: stdout)")

    args = parser.parse_args()

    source_path = args.source
    if not source_path.exists():
        print(f"Error: Source file not found: {source_path}", file=sys.stderr)
        sys.exit(1)

    goaldump_path = args.goaldump or Path(str(source_path) + ".json.goaldump")
    if not goaldump_path.exists():
        print(f"Error: Goaldump file not found: {goaldump_path}", file=sys.stderr)
        print(f"Generate it with: fcc --no_vo --plugin=coq-lsp.plugin.goaldump {source_path}",
              file=sys.stderr)
        sys.exit(1)

    try:
        result = convert_goaldump_to_alectryon(source_path, goaldump_path)
    except Exception as e:
        print(f"Error: Failed to convert {source_path}: {e}", file=sys.stderr)
        sys.exit(1)

    # Validate that we produced some fragments (empty output usually means
    # fcc failed to produce a usable goaldump)
    fragments = result[0] if result else []
    sentences = [f for f in fragments if f.get("_type") == "sentence"]
    if not sentences:
        print(f"Warning: No sentences produced for {source_path}. "
              f"The goaldump may be empty or malformed.", file=sys.stderr)

    output = json.dumps(result, indent=2)

    if args.output:
        args.output.write_text(output)
    else:
        print(output)


if __name__ == "__main__":
    main()
