#!/usr/bin/env python3
"""Pure stage-0 → stage-1 YOCO-3B reshape authority repair."""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import math
import os
import re
import tempfile
from pathlib import Path

INPUT_SHA256 = "6a0cc311915ff1e0b1bd3e0e2fff5ebf3ce60ccf8e8bf8804067f7e569c79c49"
OUTPUT_SHA256 = "004c1ecaad96fcea186dc6050fec40bbfb74d96c12343068fa813e788cd0e1a3"
EXPECTED_SET_SHA256 = "e14f81dbff4eb14b5c17fd192be371132d423d241adef3e7e887f4746d626c3a"
EXPECTED_GRAPH_NODES = {"sm": 1343, "pm": 2973}
EXPECTED_SHAPE_COUNTS = {"sm": 3935, "pm": 7992}
EXPECTED_HISTOGRAM = {
    ("sm", 0, (8192, 3072)): 170,
    ("sm", 0, (8192, 6144)): 30,
    ("sm", 0, (8192, 9216)): 40,
}
for rank in (0, 1):
    EXPECTED_HISTOGRAM.update({
        ("pm", rank, (4096, 3072)): 130,
        ("pm", rank, (4096, 6144)): 30,
        ("pm", rank, (4096, 9216)): 20,
        ("pm", rank, (8192, 3072)): 40,
        ("pm", rank, (8192, 4608)): 20,
    })


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def definition(source: str, name: str) -> tuple[int, int, str]:
    match = re.search(rf"(?m)^def\s+{re.escape(name)}\b[^:]*:.*?:=", source)
    if match is None:
        raise RuntimeError(f"missing definition {name}")
    next_def = re.search(r"(?m)^def\s+", source[match.end():])
    end = len(source) if next_def is None else match.end() + next_def.start()
    return match.start(), end, source[match.start():end]


def shape_map(source: str, name: str) -> dict[int, tuple[int, ...]]:
    _start, _end, block = definition(source, name)
    pairs = re.findall(r"\(\s*(\d+)\s*,\s*\[([0-9,\s]*)\]\s*\)", block)
    result = {}
    for tid_text, dims_text in pairs:
        tid = int(tid_text); shape = tuple(map(int, re.findall(r"\d+", dims_text)))
        if tid in result:
            raise RuntimeError(f"duplicate shape TID {name}:{tid}")
        result[tid] = shape
    return result


RESHAPE = re.compile(
    r'^(?P<indent>\s*)\{\s*rank\s*:=\s*(?P<rank>\d+),\s*'
    r'op\s*:=\s*"OpName\.FW_reshape",\s*ins\s*:=\s*\[(?P<input>\d+)\],\s*'
    r'outs\s*:=\s*\[(?P<output>\d+)\]'
    r'(?:,\s*params\s*:=\s*\[(?P<params>[0-9,\s]+)\])?\s*\},(?P<newline>\n?)$'
)


def transform(source: str) -> tuple[str, int]:
    shapes = {
        "sm": shape_map(source, "smInitShapes"),
        "pm": shape_map(source, "pmInitShapes"),
    }
    for graph, count in EXPECTED_SHAPE_COUNTS.items():
        if len(shapes[graph]) != count:
            raise RuntimeError(f"{graph} shape table count mismatch: {len(shapes[graph])}")
    replacements = []
    mutation_records = []
    histogram = collections.Counter()
    for graph in ("sm", "pm"):
        start, end, block = definition(source, graph)
        lines = block.splitlines(keepends=True)
        node_index = -1
        declared = 0
        for local_offset, line in enumerate(lines):
            if re.search(r"\{\s*rank\s*:=", line):
                declared += 1; node_index += 1
            match = RESHAPE.match(line)
            if match is None:
                continue
            rank = int(match.group("rank")); input_tid = int(match.group("input")); output_tid = int(match.group("output"))
            output_shape = shapes[graph].get(output_tid); input_shape = shapes[graph].get(input_tid)
            if input_shape is None or output_shape is None:
                raise RuntimeError(f"reshape lacks pinned shapes: {graph}[{node_index}]")
            if len(output_shape) != 2 or math.prod(input_shape) != math.prod(output_shape):
                raise RuntimeError(f"reshape shape contract fails: {graph}[{node_index}]")
            params_text = match.group("params")
            params = None if params_text is None else tuple(map(int, re.findall(r"\d+", params_text)))
            if params is not None and params != output_shape:
                raise RuntimeError(f"reshape has wrong existing params: {graph}[{node_index}]")
            histogram[(graph, rank, output_shape)] += 1
            mutation_records.append({
                "graph": graph, "index": node_index, "rank": rank,
                "input": input_tid, "output": output_tid, "params": list(output_shape),
            })
            if params is None:
                old = line
                base = line[:line.rfind("}")].rstrip()
                if base.endswith(","):
                    base = base[:-1].rstrip()
                new = f"{base}, params := [{', '.join(map(str, output_shape))}] }},{match.group('newline')}"
                replacements.append((start + sum(map(len, lines[:local_offset])), old, new))
        if declared != EXPECTED_GRAPH_NODES[graph]:
            raise RuntimeError(f"{graph} graph node count mismatch: {declared}")
    if histogram != collections.Counter(EXPECTED_HISTOGRAM):
        raise RuntimeError(f"reshape histogram mismatch: {histogram}")
    payload = json.dumps(mutation_records, sort_keys=True, separators=(",", ":")).encode()
    if digest(payload) != EXPECTED_SET_SHA256:
        raise RuntimeError(f"reshape exact-set digest mismatch: {digest(payload)}")
    if len(mutation_records) != 720:
        raise RuntimeError(f"reshape census mismatch: {len(mutation_records)}")
    if len(replacements) not in {0, 720}:
        raise RuntimeError(f"mixed reshape migration state: {len(replacements)} missing params")
    result = source
    for absolute, old, new in sorted(replacements, reverse=True):
        if result[absolute:absolute + len(old)] != old:
            raise RuntimeError("reshape replacement span changed")
        result = result[:absolute] + new + result[absolute + len(old):]
    return result, len(replacements)


def write_atomic(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data); stream.flush(); os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try: os.unlink(temporary)
        except FileNotFoundError: pass
        raise


def main() -> None:
    parser = argparse.ArgumentParser(); parser.add_argument("input", type=Path); parser.add_argument("output", type=Path)
    args = parser.parse_args(); data = args.input.read_bytes(); input_digest = digest(data)
    if input_digest not in {INPUT_SHA256, OUTPUT_SHA256}:
        raise RuntimeError(f"unexpected input SHA-256: {input_digest}")
    result, changed = transform(data.decode("utf-8")); output = result.encode(); output_digest = digest(output)
    if output_digest != OUTPUT_SHA256:
        raise RuntimeError(f"unexpected output SHA-256: {output_digest}")
    expected = 720 if input_digest == INPUT_SHA256 else 0
    if changed != expected:
        raise RuntimeError(f"unexpected reshape mutation count: {changed}")
    write_atomic(args.output, output)
    print(f"authority_reshape_migration input={input_digest} output={output_digest} changed={changed}")


if __name__ == "__main__":
    main()
