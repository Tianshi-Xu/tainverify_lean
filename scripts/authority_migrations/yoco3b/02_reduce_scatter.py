#!/usr/bin/env python3
"""Pure stage-1 → stage-2 YOCO-3B ReduceScatter authority repair."""
from __future__ import annotations

import argparse
import hashlib
import os
import tempfile
from pathlib import Path

INPUT_SHA256 = "004c1ecaad96fcea186dc6050fec40bbfb74d96c12343068fa813e788cd0e1a3"
OUTPUT_SHA256 = "0d0c38b76af3830ed08f06a61e38697537f3ef004139c107bdff7d5e9b555381"
REPLACEMENTS = (
    (
        '    { rank := 0, op := "OpName.AllReducePrim", ins := [9819, 9820], outs := [9811] },',
        '    { rank := 0, op := "OpName.ReduceScatterPrim", ins := [9819, 9820], outs := [9811], params := [0] },',
    ),
    (
        '    { rank := 1, op := "OpName.AllReducePrim", ins := [9819, 9820], outs := [9812] },',
        '    { rank := 1, op := "OpName.ReduceScatterPrim", ins := [9819, 9820], outs := [9812], params := [0] },',
    ),
)
EXPECTED_SHAPES = {
    9819: (8192, 3072), 9820: (8192, 3072),
    9811: (4096, 3072), 9812: (4096, 3072),
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def validate_shape_evidence(source: str) -> None:
    for tid, shape in EXPECTED_SHAPES.items():
        literal = f"({tid}, [{', '.join(map(str, shape))}])"
        if source.count(literal) != 1:
            raise RuntimeError(f"missing or duplicate pinned PM shape evidence: {literal}")


def transform(source: str) -> tuple[str, int]:
    validate_shape_evidence(source)
    old_counts = tuple(source.count(old) for old, _new in REPLACEMENTS)
    new_counts = tuple(source.count(new) for _old, new in REPLACEMENTS)
    if old_counts == (1, 1) and new_counts == (0, 0):
        result = source
        for old, new in REPLACEMENTS:
            result = result.replace(old, new, 1)
        return result, 2
    if old_counts == (0, 0) and new_counts == (1, 1):
        return source, 0
    raise RuntimeError(
        f"mixed or malformed reduce-scatter authority: old={old_counts} new={new_counts}"
    )


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
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path); parser.add_argument("output", type=Path)
    args = parser.parse_args()
    data = args.input.read_bytes(); input_digest = digest(data)
    if input_digest not in {INPUT_SHA256, OUTPUT_SHA256}:
        raise RuntimeError(f"unexpected input SHA-256: {input_digest}")
    source = data.decode("utf-8")
    result, changed = transform(source)
    output = result.encode("utf-8"); output_digest = digest(output)
    if output_digest != OUTPUT_SHA256:
        raise RuntimeError(f"unexpected output SHA-256: {output_digest}")
    if (input_digest == INPUT_SHA256 and changed != 2) or (input_digest == OUTPUT_SHA256 and changed != 0):
        raise RuntimeError(f"unexpected mutation count {changed}")
    write_atomic(args.output, output)
    print(f"authority_reduce_scatter_migration input={input_digest} output={output_digest} changed={changed}")


if __name__ == "__main__":
    main()
