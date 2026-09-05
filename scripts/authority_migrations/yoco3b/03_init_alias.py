#!/usr/bin/env python3
"""Deterministically repair YOCO-3B singleton InitGoal aliases.

Pure byte transform: INPUT and OUTPUT are explicit paths.  The accepted input
is either the pinned stage-2 authority or the already-migrated stage-3 bytes.
No project modules or worktree authority files are imported.
"""
from __future__ import annotations

import argparse
import hashlib
import os
import re
import tempfile
from pathlib import Path

INPUT_SHA256 = "0d0c38b76af3830ed08f06a61e38697537f3ef004139c107bdff7d5e9b555381"
OUTPUT_SHA256 = "3fe2cd76ca48a616960478ed0861dbfe0713b93ca5a1caebeaa4246d7f1f6b38"
EXPECTED = {
    6315: 15935, 6318: 15949, 6322: 15962, 6327: 15975,
    6361: 15987, 6364: 16001, 6368: 16014, 6373: 16027,
    6407: 16039, 6410: 16053, 6414: 16066, 6419: 16079,
    6453: 16091, 6456: 16105, 6460: 16118, 6465: 16131,
    6499: 16143, 6502: 16157, 6506: 16170, 6511: 16183,
    6545: 16195, 6548: 16209, 6552: 16222, 6557: 16235,
    6591: 16247, 6594: 16261, 6598: 16274, 6603: 16287,
    6637: 16299, 6640: 16313, 6644: 16326, 6649: 16339,
    6683: 16351, 6686: 16365, 6690: 16378, 6695: 16391,
    6729: 16403, 6732: 16417, 6736: 16430, 6741: 16443,
}
EXPECTED_PROJECTIONS = {0: 10, 1: 30}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def definition(source: str, name: str) -> str:
    match = re.search(rf"(?m)^def\s+{re.escape(name)}\b[^:]*:.*?:=", source)
    if match is None:
        raise RuntimeError(f"missing definition {name}")
    start = match.start()
    next_def = re.search(r"(?m)^def\s+", source[match.end():])
    end = len(source) if next_def is None else match.end() + next_def.start()
    return source[start:end]


def shape_map(source: str, name: str) -> dict[int, tuple[int, ...]]:
    block = definition(source, name)
    pairs = re.findall(r"\(\s*(\d+)\s*,\s*\[([0-9,\s]*)\]\s*\)", block)
    result: dict[int, tuple[int, ...]] = {}
    for tid_text, dims_text in pairs:
        tid = int(tid_text)
        dims = tuple(int(value) for value in re.findall(r"\d+", dims_text))
        if tid in result:
            raise RuntimeError(f"duplicate {name} TID {tid}")
        result[tid] = dims
    if not result:
        raise RuntimeError(f"empty or malformed {name}")
    return result


def parse_pm_producers(source: str):
    block = definition(source, "pm")
    node_re = re.compile(
        r'\{\s*rank\s*:=\s*(\d+),\s*op\s*:=\s*"OpName\.([^"\n]+)"'
        r'[^\n]*?ins\s*:=\s*\[([0-9,\s]*)\][^\n]*?outs\s*:=\s*\[([0-9,\s]*)\]'
        r'(?:[^\n]*?params\s*:=\s*\[([0-9,\s]*)\])?[^\n]*?\}'
    )
    matches = list(node_re.finditer(block))
    declared = len(re.findall(r"\{\s*rank\s*:=", block))
    if len(matches) != declared:
        raise RuntimeError(
            f"PM graph parser consumed {len(matches)} of {declared} declared nodes"
        )
    producers = {}
    for node_index, match in enumerate(matches):
        rank = int(match.group(1))
        op = match.group(2)
        ins = tuple(int(value) for value in re.findall(r"\d+", match.group(3)))
        outs = tuple(int(value) for value in re.findall(r"\d+", match.group(4)))
        params = tuple(int(value) for value in re.findall(r"\d+", match.group(5) or ""))
        node = (node_index, rank, op, ins, outs, params)
        for output in outs:
            key = (rank, output)
            if key in producers:
                raise RuntimeError(f"duplicate PM producer for rank/TID {key}")
            producers[key] = node
    if not producers:
        raise RuntimeError("PM graph parser found no producers")
    return producers


def init_goal(source: str, ts: int):
    matches = list(re.finditer(
        rf"(?m)^def initGoal_{ts}\s*:\s*LineageGoal\s*:=\s*\n"
        rf"(?P<line>\s*\{{\s*ts\s*:=\s*{ts}\b[^\n]*\}}\s*)$",
        source,
    ))
    if len(matches) != 1:
        raise RuntimeError(f"expected one exact initGoal_{ts}, found {len(matches)}")
    line = matches[0].group("line")
    shape_match = re.search(r"tsShape\s*:=\s*\[([0-9,\s]*)\]", line)
    pieces = re.findall(r"\{\s*rank\s*:=\s*(\d+),\s*tid\s*:=\s*(\d+)\s*\}", line)
    tp_shapes_match = re.search(r"tpShapes\s*:=\s*\[\[([0-9,\s]*)\]\]", line)
    if shape_match is None or tp_shapes_match is None or len(pieces) != 1:
        raise RuntimeError(f"malformed singleton initGoal_{ts}")
    full_shape = tuple(int(value) for value in re.findall(r"\d+", shape_match.group(1)))
    tp_shape = tuple(int(value) for value in re.findall(r"\d+", tp_shapes_match.group(1)))
    return matches[0], (int(pieces[0][0]), int(pieces[0][1])), full_shape, tp_shape


def validate_and_transform(source: str) -> tuple[str, dict[int, int]]:
    producers = parse_pm_producers(source)
    shapes = shape_map(source, "pmInitShapes")
    replacements: dict[int, int] = {}
    projections = {0: 0, 1: 0}
    output = source
    for ts, expected_piece in sorted(EXPECTED.items()):
        match, piece, full_shape, tp_shape = init_goal(source, ts)
        if piece == (0, ts):
            continue
        if piece != (0, expected_piece):
            raise RuntimeError(
                f"initGoal_{ts} expected rank-0 piece {expected_piece}, got {piece}"
            )
        node = producers.get((0, expected_piece))
        if node is None:
            raise RuntimeError(f"initGoal_{ts} expected rank-0 producer is missing")
        _index, rank, op, ins, outs, params = node
        if rank != 0 or op != "FW_multiref" or ins != (ts,):
            raise RuntimeError(f"initGoal_{ts} producer identity is malformed: {node}")
        if params != (len(outs),) or expected_piece not in outs:
            raise RuntimeError(f"initGoal_{ts} producer arity/projection is malformed")
        projection = outs.index(expected_piece)
        if projection not in projections:
            raise RuntimeError(f"initGoal_{ts} unexpected projection {projection}")
        if any(key[1] == ts for key in producers):
            raise RuntimeError(f"initGoal_{ts} source TID is graph-written")
        if full_shape != tp_shape or shapes.get(ts) != full_shape or shapes.get(expected_piece) != full_shape:
            raise RuntimeError(f"initGoal_{ts} lineage/input/output shapes disagree")
        old_line = match.group("line")
        new_line, count = re.subn(
            rf"(tps\s*:=\s*\[\{{\s*rank\s*:=\s*0,\s*tid\s*:=\s*){expected_piece}(\s*\}}\])",
            rf"\g<1>{ts}\g<2>", old_line, count=1,
        )
        if count != 1:
            raise RuntimeError(f"initGoal_{ts} exact TID replacement failed")
        output, count = re.subn(re.escape(old_line), lambda _m, value=new_line: value, output, count=1)
        if count != 1:
            raise RuntimeError(f"initGoal_{ts} exact line replacement was non-unique")
        replacements[ts] = expected_piece
        projections[projection] += 1
    if replacements and replacements != EXPECTED:
        raise RuntimeError(f"migration exact-set mismatch: {replacements}")
    if replacements and projections != EXPECTED_PROJECTIONS:
        raise RuntimeError(f"migration projection histogram mismatch: {projections}")
    return output, replacements


def write_atomic(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    data = args.input.read_bytes()
    digest = sha256(data)
    if digest not in {INPUT_SHA256, OUTPUT_SHA256}:
        raise RuntimeError(f"unexpected input SHA-256: {digest}")
    source = data.decode("utf-8")
    transformed, replacements = validate_and_transform(source)
    result = transformed.encode("utf-8")
    result_digest = sha256(result)
    if result_digest != OUTPUT_SHA256:
        raise RuntimeError(f"unexpected output SHA-256: {result_digest}")
    if digest == INPUT_SHA256 and len(replacements) != 40:
        raise RuntimeError(f"expected 40 migrations, got {len(replacements)}")
    if digest == OUTPUT_SHA256 and replacements:
        raise RuntimeError("already-migrated input unexpectedly changed")
    write_atomic(args.output, result)
    print(
        f"authority_init_alias_migration input={digest} output={result_digest} "
        f"changed={len(replacements)}"
    )


if __name__ == "__main__":
    main()
