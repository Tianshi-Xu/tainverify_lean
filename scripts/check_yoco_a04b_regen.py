#!/usr/bin/env python3
"""Compare a regenerated YOCO A0.4B snapshot with the checked-in authority."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LEAN = ROOT / "trainverify" / "denote" / "GeneratedYOCOMoE.lean"
DEFAULT_MANIFEST = ROOT / "trainverify" / "denote" / "GeneratedYOCOMoE.manifest.json"


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _definition_region(text: str, name: str, next_name: str | None = None) -> str:
    start_match = re.search(rf"(?:^|\n)def {re.escape(name)}\b", text)
    if not start_match:
        return ""
    start = start_match.start()
    if next_name:
        end_match = re.search(rf"\ndef {re.escape(next_name)}\b", text[start + 1 :])
        if end_match:
            return text[start : start + 1 + end_match.start()]
    end_match = re.search(r"\ndef \w+\b", text[start + 1 :])
    return text[start : start + 1 + end_match.start()] if end_match else text[start:]


def _nodes(text: str, graph: str, next_graph: str | None) -> list[list[Any]]:
    region = _definition_region(text, graph, next_graph)
    pattern = re.compile(
        r'\{ rank := (\d+), op := "([^"]+)", ins := (.*?), outs := (.*?)(?:, params := (.*?))? \},$'
    )
    result: list[list[Any]] = []
    for raw_line in region.splitlines():
        match = pattern.search(raw_line.strip())
        if match:
            result.append([
                int(match.group(1)), match.group(2), match.group(3),
                match.group(4), match.group(5) or "[]",
            ])
    return result


def _shapes(text: str, graph: str) -> list[list[Any]]:
    region = _definition_region(text, f"{graph}InitShapes")
    result: list[list[Any]] = []
    for tid, dims in re.findall(r"\((\d+),\s*(\[[0-9, ]*\])\)", region):
        result.append([int(tid), ast.literal_eval(dims)])
    return result


def _lineages(text: str, prefix: str) -> dict[str, list[list[int]]]:
    result: dict[str, list[list[int]]] = {}
    pattern = re.compile(
        rf"def {re.escape(prefix)}(\d+)\s*: LineageGoal :=\s*\n\s*\{{(.*?)\}}\s*(?=\n)", re.DOTALL
    )
    for name_tid, body in pattern.findall(text):
        pieces = [[int(rank), int(tid)] for rank, tid in re.findall(
            r"rank := (\d+), tid := (\d+)", body
        )]
        result[str(int(name_tid))] = pieces
    return result


def _nat_list_definition(text: str, name: str) -> list[int]:
    match = re.search(rf"def {re.escape(name)}\s*: List Nat := \[([0-9, ]*)\]", text)
    if not match or not match.group(1).strip():
        return []
    return [int(item.strip()) for item in match.group(1).split(",")]


def extract_snapshot(data: bytes) -> dict[str, Any]:
    text = data.decode("utf-8")
    return {
        "ordered_nodes": {"sm": _nodes(text, "sm", "pm"), "pm": _nodes(text, "pm", None)},
        "shapes": {"sm": _shapes(text, "sm"), "pm": _shapes(text, "pm")},
        "init_lineages": _lineages(text, "initGoal_"),
        "final_goal_tids": _nat_list_definition(text, "obsTids"),
        "intermediate_goal_tids": sorted(map(int, _lineages(text, "intermediateGoal_").keys())),
    }


def _load_manifest(path: Path) -> tuple[bytes, dict[str, Any]]:
    raw = path.read_bytes()
    return raw, json.loads(raw)


def compare_snapshots(
    expected_lean: Path, regenerated_lean: Path,
    expected_manifest: Path, regenerated_manifest: Path,
) -> None:
    expected_bytes = expected_lean.read_bytes()
    regenerated_bytes = regenerated_lean.read_bytes()
    expected_manifest_bytes, expected_meta = _load_manifest(expected_manifest)
    regenerated_manifest_bytes, regenerated_meta = _load_manifest(regenerated_manifest)

    assert extract_snapshot(regenerated_bytes) == extract_snapshot(expected_bytes), (
        "ordered nodes, shapes, init lineages, or final/intermediate goal sets differ"
    )
    assert regenerated_manifest_bytes == expected_manifest_bytes, "manifest bytes differ"
    assert regenerated_meta == expected_meta, "manifest values differ"
    assert regenerated_bytes == expected_bytes, "Lean bytes differ"
    assert expected_meta["generated_lean_sha256"] == _sha256(expected_bytes), (
        "checked-in manifest does not hash the checked-in Lean snapshot"
    )
    assert regenerated_meta["generated_lean_sha256"] == _sha256(regenerated_bytes), (
        "regenerated manifest does not hash regenerated Lean"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-lean", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--expected-manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--regenerated-lean", type=Path, required=True)
    parser.add_argument("--regenerated-manifest", type=Path, required=True)
    args = parser.parse_args()
    compare_snapshots(
        args.expected_lean, args.regenerated_lean,
        args.expected_manifest, args.regenerated_manifest,
    )
    snapshot = extract_snapshot(args.regenerated_lean.read_bytes())
    print(
        "YOCO A0.4B regeneration matches: "
        f"SM nodes={len(snapshot['ordered_nodes']['sm'])}, "
        f"PM nodes={len(snapshot['ordered_nodes']['pm'])}, "
        f"final={len(snapshot['final_goal_tids'])}, "
        f"intermediate={len(snapshot['intermediate_goal_tids'])}"
    )


if __name__ == "__main__":
    main()
