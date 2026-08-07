#!/usr/bin/env python3
"""Compare a regenerated YOCO A0.4B snapshot with the checked-in authority."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
from pathlib import Path, PurePosixPath
from typing import Any, cast


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LEAN = ROOT / "trainverify" / "denote" / "GeneratedYOCOMoE.lean"
DEFAULT_MANIFEST = ROOT / "trainverify" / "denote" / "GeneratedYOCOMoE.manifest.json"


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


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


def _replica_groups(text: str, graph: str, next_graph: str | None) -> list[list[Any]]:
    region = _definition_region(text, graph, next_graph)
    result: list[list[Any]] = []
    pattern = re.compile(
        r'\{ logical := \{ cid := (\d+), mb := (\d+), irname := "([^"]+)" \}, '
        r'members := \[(.*?)\] \}'
    )
    for cid, mb, irname, members_body in pattern.findall(region):
        members = [[int(rank), int(tid)] for rank, tid in re.findall(
            r"rank := (\d+), primaryOutTid := (\d+)", members_body
        )]
        result.append([int(cid), int(mb), irname, members])
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


def _input_value_classes(text: str, graph: str) -> list[list[Any]]:
    region = _definition_region(text, f"{graph}InputValueClasses")
    result: list[list[Any]] = []
    pattern = re.compile(
        r'\{ source := "((?:[^"\\]|\\.)*)", tids := \[([0-9, ]*)\] \}'
    )
    for source, tids_body in pattern.findall(region):
        tids = [int(item.strip()) for item in tids_body.split(",") if item.strip()]
        result.append([bytes(source, "utf-8").decode("unicode_escape"), tids])
    return result


def extract_snapshot(data: bytes) -> dict[str, Any]:
    text = data.decode("utf-8")
    return {
        "ordered_nodes": {"sm": _nodes(text, "sm", "pm"), "pm": _nodes(text, "pm", None)},
        "replica_groups": {
            "sm": _replica_groups(text, "sm", "pm"),
            "pm": _replica_groups(text, "pm", None),
        },
        "shapes": {"sm": _shapes(text, "sm"), "pm": _shapes(text, "pm")},
        "input_value_classes": {
            "sm": _input_value_classes(text, "sm"),
            "pm": _input_value_classes(text, "pm"),
        },
        "init_lineages": _lineages(text, "initGoal_"),
        "final_goal_tids": _nat_list_definition(text, "obsTids"),
        "intermediate_goal_tids": sorted(map(int, _lineages(text, "intermediateGoal_").keys())),
    }


def _load_manifest(path: Path) -> tuple[bytes, dict[str, Any]]:
    raw = path.read_bytes()
    return raw, json.loads(raw)


def _validate_candidate_manifest(meta: dict[str, Any]) -> None:
    _require(meta.get("schema_version") == 3, "candidate manifest is not schema v3")
    artifacts = meta.get("artifact_sha256")
    expected_artifacts = {"nnscaler_dp_solver.so", "comp_profile.json"}
    _require(isinstance(artifacts, dict) and set(artifacts) == expected_artifacts,
        "candidate manifest must contain exactly the solver and computation profile hashes"
    )
    artifacts = cast(dict[str, Any], artifacts)
    for name in sorted(expected_artifacts):
        digest = artifacts[name]
        _require(
            isinstance(digest, str)
            and len(digest) == 64
            and all(character in "0123456789abcdef" for character in digest),
            f"candidate artifact hash is malformed: {name}",
        )
    snapshots = meta.get("snapshot_sha256")
    if snapshots is not None:
        _require(isinstance(snapshots, dict) and bool(snapshots),
                 "candidate snapshot ledger must be a nonempty object")
        snapshots = cast(dict[str, Any], snapshots)
        for name, digest in snapshots.items():
            _require(isinstance(name, str), "candidate snapshot path is not a string")
            path = PurePosixPath(name)
            _require(
                not path.is_absolute()
                and name == path.as_posix()
                and all(part not in {"", ".", ".."} for part in path.parts)
                and path.suffix == ".lean",
                f"candidate snapshot path is malformed: {name}",
            )
            _require(
                isinstance(digest, str)
                and len(digest) == 64
                and all(character in "0123456789abcdef" for character in digest),
                f"candidate snapshot hash is malformed: {name}",
            )


def compare_snapshots(
    expected_lean: Path, regenerated_lean: Path,
    expected_manifest: Path, regenerated_manifest: Path,
) -> None:
    expected_bytes = expected_lean.read_bytes()
    regenerated_bytes = regenerated_lean.read_bytes()
    expected_manifest_bytes, expected_meta = _load_manifest(expected_manifest)
    regenerated_manifest_bytes, regenerated_meta = _load_manifest(regenerated_manifest)
    _validate_candidate_manifest(expected_meta)
    _validate_candidate_manifest(regenerated_meta)

    _require(extract_snapshot(regenerated_bytes) == extract_snapshot(expected_bytes),
        "ordered nodes, shapes, init lineages, or final/intermediate goal sets differ"
    )
    _require(regenerated_manifest_bytes == expected_manifest_bytes, "manifest bytes differ")
    _require(regenerated_meta == expected_meta, "manifest values differ")
    _require(regenerated_bytes == expected_bytes, "Lean bytes differ")
    _require(expected_meta["generated_lean_sha256"] == _sha256(expected_bytes),
        "checked-in manifest does not hash the checked-in Lean snapshot"
    )
    _require(regenerated_meta["generated_lean_sha256"] == _sha256(regenerated_bytes),
        "regenerated manifest does not hash regenerated Lean"
    )


def audit_metadata_extension(
    authority_lean: Path, candidate_lean: Path,
    authority_manifest: Path, candidate_manifest: Path,
) -> None:
    """Audit a metadata-only candidate without overwriting the authority snapshot."""
    authority_snapshot = extract_snapshot(authority_lean.read_bytes())
    candidate_bytes = candidate_lean.read_bytes()
    candidate_snapshot = extract_snapshot(candidate_bytes)
    structural_keys = set(authority_snapshot) - {"input_value_classes"}
    _require(all(
        candidate_snapshot[key] == authority_snapshot[key] for key in structural_keys
    ), "baseline graph nodes, replica groups, shapes, lineages, or goal sets differ")
    _require(any(candidate_snapshot["input_value_classes"].values()),
        "candidate has no input value-equivalence classes"
    )

    _, authority_meta = _load_manifest(authority_manifest)
    _, candidate_meta = _load_manifest(candidate_manifest)
    _validate_candidate_manifest(authority_meta)
    _validate_candidate_manifest(candidate_meta)
    mutable = {
        "emitter_sha256", "generated_lean_sha256", "schema_version",
        "input_value_class_count", "input_value_classes",
    }
    _require(candidate_meta["artifact_sha256"] == authority_meta["artifact_sha256"],
        "candidate changed the existing authority artifact hash"
    )
    _require({
        key: value for key, value in candidate_meta.items() if key not in mutable
    } == {
        key: value for key, value in authority_meta.items() if key not in mutable
    }, "authority provenance changed outside the metadata extension")
    expected_manifest_classes = {
        side: [{"source": source, "tids": tids} for source, tids in classes]
        for side, classes in candidate_snapshot["input_value_classes"].items()
    }
    _require(candidate_meta.get("input_value_classes") == expected_manifest_classes,
             "candidate manifest value classes differ from Lean")
    _require(candidate_meta.get("input_value_class_count") == sum(
        len(classes) for classes in expected_manifest_classes.values()
    ), "candidate manifest value-class count differs")
    _require(candidate_meta.get("schema_version") == 3, "candidate manifest is not schema v3")
    _require(candidate_meta.get("generated_lean_sha256") == _sha256(candidate_bytes),
             "candidate manifest does not hash candidate Lean")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-lean", type=Path, default=DEFAULT_LEAN)
    parser.add_argument("--expected-manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--regenerated-lean", type=Path, required=True)
    parser.add_argument("--regenerated-manifest", type=Path, required=True)
    parser.add_argument(
        "--metadata-extension", action="store_true",
        help="audit an intentional value-class extension while preserving authority structure",
    )
    args = parser.parse_args()
    if args.metadata_extension:
        audit_metadata_extension(
            args.expected_lean, args.regenerated_lean,
            args.expected_manifest, args.regenerated_manifest,
        )
    else:
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
