#!/usr/bin/env python3
"""Compile SM/PM graph relations into a deterministic certificate DAG or finding."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from trainverify.proof_compiler import compile_job


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict:
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def _reject_nonfinite_constant(value: str) -> None:
    raise ValueError(f"nonfinite JSON number: {value}")


def _load_json(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as handle:
        value = json.load(
            handle,
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_nonfinite_constant,
        )
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--job", type=Path, required=True)
    parser.add_argument("--library", type=Path, required=True)
    args = parser.parse_args()
    loaded = {}
    for source, path in (("job", args.job), ("library", args.library)):
        try:
            loaded[source] = _load_json(path)
        except (OSError, ValueError, json.JSONDecodeError):
            result = {
                "schema_version": 1,
                "status": "failure",
                "failure": {
                    "category": "ambiguous_authority",
                    "stage": "schema_validation",
                    "source": source,
                    "reason": "invalid_json",
                },
            }
            print(json.dumps(
                result, sort_keys=True, separators=(",", ":"), allow_nan=False
            ))
            return 2
    result = compile_job(loaded["job"], loaded["library"])
    print(json.dumps(result, sort_keys=True, separators=(",", ":"), allow_nan=False))
    return 0 if result["status"] == "certificate" else 2


if __name__ == "__main__":
    raise SystemExit(main())
