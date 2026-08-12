"""Strict JSON readers for authenticated release metadata."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def _reject_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON constant: {value}")


def _reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def loads_strict_json(content: bytes, label: str) -> Any:
    """Decode UTF-8 JSON while rejecting duplicate keys and non-finite numbers."""
    try:
        return json.loads(
            content.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_pairs,
            parse_constant=_reject_constant,
        )
    except (UnicodeDecodeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"invalid JSON in {label}: {exc}") from exc


def load_strict_json(path: Path) -> Any:
    return loads_strict_json(path.read_bytes(), path.name)
