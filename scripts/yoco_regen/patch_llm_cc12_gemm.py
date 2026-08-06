#!/usr/bin/env python3
"""Patch pinned llm-train CC12 GEMM dispatch to avoid B200-only configs."""
from __future__ import annotations

import argparse
from pathlib import Path

MARKER = "[TRAINVERIFY_CC12_GEMM_FALLBACK]"
NEEDLE = "if (_cuda_compute_capability_major() or 0) >= 10:"
REPLACEMENT = (
    "if (_cuda_compute_capability_major() or 0) == 10:  "
    f"# {MARKER} B200-only configs"
)


def patch_source(source: str) -> str:
    if MARKER in source:
        if source.count(REPLACEMENT) != 2 or NEEDLE in source:
            raise RuntimeError("malformed or partial CC12 GEMM patch")
        return source
    count = source.count(NEEDLE)
    if count != 2:
        raise RuntimeError(
            f"expected exactly two CC>=10 GEMM selectors, found {count}; refusing to patch"
        )
    return source.replace(NEEDLE, REPLACEMENT)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("gemm_py", type=Path)
    args = parser.parse_args()
    path = args.gemm_py.resolve()
    source = path.read_text(encoding="utf-8")
    patched = patch_source(source)
    if patched == source:
        print(f"already patched: {path}")
        return
    temporary = path.with_suffix(path.suffix + ".tmp")
    try:
        temporary.write_text(patched, encoding="utf-8")
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)
    print(f"patched: {path}")


if __name__ == "__main__":
    main()
