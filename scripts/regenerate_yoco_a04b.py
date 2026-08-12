#!/usr/bin/env python3
"""Compatibility name for the atomic YOCO authority snapshot emitter."""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.yoco_regen.torch_compat import (
    ensure_torch_recompile_limit as ensure_torch_recompile_limit,
)


def main() -> None:
    from scripts.yoco_regen.emit_yoco_a04b import main as emit_main

    emit_main()


if __name__ == "__main__":
    main()
