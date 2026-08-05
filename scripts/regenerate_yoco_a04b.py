#!/usr/bin/env python3
"""Compatibility name for the atomic YOCO authority snapshot emitter."""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


def ensure_torch_recompile_limit(torch_module, entry_factory=None) -> bool:
    """Install Torch 2.6's missing Dynamo key; return whether it was added."""
    config = torch_module._dynamo.config._config
    if "recompile_limit" in config:
        return False
    if entry_factory is None:
        from torch.utils._config_module import Config, _ConfigEntry

        entry_factory = lambda: _ConfigEntry(Config(default=32, value_type=int))
    config["recompile_limit"] = entry_factory()
    return True


def main() -> None:
    from scripts.yoco_regen.emit_yoco_a04b import main as emit_main

    emit_main()


if __name__ == "__main__":
    main()
