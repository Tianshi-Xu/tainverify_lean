"""Torch compatibility hooks shared by YOCO release entrypoints."""
from __future__ import annotations


def ensure_torch_recompile_limit(torch_module, entry_factory=None) -> bool:
    """Install Torch 2.6's missing Dynamo key; return whether it was added."""
    config = torch_module._dynamo.config._config
    if "recompile_limit" in config:
        return False
    factory = entry_factory
    if factory is None:
        from torch.utils._config_module import Config, _ConfigEntry

        def default_factory():
            return _ConfigEntry(Config(default=32, value_type=int))

        factory = default_factory
    config["recompile_limit"] = factory()
    return True
