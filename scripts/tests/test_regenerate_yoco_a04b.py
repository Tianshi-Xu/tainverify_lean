from types import SimpleNamespace

from scripts.regenerate_yoco_a04b import ensure_torch_recompile_limit


def _fake_torch(config):
    return SimpleNamespace(_dynamo=SimpleNamespace(config=SimpleNamespace(_config=config)))


def test_torch26_recompile_limit_compatibility_patch_is_idempotent():
    config = {}
    sentinel = object()
    torch = _fake_torch(config)
    assert ensure_torch_recompile_limit(torch, lambda: sentinel) is True
    assert config["recompile_limit"] is sentinel
    assert ensure_torch_recompile_limit(torch, lambda: object()) is False
    assert config["recompile_limit"] is sentinel


def test_existing_recompile_limit_is_preserved():
    sentinel = object()
    config = {"recompile_limit": sentinel}
    assert ensure_torch_recompile_limit(_fake_torch(config), lambda: object()) is False
    assert config["recompile_limit"] is sentinel
