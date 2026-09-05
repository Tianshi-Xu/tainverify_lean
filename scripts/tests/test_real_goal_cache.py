import gc
import weakref
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.tests import real_goal_cache


def _authority_tree(tmp_path: Path) -> Path:
    denote = tmp_path / "denote"
    denote.mkdir()
    (denote / "Generated.lean").write_text("def generated := 1\n")
    (denote / "Goal_1.lean").write_text("def goal := 1\n")
    (denote / "Statement.lean").write_text("def statement := 1\n")
    return tmp_path


def test_planned_goal_cache_reuses_parse_and_proof_without_compiling_relation(
    tmp_path, monkeypatch
):
    root = _authority_tree(tmp_path)
    monkeypatch.setattr(real_goal_cache.parser_module, "DENOTE_DIR", "denote")
    monkeypatch.setattr(real_goal_cache.parser_module, "GEN_DIR", "denote")
    monkeypatch.setattr(real_goal_cache.parser_module, "GEN_FILE", "Generated.lean")
    monkeypatch.setattr(real_goal_cache.parser_module, "MOD_PREFIX", "denote")
    calls = {"parse": 0, "proof": 0, "relation": 0}

    def load(goal_id, requested_root):
        calls["parse"] += 1
        return SimpleNamespace(goal_id=goal_id, root=requested_root, values=[1])

    def compile_proof(ir, registry):
        calls["proof"] += 1
        return SimpleNamespace(ir=ir, registry=registry, values=[2])

    def compile_relation(ir, proof, **options):
        calls["relation"] += 1
        return SimpleNamespace(ir=ir, proof=proof, options=options)

    monkeypatch.setattr(real_goal_cache.parser_module, "load_goal_ir", load)
    monkeypatch.setattr(real_goal_cache.proof_compiler_module, "build_default_registry", lambda: "registry")
    monkeypatch.setattr(real_goal_cache.proof_compiler_module, "compile_proof_plan", compile_proof)
    monkeypatch.setattr(real_goal_cache.relation_compiler_module, "compile_relation_plan", compile_relation)
    real_goal_cache.clear_compiled_goal_cache()

    first = real_goal_cache.planned_goal(1, str(root))
    first[0].values.append(99)
    second = real_goal_cache.planned_goal(1, str(root))

    assert calls == {"parse": 1, "proof": 1, "relation": 0}
    assert second[0].values == [1]
    assert second[1].values == [2]

    real_goal_cache.compiled_goal(1, str(root))
    assert calls == {"parse": 1, "proof": 1, "relation": 1}


def test_compiled_goal_cache_is_content_keyed_and_returns_independent_snapshots(
    tmp_path, monkeypatch
):
    root = _authority_tree(tmp_path)
    monkeypatch.setattr(real_goal_cache.parser_module, "DENOTE_DIR", "denote")
    monkeypatch.setattr(real_goal_cache.parser_module, "GEN_DIR", "denote")
    monkeypatch.setattr(real_goal_cache.parser_module, "GEN_FILE", "Generated.lean")
    monkeypatch.setattr(real_goal_cache.parser_module, "MOD_PREFIX", "denote")
    calls = {"parse": 0, "proof": 0, "relation": 0}

    def load(goal_id, requested_root):
        calls["parse"] += 1
        return SimpleNamespace(goal_id=goal_id, root=requested_root, values=[1])

    def compile_proof(ir, registry):
        calls["proof"] += 1
        return SimpleNamespace(ir=ir, registry=registry, values=[2])

    def compile_relation(ir, proof, **options):
        calls["relation"] += 1
        return SimpleNamespace(ir=ir, proof=proof, options=options, values=[3])

    monkeypatch.setattr(real_goal_cache.parser_module, "load_goal_ir", load)
    monkeypatch.setattr(real_goal_cache.proof_compiler_module, "build_default_registry", lambda: "registry")
    monkeypatch.setattr(real_goal_cache.proof_compiler_module, "compile_proof_plan", compile_proof)
    monkeypatch.setattr(real_goal_cache.relation_compiler_module, "compile_relation_plan", compile_relation)
    real_goal_cache.clear_compiled_goal_cache()

    first = real_goal_cache.compiled_goal(1, str(root))
    first[0].values.append(99)
    first[1].values.append(99)
    first[2].values.append(99)
    second = real_goal_cache.compiled_goal(1, str(root))

    assert calls == {"parse": 1, "proof": 1, "relation": 1}
    assert second[0].values == [1]
    assert second[1].values == [2]
    assert second[2].values == [3]
    assert all(left is not right for left, right in zip(first, second))

    nondefault = real_goal_cache.compiled_goal(
        1, str(root), peel_aliases=False, deduplicate_frontiers=False
    )
    assert calls == {"parse": 1, "proof": 1, "relation": 2}
    assert nondefault[2].options == {
        "peel_aliases": False,
        "deduplicate_frontiers": False,
    }
    real_goal_cache.compiled_goal(
        1, str(root), peel_aliases=False, deduplicate_frontiers=False
    )
    assert calls == {"parse": 1, "proof": 1, "relation": 2}

    (root / "denote" / "Statement.lean").write_text("def statement := 2\n")
    real_goal_cache.compiled_goal(1, str(root))
    assert calls == {"parse": 2, "proof": 2, "relation": 3}

    monkeypatch.setattr(real_goal_cache.parser_module, "MOD_PREFIX", "other")
    real_goal_cache.compiled_goal(1, str(root))
    assert calls == {"parse": 3, "proof": 3, "relation": 4}


def test_compiled_goal_cache_bypasses_stale_entries_after_compiler_monkeypatch(
    tmp_path, monkeypatch
):
    root = _authority_tree(tmp_path)
    monkeypatch.setattr(real_goal_cache.parser_module, "DENOTE_DIR", "denote")
    monkeypatch.setattr(real_goal_cache.parser_module, "GEN_DIR", "denote")
    monkeypatch.setattr(real_goal_cache.parser_module, "GEN_FILE", "Generated.lean")
    monkeypatch.setattr(real_goal_cache.parser_module, "MOD_PREFIX", "denote")
    monkeypatch.setattr(
        real_goal_cache.proof_compiler_module,
        "build_default_registry",
        lambda: None,
    )
    monkeypatch.setattr(
        real_goal_cache.proof_compiler_module,
        "compile_proof_plan",
        lambda ir, _registry: SimpleNamespace(marker=ir.marker),
    )
    monkeypatch.setattr(
        real_goal_cache.relation_compiler_module,
        "compile_relation_plan",
        lambda ir, proof, **_options: SimpleNamespace(marker=proof.marker),
    )
    real_goal_cache.clear_compiled_goal_cache()

    monkeypatch.setattr(
        real_goal_cache.parser_module,
        "load_goal_ir",
        lambda _goal_id, _root: SimpleNamespace(marker="first"),
    )
    assert real_goal_cache.compiled_goal(1, str(root))[0].marker == "first"

    monkeypatch.setattr(
        real_goal_cache.parser_module,
        "load_goal_ir",
        lambda _goal_id, _root: SimpleNamespace(marker="second"),
    )
    assert real_goal_cache.compiled_goal(1, str(root))[0].marker == "second"


def test_compiled_goal_cache_rejects_authority_changed_during_compilation(
    tmp_path, monkeypatch
):
    root = _authority_tree(tmp_path)
    monkeypatch.setattr(real_goal_cache.parser_module, "DENOTE_DIR", "denote")
    monkeypatch.setattr(real_goal_cache.parser_module, "GEN_DIR", "denote")
    monkeypatch.setattr(real_goal_cache.parser_module, "GEN_FILE", "Generated.lean")
    monkeypatch.setattr(real_goal_cache.parser_module, "MOD_PREFIX", "denote")
    monkeypatch.setattr(
        real_goal_cache.parser_module,
        "load_goal_ir",
        lambda _goal_id, _root: SimpleNamespace(marker="parsed"),
    )
    monkeypatch.setattr(
        real_goal_cache.proof_compiler_module,
        "build_default_registry",
        lambda: None,
    )
    monkeypatch.setattr(
        real_goal_cache.proof_compiler_module,
        "compile_proof_plan",
        lambda ir, _registry: SimpleNamespace(marker=ir.marker),
    )

    def mutate_authority(ir, proof, **_options):
        (root / "denote" / "Statement.lean").write_text("def statement := changed\n")
        return SimpleNamespace(marker=proof.marker)

    monkeypatch.setattr(
        real_goal_cache.relation_compiler_module,
        "compile_relation_plan",
        mutate_authority,
    )
    real_goal_cache.clear_compiled_goal_cache()

    with pytest.raises(RuntimeError, match="authority changed during compilation"):
        real_goal_cache.compiled_goal(1, str(root))
    assert not real_goal_cache._CACHE


def test_compiled_goal_cache_key_keeps_callable_authority_alive(tmp_path, monkeypatch):
    root = _authority_tree(tmp_path)
    monkeypatch.setattr(real_goal_cache.parser_module, "DENOTE_DIR", "denote")
    monkeypatch.setattr(real_goal_cache.parser_module, "GEN_DIR", "denote")
    monkeypatch.setattr(real_goal_cache.parser_module, "GEN_FILE", "Generated.lean")
    monkeypatch.setattr(real_goal_cache.parser_module, "MOD_PREFIX", "denote")

    def load(_goal_id, _root):
        return SimpleNamespace(marker="parsed")

    reference = weakref.ref(load)
    original_load = real_goal_cache.parser_module.load_goal_ir
    real_goal_cache.parser_module.load_goal_ir = load
    monkeypatch.setattr(
        real_goal_cache.proof_compiler_module,
        "build_default_registry",
        lambda: None,
    )
    monkeypatch.setattr(
        real_goal_cache.proof_compiler_module,
        "compile_proof_plan",
        lambda ir, _registry: SimpleNamespace(marker=ir.marker),
    )
    monkeypatch.setattr(
        real_goal_cache.relation_compiler_module,
        "compile_relation_plan",
        lambda ir, proof, **_options: SimpleNamespace(marker=proof.marker),
    )
    real_goal_cache.clear_compiled_goal_cache()
    try:
        real_goal_cache.compiled_goal(1, str(root))
        real_goal_cache.parser_module.load_goal_ir = (
            lambda _goal_id, _root: SimpleNamespace(marker="replacement")
        )
        del load
        gc.collect()
        assert reference() is not None
    finally:
        real_goal_cache.parser_module.load_goal_ir = original_load
        real_goal_cache.clear_compiled_goal_cache()
