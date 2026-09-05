"""Test-only cache for expensive, immutable real-goal compiler snapshots."""

from __future__ import annotations

import copy
import hashlib
from pathlib import Path

import trainverify.bridge_emitter.parser as parser_module
import trainverify.bridge_emitter.proof_compiler as proof_compiler_module
import trainverify.bridge_emitter.relation_compiler as relation_compiler_module


_PLAN_CACHE: dict[tuple[object, ...], tuple[object, object]] = {}
_CACHE: dict[tuple[object, ...], tuple[object, object, object]] = {}


def clear_compiled_goal_cache() -> None:
    _PLAN_CACHE.clear()
    _CACHE.clear()


def _authority_digest(root: Path, goal_id: int) -> str:
    generated = root / parser_module.GEN_DIR / parser_module.GEN_FILE
    requested_goal = root / parser_module.DENOTE_DIR / f"Goal_{goal_id}.lean"
    goal = requested_goal if requested_goal.is_file() else generated
    nodes = generated.parent / "GeneratedGraphNodes.lean"

    paths = set(goal.parent.glob("*.lean"))
    paths.add(generated)
    if nodes.exists():
        paths.add(nodes)

    digest = hashlib.sha256()
    digest.update(b"requested-goal\0")
    digest.update(str(requested_goal.relative_to(root)).encode())
    digest.update(b"\0present\0" if requested_goal.is_file() else b"\0absent\0")
    for path in sorted(paths, key=lambda item: str(item.relative_to(root))):
        relative = str(path.relative_to(root)).encode()
        data = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(data).to_bytes(8, "big"))
        digest.update(data)
    return digest.hexdigest()


def planned_goal(goal_id: int, root: str):
    canonical_root = Path(root).resolve(strict=True)
    configuration = (
        parser_module.DENOTE_DIR,
        parser_module.GEN_DIR,
        parser_module.GEN_FILE,
        parser_module.MOD_PREFIX,
    )
    callable_authorities = (
        parser_module.load_goal_ir,
        proof_compiler_module.build_default_registry,
        proof_compiler_module.compile_proof_plan,
    )
    authority_digest = _authority_digest(canonical_root, int(goal_id))
    key = (
        str(canonical_root),
        int(goal_id),
        configuration,
        callable_authorities,
        authority_digest,
    )
    snapshot = _PLAN_CACHE.get(key)
    if snapshot is None:
        ir = parser_module.load_goal_ir(int(goal_id), str(canonical_root))
        proof = proof_compiler_module.compile_proof_plan(
            ir, proof_compiler_module.build_default_registry()
        )
        current_configuration = (
            parser_module.DENOTE_DIR,
            parser_module.GEN_DIR,
            parser_module.GEN_FILE,
            parser_module.MOD_PREFIX,
        )
        current_callables = (
            parser_module.load_goal_ir,
            proof_compiler_module.build_default_registry,
            proof_compiler_module.compile_proof_plan,
        )
        if (
            current_configuration != configuration
            or any(current is not expected for current, expected in zip(
                current_callables, callable_authorities
            ))
            or _authority_digest(canonical_root, int(goal_id)) != authority_digest
        ):
            raise RuntimeError("real-goal authority changed during compilation")
        snapshot = (ir, proof)
        _PLAN_CACHE[key] = snapshot
    return copy.deepcopy(snapshot)


def compiled_goal(
    goal_id: int,
    root: str,
    *,
    peel_aliases: bool = True,
    deduplicate_frontiers: bool = True,
):
    canonical_root = Path(root).resolve(strict=True)
    configuration = (
        parser_module.DENOTE_DIR,
        parser_module.GEN_DIR,
        parser_module.GEN_FILE,
        parser_module.MOD_PREFIX,
    )
    callable_authorities = (
        parser_module.load_goal_ir,
        proof_compiler_module.build_default_registry,
        proof_compiler_module.compile_proof_plan,
        relation_compiler_module.compile_relation_plan,
    )
    authority_digest = _authority_digest(canonical_root, int(goal_id))
    key = (
        str(canonical_root),
        int(goal_id),
        configuration,
        bool(peel_aliases),
        bool(deduplicate_frontiers),
        callable_authorities,
        authority_digest,
    )
    snapshot = _CACHE.get(key)
    if snapshot is None:
        ir, proof = planned_goal(int(goal_id), str(canonical_root))
        relation = relation_compiler_module.compile_relation_plan(
            ir,
            proof,
            peel_aliases=peel_aliases,
            deduplicate_frontiers=deduplicate_frontiers,
        )
        current_configuration = (
            parser_module.DENOTE_DIR,
            parser_module.GEN_DIR,
            parser_module.GEN_FILE,
            parser_module.MOD_PREFIX,
        )
        current_callables = (
            parser_module.load_goal_ir,
            proof_compiler_module.build_default_registry,
            proof_compiler_module.compile_proof_plan,
            relation_compiler_module.compile_relation_plan,
        )
        if (
            current_configuration != configuration
            or any(current is not expected for current, expected in zip(
                current_callables, callable_authorities
            ))
            or _authority_digest(canonical_root, int(goal_id)) != authority_digest
        ):
            raise RuntimeError("real-goal authority changed during compilation")
        snapshot = (ir, proof, relation)
        _CACHE[key] = snapshot
    return copy.deepcopy(snapshot)
