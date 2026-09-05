#!/usr/bin/env python3
"""Fail-closed incremental test/formal-gate selection for TrainVerify changes."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import PurePosixPath


ALL_MODELS = ("gpt2", "yoco-a04b", "yoco-3b")
FULL_PYTHON_TESTS = (
    "scripts/tests/test_node_authority_policy.py",
    "scripts/tests/test_relation_certificate_models.py",
    "scripts/tests/test_external_pre_fact_selector.py",
    "scripts/tests/test_ordered_buddy_authority_policy.py",
    "scripts/tests/test_relation_authority_policy.py",
    "scripts/tests/test_closed_segment_import_policy.py",
    "scripts/tests/test_compound_rule_dispatch.py",
    "scripts/tests/test_k_rank_gelu_renderer.py",
    "scripts/tests/test_k_rank_bw_layernorm.py",
    "scripts/tests/test_k_rank_bw_multiref.py",
    "scripts/tests/test_k_rank_bw_linear_dx_column.py",
    "scripts/tests/test_k_rank_bw_sum.py",
    "scripts/tests/test_sharded_contiguous_propagation.py",
    "scripts/tests/test_proof_compiler.py",
    "scripts/tests/test_model_authority.py",
    "scripts/tests/test_real_goal_cache.py",
    "scripts/tests/test_incremental_test_selector.py",
    "scripts/tests/test_joined_view_propagation.py",
    "scripts/tests/test_mixed_linear_transition_sequence_renderer.py",
    "scripts/tests/test_parser_public_statement_module.py",
    "scripts/tests/test_sharded_transpose_propagation.py",
    "scripts/tests/test_yoco3b_init_alias_migration.py",
    "scripts/tests/test_joined_init_multiref_grouping.py",
    "scripts/tests/test_mixed_k_rank_layernorm_alltoall_atomic_renderer.py",
    "scripts/tests/test_k_rank_local_linear_allgather_atomic_renderer.py",
    "scripts/tests/test_local_linear_alltoall_tuple_atomic_renderer.py",
    "scripts/tests/test_k_rank_local_renderer.py",
    "scripts/tests/test_mixed_k_rank_linear_atomic_renderer.py",
    "scripts/tests/test_k_rank_div_compiler.py",
    "scripts/tests/test_k_rank_matmul_output_axis.py",
    "scripts/tests/test_k_rank_softmax_compiler.py",
    "scripts/tests/test_k_rank_output_sharded_linear_renderer.py",
    "scripts/tests/test_k_rank_add_renderer.py",
    "scripts/tests/test_k_rank_matmul_contraction.py",
    "scripts/tests/test_k_rank_matmul_head_axis.py",
    "scripts/tests/test_reduction_linear_producer.py",
    "scripts/tests/test_yoco_regen_driver.py",
    "scripts/tests/test_reduction_linear_tuple_allgather_atomic_renderer.py",
    "scripts/tests/test_regenerate_yoco_a04b.py",
    "scripts/tests/test_k_rank_reconstruction.py",
    "scripts/tests/test_mixed_reduction_output_linear_atomic_renderer.py",
    "scripts/tests/test_k_rank_alltoall_allgather_atomic_renderer.py",
    "scripts/tests/test_k_rank_matmul_query_axis_compiler.py",
    "Verdict/tests/test_graph_to_lean_lineage.py",
    "Verdict/tests/test_zigzag_ownership.py",
    "Verdict/tests/test_yoco_cut_local_zigzag_boundaries.py",
    "Verdict/tests/test_provenance.py",
    "Verdict/tests/test_yoco_a04b_snapshot.py",
    "Verdict/tests/test_replica_groups.py",
)
CACHE_FOCUSED_TESTS = (
    "scripts/tests/test_real_goal_cache.py",
    "scripts/tests/test_proof_compiler.py::test_ce_terminal_relation_plan_normalizes_the_backbone",
    "scripts/tests/test_proof_compiler.py::test_ce_terminal_unshuffle_discharges_cu_obligation_from_public_contract",
    "scripts/tests/test_model_authority.py::test_gpt_goal107_bw_sum_scalar_broadcast_preserves_dim2_sharding",
)
BW_SUM_TESTS = (
    "scripts/tests/test_k_rank_bw_sum.py",
    "scripts/tests/test_compound_rule_dispatch.py",
    "scripts/tests/test_k_rank_gelu_renderer.py::test_bw_and_collective_singleton_backends_are_registry_driven",
    "scripts/tests/test_model_authority.py::test_gpt_goal107_bw_sum_scalar_broadcast_preserves_dim2_sharding",
    "scripts/tests/test_proof_compiler.py::test_gpt_goal107_mixed_linear_collective_tuple_is_atomic",
)
BW_SUM_PATHS = frozenset((
    "trainverify/bridge_emitter/relation_compiler.py",
    "trainverify/bridge_emitter/bw_sum_renderer.py",
    "trainverify/bridge_emitter/compound_rule_dispatch.py",
    "trainverify/bridge_emitter/sum_bw_sum_atomic_renderer.py",
    "trainverify/denote/KRankBWSum.lean",
    "scripts/tests/test_k_rank_bw_sum.py",
    "scripts/tests/test_k_rank_gelu_renderer.py",
    "scripts/tests/test_model_authority.py",
    "scripts/tests/test_proof_compiler.py",
))
BW_LINEAR_DX_TESTS = (
    "scripts/tests/test_k_rank_bw_sum.py",
    "scripts/tests/test_proof_compiler.py::test_gpt_goal107_mixed_linear_collective_tuple_is_atomic",
    "scripts/tests/test_mixed_linear_transition_sequence_renderer.py",
    "scripts/tests/test_closed_segment_import_policy.py",
    "scripts/tests/test_incremental_test_selector.py",
)
BW_LINEAR_DX_PATHS = frozenset((
    "trainverify/bridge_emitter/relation_compiler.py",
    "trainverify/bridge_emitter/bw_linear_dx_renderer.py",
    "trainverify/denote/KRankBWLinearDx.lean",
    "trainverify/denote/GeneratedKRankBWLinearDxWitness.lean",
    "scripts/tests/test_k_rank_bw_sum.py",
    "scripts/tests/test_proof_compiler.py",
    "scripts/incremental_test_selector.py",
    "scripts/tests/test_incremental_test_selector.py",
))

BW_LINEAR_COLUMN_TESTS = (
    "scripts/tests/test_model_authority.py::test_gpt_goal107_bw_linear_dx_classifies_three_relation_families",
    "scripts/tests/test_k_rank_bw_linear_dx_column.py",
    "scripts/tests/test_k_rank_bw_layernorm.py",
    "scripts/tests/test_proof_compiler.py::test_gpt_goal107_mixed_linear_collective_tuple_is_atomic",
    "scripts/tests/test_compound_rule_dispatch.py",
    "scripts/tests/test_k_rank_gelu_renderer.py::test_bw_and_collective_singleton_backends_are_registry_driven",
    "scripts/tests/test_mixed_linear_transition_sequence_renderer.py",
    "scripts/tests/test_closed_segment_import_policy.py",
    "scripts/tests/test_incremental_test_selector.py",
)
BW_LINEAR_COLUMN_PATHS = frozenset((
    "scripts/tests/test_model_authority.py",
    "trainverify/bridge_emitter/relation_compiler.py",
    "trainverify/bridge_emitter/bw_linear_dx_column_renderer.py",
    "trainverify/bridge_emitter/bw_linear_column_dual_renderer.py",
    "trainverify/bridge_emitter/bw_linear_gather_view_alltoall_renderer.py",
    "trainverify/bridge_emitter/closed_segment_import_policy.py",
    "trainverify/bridge_emitter/compound_rule_dispatch.py",
    "scripts/tests/test_k_rank_bw_layernorm.py",
    "trainverify/denote/KRankBWLinearDxColumn.lean",
    "trainverify/denote/GeneratedKRankBWLinearDxColumnWitness.lean",
    "scripts/tests/test_k_rank_bw_linear_dx_column.py",
    "scripts/tests/test_proof_compiler.py",
    "scripts/tests/test_k_rank_gelu_renderer.py",
    "scripts/incremental_test_selector.py",
    "scripts/tests/test_incremental_test_selector.py",
    "docs/GENERAL_PARALLEL_STATUS.md",
))

BW_MULTIREF_TESTS = (
    "scripts/tests/test_k_rank_bw_multiref.py",
    "scripts/tests/test_proof_compiler.py::test_gpt_goal107_mixed_linear_collective_tuple_is_atomic",
    "scripts/tests/test_compound_rule_dispatch.py",
    "scripts/tests/test_k_rank_gelu_renderer.py::test_bw_and_collective_singleton_backends_are_registry_driven",
    "scripts/tests/test_mixed_linear_transition_sequence_renderer.py",
    "scripts/tests/test_closed_segment_import_policy.py",
    "scripts/tests/test_incremental_test_selector.py",
)
BW_MULTIREF_PATHS = frozenset((
    "trainverify/bridge_emitter/relation_compiler.py",
    "trainverify/bridge_emitter/bw_multiref_sum_renderer.py",
    "trainverify/bridge_emitter/bw_multiref_wred_renderer.py",
    "trainverify/bridge_emitter/closed_segment_import_policy.py",
    "trainverify/denote/KRankBWMultiref.lean",
    "trainverify/denote/GeneratedKRankBWMultirefWitness.lean",
    "scripts/tests/test_k_rank_bw_multiref.py",
    "scripts/tests/test_proof_compiler.py",
    "scripts/tests/test_k_rank_gelu_renderer.py",
    "scripts/incremental_test_selector.py",
    "scripts/tests/test_incremental_test_selector.py",
    "docs/GENERAL_PARALLEL_STATUS.md",
))

BW_LAYERNORM_DX_TESTS = (
    "scripts/tests/test_k_rank_bw_layernorm.py",
    "scripts/tests/test_proof_compiler.py::test_gpt_goal107_mixed_linear_collective_tuple_is_atomic",
    "scripts/tests/test_compound_rule_dispatch.py",
    "scripts/tests/test_k_rank_gelu_renderer.py::test_bw_and_collective_singleton_backends_are_registry_driven",
    "scripts/tests/test_closed_segment_import_policy.py",
    "scripts/tests/test_incremental_test_selector.py",
)
BW_LAYERNORM_DX_PATHS = frozenset((
    "trainverify/bridge_emitter/relation_compiler.py",
    "trainverify/bridge_emitter/bw_layernorm_dx_renderer.py",
    "trainverify/bridge_emitter/bw_layernorm_triple_renderer.py",
    "trainverify/bridge_emitter/compound_rule_dispatch.py",
    "trainverify/bridge_emitter/closed_segment_import_policy.py",
    "trainverify/denote/KRankBWLayernorm.lean",
    "trainverify/denote/GeneratedKRankBWLayernormWitness.lean",
    "scripts/tests/test_k_rank_bw_layernorm.py",
    "scripts/tests/test_proof_compiler.py",
    "scripts/tests/test_k_rank_gelu_renderer.py",
    "scripts/incremental_test_selector.py",
    "scripts/tests/test_incremental_test_selector.py",
    "docs/GENERAL_PARALLEL_STATUS.md",
))


@dataclass(frozen=True)
class GatePlan:
    pytest_nodes: tuple[str, ...]
    exact_models: tuple[str, ...] = ()
    lean_modules: tuple[str, ...] = ()
    staged_lean: bool = False
    axiom_audit: bool = False
    full_python: bool = False
    formal_publication: bool = False
    explanations: tuple[str, ...] = ()


def _dedupe(items):
    return tuple(dict.fromkeys(items))


def _full_plan(reason: str) -> GatePlan:
    return GatePlan(
        pytest_nodes=FULL_PYTHON_TESTS,
        exact_models=ALL_MODELS,
        staged_lean=True,
        axiom_audit=True,
        full_python=True,
        formal_publication=True,
        explanations=(reason,),
    )


def _normalize(path: str) -> str:
    while path.startswith("./"):
        path = path[2:]
    normalized = PurePosixPath(path)
    if (
        not path
        or path == "."
        or "\\" in path
        or normalized.is_absolute()
        or ".." in normalized.parts
        or normalized.as_posix() != path
    ):
        raise ValueError(f"noncanonical changed path: {path!r}")
    return path


def select_gates(
    changed_paths: tuple[str, ...] | list[str],
    *,
    family: str | None = None,
    release: bool = False,
) -> GatePlan:
    try:
        paths = tuple(_normalize(str(path)) for path in changed_paths)
    except ValueError as exc:
        return _full_plan(str(exc))
    if not paths:
        return _full_plan("no changed paths were supplied; refusing an empty gate")
    if release:
        return _full_plan("release mode requires the complete Python and formal transaction")

    if family is not None:
        if family == "k-rank-bw-linear-dx-column":
            outside = tuple(path for path in paths if path not in BW_LINEAR_COLUMN_PATHS)
            if outside:
                return _full_plan("paths outside k-rank-bw-linear-dx-column family scope: " + ", ".join(outside))
            return GatePlan(
                pytest_nodes=BW_LINEAR_COLUMN_TESTS, exact_models=("gpt2",),
                lean_modules=("denote.KRankBWLinearDxColumn", "denote.GeneratedKRankBWLinearDxColumnWitness"),
                staged_lean=True, axiom_audit=True, formal_publication=True,
                explanations=(
                    "BW_linear column dX ordered weight gather affects GPT Goal 107 and dX/dW compound frames",
                    "canonical GPT targets exclude Goal 107; compile affected exact segments separately",
                ),
            )
        if family == "k-rank-bw-multiref":
            outside = tuple(path for path in paths if path not in BW_MULTIREF_PATHS)
            if outside:
                return _full_plan("paths outside k-rank-bw-multiref family scope: " + ", ".join(outside))
            return GatePlan(
                pytest_nodes=BW_MULTIREF_TESTS, exact_models=("gpt2",),
                lean_modules=("denote.KRankBWMultiref", "denote.GeneratedKRankBWMultirefWitness"),
                staged_lean=True, axiom_audit=True, formal_publication=True,
                explanations=(
                    "BW_multiref ordered sum/gather changes affect GPT Goal 107 including WRED compound frames",
                    "canonical GPT targets exclude Goal 107; compile affected exact segments separately",
                ),
            )
        if family == "k-rank-bw-layernorm-dx":
            outside = tuple(path for path in paths if path not in BW_LAYERNORM_DX_PATHS)
            if outside:
                return _full_plan("paths outside k-rank-bw-layernorm-dx family scope: " + ", ".join(outside))
            return GatePlan(
                pytest_nodes=BW_LAYERNORM_DX_TESTS,
                exact_models=("gpt2",),
                lean_modules=("denote.KRankBWLayernorm", "denote.GeneratedKRankBWLayernormWitness"),
                staged_lean=True, axiom_audit=True, formal_publication=True,
                explanations=(
                    "K-rank BW_layernorm dX changes affect GPT Goal 107 and rank4 triple projection",
                    "canonical GPT targets do not include Goal 107; compile its changed exact segments separately",
                ),
            )
        if family == "k-rank-bw-linear-dx-row":
            outside = tuple(path for path in paths if path not in BW_LINEAR_DX_PATHS)
            if outside:
                return _full_plan(
                    "paths outside k-rank-bw-linear-dx-row family scope: "
                    + ", ".join(outside)
                )
            return GatePlan(
                pytest_nodes=BW_LINEAR_DX_TESTS,
                exact_models=("gpt2",),
                lean_modules=(
                    "denote.KRankBWLinearDx",
                    "denote.GeneratedKRankBWLinearDxWitness",
                ),
                staged_lean=True,
                axiom_audit=True,
                formal_publication=True,
                explanations=(
                    "K-rank BW_linear dX row reduction changes affect GPT Goal 107",
                    "proof bytes may change, so staged Lean, axiom, and publication gates remain required",
                ),
            )
        if family != "k-rank-bw-sum":
            return _full_plan(f"unknown semantic family {family!r}")
        outside = tuple(path for path in paths if path not in BW_SUM_PATHS)
        if outside:
            return _full_plan(
                "paths outside k-rank-bw-sum family scope: " + ", ".join(outside)
            )
        return GatePlan(
            pytest_nodes=BW_SUM_TESTS,
            exact_models=("gpt2",),
            lean_modules=("denote.KRankBWSum",),
            staged_lean=True,
            axiom_audit=True,
            formal_publication=True,
            explanations=(
                "K-rank BW_sum changes affect the real GPT Goal 107 path",
                "proof bytes may change, so staged Lean, axiom, and publication gates remain required",
            ),
        )

    tests: list[str] = []
    explanations: list[str] = []
    for path in paths:
        if path.startswith("docs/"):
            explanations.append(f"documentation-only path: {path}")
        elif path == "scripts/tests/real_goal_cache.py":
            tests.extend(CACHE_FOCUSED_TESTS)
            explanations.append("test-only compiler cache: unit plus representative cache users")
        elif path.startswith("scripts/tests/test_") and path.endswith(".py"):
            tests.append(path)
            explanations.append(f"direct test change: {path}")
        elif path == "trainverify/bridge_emitter/relation_compiler.py":
            return _full_plan(
                "shared relation compiler changed without an explicit semantic family"
            )
        else:
            return _full_plan(f"unrecognized changed path: {path}")

    return GatePlan(
        pytest_nodes=_dedupe(tests),
        explanations=tuple(explanations),
    )


def _explain(plan: GatePlan) -> str:
    lines = [*(f"reason: {reason}" for reason in plan.explanations)]
    lines.extend(f"pytest: {node}" for node in plan.pytest_nodes)
    lines.extend(f"exact-model: {model}" for model in plan.exact_models)
    lines.extend(f"lean-module: {module}" for module in plan.lean_modules)
    for name in ("staged_lean", "axiom_audit", "full_python", "formal_publication"):
        lines.append(f"{name}: {str(getattr(plan, name)).lower()}")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family")
    parser.add_argument("--release", action="store_true")
    parser.add_argument("--explain", action="store_true")
    parser.add_argument("paths", nargs="+")
    args = parser.parse_args(argv)
    plan = select_gates(args.paths, family=args.family, release=args.release)
    if args.explain:
        print(_explain(plan), end="")
    else:
        print(json.dumps(asdict(plan), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
