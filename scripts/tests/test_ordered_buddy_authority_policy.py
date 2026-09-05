from dataclasses import replace
import inspect
from pathlib import Path

import pytest


def _rows():
    from trainverify.bridge_emitter.ordered_buddy_authority_policy import OrderedBuddyRow

    return (
        OrderedBuddyRow(10, "BW_maybe_shuffle", (2, 0), (100, 500)),
        OrderedBuddyRow(11, "BW_maybe_shuffle", (2, 1), (101, 500)),
    )


@pytest.mark.parametrize(
    "mutate, expected",
    (
        (lambda rows: rows[:1], "INCOMPLETE"),
        (lambda rows: tuple(reversed(rows)), "OUT_OF_ORDER"),
        (lambda rows: (rows[0], replace(rows[1], op="BW_maybe_unshuffle")), "OP_MISMATCH"),
        (lambda rows: (rows[0], replace(rows[1], parameters=(3, 1))), "PARAMETER_MISMATCH"),
        (lambda rows: (rows[0], replace(rows[1], input_tids=(101,))), "SIGNATURE_MISMATCH"),
        (lambda rows: (rows[0], replace(rows[1], input_tids=(101, 501))), "METADATA_MISMATCH"),
    ),
)
def test_ordered_cp_buddy_policy_rejects_each_malformed_authority(mutate, expected):
    from trainverify.bridge_emitter.ordered_buddy_authority_policy import (
        check_ordered_cp_buddy_authority,
    )

    decision = check_ordered_cp_buddy_authority(
        mutate(_rows()), cp_size=2, expected_op="BW_maybe_shuffle"
    )
    assert decision.failure is not None
    assert decision.failure.name == expected
    assert decision.metadata_tid is None


def test_ordered_cp_buddy_policy_accepts_exact_order_and_current_slot():
    from trainverify.bridge_emitter.ordered_buddy_authority_policy import (
        check_ordered_cp_buddy_authority,
    )

    assert check_ordered_cp_buddy_authority(
        _rows(), cp_size=2, expected_op="BW_maybe_shuffle", current_node_key=11
    ).metadata_tid == 500
    decision = check_ordered_cp_buddy_authority(
        _rows(), cp_size=2, expected_op="BW_maybe_shuffle", current_node_key=99
    )
    assert decision.failure is not None
    assert decision.failure.name == "CURRENT_NODE_MISMATCH"


def test_ordered_cp_buddy_policy_rejects_invalid_cp_size_and_partial_parameters():
    from trainverify.bridge_emitter.ordered_buddy_authority_policy import (
        check_ordered_cp_buddy_authority,
    )

    decision = check_ordered_cp_buddy_authority(
        _rows(), cp_size=1, expected_op="BW_maybe_shuffle"
    )
    assert decision.failure is not None
    assert decision.failure.name == "INVALID_CP_SIZE"
    partial = (_rows()[0], replace(_rows()[1], parameters=(2,)))
    decision = check_ordered_cp_buddy_authority(
        partial, cp_size=2, expected_op="BW_maybe_shuffle"
    )
    assert decision.failure is not None
    assert decision.failure.name == "PARAMETER_MISMATCH"


def test_unshuffle_relation_adapter_preserves_failure_classes(monkeypatch):
    from trainverify.bridge_emitter import parser as parser_module
    from trainverify.bridge_emitter.proof_compiler import (
        build_default_registry,
        compile_proof_plan,
    )
    from trainverify.bridge_emitter.relation_compiler import (
        RelationCompositionError,
        advance_unshuffle_relation_frontiers,
    )

    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    root = Path(__file__).resolve().parents[2]
    plan = compile_proof_plan(parser_module.load_goal_ir(1, str(root)), build_default_registry())
    selected = tuple(
        step for step in plan.steps
        if step.op == "FW_maybe_unshuffle"
        and len(step.input_bindings) == 2
        and step.input_bindings[1] == "init:6252"
    )
    assert len(selected) == 3
    frontier = (tuple(step.step_id for step in selected),)

    def run_with(replacement):
        changed = tuple(
            replacement if step.step_id == replacement.step_id else step
            for step in plan.steps
        )
        return advance_unshuffle_relation_frontiers(
            replace(plan, steps=changed), frontier, ("ordinary",)
        )

    with pytest.raises(RelationCompositionError, match="parameters are malformed"):
        run_with(replace(selected[2], parameters=(2, 0)))
    with pytest.raises(RelationCompositionError, match="parameters are malformed"):
        run_with(replace(
            selected[2],
            parameters=(2, 0),
            input_tids=selected[2].input_tids[:1],
            input_bindings=selected[2].input_bindings[:1],
            input_shapes=selected[2].input_shapes[:1],
        ))
    with pytest.raises(RelationCompositionError, match="signature mismatch"):
        run_with(replace(
            selected[2],
            input_tids=selected[2].input_tids[:1],
            input_bindings=selected[2].input_bindings[:1],
        ))
    with pytest.raises(RelationCompositionError, match="signature mismatch"):
        run_with(replace(
            selected[2],
            input_shapes=selected[2].input_shapes[:1],
            input_tids=(selected[2].input_tids[0], 6253),
            input_bindings=(selected[2].input_bindings[0], "init:6253"),
        ))
    with pytest.raises(RelationCompositionError, match="one shared external input"):
        run_with(replace(
            selected[2],
            input_tids=(selected[2].input_tids[0], 6253),
            input_bindings=(selected[2].input_bindings[0], "init:6253"),
        ))


def test_compiler_adapters_delegate_ordered_buddy_policy_without_old_duplicate_logic():
    from trainverify.bridge_emitter import proof_compiler, relation_compiler

    proof_source = inspect.getsource(proof_compiler.compile_proof_plan)
    relation_source = inspect.getsource(
        relation_compiler.advance_unshuffle_relation_frontiers
    )
    assert "check_ordered_cp_buddy_authority" in proof_source
    assert "check_ordered_cp_buddy_authority" in relation_source
    assert "actual_local_ranks" not in proof_source
    assert "(full.parameters, rank0.parameters, rank1.parameters)" not in relation_source
