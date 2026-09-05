import inspect

import pytest


def test_registered_singleton_uses_exact_registry_theorem_and_import_authority():
    from trainverify.bridge_emitter.closed_segment_import_policy import (
        plan_closed_segment_imports,
    )
    from trainverify.bridge_emitter.relation_compiler import CLOSED_RULE_REGISTRY

    spec = CLOSED_RULE_REGISTRY["linear-sharded-k-rank-dim1"]
    assert plan_closed_segment_imports(
        (spec.rule_id,), spec.lean_theorems[:1], CLOSED_RULE_REGISTRY
    ) == spec.lean_imports
    with pytest.raises(ValueError, match="inconsistent theorem imports"):
        plan_closed_segment_imports(
            (spec.rule_id,), ("TrainVerify.Denote.not_authorized",), CLOSED_RULE_REGISTRY
        )


def test_transpose_imports_follow_transition_theorems_in_stable_first_seen_order():
    from trainverify.bridge_emitter.closed_segment_import_policy import (
        plan_closed_segment_imports,
    )

    family = ("transpose-sharded-k-rank",) * 3
    theorems = (
        "TrainVerify.Denote.fw_transposeAxes_2_3_example",
        "TrainVerify.Denote.fw_transposeAxes_1_2_example",
        "TrainVerify.Denote.fw_transposeAxes_2_3_other",
    )
    assert plan_closed_segment_imports(family, theorems, {}) == (
        "denote.KRankTranspose23Extra",
        "denote.KRankTranspose",
    )
    with pytest.raises(ValueError, match="one theorem identity per transition"):
        plan_closed_segment_imports(family, theorems[:-1], {})
    with pytest.raises(ValueError, match="no closed renderer import"):
        plan_closed_segment_imports(family, (*theorems[:-1], "Unknown.theorem"), {})


def test_compound_import_policy_preserves_theorem_and_family_planning():
    from trainverify.bridge_emitter.closed_segment_import_policy import (
        plan_closed_segment_imports,
    )

    assert plan_closed_segment_imports(
        ("arbitrary-compound",),
        (
            "TrainVerify.Denote.fw_transposeAxes_1_2_x",
            "TrainVerify.Denote.fw_matmul_query_axis_rank4_x",
            "TrainVerify.Denote.fw_transposeAxes_1_2_y",
        ),
        {},
    ) == ("denote.KRankTranspose", "denote.KRankMatmulQueryAxis")
    assert plan_closed_segment_imports(
        (
            "embedding-vocab-sharded-reduction-k-rank",
            "embedding-sharded-ids-k-rank",
            "allreduce-reconstruction-k-rank",
        ),
        (),
        {},
    ) == ("denote.EmbeddingSequenceShard", "denote.KRankAllToAll")
    assert plan_closed_segment_imports(
        (
            "linear-reduction-producer-k-rank",
            "linear-reduction-producer-k-rank",
            "linear-output-sharded-k-rank",
        ),
        (),
        {},
    ) == ("denote.KRankLinearReduction", "denote.KRankLinearGather")
    assert plan_closed_segment_imports(("unknown",), (), {}) == ()


def test_composer_delegates_import_policy_without_retaining_old_dispatch():
    from trainverify.bridge_emitter import composer

    source = inspect.getsource(composer._closed_segment_family_imports)
    assert "plan_closed_segment_imports" in source
    for old in (
        "fw_transposeAxes_1_2_",
        "fw_transposeAxes_2_3_",
        "fw_matmul_query_axis_rank4",
        "embedding-vocab-sharded-reduction-k-rank",
        "linear-reduction-producer-k-rank",
    ):
        assert old not in source
