import pytest


def test_bw_compound_rule_selector_preserves_exact_order_and_count():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_bw_compound_renderer

    assert select_bw_compound_renderer((
        "bw-matmul-fst-query-sharded-rank4",
        "bw-matmul-snd-contraction-reduction-rank4",
        "bw-view-joined",
    )) == "bw_matmul_view_renderer:render_closed_bw_matmul_view_segment"
    assert select_bw_compound_renderer((
        "bw-matmul-snd-contraction-reduction-rank4",
        "bw-matmul-fst-query-sharded-rank4",
        "bw-view-joined",
    )) is None


def test_bw_compound_rule_selector_keeps_count_grammar_imperative():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_bw_compound_renderer

    family = (
        "bw-multiref-sum-sharded-k-rank",
        "cross-dp-wred-reconstruction-k-rank",
        "cross-dp-wred-reconstruction-k-rank",
    )
    assert select_bw_compound_renderer(family) == (
        "bw_multiref_wred_renderer:render_closed_bw_multiref_wred_segment"
    )
    assert select_bw_compound_renderer(family + ("bw-view-joined",)) is None


def test_bw_compound_rule_selector_rejects_singletons_and_unknown_families():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_bw_compound_renderer

    assert select_bw_compound_renderer(("bw-view-joined",)) is None
    assert select_bw_compound_renderer(("unknown", "bw-view-joined")) is None


def test_composer_no_longer_owns_bw_compound_grammar():
    from pathlib import Path
    from trainverify.bridge_emitter import composer

    source = Path(composer.__file__).read_text()
    assert "select_compound_renderer(family)" in source
    assert 'family.count("bw-multiref-sum-sharded-k-rank")' not in source
    assert 'family == (\n        "bw-matmul-fst-query-sharded-rank4"' not in source


def test_k_rank_compound_selector_preserves_prefix_and_count_grammar():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_k_rank_compound_renderer

    linear = "linear-sharded-k-rank-dim1"
    alltoall = "alltoall-k-rank-layout-transport"
    assert select_k_rank_compound_renderer((linear, linear)) == (
        "local_linear_tuple_renderer:render_closed_k_rank_local_linear_tuple_segment"
    )
    assert select_k_rank_compound_renderer((linear, linear, alltoall, alltoall)) == (
        "mixed_local_linear_alltoall_renderer:render_closed_k_rank_local_linear_alltoall_segment"
    )
    assert select_k_rank_compound_renderer((alltoall, alltoall)) == (
        "alltoall_tuple_renderer:render_closed_k_rank_alltoall_tuple_segment"
    )
    assert select_k_rank_compound_renderer((linear, alltoall, linear)) is None


def test_composer_no_longer_owns_k_rank_compound_grammar():
    from pathlib import Path
    from trainverify.bridge_emitter import composer

    source = Path(composer.__file__).read_text()
    assert "select_compound_renderer(family)" in source
    assert 'local_prefix = 0' not in source
    assert 'family.count("alltoall-k-rank-layout-transport") == 1' not in source


def test_front_compound_selector_preserves_anchor_and_tuple_precedence():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_front_compound_renderer

    hybrid = (
        "faithful-maybe-shuffle-ordinary-to-zigzag-two-rank",
        "rms-norm-zigzag-two-rank",
        "rms-norm-joined-two-rank",
        "flatten-3d-zigzag-two-rank",
        "allgather-reconstruction-k-rank",
        "joined-to-unary",
    )
    assert select_front_compound_renderer(hybrid) == (
        "hybrid_attention_component_renderer:render_closed_hybrid_attention_component_segment"
    )
    assert select_front_compound_renderer((
        "transpose-sharded-k-rank",
        "alltoall-k-rank-layout-transport",
        "transpose-sharded-k-rank",
    )) == "transpose_alltoall_transpose_renderer:render_closed_transpose_alltoall_transpose_segment"
    assert select_front_compound_renderer((
        "transpose-sharded-k-rank",
        "transpose-sharded-k-rank",
    )) == "@local:render_closed_k_rank_transpose_segment"
    assert select_front_compound_renderer(("multiref-sharded-k-rank",) * 2) == (
        "@local:render_closed_k_rank_multiref_segment"
    )


def test_mixed_linear_sequence_requires_all_three_semantic_anchors():
    from trainverify.bridge_emitter.compound_rule_dispatch import (
        select_compound_renderer,
        select_front_compound_renderer,
    )

    linear = "linear-sharded-k-rank-dim1"
    alltoall = "alltoall-k-rank-layout-transport"
    reduction = "linear-reduction-producer-k-rank"
    allgather = "allgather-reconstruction-k-rank"
    output = "linear-output-sharded-k-rank"
    assert select_compound_renderer((linear, alltoall, reduction)) == (
        "mixed_linear_sequence_renderer:render_closed_mixed_linear_sequence_segment"
    )
    assert select_compound_renderer((
        linear, allgather, output, allgather, output,
    )) == "mixed_linear_sequence_renderer:render_closed_mixed_linear_sequence_segment"
    assert select_compound_renderer((linear, linear, allgather)) == (
        "mixed_linear_sequence_renderer:render_closed_mixed_linear_sequence_segment"
    )
    expected = {
        (linear, allgather): "mixed_local_linear_allgather_renderer:render_closed_k_rank_local_linear_allgather_segment",
        (linear, linear, allgather, output): "mixed_linear_renderer:render_closed_mixed_k_rank_linear_segment",
        (linear, alltoall): "mixed_local_linear_alltoall_renderer:render_closed_k_rank_local_linear_alltoall_segment",
        (reduction, allgather): "reduction_linear_tuple_renderer:render_closed_k_rank_reduction_linear_tuple_segment",
        (reduction, output): "mixed_reduction_linear_renderer:render_closed_mixed_reduction_output_linear_segment",
        (allgather, output): None,
    }
    for family, renderer in expected.items():
        assert select_front_compound_renderer(family) is None
        assert select_compound_renderer(family) == renderer


def test_composer_no_longer_owns_front_compound_grammar():
    import inspect
    from pathlib import Path
    from trainverify.bridge_emitter import composer

    source = inspect.getsource(composer.render_closed_segment)
    assert "select_compound_renderer(family)" in source
    assert "hybrid_attention_rules =" not in source
    assert 'all(item == "transpose-sharded-k-rank" for item in family)' not in source


def test_middle_compound_selector_preserves_initial_and_reduction_prefixes():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_middle_compound_renderer

    assert select_middle_compound_renderer((
        "embedding-hidden-sharded-k-rank",
        "embedding-vocab-sharded-reduction-k-rank",
    )) == "@local:render_closed_mixed_k_rank_embedding_segment"
    assert select_middle_compound_renderer((
        "embedding-vocab-sharded-reduction-k-rank",
        "init-lineage-full-to-two-chunks",
        "joined-init-multiref-alias-group",
        "joined-init-multiref-alias-group",
    )) == "generic_initial_component_renderer:render_closed_generic_initial_component_segment"
    assert select_middle_compound_renderer((
        "linear-reduction-producer-k-rank",
        "linear-reduction-producer-k-rank",
        "allgather-reconstruction-k-rank",
    )) == "reduction_linear_tuple_renderer:render_closed_k_rank_reduction_linear_tuple_segment"


def test_composer_no_longer_owns_middle_compound_grammar():
    import inspect
    from trainverify.bridge_emitter import composer

    source = inspect.getsource(composer.render_closed_segment)
    assert "select_compound_renderer(family)" in source
    assert 'generic_e = "embedding-vocab-sharded-reduction-k-rank"' not in source
    assert "reduction_prefix =" not in source


def test_ordinary_compound_selector_preserves_prefix_and_special_singletons():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_ordinary_compound_renderer

    assert select_ordinary_compound_renderer((
        "hidden-sharded-embedding-alltoall-ordinary-two-rank",
        "init-lineage-full-to-two-chunks",
        "init-lineage-full-to-two-chunks",
    )) == "@local:render_closed_initial_component"
    assert select_ordinary_compound_renderer((
        "flatten-3d-ordinary-two-rank",
        "rms-norm-ordinary-two-rank",
        "ordinary-to-sharded-cp2-fw_reshape-output",
    )) == "flatten_rms_renderer:render_closed_flatten_rms_segment"
    assert select_ordinary_compound_renderer(("zigzag-topk-unshuffle-two-rank",)) == (
        "@local:render_closed_topk_unshuffle_segment"
    )
    assert select_ordinary_compound_renderer((
        "inner-chunk-ce-projection-gather-two-rank",
        "inner-chunk-ce-projection-gather-two-rank",
    )) == "dual_ce_renderer:render_closed_ce_dual_projection_segment"


def test_tail_compound_selector_preserves_count_and_semantic_filter_grammar():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_tail_compound_renderer

    assert select_tail_compound_renderer((
        "identity-view-ordinary-two-rank",
        "view-sharded-k-rank",
        "identity-view-ordinary-two-rank",
        "view-sharded-k-rank",
    )) == "mixed_identity_tuple_renderer:render_closed_mixed_identity_tuple_segment"
    moe = (
        "FW_norm_linear-full-producer-chunks-ordinary-two-rank",
        *("moe-step" for _ in range(15)),
        "ordinary-topk-projection-two-rank",
    )
    assert select_tail_compound_renderer(moe) == "@local:render_closed_mixed_moe_segment"
    assert select_tail_compound_renderer((
        "flatten-3d-zigzag-two-rank",
        "attention-zigzag-qkv-two-rank",
    )) == "@local:_render_closed_zigzag_attention_segment"


def test_composer_delegates_relation_dependent_compound_cases():
    import inspect
    from trainverify.bridge_emitter import composer

    source = inspect.getsource(composer.render_closed_segment)
    assert "select_compound_renderer(family)" in source
    assert "select_relation_dependent_renderer" in source
    assert "identity_pairs =" not in source
    assert "semantic_family =" not in source
    assert "multiref-projection-alias" not in source
    assert "inner-chunk-ce-projection-gather-two-rank" not in source


def test_unified_compound_selector_preserves_ordered_subgrammar_precedence():
    from trainverify.bridge_emitter.compound_rule_dispatch import select_compound_renderer

    assert select_compound_renderer((
        "transpose-sharded-k-rank",
        "alltoall-k-rank-layout-transport",
        "transpose-sharded-k-rank",
    )) == "transpose_alltoall_transpose_renderer:render_closed_transpose_alltoall_transpose_segment"
    assert select_compound_renderer((
        "bw-view-joined",
        "transpose-sharded-k-rank",
    )) == "bw_view_transpose_renderer:render_closed_bw_view_transpose_segment"
    assert select_compound_renderer((
        "identity-reshape-ordinary-two-rank",
        "reshape-sharded-k-rank",
    )) == "mixed_identity_renderer:render_closed_mixed_identity_segment"


def test_composer_has_one_family_only_compound_dispatch_call():
    import inspect
    from trainverify.bridge_emitter import composer

    source = inspect.getsource(composer.render_closed_segment)
    assert source.count("select_compound_renderer(family)") == 1
    for old in (
        "select_front_compound_renderer",
        "select_bw_compound_renderer",
        "select_k_rank_compound_renderer",
        "select_middle_compound_renderer",
        "select_ordinary_compound_renderer",
        "select_tail_compound_renderer",
    ):
        assert old not in source


def test_relation_dependent_selector_uses_layout_and_exact_ce_projection():
    from types import SimpleNamespace
    from trainverify.bridge_emitter.compound_rule_dispatch import (
        select_relation_dependent_renderer,
    )

    alias_family = ("multiref-projection-alias", "multiref-projection-alias")
    joined = tuple(
        SimpleNamespace(pre_facts=(SimpleNamespace(layout="joined"),))
        for _ in alias_family
    )
    ordinary = tuple(
        SimpleNamespace(pre_facts=(SimpleNamespace(layout="ordinary"),))
        for _ in alias_family
    )
    assert select_relation_dependent_renderer(alias_family, joined, ()) == (
        "joined_multiref_renderer:render_closed_joined_multiref_segment"
    )
    assert select_relation_dependent_renderer(alias_family, ordinary, ()) == (
        "@local:render_closed_multiref_segment"
    )

    ce_family = ("inner-chunk-ce-projection-gather-two-rank",)
    fst = SimpleNamespace(rule_id=ce_family[0], output_projection=".fst")
    snd = SimpleNamespace(rule_id=ce_family[0], output_projection=".snd")
    assert select_relation_dependent_renderer(ce_family, (), (fst,)) == (
        "@local:render_closed_ce_fst_segment"
    )
    assert select_relation_dependent_renderer(ce_family, (), (snd,)) == (
        "@local:render_closed_ce_snd_segment"
    )
    with pytest.raises(ValueError, match="one exact certificate"):
        select_relation_dependent_renderer(ce_family, (), ())
    invalid = SimpleNamespace(rule_id=ce_family[0], output_projection=".third")
    with pytest.raises(ValueError, match="unsupported closed CE projection"):
        select_relation_dependent_renderer(ce_family, (), (invalid,))


def test_composer_owns_no_compound_family_predicates():
    import inspect
    from trainverify.bridge_emitter import composer

    source = inspect.getsource(composer.render_closed_segment)
    assert "select_relation_dependent_renderer" in source
    assert "multiref-projection-alias" not in source
    assert "inner-chunk-ce-projection-gather-two-rank" not in source
