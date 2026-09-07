"""Imperative dispatch for compound closed-rule families.

Compound tuple/count/order grammar stays separate from the singleton identity
registry because its renderer choice depends on the whole atomic family.
"""


def select_bw_compound_renderer(family: tuple[str, ...]) -> str | None:
    """Return the lazy renderer binding for a supported BW compound family."""
    if (family.count("bw-linear-dx-sequence-sharded-k-rank") == 1
            and family.count("bw-linear-dw-sequence-reduction-k-rank") == 1
            and len(family) == 2):
        return "bw_linear_dw_sequence_renderer:render_closed_bw_linear_dw_sequence_segment"
    if (family.count("transpose-sharded-k-rank") == 2
            and family.count("bw-linear-dx-sequence-sharded-k-rank") == 1
            and family.count("bw-linear-dw-sequence-reduction-k-rank") == 1
            and len(family) == 4):
        return "transpose_linear_transpose_renderer:render_closed_transpose_linear_transpose_segment"
    if family == (
        "transpose-sharded-k-rank",
        "bw-linear-dx-sequence-sharded-k-rank",
        "transpose-sharded-k-rank",
    ):
        return "transpose_linear_transpose_renderer:render_closed_transpose_linear_transpose_segment"
    query_rules = {
        "bw-matmul-fst-query-sharded-k-rank",
        "bw-matmul-snd-contraction-reduction-k-rank",
    }
    if (len(family) in (2, 3) and len(set(family)) == len(family)
            and query_rules <= set(family)
            and set(family) <= query_rules | {"bw-view-joined"}):
        return "bw_matmul_query_renderer:render_closed_bw_matmul_query_segment"
    if family == (
        "bw-matmul-head-sharded-k-rank",
        "bw-matmul-head-sharded-k-rank",
    ):
        return "bw_matmul_head_renderer:render_closed_bw_matmul_head_segment"
    if (family.count("bw-linear-dx-sequence-sharded-k-rank") == 1
            and family.count("bw-linear-dw-sequence-reduction-k-rank") == 1
            and family.count("bw-matmul-head-sharded-k-rank") == 2
            and len(family) == 4):
        return "bw_linear_matmul_quad_renderer:render_closed_bw_linear_matmul_quad_segment"
    if family == (
        "bw-linear-dx-sequence-sharded-k-rank",
        "bw-matmul-head-sharded-k-rank",
        "bw-matmul-head-sharded-k-rank",
    ):
        return "bw_linear_matmul_batch_renderer:render_closed_bw_linear_matmul_batch_segment"
    if family in {
        (
            "bw-linear-dx-column-sharded-k-rank",
            "bw-linear-dw-input-column-sharded-k-rank",
            "allgather-reconstruction-k-rank",
            "bw-view-joined",
            "alltoall-k-rank-layout-transport",
        ),
        (
            "bw-linear-dx-column-sharded-k-rank",
            "allgather-reconstruction-k-rank",
            "bw-view-joined",
            "alltoall-k-rank-layout-transport",
        ),
    }:
        return "bw_linear_gather_view_alltoall_renderer:render_closed_bw_linear_gather_view_alltoall_segment"
    if family == ("bw-view-joined", "transpose-sharded-k-rank"):
        return "bw_view_transpose_renderer:render_closed_bw_view_transpose_segment"
    if family == ("bw-view-joined", "div-sharded-k-rank-dim2"):
        return "bw_view_bw_div_renderer:render_closed_bw_view_bw_div_segment"
    if family in {
        ("transpose-sharded-k-rank", "bw-softmax-sharded-dim1-k-rank"),
        ("bw-softmax-sharded-dim2-k-rank", "transpose-sharded-k-rank"),
    }:
        return "transpose_bw_softmax_renderer:render_closed_transpose_bw_softmax_segment"
    if (family.count("bw-linear-dw-output-row-sharded-k-rank") == 1
            and family.count("bw-linear-dx-row-reduction-k-rank") == 1
            and family.count("allgather-reconstruction-k-rank") == 1
            and family.count("bw-matmul-snd-x-sharded-rank4") == 1
            and family.count("bw-matmul-fst-y-sharded-rank4") == 1
            and family.count("allreduce-reconstruction-k-rank") == 1
            and len(family) == 6):
        return "linear_matmul_reconstruction_renderer:render_closed_linear_matmul_reconstruction_segment"
    if family == (
        "bw-linear-dx-row-reduction-k-rank",
        "allgather-reconstruction-k-rank",
        "bw-matmul-fst-y-sharded-rank4",
        "bw-matmul-snd-x-sharded-rank4",
        "allreduce-reconstruction-k-rank",
    ):
        return "linear_matmul_reconstruction_renderer:render_closed_linear_matmul_reconstruction_segment"
    if family == (
        "bw-view-joined",
        "alltoall-k-rank-layout-transport",
        "div-sharded-k-rank-dim1",
        "full-producer-chunks-k-rank",
    ):
        return "view_alltoall_div_chunks_renderer:render_closed_view_alltoall_div_chunks_segment"
    if family == (
        "transpose-sharded-k-rank",
        "allreduce-reconstruction-k-rank",
        "full-producer-chunks-k-rank",
        "bw-softmax-sharded-dim2-k-rank",
        "allgather-reconstruction-k-rank",
    ):
        return "reconstruction_softmax_renderer:render_closed_reconstruction_softmax_segment"
    if family == (
        "bw-matmul-snd-x-sharded-rank4",
        "bw-matmul-fst-y-sharded-rank4",
    ):
        return "bw_matmul_dual_sharded_renderer:render_closed_dual_sharded_bw_matmul_segment"
    if (family.count("bw-matmul-snd-g-sharded-rank4") == 1
            and family.count("bw-matmul-fst-contraction-reduction-rank4") == 1
            and len(family) == 2):
        return "bw_matmul_shared_renderer:render_closed_shared_bw_matmul_segment"
    if (family.count("bw-multiref-sum-sharded-k-rank") == 1
            and family.count("cross-dp-wred-reconstruction-k-rank") >= 1
            and set(family) <= {
                "bw-multiref-sum-sharded-k-rank",
                "cross-dp-wred-reconstruction-k-rank",
            }):
        return "bw_multiref_wred_renderer:render_closed_bw_multiref_wred_segment"
    if (family.count("bw-linear-dx-column-sharded-k-rank") == 1
            and family.count("bw-linear-dw-input-column-sharded-k-rank") == 1
            and family.count("bw-view-joined") <= 1
            and set(family) <= {
                "bw-linear-dx-column-sharded-k-rank",
                "bw-linear-dw-input-column-sharded-k-rank",
                "bw-view-joined",
            }):
        return "bw_linear_column_dual_renderer:render_closed_k_rank_bw_linear_column_dual_segment"
    if family in {
        ("bw-linear-dx-column-sharded-k-rank", "bw-view-joined"),
    }:
        return "bw_linear_dx_column_renderer:render_closed_k_rank_bw_linear_dx_column_segment"
    if (len(family) == 2 and set(family) == {
        "bw-embedding-sequence-reduction-k-rank",
        "bw-embedding-vocab-sharded-k-rank",
    }):
        return "bw_embedding_sequence_renderer:render_closed_k_rank_bw_embedding_sequence_segment"
    if (family.count("bw-add-identity-sharded-k-rank") == 2
            and family.count("cross-dp-wred-reconstruction-k-rank") >= 1
            and set(family) <= {
                "bw-add-identity-sharded-k-rank",
                "cross-dp-wred-reconstruction-k-rank",
            }):
        return "bw_add_wred_renderer:render_closed_bw_add_wred_segment"
    if family and all(item == "bw-add-identity-sharded-k-rank" for item in family):
        return "bw_add_identity_renderer:render_closed_k_rank_bw_add_identity_segment"
    if (2 <= len(family) <= 3 and len(set(family)) == len(family) and set(family) <= {
            "bw-layernorm-dx-dim1-k-rank",
            "bw-layernorm-dgamma-sequence-reduction-k-rank",
            "bw-layernorm-dbeta-sequence-reduction-k-rank",
        }):
        return "bw_layernorm_triple_renderer:render_closed_k_rank_bw_layernorm_triple_segment"
    if (
        len(family) in (2, 3) and len(set(family)) == len(family)
        and family.count("bw-linear-dw-output-row-sharded-k-rank") == 1
        and not {"allreduce-reconstruction-k-rank", "bw-view-joined"} <= set(family)
        and set(family) <= {
            "bw-linear-dx-row-reduction-k-rank",
            "bw-linear-dw-output-row-sharded-k-rank",
            "allreduce-reconstruction-k-rank",
            "bw-view-joined",
        }
    ):
        return "bw_linear_dual_renderer:render_closed_k_rank_bw_linear_dual_segment"
    if family == ("bw-linear-dx-row-reduction-k-rank", "bw-view-joined"):
        return "bw_linear_dx_renderer:render_closed_k_rank_bw_linear_dx_segment"
    if family == (
        "sum-producer-sharded-k-rank-dim1",
        "bw-sum-scalar-broadcast-dim2-k-rank",
    ):
        return "sum_bw_sum_atomic_renderer:render_closed_sum_bw_sum_atomic_segment"
    return None


def select_k_rank_compound_renderer(family: tuple[str, ...]) -> str | None:
    """Return the lazy renderer binding for K-rank tuple/prefix grammar."""
    if len(family) == 2 and set(family) == {
        "embedding-hidden-sharded-k-rank", "embedding-sharded-ids-k-rank"
    }:
        return "embedding_hidden_ids_renderer:render_closed_embedding_hidden_ids_segment"
    linear = "linear-sharded-k-rank-dim1"
    alltoall = "alltoall-k-rank-layout-transport"
    allgather = "allgather-reconstruction-k-rank"

    if len(family) > 1 and all(item == linear for item in family):
        return "local_linear_tuple_renderer:render_closed_k_rank_local_linear_tuple_segment"
    if family == (
        linear,
        linear,
        allgather,
        "linear-output-sharded-k-rank",
    ):
        return "mixed_linear_renderer:render_closed_mixed_k_rank_linear_segment"
    local_prefix = 0
    while local_prefix < len(family) and family[local_prefix] == linear:
        local_prefix += 1
    if 0 < local_prefix < len(family) and all(item == allgather for item in family[local_prefix:]):
        return "mixed_local_linear_allgather_renderer:render_closed_k_rank_local_linear_allgather_segment"
    if (
        local_prefix > 0
        and local_prefix < len(family)
        and all(item == alltoall for item in family[local_prefix:])
    ):
        return "mixed_local_linear_alltoall_renderer:render_closed_k_rank_local_linear_alltoall_segment"
    if family == ("layernorm-sharded-k-rank-dim1", alltoall):
        return "mixed_layernorm_alltoall_renderer:render_closed_mixed_k_rank_layernorm_alltoall_segment"
    if (family.count(alltoall) == 1
            and family.count("cross-dp-wred-reconstruction-k-rank") >= 1
            and set(family) <= {alltoall, "cross-dp-wred-reconstruction-k-rank"}):
        return "alltoall_wred_renderer:render_closed_alltoall_wred_segment"
    if len(family) > 1 and all(item == alltoall for item in family):
        return "alltoall_tuple_renderer:render_closed_k_rank_alltoall_tuple_segment"
    if family[:-1] and all(item == alltoall for item in family[:-1]) and family[-1] == allgather:
        return "mixed_collective_renderer:render_closed_k_rank_alltoall_allgather_segment"
    return None


def select_front_compound_renderer(family: tuple[str, ...]) -> str | None:
    """Select the ordered front-of-dispatch compound family renderer."""
    hybrid_attention_rules = {
        "faithful-maybe-shuffle-ordinary-to-zigzag-two-rank",
        "multiref-projection-alias", "rms-norm-zigzag-two-rank",
        "rms-norm-joined-two-rank", "per-head-linear-zigzag-two-rank",
        "per-head-linear-joined", "flatten-3d-zigzag-two-rank",
        "allgather-reconstruction-k-rank", "joined-to-unary",
    }
    hybrid_attention_anchors = {
        "faithful-maybe-shuffle-ordinary-to-zigzag-two-rank",
        "rms-norm-zigzag-two-rank", "rms-norm-joined-two-rank",
        "flatten-3d-zigzag-two-rank", "allgather-reconstruction-k-rank",
        "joined-to-unary",
    }
    if set(family) <= hybrid_attention_rules and hybrid_attention_anchors <= set(family):
        return "hybrid_attention_component_renderer:render_closed_hybrid_attention_component_segment"

    if family == (
        "transpose-sharded-k-rank",
        "alltoall-k-rank-layout-transport",
        "transpose-sharded-k-rank",
    ):
        return "transpose_alltoall_transpose_renderer:render_closed_transpose_alltoall_transpose_segment"
    if family and all(item == "transpose-sharded-k-rank" for item in family):
        return "@local:render_closed_k_rank_transpose_segment"
    if (
        len(family) >= 2
        and all(item == "transpose-sharded-k-rank" for item in family[:-1])
        and family[-1] == "full-producer-chunks-k-rank"
    ):
        return "mixed_transpose_chunks_renderer:render_closed_transpose_tuple_chunks_segment"
    if (
        "multiref-sharded-k-rank" in family
        and "multiref-projection-alias" in family
        and set(family) <= {"multiref-sharded-k-rank", "multiref-projection-alias"}
    ):
        return "mixed_multiref_renderer:render_closed_mixed_multiref_segment"
    if family and all(item == "multiref-sharded-k-rank" for item in family):
        return "@local:render_closed_k_rank_multiref_segment"
    return None


def select_middle_compound_renderer(family: tuple[str, ...]) -> str | None:
    """Select initial/reduction K-rank compound families."""
    if family == (
        "embedding-hidden-sharded-k-rank",
        "embedding-vocab-sharded-reduction-k-rank",
    ):
        return "@local:render_closed_mixed_k_rank_embedding_segment"
    if family == (
        "embedding-vocab-sharded-reduction-k-rank",
        "embedding-sharded-ids-k-rank",
        "allreduce-reconstruction-k-rank",
    ):
        return "mixed_initial_embedding_renderer:render_closed_mixed_initial_embedding_segment"

    generic_e = "embedding-vocab-sharded-reduction-k-rank"
    generic_f = "init-lineage-full-to-two-chunks"
    generic_g = "joined-init-multiref-alias-group"
    generic_g_start = family.index(generic_g) if generic_g in family else len(family)
    if (
        len(family) >= 3
        and family[0] == generic_e
        and generic_g in family
        and generic_g_start > 1
        and all(item == generic_f for item in family[1:generic_g_start])
        and all(item == generic_g for item in family[generic_g_start:])
    ):
        return "generic_initial_component_renderer:render_closed_generic_initial_component_segment"

    reduction_prefix = (
        family[:-1]
        if family and family[-1] == "allgather-reconstruction-k-rank"
        else family
    )
    if reduction_prefix and all(
        item == "linear-reduction-producer-k-rank" for item in reduction_prefix
    ):
        return "reduction_linear_tuple_renderer:render_closed_k_rank_reduction_linear_tuple_segment"
    if (
        len(family) >= 2
        and all(item == "linear-reduction-producer-k-rank" for item in family[:-1])
        and family[-1] == "linear-output-sharded-k-rank"
    ):
        return "mixed_reduction_linear_renderer:render_closed_mixed_reduction_output_linear_segment"
    if family == (
        "reduce-scatter-reconstruction-k-rank",
        "sharded-to-ordinary-cp2-embedding-reduce-scatter",
    ):
        return "reduce_scatter_renderer:render_closed_k_rank_reduce_scatter_segment"
    if (
        len(family) >= 2
        and all(item == "joined-view-unary" for item in family[:-1])
        and family[-1] == "allreduce-reconstruction-k-rank"
    ):
        return "mixed_joined_view_allreduce_renderer:render_closed_joined_views_allreduce_segment"
    return None


def select_ordinary_compound_renderer(family: tuple[str, ...]) -> str | None:
    """Select ordinary/prefix compound families before CE projection dispatch."""
    if (
        family
        and family[0] == "hidden-sharded-embedding-alltoall-ordinary-two-rank"
        and all(item == "init-lineage-full-to-two-chunks" for item in family[1:])
    ):
        return "@local:render_closed_initial_component"
    if (
        len(family) >= 2
        and family[0] == "flatten-3d-ordinary-two-rank"
        and all(item == "rms-norm-ordinary-two-rank" for item in family[1:-1])
        and family[-1] == "ordinary-to-sharded-cp2-fw_reshape-output"
    ):
        return "flatten_rms_renderer:render_closed_flatten_rms_segment"
    if (
        len(family) >= 2
        and family[0] == "flatten-3d-ordinary-two-rank"
        and all(item == "rms-norm-ordinary-two-rank" for item in family[1:])
    ):
        return "flatten_rms_renderer:render_closed_flatten_rms_segment"
    if family in {
        ("float-sharded-k-rank", "float-ordinary-two-rank"),
        ("float-ordinary-two-rank", "float-sharded-k-rank"),
    }:
        return "mixed_float_renderer:render_closed_mixed_float_segment"
    if family == ("zigzag-topk-unshuffle-two-rank",):
        return "@local:render_closed_topk_unshuffle_segment"
    if family == ("FW_norm_linear-full-producer-chunks-zigzag-two-rank",):
        return "@local:render_closed_norm_full_producer_segment"
    if family == (
        "inner-chunk-ce-projection-gather-two-rank",
        "inner-chunk-ce-projection-gather-two-rank",
    ):
        return "dual_ce_renderer:render_closed_ce_dual_projection_segment"
    return None


def select_tail_compound_renderer(family: tuple[str, ...]) -> str | None:
    """Select family-only grammar after relation-dependent CE dispatch."""
    if family in {
        ("rms-norm-ordinary-two-rank", "faithful-maybe-shuffle-ordinary-to-zigzag-two-rank"),
        ("rms-norm-ordinary-two-rank", "bw-maybe-unshuffle-ordinary-to-zigzag-two-rank"),
    }:
        return "@local:render_closed_rms_shuffle_segment"
    if family == ("swiglu-ordinary-two-rank", "swiglu-sharded-two-rank-dim0"):
        return "mixed_swiglu_renderer:render_closed_mixed_swiglu_segment"
    if family in {
        ("rms-norm-ordinary-two-rank", "rms-norm-sharded-two-rank-dim0"),
        ("rms-norm-sharded-two-rank-dim0", "rms-norm-ordinary-two-rank"),
    }:
        return "mixed_rms_renderer:render_closed_mixed_rms_segment"
    if family == (
        "reduction-allreduce-chunks-ordinary-two-rank",
        "allreduce-reconstruction-k-rank",
        "joined-view-unary",
        "full-producer-chunks-k-rank",
    ):
        return "reduction_view_chunks_renderer:render_closed_reduction_view_chunks_segment"
    if family == ("elementwise-add-ordinary-two-rank", "add-sharded-k-rank"):
        return "mixed_add_renderer:render_closed_mixed_add_segment"
    if (len(family) > 2
            and set(family) == {
                "mix-precision-linear-ordinary-two-rank",
                "mix-linear-sharded-two-rank-dim0",
            }
            and family.count("mix-precision-linear-ordinary-two-rank") * 2 == len(family)):
        return "mixed_replicated_linear_tuple_renderer:render_closed_mixed_replicated_linear_tuple_segment"
    if family == (
        "mix-precision-linear-ordinary-two-rank",
        "mix-linear-sharded-two-rank-dim0",
    ):
        return "mixed_replicated_linear_renderer:render_closed_mixed_replicated_linear_segment"
    identity_pairs = {
        frozenset({"identity-reshape-ordinary-two-rank", "reshape-sharded-k-rank"}),
        frozenset({"identity-view-ordinary-two-rank", "view-sharded-k-rank"}),
    }
    if (len(family) > 2 and frozenset(family) in identity_pairs
            and family.count(next(item for item in family if item.startswith("identity-"))) * 2
            == len(family)):
        return "mixed_identity_tuple_renderer:render_closed_mixed_identity_tuple_segment"
    if family in {
        ("identity-reshape-ordinary-two-rank", "reshape-sharded-k-rank"),
        ("identity-view-ordinary-two-rank", "view-sharded-k-rank"),
    }:
        return "mixed_identity_renderer:render_closed_mixed_identity_segment"
    if family == ("glu-ordinary-two-rank", "glu-sharded-two-rank-dim0"):
        return "mixed_glu_renderer:render_closed_mixed_glu_segment"
    if family == ("flatten-3d-zigzag-two-rank", "attention-zigzag-qkv-two-rank"):
        return "@local:_render_closed_zigzag_attention_segment"
    if family and len(set(family)) == 1 and family[0] in {
        "joined-view-unary", "joined-reshape-unary", "joined_zigzag-reshape-unary",
    }:
        return "@local:render_closed_joined_view_segment"
    if (
        len(family) == 3
        and family[0] == "FW_per_head_mix_precision_linear-full-producer-chunks-ordinary-two-rank"
        and family[1:] == ("per-head-linear-ordinary-two-rank",) * 2
    ) or (
        family
        and all(item in {
            "per-head-linear-ordinary-two-rank",
            "per-head-linear-zigzag-two-rank",
        } for item in family)
        and len(set(family)) == 1
    ) or family == (
        "per-head-linear-ordinary-two-rank",
        "per-head-linear-ordinary-two-rank",
        "rms-norm-zigzag-two-rank",
    ):
        return "@local:render_closed_linear_segment"
    if (
        family
        and family[0] == "FW_per_head_mix_precision_linear-full-producer-chunks-zigzag-two-rank"
        and all(item == "to-ordinary-two-rank" for item in family[1:])
    ):
        return "@local:render_closed_full_producer_to_segment"
    semantic_family = tuple(
        item for item in family
        if item not in (
            "ordinary-topk-projection-two-rank",
            "zigzag-topk-unshuffle-two-rank",
        )
    )
    if (
        len(semantic_family) == 16
        and len(family) - len(semantic_family) <= 1
        and semantic_family[0] in (
            "FW_norm_linear-full-producer-chunks-ordinary-two-rank",
            "FW_norm_linear-full-producer-chunks-zigzag-two-rank",
        )
    ):
        return "@local:render_closed_mixed_moe_segment"
    return None


def select_mixed_linear_sequence_renderer(family: tuple[str, ...]) -> str | None:
    """Select only the broad mixed-linear schedules not owned by narrower grammar."""
    rules = {
        "linear-sharded-k-rank-dim1",
        "alltoall-k-rank-layout-transport",
        "linear-reduction-producer-k-rank",
        "allgather-reconstruction-k-rank",
        "linear-output-sharded-k-rank",
    }
    original_anchors = {
        "linear-sharded-k-rank-dim1",
        "alltoall-k-rank-layout-transport",
        "linear-reduction-producer-k-rank",
    }
    linear = "linear-sharded-k-rank-dim1"
    allgather = "allgather-reconstruction-k-rank"
    output = "linear-output-sharded-k-rank"
    local_tuple_gather = (
        len(family) >= 3
        and all(item == linear for item in family[:-1])
        and family[-1] == allgather
    )
    repeated_output = (
        len(family) >= 5
        and len(family) % 2 == 1
        and family[0] == linear
        and family[1:] == (allgather, output) * ((len(family) - 1) // 2)
    )
    if (
        family
        and set(family) <= rules
        and (
            original_anchors <= set(family)
            or local_tuple_gather
            or repeated_output
        )
    ):
        return "mixed_linear_sequence_renderer:render_closed_mixed_linear_sequence_segment"
    return None


def select_compound_renderer(family: tuple[str, ...]) -> str | None:
    """Select any family-only compound renderer in production precedence order."""
    for selector in (
        select_front_compound_renderer,
        select_mixed_linear_sequence_renderer,
        select_bw_compound_renderer,
        select_k_rank_compound_renderer,
        select_middle_compound_renderer,
        select_ordinary_compound_renderer,
        select_tail_compound_renderer,
    ):
        binding = selector(family)
        if binding is not None:
            return binding
    return None


def select_relation_dependent_renderer(
    family: tuple[str, ...],
    selected_transitions: tuple,
    certificates: tuple,
) -> str | None:
    """Select the two compound routes whose identity needs typed payload data."""
    if family and all(item == "multiref-projection-alias" for item in family):
        if all(
            transition.pre_facts
            and transition.pre_facts[0].layout in {"joined", "joined_zigzag"}
            for transition in selected_transitions
        ):
            return "joined_multiref_renderer:render_closed_joined_multiref_segment"
        return "@local:render_closed_multiref_segment"
    if family == ("inner-chunk-ce-projection-gather-two-rank",):
        ce_certificates = [
            certificate for certificate in certificates
            if getattr(certificate, "rule_id", None)
            == "inner-chunk-ce-projection-gather-two-rank"
        ]
        if len(ce_certificates) != 1:
            raise ValueError("closed CE segment lacks one exact certificate")
        projection = ce_certificates[0].output_projection
        if projection == ".fst":
            return "@local:render_closed_ce_fst_segment"
        if projection == ".snd":
            return "@local:render_closed_ce_snd_segment"
        raise ValueError(f"unsupported closed CE projection: {projection!r}")
    return None
