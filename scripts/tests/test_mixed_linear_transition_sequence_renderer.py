from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import re
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import parser as parser_module
from trainverify.bridge_emitter.composer import render_closed_segment
from trainverify.bridge_emitter.proof_compiler import build_default_registry, compile_proof_plan
from trainverify.bridge_emitter.relation_compiler import compile_relation_plan


AUTHORITY = (
    Path(__file__).resolve().parents[2]
    / "trainverify/denote/gpt_ly4_regen"
)
RULES = {
    "linear-sharded-k-rank-dim1",
    "alltoall-k-rank-layout-transport",
    "linear-reduction-producer-k-rank",
    "allgather-reconstruction-k-rank",
    "linear-output-sharded-k-rank",
}


@pytest.fixture(scope="module")
def real_authority():
    assert AUTHORITY.is_dir()
    old = (
        parser_module.DENOTE_DIR,
        parser_module.GEN_DIR,
        parser_module.GEN_FILE,
        parser_module.MOD_PREFIX,
    )
    parser_module.DENOTE_DIR = str(AUTHORITY)
    parser_module.GEN_DIR = str(AUTHORITY)
    parser_module.GEN_FILE = "GeneratedData.lean"
    parser_module.MOD_PREFIX = "denote.gpt_ly4_regen"
    try:
        ir = parser_module.load_goal_ir(1, "/")
        proof = compile_proof_plan(ir, build_default_registry())
        relation = compile_relation_plan(ir, proof)
    finally:
        (
            parser_module.DENOTE_DIR,
            parser_module.GEN_DIR,
            parser_module.GEN_FILE,
            parser_module.MOD_PREFIX,
        ) = old
    assert (len(ir.sm_nodes), len(ir.pm_nodes), len(relation.dependent_chain_plan.segments)) == (236, 1565, 190)
    return ir, relation


@pytest.mark.parametrize(
    ("segment_id", "family", "sm_range", "pm_range"),
    (
        (
            "segment_000053",
            (
                "linear-sharded-k-rank-dim1",
                "alltoall-k-rank-layout-transport",
                "linear-reduction-producer-k-rank",
                "alltoall-k-rank-layout-transport",
                "linear-reduction-producer-k-rank",
                "allgather-reconstruction-k-rank",
            ),
            (34, 37),
            (205, 226),
        ),
        (
            "segment_000142",
            (
                "linear-sharded-k-rank-dim1",
                "alltoall-k-rank-layout-transport",
                "linear-reduction-producer-k-rank",
                "alltoall-k-rank-layout-transport",
                "linear-reduction-producer-k-rank",
            ),
            (90, 93),
            (582, 602),
        ),
    ),
)
def test_real_mixed_linear_sequence_is_generic_atomic_and_deterministic(
    real_authority, segment_id, family, sm_range, pm_range
):
    ir, relation = real_authority
    segment = next(s for s in relation.dependent_chain_plan.segments if s.segment_id == segment_id)
    transitions = {t.transition_id: t for t in relation.transition_specs}
    assert tuple(transitions[tid].rule_id for tid in segment.transition_ids) == family
    assert segment.sm_range == sm_range and segment.pm_range == pm_range

    first = render_closed_segment(ir, relation, segment_id)
    second = render_closed_segment(ir, relation, segment_id)
    assert first == second
    assert first.count("@[irreducible] private def " + segment_id + "_smFinal") == 1
    assert first.count("@[irreducible] private def " + segment_id + "_pmFinal") == 1
    assert "let rankCount" in first
    assert "K := 4" not in first and "rankCount = 4" not in first
    assert first.count("fw_linear_3d_allGatherPrimDimN_dim1_comm") == 1
    assert first.count("allGatherPrimDimN_allToAllPrimWithDims_ofFn") == family.count(
        "alltoall-k-rank-layout-transport"
    )
    assert first.count("fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d") == family.count(
        "linear-reduction-producer-k-rank"
    )
    assert first.count("RelationCompiler.ShardedRel.to_joined_allGather") == family.count(
        "allgather-reconstruction-k-rank"
    )
    assert first.count("fw_linear_3d_weight_allGatherPrimDimN_dim0_comm") == family.count(
        "linear-output-sharded-k-rank"
    )
    assert "++ [" not in first.split("private def", 1)[0]


def test_real_mixed_sequence_rejects_non_exhaustive_footprint(real_authority):
    ir, relation = real_authority
    segment = next(s for s in relation.dependent_chain_plan.segments if s.segment_id == "segment_000142")
    target = segment.transition_ids[0]
    transitions = tuple(
        replace(t, pm_node_indices=t.pm_node_indices[:-1]) if t.transition_id == target else t
        for t in relation.transition_specs
    )
    with pytest.raises(ValueError, match="footprint|exhaustive|partition"):
        render_closed_segment(ir, replace(relation, transition_specs=transitions), segment.segment_id)


def test_generic_renderer_source_has_no_real_segment_model_or_transition_literals():
    source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/mixed_linear_sequence_renderer.py"
    ).read_text(encoding="utf-8")
    forbidden = {
        "segment_000429", "segment_000471", "segment_000097",
        "Goal107", "GPT2", "000227", "000120",
    }
    assert not any(item in source for item in forbidden)
    assert "len(transitions) == 5" not in source
    assert "len(transitions) != 5" not in source
    assert "[single]" not in source

    bw_sum_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_sum_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_sum_source for item in (
        "segment_000188", "Goal107", "fact_000102", "fact_000197", "fact_000198",
        "3373", "3387",
    ))

    bw_linear_dx_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_linear_dx_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_linear_dx_source for item in (
        "segment_000189", "Goal107", "fact_000008", "fact_000107", "fact_000170",
        "3387", "3394",
    ))

    bw_layernorm_dx_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_layernorm_dx_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_layernorm_dx_source for item in (
        "segment_000192", "Goal107", "fact_000168", "fact_000201", "3335",
        "800000",
    ))

    bw_add_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_add_identity_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_add_source for item in (
        "segment_000193", "Goal107", "fact_000187", "fact_000203", "3333",
    ))

    bw_linear_column_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_linear_dx_column_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_linear_column_source for item in (
        "segment_000195", "Goal107", "fact_000", "3305",
        "2000000",
    ))

    bw_gelu_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_gelu_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_gelu_source for item in (
        "segment_000197", "Goal107", "fact_000", "BW_gelu [",
    ))

    bw_multiref_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_multiref_sum_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_multiref_source for item in (
        "segment_000202", "Goal107", "fact_000", "3191",
    ))

    bw_view_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_view_joined_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_view_source for item in (
        "segment_000207", "Goal107", "fact_000",
    ))

    bw_matmul_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_matmul_shared_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_matmul_source for item in (
        "segment_000213", "Goal107", "fact_000", "3090",
    ))

    bw_softmax_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/transpose_bw_softmax_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_softmax_source for item in (
        "segment_000217", "Goal107", "fact_000", "3057",
    ))

    bw_div_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_view_bw_div_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_div_source for item in (
        "segment_000220", "Goal107", "fact_000", "3033",
    ))

    bw_attention_source = (
        Path(__file__).resolve().parents[2]
        / "trainverify/bridge_emitter/bw_linear_matmul_batch_renderer.py"
    ).read_text(encoding="utf-8")
    assert not any(item in bw_attention_source for item in (
        "segment_000223", "Goal107", "fact_000", "2914",
    ))


LOCAL_THEOREM = "TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm"
A2A_THEOREM = "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
REDUCTION_THEOREM = "TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d"
GATHER_THEOREM = "TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather"
OUTPUT_THEOREM = "TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm"


def _closed_sharded(rc, fact_id, source, sm_tid, pm_tids, full, shard, dim):
    return rc.ClosedRelationFactRecord(
        fact_id, source, "sharded", sm_tid, tuple(pm_tids), None, None,
        tuple(full), tuple(shard), dim,
    )


def _synthetic_mixed_sequence_fixture(family):
    """Compact authority with topological, deliberately interleaved PM footprints."""
    from trainverify.bridge_emitter import relation_compiler as rc
    from trainverify.bridge_emitter.parser import Node

    if family == "gather-output":
        k = 2
        local_in_spec = rc.RelationFactSpec(
            "sharded", ("init:100", "init:200", "init:201"), gather_dim=1)
        local_out_spec = rc.RelationFactSpec(
            "sharded", ("sm:0:0", "pm:0:0", "pm:1:0"), gather_dim=1)
        a2a_out_spec = rc.RelationFactSpec(
            "sharded", ("sm:0:0", "pm:2:0", "pm:3:0"), gather_dim=2)
        reduction_weight_spec = rc.RelationFactSpec(
            "sharded", ("init:130", "init:230", "init:231"), gather_dim=1)
        reduction_out_spec = rc.RelationFactSpec(
            "reduction", ("sm:1:0", "pm:4:0", "pm:6:0"))
        gather_in_spec = rc.RelationFactSpec(
            "sharded", ("init:110", "init:250", "init:251"), gather_dim=1)
        joined_spec = rc.RelationFactSpec(
            "joined", ("init:110",), joined_pm_step="pm:5:0")
        output_weight_spec = rc.RelationFactSpec(
            "sharded", ("init:131", "init:270", "init:271"), gather_dim=0)
        output_spec = rc.RelationFactSpec(
            "sharded", ("sm:2:0", "pm:7:0", "pm:8:0"), gather_dim=2)

        certs = (
            rc.KRankLocalRelationCertificate(
                "linear-sharded-k-rank-dim1", "FW_linear", k, 1,
                local_in_spec, local_out_spec, "sm:0:0", ("pm:0:0", "pm:1:0"),
                (500,), ((6, 5),), LOCAL_THEOREM),
            rc.KRankAllToAllRelationCertificate(
                "alltoall-k-rank-layout-transport", k, 1, 2,
                local_out_spec, a2a_out_spec, ("pm:2:0", "pm:3:0"), A2A_THEOREM),
            rc.KRankReductionLinearProducerCertificate(
                "linear-reduction-producer-k-rank", k, 2, 1,
                (2, 6, 6), (2, 6, 3), (7, 6), (7, 3), (2, 6, 7),
                a2a_out_spec, reduction_weight_spec, reduction_out_spec,
                "sm:1:0", ("pm:4:0", "pm:6:0"), REDUCTION_THEOREM),
            rc.KRankAllGatherReconstructionCertificate(
                "allgather-reconstruction-k-rank", k, 1, (2, 6, 5), (2, 3, 5),
                gather_in_spec, joined_spec, "pm:5:0", GATHER_THEOREM),
            rc.KRankOutputShardedLinearCertificate(
                "linear-output-sharded-k-rank", k, 2,
                joined_spec, output_weight_spec, output_spec,
                "sm:2:0", ("pm:7:0", "pm:8:0"),
                (2, 6, 5), (8, 5), (4, 5), (2, 6, 8), (2, 6, 4),
                OUTPUT_THEOREM),
        )
        sm_nodes = [
            Node(0, "FW_linear", [100, 500], [101], []),
            Node(0, "FW_linear", [101, 130], [102], []),
            Node(0, "FW_linear", [110, 131], [103], []),
        ]
        pm_nodes = [
            Node(0, "FW_linear", [200, 500], [210], []),
            Node(1, "FW_linear", [201, 500], [211], []),
            Node(0, "AllToAllPrim", [210, 211], [212], [1, 2]),
            Node(1, "AllToAllPrim", [210, 211], [213], [1, 2]),
            Node(0, "FW_linear", [212, 230], [240], []),
            Node(0, "AllGatherPrim", [250, 251], [260], [1]),
            Node(1, "FW_linear", [213, 231], [241], []),
            Node(0, "FW_linear", [260, 270], [280], []),
            Node(1, "FW_linear", [260, 271], [281], []),
        ]
        records = (
            _closed_sharded(rc, "local_in", local_in_spec, 100, (200, 201), (2, 6, 5), (2, 3, 5), 1),
            _closed_sharded(rc, "local_out", local_out_spec, 101, (210, 211), (2, 6, 6), (2, 3, 6), 1),
            _closed_sharded(rc, "a2a_out", a2a_out_spec, 101, (212, 213), (2, 6, 6), (2, 6, 3), 2),
            _closed_sharded(rc, "reduction_weight", reduction_weight_spec, 130, (230, 231), (7, 6), (7, 3), 1),
            rc.ClosedRelationFactRecord(
                "reduction_out", reduction_out_spec, "reduction", 102, (240, 241),
                None, None, (2, 6, 7), (2, 6, 7)),
            _closed_sharded(rc, "gather_in", gather_in_spec, 110, (250, 251), (2, 6, 5), (2, 3, 5), 1),
            rc.ClosedRelationFactRecord(
                "joined", joined_spec, "joined", 110, (), None, None,
                (2, 6, 5), (2, 6, 5), joined_pm_tid=260),
            _closed_sharded(rc, "output_weight", output_weight_spec, 131, (270, 271), (8, 5), (4, 5), 0),
            _closed_sharded(rc, "output", output_spec, 103, (280, 281), (2, 6, 8), (2, 6, 4), 2),
        )
        pre_relations = ("local_in", "reduction_weight", "gather_in", "output_weight")
        post_relations = ("local_out", "a2a_out", "reduction_out", "joined", "output")
        namespace = "GeneratedMixedLinearSequenceK2GatherOutputWitness"
    elif family == "double-reduction":
        k = 3
        local_in_spec = rc.RelationFactSpec(
            "sharded", ("init:100", "init:200", "init:201", "init:202"), gather_dim=1)
        local_out_spec = rc.RelationFactSpec(
            "sharded", ("sm:0:0", "pm:0:0", "pm:1:0", "pm:2:0"), gather_dim=1)
        a2a1_out_spec = rc.RelationFactSpec(
            "sharded", ("sm:0:0", "pm:3:0", "pm:4:0", "pm:5:0"), gather_dim=2)
        weight1_spec = rc.RelationFactSpec(
            "sharded", ("init:130", "init:230", "init:231", "init:232"), gather_dim=1)
        reduction1_spec = rc.RelationFactSpec(
            "reduction", ("sm:1:0", "pm:6:0", "pm:8:0", "pm:10:0"))
        a2a2_in_spec = rc.RelationFactSpec(
            "sharded", ("init:110", "init:250", "init:251", "init:252"), gather_dim=1)
        a2a2_out_spec = rc.RelationFactSpec(
            "sharded", ("init:110", "pm:7:0", "pm:9:0", "pm:11:0"), gather_dim=2)
        weight2_spec = rc.RelationFactSpec(
            "sharded", ("init:131", "init:270", "init:271", "init:272"), gather_dim=1)
        reduction2_spec = rc.RelationFactSpec(
            "reduction", ("sm:2:0", "pm:12:0", "pm:13:0", "pm:14:0"))
        certs = (
            rc.KRankLocalRelationCertificate(
                "linear-sharded-k-rank-dim1", "FW_linear", k, 1,
                local_in_spec, local_out_spec, "sm:0:0", ("pm:0:0", "pm:1:0", "pm:2:0"),
                (500,), ((6, 5),), LOCAL_THEOREM),
            rc.KRankAllToAllRelationCertificate(
                "alltoall-k-rank-layout-transport", k, 1, 2,
                local_out_spec, a2a1_out_spec, ("pm:3:0", "pm:4:0", "pm:5:0"), A2A_THEOREM),
            rc.KRankReductionLinearProducerCertificate(
                "linear-reduction-producer-k-rank", k, 2, 1,
                (2, 6, 6), (2, 6, 2), (7, 6), (7, 2), (2, 6, 7),
                a2a1_out_spec, weight1_spec, reduction1_spec,
                "sm:1:0", ("pm:6:0", "pm:8:0", "pm:10:0"), REDUCTION_THEOREM),
            rc.KRankAllToAllRelationCertificate(
                "alltoall-k-rank-layout-transport", k, 1, 2,
                a2a2_in_spec, a2a2_out_spec, ("pm:7:0", "pm:9:0", "pm:11:0"), A2A_THEOREM),
            rc.KRankReductionLinearProducerCertificate(
                "linear-reduction-producer-k-rank", k, 2, 1,
                (2, 6, 6), (2, 6, 2), (8, 6), (8, 2), (2, 6, 8),
                a2a2_out_spec, weight2_spec, reduction2_spec,
                "sm:2:0", ("pm:12:0", "pm:13:0", "pm:14:0"), REDUCTION_THEOREM),
        )
        sm_nodes = [
            Node(0, "FW_linear", [100, 500], [101], []),
            Node(0, "FW_linear", [101, 130], [102], []),
            Node(0, "FW_linear", [110, 131], [103], []),
        ]
        pm_nodes = [
            Node(0, "FW_linear", [200, 500], [210], []),
            Node(1, "FW_linear", [201, 500], [211], []),
            Node(2, "FW_linear", [202, 500], [212], []),
            Node(0, "AllToAllPrim", [210, 211, 212], [213], [1, 2]),
            Node(1, "AllToAllPrim", [210, 211, 212], [214], [1, 2]),
            Node(2, "AllToAllPrim", [210, 211, 212], [215], [1, 2]),
            Node(0, "FW_linear", [213, 230], [240], []),
            Node(0, "AllToAllPrim", [250, 251, 252], [253], [1, 2]),
            Node(1, "FW_linear", [214, 231], [241], []),
            Node(1, "AllToAllPrim", [250, 251, 252], [254], [1, 2]),
            Node(2, "FW_linear", [215, 232], [242], []),
            Node(2, "AllToAllPrim", [250, 251, 252], [255], [1, 2]),
            Node(0, "FW_linear", [253, 270], [280], []),
            Node(1, "FW_linear", [254, 271], [281], []),
            Node(2, "FW_linear", [255, 272], [282], []),
        ]
        records = (
            _closed_sharded(rc, "local_in", local_in_spec, 100, (200, 201, 202), (2, 6, 5), (2, 2, 5), 1),
            _closed_sharded(rc, "local_out", local_out_spec, 101, (210, 211, 212), (2, 6, 6), (2, 2, 6), 1),
            _closed_sharded(rc, "a2a1_out", a2a1_out_spec, 101, (213, 214, 215), (2, 6, 6), (2, 6, 2), 2),
            _closed_sharded(rc, "weight1", weight1_spec, 130, (230, 231, 232), (7, 6), (7, 2), 1),
            rc.ClosedRelationFactRecord(
                "reduction1", reduction1_spec, "reduction", 102, (240, 241, 242),
                None, None, (2, 6, 7), (2, 6, 7)),
            _closed_sharded(rc, "a2a2_in", a2a2_in_spec, 110, (250, 251, 252), (2, 6, 6), (2, 2, 6), 1),
            _closed_sharded(rc, "a2a2_out", a2a2_out_spec, 110, (253, 254, 255), (2, 6, 6), (2, 6, 2), 2),
            _closed_sharded(rc, "weight2", weight2_spec, 131, (270, 271, 272), (8, 6), (8, 2), 1),
            rc.ClosedRelationFactRecord(
                "reduction2", reduction2_spec, "reduction", 103, (280, 281, 282),
                None, None, (2, 6, 8), (2, 6, 8)),
        )
        pre_relations = ("local_in", "weight1", "a2a2_in", "weight2")
        post_relations = ("local_out", "a2a1_out", "reduction1", "a2a2_out", "reduction2")
        namespace = "GeneratedMixedLinearSequenceK3DoubleReductionWitness"
    else:
        raise AssertionError(family)

    authorities = (
        rc.ClosedTensorEqFactRecord("local_weight_eq", "sm", 500, "pm", 500),
        rc.ClosedTensorShapeFactRecord("local_weight_shape", "pm", 500, (6, 5), 500),
    )
    anchor = rc.ClosedTensorShapeFactRecord("anchor", "sm", 999, (1,), 999)
    before = rc.ClosedRelationStateRecord(
        "state_pre", ("anchor", *pre_relations, "local_weight_eq", "local_weight_shape"))
    after = rc.ClosedRelationStateRecord("state_post", ("anchor", *post_relations))
    transitions = rc.build_certificate_transition_specs(SimpleNamespace(), certs)
    segment = rc.ClosedDependentSegmentRecord(
        "segment_synthetic", "component", before.state_id, after.state_id,
        tuple(t.transition_id for t in transitions), (0, len(sm_nodes)), (0, len(pm_nodes)))
    chain = SimpleNamespace(
        complete=True, relation_facts=records, authority_facts=authorities,
        anchor_fact=anchor, states=(before, after), segments=(segment,))
    ir = SimpleNamespace(
        sm_nodes=sm_nodes, pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref=f"TrainVerify.Denote.{namespace}.smGraph",
        pm_graph_ref=f"TrainVerify.Denote.{namespace}.pmGraph")
    relation = SimpleNamespace(
        certificates=certs, transition_specs=transitions, dependent_chain_plan=chain)
    return ir, relation, segment, namespace


@pytest.mark.parametrize(
    ("family", "expected_rules", "interleaved_footprints"),
    (
        (
            "gather-output",
            (
                "linear-sharded-k-rank-dim1", "alltoall-k-rank-layout-transport",
                "linear-reduction-producer-k-rank", "allgather-reconstruction-k-rank",
                "linear-output-sharded-k-rank",
            ),
            ((4, 6), (5,)),
        ),
        (
            "double-reduction",
            (
                "linear-sharded-k-rank-dim1", "alltoall-k-rank-layout-transport",
                "linear-reduction-producer-k-rank", "alltoall-k-rank-layout-transport",
                "linear-reduction-producer-k-rank",
            ),
            ((6, 8, 10), (7, 9, 11)),
        ),
    ),
)
def test_synthetic_mixed_sequence_covers_dynamic_interleaved_semantics(
    family, expected_rules, interleaved_footprints
):
    ir, relation, segment, _ = _synthetic_mixed_sequence_fixture(family)
    transitions = {t.transition_id: t for t in relation.transition_specs}
    ordered = tuple(transitions[tid] for tid in segment.transition_ids)
    assert tuple(t.rule_id for t in ordered) == expected_rules
    assert tuple(t.pm_node_indices for t in ordered[2:4]) == interleaved_footprints
    rendered = render_closed_segment(ir, relation, segment.segment_id)
    assert rendered == render_closed_segment(ir, relation, segment.segment_id)
    assert rendered.count("@[irreducible] private def " + segment.segment_id + "_smFinal") == 1
    assert rendered.count("@[irreducible] private def " + segment.segment_id + "_pmFinal") == 1
    assert f"numRanks := {ir.pm_num_ranks}" not in rendered
    assert "rankCount" in rendered
    transition_helpers = re.findall(
        rf"private theorem {segment.segment_id}_transition_[^ ]+ \(smStore pmStore : Store\)",
        rendered,
    )
    assert len(transition_helpers) == len(expected_rules)
    for helper in transition_helpers:
        helper_start = rendered.index(helper)
        result_start = rendered.index(" :", helper_start)
        result_end = rendered.index(" := by", result_start)
        result = rendered[result_start:result_end]
        assert f"{segment.segment_id}_smFinal smStore" in result
        assert f"{segment.segment_id}_pmFinal pmStore" in result
    publish_start = rendered.index(f"private theorem {segment.segment_id}_publish_state")
    certificate_start = rendered.index(f"private def {segment.segment_id} :", publish_start)
    publish = rendered[publish_start:certificate_start]
    assert f"{segment.segment_id}_frame smStore pmStore hstate" in publish
    assert publish.count(f"{segment.segment_id}_transition_") == len(expected_rules)
    assert not any(theorem in publish for theorem in (
        LOCAL_THEOREM, A2A_THEOREM, REDUCTION_THEOREM, GATHER_THEOREM, OUTPUT_THEOREM,
    ))
    assert "foldl" not in publish and "applyNode" not in publish


def test_generated_synthetic_mixed_sequence_witnesses_are_exact_and_self_contained():
    from trainverify.bridge_emitter.composer import render_closed_relation_declarations

    root = Path(__file__).resolve().parents[2]
    for family in ("gather-output", "double-reduction"):
        ir, relation, segment, namespace = _synthetic_mixed_sequence_fixture(family)
        declarations = render_closed_relation_declarations(
            relation.dependent_chain_plan, namespace)
        rendered = render_closed_segment(ir, relation, segment.segment_id)
        source = "\n".join((
            declarations,
            f"namespace TrainVerify.Denote.{namespace}",
            "noncomputable section",
            "private def smGraph : GraphDecl := { numRanks := 1, nodes := [] }",
            f"private def pmGraph : GraphDecl := {{ numRanks := {ir.pm_num_ranks}, nodes := [] }}",
            rendered,
            f"#print axioms {segment.segment_id}",
            "end",
            f"end TrainVerify.Denote.{namespace}",
            "",
        ))
        witness = root / "trainverify/denote" / f"{namespace}.lean"
        assert witness.read_text(encoding="utf-8") == source
        assert witness.stat().st_size < 2_500_000
        assert "sorry" not in source and "False.elim" not in source
        assert "/tmp/" not in source and "GPT2SmallArchiveFresh" not in source
