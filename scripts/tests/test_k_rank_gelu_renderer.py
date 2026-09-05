from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node


RULE = "gelu-sharded-k-rank"
THEOREM = "TrainVerify.Denote.fw_gelu_allGatherPrimDimN_eq"


def test_gelu_identity_and_singleton_dispatch_are_registry_driven(monkeypatch):
    assert set(rc.CLOSED_RULE_REGISTRY) >= {
        "linear-sharded-k-rank-dim1",
        "layernorm-sharded-k-rank-dim1",
        RULE,
    }
    assert set(rc.CLOSED_RULE_REGISTRY) <= set(composer.CLOSED_SINGLETON_RENDERERS)
    spec = rc.CLOSED_RULE_REGISTRY[RULE]
    assert spec.certificate_type is rc.KRankLocalRelationCertificate
    assert spec.op == "FW_gelu"
    assert spec.lean_theorems == (THEOREM,)

    captured = {}

    def fake_advance(plan, frontiers, layouts, **kwargs):
        captured.update(kwargs)
        return (), frontiers, layouts

    monkeypatch.setattr(rc, "_advance_k_rank_local_relation_frontiers", fake_advance)
    rc.advance_k_rank_gelu_relation_frontiers(object(), (), ())
    assert captured["rule_id"] == spec.rule_id
    assert captured["lean_theorem"] == spec.lean_theorems[0]
    assert captured["op"] == spec.op

    ir, relation, segment, *_ = _closed_fixture()
    called = []

    def fake_renderer(actual_ir, actual_relation, segment_id):
        called.append(segment_id)
        return "registry-rendered"

    monkeypatch.setitem(composer.CLOSED_SINGLETON_RENDERERS, spec.rule_id, fake_renderer)
    assert composer.render_closed_segment(ir, relation, segment.segment_id) == "registry-rendered"
    assert called == [segment.segment_id]


def test_additional_singleton_rule_identity_and_backends_are_registry_driven():
    expected = {
        "rms-norm-sharded-two-rank-dim0": (
            rc.KRankLocalRelationCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_rms_norm_2d",),
            "FW_rms_norm",
            "rms_norm_sharded_renderer:render_closed_two_rank_rms_norm_segment",
            (),
        ),
        "linear-output-sharded-k-rank": (
            rc.KRankOutputShardedLinearCertificate,
            ("TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm",),
            "FW_linear",
            "sparse_output_linear_renderer:render_closed_sparse_output_sharded_linear_segment",
            ("denote.KRankLinearGather",),
        ),
        "add-sharded-k-rank": (
            rc.KRankBinaryRelationCertificate,
            ("TrainVerify.Denote.fw_add_allGather_dim_K",),
            "FW_add",
            "add_renderer:render_closed_k_rank_add_segment",
            ("denote.KRankAddGather",),
        ),
        "embedding-sharded-ids-k-rank": (
            rc.KRankShardedIdsEmbeddingCertificate,
            ("TrainVerify.Denote.fw_embedding_allGatherPrimDimN_dim1_shared_weight",),
            None,
            "sharded_ids_embedding_renderer:render_closed_k_rank_sharded_ids_embedding_segment",
            ("denote.EmbeddingSequenceShard", "denote.KRankAllToAll"),
        ),
        "matmul-output-axis-sharded-k-rank-dim3": (
            rc.KRankMatmulOutputAxisCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_output_axis_rank4",),
            None, "composer:render_closed_k_rank_matmul_output_axis_segment",
            ("denote.KRankMatmul",),
        ),
        "matmul-head-axis-sharded-k-rank-dim1": (
            rc.KRankMatmulHeadAxisCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_head_axis_rank4",),
            None, "composer:render_closed_k_rank_matmul_head_axis_segment",
            ("denote.KRankMatmulHeadAxis",),
        ),
        "matmul-query-axis-sharded-k-rank-dim2": (
            rc.KRankMatmulQueryAxisCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4",),
            None, "composer:render_closed_k_rank_matmul_query_axis_segment",
            ("denote.KRankMatmulQueryAxis",),
        ),
        "matmul-contraction-reduction-k-rank": (
            rc.KRankMatmulContractionCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_contraction_axis_rank4",),
            None, "composer:render_closed_k_rank_matmul_contraction_segment",
            ("denote.KRankMatmulContractionReduction",),
        ),
        "softmax-sharded-k-rank-dim1": (
            rc.KRankSoftmaxCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_softmax_dim1_rank4",),
            None, "composer:render_closed_k_rank_softmax_segment",
            ("denote.KRankSoftmaxGather",),
        ),
        "softmax-sharded-k-rank-dim2": (
            rc.KRankSoftmaxCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_softmax_dim2_rank4",),
            None, "composer:render_closed_k_rank_softmax_segment",
            ("denote.KRankSoftmaxGather",),
        ),
        "div-sharded-k-rank-dim1": (
            rc.KRankDivCertificate,
            (
                "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_div_dim1_rank4",
                "TrainVerify.Denote.bw_div_allGatherPrimDimN_eq_g128",
            ),
            None, "composer:render_closed_k_rank_div_segment",
            ("denote.KRankDivGather",),
        ),
        "div-sharded-k-rank-dim2": (
            rc.KRankDivCertificate,
            (
                "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_div_dim2_rank4",
                "TrainVerify.Denote.bw_div_allGatherPrimDimN_eq_g128",
            ),
            None, "composer:render_closed_k_rank_div_segment",
            ("denote.KRankDivGather",),
        ),
        "div-sharded-k-rank-dim3": (
            rc.KRankDivCertificate,
            (
                "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_div_dim3_rank4",
                "TrainVerify.Denote.bw_div_allGatherPrimDimN_eq_g128",
            ),
            None, "composer:render_closed_k_rank_div_segment",
            ("denote.KRankDivGather",),
        ),
        "contiguous-sharded-k-rank": (
            rc.KRankContiguousRelationCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_contiguous",),
            None, "composer:render_closed_k_rank_contiguous_segment", (),
        ),
        "float-sharded-k-rank": (
            rc.KRankContiguousRelationCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_contiguous",),
            None, "composer:render_closed_k_rank_contiguous_segment", (),
        ),
        "reshape-sharded-k-rank": (
            rc.KRankContiguousRelationCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_view_id",),
            "FW_reshape", "sharded_identity_renderer:render_closed_sharded_identity_segment", (),
        ),
        "view-sharded-k-rank": (
            rc.KRankContiguousRelationCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_view_id",),
            "FW_view", "sharded_identity_renderer:render_closed_sharded_identity_segment", (),
        ),
        "full-producer-chunks-k-rank": (
            rc.KRankFullProducerChunksCertificate,
            ("TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn",),
            None, "composer:render_closed_k_rank_full_producer_chunks_segment", (),
        ),
        "allgather-reconstruction-k-rank": (
            rc.KRankAllGatherReconstructionCertificate,
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather",),
            None, "composer:render_closed_k_rank_allgather_segment", (),
        ),
        "allreduce-reconstruction-k-rank": (
            rc.KRankAllReduceReconstructionCertificate,
            ("TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce",),
            None, "composer:render_closed_k_rank_allreduce_segment", (),
        ),
        "embedding-vocab-sharded-reduction-k-rank": (
            rc.KRankVocabShardedEmbeddingProducerCertificate,
            ("TrainVerify.Denote.fw_embedding_eq_allReduce_offset_shards",),
            None, "composer:render_closed_k_rank_vocab_embedding_segment", (),
        ),
        "sum-producer-sharded-k-rank-dim1": (
            rc.KRankSumProducerCertificate,
            ("TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum",),
            None, "composer:render_closed_k_rank_sum_producer_segment", (),
        ),
        "embedding-hidden-sharded-k-rank": (
            rc.KRankHiddenShardedEmbeddingCertificate,
            (
                "TrainVerify.Denote.fw_embedding_hidden_shards_two",
                "TrainVerify.Denote.fw_embedding_hidden_shards_k_rank",
            ),
            None, "hidden_sharded_embedding_renderer:render_closed_k_rank_hidden_sharded_embedding_segment", (),
        ),
    }
    for rule_id, identity in expected.items():
        spec = rc.CLOSED_RULE_REGISTRY[rule_id]
        assert (
            spec.certificate_type, spec.lean_theorems, spec.op,
            spec.singleton_renderer, spec.lean_imports,
        ) == identity
        assert rule_id in composer.CLOSED_SINGLETON_RENDERERS


def test_bw_and_collective_singleton_backends_are_registry_driven():
    rules = {
        "bw-add-identity-sharded-k-rank",
        "bw-embedding-sequence-reduction-rank4",
        "bw-embedding-vocab-sharded-k-rank",
        "bw-gelu-pointwise-sharded-k-rank",
        "bw-layernorm-dx-dim1-rank4-1-2-32",
        "bw-linear-dx-column-sharded-rank4",
        "bw-linear-dx-row-reduction-rank4",
        "bw-linear-dx-sequence-sharded-rank4",
        "bw-multiref-sum-sharded-k-rank",
        "bw-sum-scalar-broadcast-dim2-k-rank",
        "bw-view-joined",
        "alltoall-k-rank-layout-transport",
        "cross-dp-wred-reconstruction-k-rank",
        "reduce-scatter-reconstruction-k-rank",
        "zigzag-allgather-joined-two-rank",
    }
    assert rules <= set(rc.CLOSED_RULE_REGISTRY)
    assert rules <= set(composer.CLOSED_SINGLETON_RENDERERS)
    for rule in rules:
        spec = rc.CLOSED_RULE_REGISTRY[rule]
        assert spec.certificate_type is not object
        assert spec.lean_theorems
        assert spec.singleton_renderer


def test_ordinary_zigzag_singleton_backends_are_registry_driven():
    rules = {
        "linear-output-sharded-two-rank-2d",
        "float-ordinary-two-rank",
        "zigzag-to-ordinary-unshuffle-two-rank",
        "indexed-stack-gather-two-rank",
        "swiglu-sharded-two-rank-dim1",
        "rms-norm-joined-two-rank",
        "rms-norm-joined_zigzag-two-rank",
        "zigzag-feature-linear-dim1-allreduce-chunks-cp2",
        "zigzag-feature-swiglu-two-rank",
        "zigzag-feature-view-id-two-rank",
        "zigzag-feature-output-linear-two-rank",
        "rotary-embedding-two-output-ordinary-two-rank",
        "mix-precision-linear-ordinary-two-rank",
        "mix-precision-linear-zigzag-two-rank",
        "elementwise-add-ordinary-two-rank",
        "elementwise-add-zigzag-two-rank",
        "broadcast-mul-ordinary-two-rank",
        "broadcast-mul-zigzag-two-rank",
        "swiglu-ordinary-two-rank",
        "swiglu-zigzag-two-rank",
        "glu-ordinary-two-rank",
        "glu-zigzag-two-rank",
        "float-zigzag-two-rank",
        "identity-view-ordinary-two-rank",
        "identity-view-zigzag-two-rank",
        "identity-reshape-ordinary-two-rank",
        "identity-reshape-zigzag-two-rank",
        "flatten-3d-ordinary-two-rank",
        "flatten-3d-zigzag-two-rank",
        "init-lineage-alias-chunks-two-rank-dim0",
        "init-lineage-alias-chunks-two-rank-dim1",
        "rms-norm-ordinary-two-rank",
        "rms-norm-zigzag-two-rank",
        "attention-ordinary-qkv-two-rank",
        "attention-zigzag-qkv-two-rank",
    }
    assert rules <= set(rc.CLOSED_RULE_REGISTRY)
    assert rules <= set(composer.CLOSED_SINGLETON_RENDERERS)


def test_legacy_gelu_renderer_path_is_retired():
    package_dir = Path(composer.__file__).resolve().parent
    assert not (package_dir / "gelu_renderer.py").exists()
    assert not hasattr(composer, "render_closed_k_rank_gelu_segment")


def _closed_fixture(k=3, gather_dim=1):
    input_tids = tuple(200 + rank for rank in range(k))
    output_tids = tuple(300 + rank for rank in range(k))
    shard = (2, 4, 5)
    full = list(shard)
    full[gather_dim] *= k
    full = tuple(full)
    input_spec = rc.RelationFactSpec(
        "sharded", ("init:100", *(f"init:{tid}" for tid in input_tids)),
        gather_dim=gather_dim,
    )
    output_spec = rc.RelationFactSpec(
        "sharded", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(k))),
        gather_dim=gather_dim,
    )
    cert = rc.KRankLocalRelationCertificate(
        rule_id=RULE, op="FW_gelu", rank_count=k, gather_dim=gather_dim,
        input_fact=input_spec, output_fact=output_spec, sm_step_id="sm:0:0",
        pm_step_ids=tuple(f"pm:{rank}:0" for rank in range(k)),
        external_tids=(), external_shapes=(), external_facts=(), lean_theorem=THEOREM,
    )
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    pre = rc.ClosedRelationFactRecord(
        fact_id="fact_in", source=input_spec, kind="sharded", sm_tid=100,
        pm_tids=input_tids, metadata_tid=None, metadata_region_id=None,
        full_shape=full, shard_shape=shard, gather_dim=gather_dim,
    )
    post = rc.ClosedRelationFactRecord(
        fact_id="fact_out", source=output_spec, kind="sharded", sm_tid=110,
        pm_tids=output_tids, metadata_tid=None, metadata_region_id=None,
        full_shape=full, shard_shape=shard, gather_dim=gather_dim,
    )
    before = SimpleNamespace(state_id="state_pre", fact_ids=(pre.fact_id,))
    after = SimpleNamespace(state_id="state_post", fact_ids=(post.fact_id,))
    segment = SimpleNamespace(
        segment_id="segment_000051", transition_ids=(transition.transition_id,),
        sm_range=(0, 1), pm_range=(0, k), pre_state_id=before.state_id,
        post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(pre, post), authority_facts=(),
        states=(before, after), segments=(segment,),
    )
    ir = SimpleNamespace(
        sm_nodes=[Node(0, "FW_gelu", [100], [110], [])],
        pm_nodes=[Node(rank, "FW_gelu", [input_tids[rank]], [output_tids[rank]], [])
                  for rank in range(k)],
        sm_graph_ref="SyntheticGelu.gSM", pm_graph_ref="SyntheticGelu.gPM",
    )
    relation = SimpleNamespace(
        certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain,
    )
    return ir, relation, segment, cert, transition, pre, post


def test_gelu_typed_certificate_has_exact_rule_theorem_and_empty_external_authority():
    _ir, _relation, _segment, cert, transition, pre, post = _closed_fixture(k=4)
    assert type(cert) is rc.KRankLocalRelationCertificate
    assert (cert.rule_id, cert.op, cert.rank_count) == (RULE, "FW_gelu", 4)
    assert cert.lean_theorem == THEOREM
    assert cert.external_tids == cert.external_shapes == ()
    assert transition.pre_facts == (pre.source,)
    assert transition.post_facts == (post.source,)


@pytest.mark.parametrize("k", (2, 3, 5))
def test_gelu_renderer_owns_exact_one_plus_dynamic_ordered_k_writers(k):
    ir, relation, segment, _cert, _transition, pre, post = _closed_fixture(k=k)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count(": List NodeDecl :=") == 2
    assert source.count("foldl_faithful_middle_writer") == 1 + k
    assert source.count("applyNode_fw_gelu_out") == 1 + k
    assert THEOREM in source
    pm_final = f"({segment.segment_id}_pmFinal pmStore)"
    assert "[" + ", ".join(f"{pm_final} {tid}" for tid in pre.pm_tids) + "].length" in source
    assert "[" + ", ".join(f"{pm_final} {tid}" for tid in post.pm_tids) + "]" in source
    assert f"rankCount = {k}" not in source


def test_gelu_renderer_selects_exact_transition_certificate_and_rejects_duplicates():
    ir, relation, segment, cert, *_ = _closed_fixture(k=3)
    expected = composer.render_closed_segment(ir, relation, segment.segment_id)
    unrelated = replace(
        cert,
        input_fact=rc.RelationFactSpec(
            "sharded", ("sm:99:0", "pm:99:0", "pm:100:0"), gather_dim=1,
        ),
    )
    with_unrelated = SimpleNamespace(**{**relation.__dict__, "certificates": (unrelated, cert)})
    assert composer.render_closed_segment(ir, with_unrelated, segment.segment_id) == expected

    for certificates in ((unrelated,), (cert, cert)):
        broken = SimpleNamespace(**{**relation.__dict__, "certificates": certificates})
        with pytest.raises(ValueError, match="one exact typed certificate"):
            composer.render_closed_segment(ir, broken, segment.segment_id)


def test_gelu_renderer_rejects_payload_digest_mismatch():
    ir, relation, segment, cert, *_ = _closed_fixture(k=3)
    broken = SimpleNamespace(
        **{**relation.__dict__, "certificates": (replace(cert, rank_count=4),)}
    )

    with pytest.raises(ValueError, match="one exact typed certificate"):
        composer.render_closed_segment(ir, broken, segment.segment_id)


@pytest.mark.parametrize(("field", "value", "message"), [
    ("rule_id", "gelu-lookalike", "unsupported closed segment family"),
    ("lean_theorem", "TrainVerify.Denote.fake_gelu", "theorem identity"),
])
def test_gelu_renderer_rejects_tampered_transition_identity(field, value, message):
    ir, relation, segment, _cert, transition, *_ = _closed_fixture(k=3)
    broken_transition = replace(transition, **{field: value})
    broken = SimpleNamespace(**{**relation.__dict__, "transition_specs": (broken_transition,)})
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, broken, segment.segment_id)


@pytest.mark.parametrize(("mutation", "message"), [
    ({"rank": 9}, "ordered ranks"),
    ({"op": "FW_sigmoid"}, "unary singleton-output FW_gelu"),
    ({"ins": [999]}, "ordered relation TIDs"),
    ({"outs": [999]}, "ordered relation TIDs"),
    ({"params": [1]}, "no parameters"),
    ({"ins": [201, 202]}, "unary singleton-output FW_gelu"),
])
def test_gelu_renderer_rejects_malformed_or_tampered_pm_writer(mutation, message):
    ir, relation, segment, *_ = _closed_fixture(k=3)
    for field, value in mutation.items():
        setattr(ir.pm_nodes[1], field, value)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def test_gelu_renderer_rejects_shape_or_state_framing_tampering():
    ir, relation, segment, _cert, _transition, pre, post = _closed_fixture(k=3)
    malformed_post = replace(post, shard_shape=(2, 4, 6))
    chain = SimpleNamespace(**{
        **relation.dependent_chain_plan.__dict__, "relation_facts": (pre, malformed_post),
    })
    with pytest.raises(ValueError, match="relation metadata"):
        composer.render_closed_segment(
            ir, SimpleNamespace(**{**relation.__dict__, "dependent_chain_plan": chain}),
            segment.segment_id,
        )

    bad_after = SimpleNamespace(state_id="state_post", fact_ids=(post.fact_id, "unproved"))
    chain = SimpleNamespace(**{
        **relation.dependent_chain_plan.__dict__,
        "states": (relation.dependent_chain_plan.states[0], bad_after),
    })
    with pytest.raises(ValueError, match="unproved fact"):
        composer.render_closed_segment(
            ir, SimpleNamespace(**{**relation.__dict__, "dependent_chain_plan": chain}),
            segment.segment_id,
        )


def test_gelu_renderer_rejects_duplicate_materialized_fact_or_state_ids():
    ir, relation, segment, _cert, _transition, pre, post = _closed_fixture(k=3)
    for field, values, message in (
        ("relation_facts", (pre, post, post), "duplicate relation fact source"),
        ("states", (*relation.dependent_chain_plan.states, relation.dependent_chain_plan.states[1]),
         "duplicate relation state id"),
    ):
        chain = SimpleNamespace(**{**relation.dependent_chain_plan.__dict__, field: values})
        broken = SimpleNamespace(**{**relation.__dict__, "dependent_chain_plan": chain})
        with pytest.raises(ValueError, match=message):
            composer.render_closed_segment(ir, broken, segment.segment_id)


def _witness_source(rendered):
    return f'''import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticGelu
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_gelu", ins := [100], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := "OpName.FW_gelu", ins := [200], outs := [300] }}, {{ rank := 1, op := "OpName.FW_gelu", ins := [201], outs := [301] }}, {{ rank := 2, op := "OpName.FW_gelu", ins := [202], outs := [302] }}] }}

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 12, 5] [2, 4, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 12, 5] [2, 4, 5]
def state_pre : RelationState where facts := [fact_in]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

{rendered}
#print axioms segment_000051
end
end SyntheticGelu
end TrainVerify.Denote
'''


def test_generated_gelu_witness_is_exact_renderer_output():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    source = _witness_source(composer.render_closed_segment(ir, relation, segment.segment_id))
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedKRankGeluRendererWitness.lean"
    assert witness.read_text(encoding="utf-8") == source
    assert source.count("import denote.RelationCompiler") == 1
    assert "sorry" not in source


def test_gelu_closed_bundle_registers_theorem_import_boundary():
    assert composer._closed_segment_family_imports((RULE,), (THEOREM,)) == ()
