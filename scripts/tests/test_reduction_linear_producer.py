import os
from pathlib import Path
from types import SimpleNamespace

import pytest

import trainverify.bridge_emitter.composer as composer
import trainverify.bridge_emitter.relation_compiler as relation_compiler
from trainverify.bridge_emitter.composer import (
    render_closed_relation_declarations,
    render_closed_segment,
)
from trainverify.bridge_emitter.parser import Node
from trainverify.bridge_emitter.relation_compiler import (
    CertificateTransitionSpec,
    ClosedDependentSegmentRecord,
    ClosedRelationFactRecord,
    ClosedRelationStateRecord,
    ClosedTensorShapeFactRecord,
    KRankReductionLinearProducerCertificate,
    RelationCompositionError,
    RelationFactSpec,
    build_certificate_transition_specs,
)


def synthetic_reduction_linear(*, rank_count=4, rank3=True):
    afull = (1, 1024, 768) if rank3 else (1024, 768)
    ashard = (1, 1024, 768 // rank_count) if rank3 else (1024, 768 // rank_count)
    wfull, wshard = (768, 768), (768, 768 // rank_count)
    output = (1, 1024, 768) if rank3 else (1024, 768)
    chunk_dim = len(afull) - 1
    sm_activation = SimpleNamespace(
        step_id="sm:22:0", side="sm", op="FW_view", rank=0,
        input_bindings=("sm:21:0",), input_shapes=(afull,), parameters=afull,
        output_shape=afull,
    )
    pm_producer = SimpleNamespace(
        step_id="pm:144:0", side="pm", op="FW_view", rank=rank_count - 1,
        input_bindings=("pm:140:0",), input_shapes=(afull,), parameters=afull,
        output_shape=afull,
    )
    pm_activations = tuple(SimpleNamespace(
        step_id=f"pm:{145 + rank}:0", side="pm", op="ChunkPrim", rank=rank,
        input_bindings=(pm_producer.step_id,), input_shapes=(afull,),
        parameters=(chunk_dim,), output_shape=ashard,
    ) for rank in range(rank_count))
    sm_linear = SimpleNamespace(
        step_id="sm:23:0", side="sm", op="FW_linear", rank=0,
        input_bindings=(sm_activation.step_id, "init:1631"),
        input_shapes=(afull, wfull), parameters=(), output_shape=output,
    )
    pm_linears = tuple(SimpleNamespace(
        step_id=f"pm:{149 + rank}:0", side="pm", op="FW_linear", rank=rank,
        input_bindings=(pm_activations[rank].step_id, f"init:{3485 + rank}"),
        input_shapes=(ashard, wshard), parameters=(), output_shape=output,
    ) for rank in range(rank_count))
    lineage = SimpleNamespace(
        ts=1631, tsShape=wfull,
        tps=tuple((rank, 3485 + rank) for rank in range(rank_count)),
        tpShapes=tuple(wshard for _ in range(rank_count)),
        gatherDim=1, replicated=False,
    )
    plan = SimpleNamespace(steps=(sm_activation, pm_producer, *pm_activations, sm_linear, *pm_linears))
    ir = SimpleNamespace(init_lineages={1631: lineage})
    reduction = RelationFactSpec("reduction", (sm_linear.step_id, *(s.step_id for s in pm_linears)))
    return plan, ir, reduction, sm_activation, pm_producer, pm_activations, sm_linear, pm_linears


def test_matcher_derives_dynamic_k_exact_chunk_lineage_and_weight_init_authority():
    plan, ir, reduction, sm_activation, _producer, chunks, sm_linear, pm_linears = synthetic_reduction_linear()
    certificates, frontiers, layouts = relation_compiler.advance_k_rank_reduction_linear_producer_frontiers(
        plan, ir, (reduction.step_triple,), ("reduction",)
    )
    assert len(certificates) == 1
    cert = certificates[0]
    assert cert.rule_id == "linear-reduction-producer-k-rank"
    assert cert.rank_count == 4
    assert cert.activation_chunk_dim == 2
    assert cert.weight_gather_dim == 1
    assert cert.activation_full_shape == (1, 1024, 768)
    assert cert.activation_shard_shape == (1, 1024, 192)
    assert cert.weight_full_shape == (768, 768)
    assert cert.weight_shard_shape == (768, 192)
    assert cert.output_shape == (1, 1024, 768)
    assert cert.activation_fact == RelationFactSpec(
        "sharded", (sm_activation.step_id, *(s.step_id for s in chunks)), gather_dim=2,
    )
    assert cert.weight_fact == RelationFactSpec(
        "sharded", ("init:1631", "init:3485", "init:3486", "init:3487", "init:3488"), gather_dim=1,
    )
    assert cert.output_fact == reduction
    assert cert.sm_linear_step == sm_linear.step_id
    assert cert.pm_linear_steps == tuple(s.step_id for s in pm_linears)
    assert cert.lean_theorem.endswith("fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d")
    assert frontiers == (cert.activation_fact.step_triple, cert.weight_fact.step_triple)
    assert layouts == ("sharded", "sharded")


def test_fixed_point_registration_and_exact_transition_footprint():
    plan, ir, reduction, *_ = synthetic_reduction_linear()
    sink = []
    frontiers, layouts = relation_compiler.normalize_relation_frontiers(
        plan, (reduction.step_triple,), ("reduction",),
        rules=("reduction_linear_producer_k",), goal_ir=ir, certificate_sink=sink,
    )
    cert = sink[0]
    assert frontiers == (cert.activation_fact.step_triple, cert.weight_fact.step_triple)
    assert layouts == ("sharded", "sharded")
    transition = build_certificate_transition_specs(plan, sink)[0]
    assert transition.pre_facts == tuple(sorted((cert.activation_fact, cert.weight_fact)))
    assert transition.post_facts == (cert.output_fact,)
    assert transition.sm_node_indices == (23,)
    assert transition.pm_node_indices == (149, 150, 151, 152)


def test_matcher_fails_closed_on_chunk_orientation_and_weight_order():
    plan, ir, reduction, _sm, _producer, chunks, *_ = synthetic_reduction_linear()
    chunks[1].parameters = (1,)
    with pytest.raises(RelationCompositionError, match="chunk dimension"):
        relation_compiler.advance_k_rank_reduction_linear_producer_frontiers(
            plan, ir, (reduction.step_triple,), ("reduction",)
        )
    chunks[1].parameters = (2,)
    ir.init_lineages[1631].tps = ((1, 3486), (0, 3485), (2, 3487), (3, 3488))
    with pytest.raises(RelationCompositionError, match="ordered ranks"):
        relation_compiler.advance_k_rank_reduction_linear_producer_frontiers(
            plan, ir, (reduction.step_triple,), ("reduction",)
        )



def synthetic_closed_reduction_linear(*, rank_count=3, rank3=True):
    afull = (2, 4, rank_count * 2) if rank3 else (4, rank_count * 2)
    ashard = (*afull[:-1], 2)
    wfull, wshard = (5, rank_count * 2), (5, 2)
    output = (*afull[:-1], 5)
    activation_spec = RelationFactSpec(
        "sharded", ("sm:100:0", *(f"pm:{100 + rank}:0" for rank in range(rank_count))),
        gather_dim=len(afull) - 1,
    )
    weight_spec = RelationFactSpec(
        "sharded", ("init:200", *(f"init:{300 + rank}" for rank in range(rank_count))),
        gather_dim=1,
    )
    output_spec = RelationFactSpec(
        "reduction", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(rank_count))),
    )
    activation = ClosedRelationFactRecord(
        "fact_activation", activation_spec, "sharded", 10,
        tuple(20 + rank for rank in range(rank_count)), None, None,
        afull, ashard, gather_dim=len(afull) - 1,
    )
    weight = ClosedRelationFactRecord(
        "fact_weight", weight_spec, "sharded", 11,
        tuple(30 + rank for rank in range(rank_count)), None, None,
        wfull, wshard, gather_dim=1,
    )
    output_fact = ClosedRelationFactRecord(
        "fact_output", output_spec, "reduction", 12,
        tuple(40 + rank for rank in range(rank_count)), None, None,
        output, output,
    )
    theorem = "TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk"
    if rank3:
        theorem += "_3d"
    certificate = KRankReductionLinearProducerCertificate(
        rule_id="linear-reduction-producer-k-rank",
        rank_count=rank_count,
        activation_chunk_dim=len(afull) - 1,
        weight_gather_dim=1,
        activation_full_shape=afull,
        activation_shard_shape=ashard,
        weight_full_shape=wfull,
        weight_shard_shape=wshard,
        output_shape=output,
        activation_fact=activation_spec,
        weight_fact=weight_spec,
        output_fact=output_spec,
        sm_linear_step="sm:0:0",
        pm_linear_steps=tuple(f"pm:{rank}:0" for rank in range(rank_count)),
        lean_theorem=theorem,
    )
    transition = CertificateTransitionSpec(
        "transition", certificate.rule_id,
        tuple(sorted((activation_spec, weight_spec))), (output_spec,),
        (0,), tuple(range(rank_count)), theorem,
        certificate_digest=composer._typed_certificate_digest(certificate),
    )
    anchor = ClosedTensorShapeFactRecord(
        fact_id="anchor", side="sm", tid=999, shape=(1,), init_goal_id=999,
    )
    states = (
        ClosedRelationStateRecord("state_pre", ("anchor", "fact_activation", "fact_weight")),
        ClosedRelationStateRecord("state_post", ("anchor", "fact_output")),
    )
    segment = ClosedDependentSegmentRecord(
        "segment_000000", "component", "state_pre", "state_post", ("transition",),
        (0, 1), (0, rank_count),
    )
    chain = SimpleNamespace(
        complete=True,
        relation_facts=(activation, weight, output_fact),
        authority_facts=(),
        anchor_fact=anchor,
        states=states,
        segments=(segment,),
    )
    relation = SimpleNamespace(
        dependent_chain_plan=chain,
        transition_specs=(transition,),
        certificates=(certificate,),
    )
    sm_nodes = [Node(0, "FW_linear", [10, 11], [12], [])]
    pm_nodes = [
        Node(rank, "FW_linear", [20 + rank, 30 + rank], [40 + rank], [])
        for rank in range(rank_count)
    ]
    ir = SimpleNamespace(
        sm_nodes=sm_nodes,
        pm_nodes=pm_nodes,
        sm_num_ranks=1,
        pm_num_ranks=rank_count,
        sm_graph_ref="SyntheticReductionLinear.smGraph",
        pm_graph_ref="SyntheticReductionLinear.pmGraph",
    )
    return ir, relation


def test_closed_renderer_owns_exact_linear_writers_and_is_dynamic():
    ir, relation = synthetic_closed_reduction_linear(rank_count=3, rank3=True)
    source = render_closed_segment(ir, relation, "segment_000000")
    assert "fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d" in source
    assert "let rankCount0 := pmActivationTids0.length" in source
    assert "pmActivationTids0 : List Tid := [20, 21, 22]" in source
    assert "pmWeightTids0 : List Tid := [30, 31, 32]" in source
    assert source.count('op := "OpName.FW_linear"') >= 8
    assert "rankCount = 3" not in source
    assert "ChunkPrim" not in source
    assert "AllReducePrim" not in source
    assert "set_option maxHeartbeats 500000 in" in source


def test_closed_renderer_selects_rank2_sibling():
    ir, relation = synthetic_closed_reduction_linear(rank_count=2, rank3=False)
    source = render_closed_segment(ir, relation, "segment_000000")
    assert "fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d" not in source
    assert "TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk" in source


def test_fresh_reduction_linear_witness_is_exact_renderer_output(tmp_path):
    ir, relation = synthetic_closed_reduction_linear(rank_count=3, rank3=True)
    namespace = "SyntheticReductionLinear"
    declarations = render_closed_relation_declarations(
        relation.dependent_chain_plan, namespace
    )
    rendered = render_closed_segment(ir, relation, "segment_000000")
    sm_nodes = "[" + ", ".join(composer._node_text(node) for node in ir.sm_nodes) + "]"
    pm_nodes = "[" + ", ".join(composer._node_text(node) for node in ir.pm_nodes) + "]"
    source = "\n".join((
        declarations,
        f"namespace TrainVerify.Denote.{namespace}",
        "noncomputable section",
        f"private def smGraph : GraphDecl := {{ numRanks := 1, nodes := {sm_nodes} }}",
        f"private def pmGraph : GraphDecl := {{ numRanks := 3, nodes := {pm_nodes} }}",
        rendered,
        "#print axioms segment_000000",
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ))
    configured = os.environ.get("REDUCTION_LINEAR_WITNESS_PATH")
    witness = Path(configured) if configured else tmp_path / "GeneratedReductionLinearWitness.lean"
    witness.write_text(source)
    assert witness.read_text() == source
    assert rendered == render_closed_segment(ir, relation, "segment_000000")
    assert "sorry" not in source
