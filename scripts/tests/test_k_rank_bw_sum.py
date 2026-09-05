from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import LineageGoal, Node
from trainverify.bridge_emitter.bw_sum_renderer import render_closed_k_rank_bw_sum_segment
from trainverify.bridge_emitter.compound_rule_dispatch import select_bw_compound_renderer
from trainverify.bridge_emitter.sum_bw_sum_atomic_renderer import render_closed_sum_bw_sum_atomic_segment
from trainverify.bridge_emitter.relation_compiler import (
    CertificateTransitionSpec,
    ClosedDependentSegmentRecord,
    ClosedRelationFactRecord,
    ClosedRelationStateRecord,
    KRankBWSumCertificate,
    KRankSumProducerCertificate,
    RelationCompositionError,
    RelationFactSpec,
    advance_k_rank_bw_sum_frontiers,
)


def _fixture(k: int):
    shard = (1, 8, 32)
    full = (1, 8, 32 * k)
    gradient = "init:900"
    sm = SimpleNamespace(
        step_id="sm:0:0", op="BW_sum", side="sm", rank=0,
        input_bindings=(gradient, "sm:10:0"), input_shapes=((1,), full),
        output_shape=full, parameters=(),
    )
    pms = tuple(
        SimpleNamespace(
            step_id=f"pm:{rank}:0", op="BW_sum", side="pm", rank=rank,
            input_bindings=(gradient, f"pm:{10 + rank}:0"),
            input_shapes=((1,), shard), output_shape=shard, parameters=(),
        )
        for rank in range(k)
    )
    plan = SimpleNamespace(steps=(sm, *pms))
    ir = SimpleNamespace(init_lineages={
        900: LineageGoal(900, [1], [(0, 900)], [[1]], replicated=False)
    })
    frontier = (sm.step_id, *(step.step_id for step in pms))
    return plan, ir, frontier, full, shard


@pytest.mark.parametrize("k", (2, 3, 4))
def test_bw_sum_matcher_derives_dynamic_rank_count_and_dim2_shapes(k):
    plan, ir, frontier, full, shard = _fixture(k)
    certs, rewritten, layouts = advance_k_rank_bw_sum_frontiers(
        plan, ir, (frontier,), ("sharded",)
    )

    assert len(certs) == 1
    cert = certs[0]
    assert cert.rule_id == "bw-sum-scalar-broadcast-dim2-k-rank"
    assert cert.rank_count == k
    assert cert.gather_dim == 2
    assert cert.lean_theorem == "TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim2_rank3"
    assert cert.activation_fact == RelationFactSpec(
        "sharded",
        ("sm:10:0", *(f"pm:{10 + rank}:0" for rank in range(k))),
        gather_dim=2,
    )
    assert cert.output_fact == RelationFactSpec("sharded", frontier, gather_dim=2)
    assert rewritten == (
        ("init:900", "init:900"),
        cert.activation_fact.step_triple,
    )
    assert layouts == ("reduction", "sharded")


@pytest.mark.parametrize("mutation", (
    "sm-rank", "rank4-output", "sm-input", "pm-input", "params", "zero-width",
))
def test_bw_sum_matcher_rejects_inputs_outside_exact_lean_domain(mutation):
    plan, ir, frontier, _full, _shard = _fixture(3)
    sm, *pms = plan.steps
    if mutation == "sm-rank":
        sm.rank = 1
    elif mutation == "rank4-output":
        sm.output_shape = (1, 8, 96, 1)
        sm.input_shapes = ((1,), sm.output_shape)
        for pm in pms:
            pm.output_shape = (1, 8, 32, 1)
            pm.input_shapes = ((1,), pm.output_shape)
    elif mutation == "sm-input":
        sm.input_shapes = ((1,), (1, 8, 95))
    elif mutation == "pm-input":
        pms[1].input_shapes = ((1,), (1, 8, 31))
    elif mutation == "params":
        pms[0].parameters = (1,)
    else:
        sm.output_shape = (1, 8, 0)
        sm.input_shapes = ((1,), sm.output_shape)
        for pm in pms:
            pm.output_shape = (1, 8, 0)
            pm.input_shapes = ((1,), pm.output_shape)

    with pytest.raises(RelationCompositionError):
        advance_k_rank_bw_sum_frontiers(plan, ir, (frontier,), ("sharded",))


def test_bw_sum_matcher_rejects_non_reduction_gradient_authority():
    plan, ir, frontier, _full, _shard = _fixture(3)
    ir.init_lineages[900] = LineageGoal(
        900, [1], [(0, 900)], [[1]], replicated=True
    )

    with pytest.raises(RelationCompositionError, match="scalar InitGoal"):
        advance_k_rank_bw_sum_frontiers(plan, ir, (frontier,), ("sharded",))


def test_bw_sum_registry_and_renderer_have_no_rank4_backend_identity():
    rule = "bw-sum-scalar-broadcast-dim2-k-rank"
    spec = rc.CLOSED_RULE_REGISTRY[rule]
    assert spec.certificate_type is rc.KRankBWSumCertificate
    assert spec.lean_theorems == (
        "TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim2_rank3",
    )
    assert spec.lean_imports == ("denote.KRankBWSum",)

    root = Path(__file__).resolve().parents[2]
    source = (root / "trainverify/bridge_emitter/bw_sum_renderer.py").read_text()
    for forbidden in (
        "dim2-rank4",
        "k != 4",
        "allGatherPrimDimN 2 4",
        "split_dim2_4_1_8_32",
        "(1, 8, 128)",
        "(1, 8, 32)",
    ):
        assert forbidden not in source
    lean_source = (root / "trainverify/denote/KRankBWSum.lean").read_text()
    assert "theorem bw_sum_allGatherPrimDimN_dim2_rank3" in lean_source


def _renderer_fixture(k: int):
    gradient = RelationFactSpec("reduction", ("init:900", "init:900"))
    activation = RelationFactSpec(
        "sharded", ("sm:0:1", *(f"pm:{rank}:1" for rank in range(k))), gather_dim=2
    )
    output = RelationFactSpec(
        "sharded", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(k))), gather_dim=2
    )
    full, shard = (1, 8, 32 * k), (1, 8, 32)
    records = (
        ClosedRelationFactRecord("fact_g", gradient, "reduction", 900, (900,), None, None, (1,), (1,)),
        ClosedRelationFactRecord("fact_x", activation, "sharded", 100, tuple(1000 + r for r in range(k)), None, None, full, shard, gather_dim=2),
        ClosedRelationFactRecord("fact_out", output, "sharded", 200, tuple(2000 + r for r in range(k)), None, None, full, shard, gather_dim=2),
    )
    states = (
        ClosedRelationStateRecord("state_before", ("fact_g", "fact_x")),
        ClosedRelationStateRecord("state_after", ("fact_g", "fact_x", "fact_out")),
    )
    segment = ClosedDependentSegmentRecord(
        "segment_000000", "component_000000", "state_before", "state_after",
        ("transition_000000",), (0, 1), (0, k),
    )
    theorem = "TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim2_rank3"
    transition = CertificateTransitionSpec(
        "transition_000000", "bw-sum-scalar-broadcast-dim2-k-rank",
        (gradient, activation), (output,), (0,), tuple(range(k)), theorem,
    )
    certificate = KRankBWSumCertificate(
        "bw-sum-scalar-broadcast-dim2-k-rank", k, 2, gradient, activation,
        output, "sm:0:0", tuple(f"pm:{rank}:0" for rank in range(k)), theorem,
    )
    chain = SimpleNamespace(relation_facts=records, states=states, segments=(segment,))
    relation = SimpleNamespace(
        dependent_chain_plan=chain, transition_specs=(transition,), certificates=(certificate,)
    )
    ir = SimpleNamespace(
        sm_nodes=[Node(0, "BW_sum", [900, 100], [200], [])],
        pm_nodes=[Node(rank, "BW_sum", [900, 1000 + rank], [2000 + rank], []) for rank in range(k)],
        sm_graph_ref="SyntheticBWSum.smGraph", pm_graph_ref="SyntheticBWSum.pmGraph",
    )
    return ir, relation


@pytest.mark.parametrize("k", (2, 3))
def test_bw_sum_renderer_emits_exact_dynamic_writer_frame(k):
    ir, relation = _renderer_fixture(k)
    source = render_closed_k_rank_bw_sum_segment(ir, relation, "segment_000000")

    activation = "[" + ", ".join(f"pmFinal {1000 + rank}" for rank in range(k)) + "]"
    assert f"allGatherPrimDimN 2 {k} 0 {activation}" in source
    assert source.count("private theorem segment_000000_hPmWriter") == k
    assert f"hPmWriter{k - 1}" in source
    assert f"hPmWriter{k}" not in source
    assert "bw_sum_allGatherPrimDimN_dim2_rank3" in source
    assert "simpa only [List.length_cons, List.length_nil, List.map] using" in source


def test_sum_bw_sum_compound_dispatch_uses_dynamic_bw_sum_identity():
    family = (
        "sum-producer-sharded-k-rank-dim1",
        "bw-sum-scalar-broadcast-dim2-k-rank",
    )
    assert select_bw_compound_renderer(family) == (
        "sum_bw_sum_atomic_renderer:render_closed_sum_bw_sum_atomic_segment"
    )
    root = Path(__file__).resolve().parents[2]
    source = (root / "trainverify/bridge_emitter/sum_bw_sum_atomic_renderer.py").read_text()
    assert "bw-sum-scalar-broadcast-dim2-rank4" not in source
    assert "bw_sum_allGatherPrimDimN_split_dim2_4_1_8_32" not in source
    assert "k != 4" not in source


def _compound_renderer_fixture(k: int):
    gradient = RelationFactSpec("reduction", ("init:900", "init:900"))
    activation = RelationFactSpec(
        "sharded", ("sm:0:1", *(f"pm:{rank}:1" for rank in range(k))), gather_dim=2
    )
    sum_output = RelationFactSpec(
        "reduction", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(k)))
    )
    bw_output = RelationFactSpec(
        "sharded", ("sm:1:0", *(f"pm:{k + rank}:0" for rank in range(k))), gather_dim=2
    )
    full, shard = (1, 8, 32 * k), (1, 8, 32)
    records = (
        ClosedRelationFactRecord("fact_g", gradient, "reduction", 900, (900,), None, None, (1,), (1,)),
        ClosedRelationFactRecord("fact_x", activation, "sharded", 100, tuple(1000 + r for r in range(k)), None, None, full, shard, gather_dim=2),
        ClosedRelationFactRecord("fact_sum", sum_output, "reduction", 300, tuple(3000 + r for r in range(k)), None, None, (1,), (1,)),
        ClosedRelationFactRecord("fact_bw", bw_output, "sharded", 200, tuple(2000 + r for r in range(k)), None, None, full, shard, gather_dim=2),
    )
    states = (
        ClosedRelationStateRecord("state_before", ("fact_g", "fact_x")),
        ClosedRelationStateRecord("state_after", ("fact_g", "fact_x", "fact_sum", "fact_bw")),
    )
    segment = ClosedDependentSegmentRecord(
        "segment_000000", "component_000000", "state_before", "state_after",
        ("transition_sum", "transition_bw"), (0, 2), (0, 2 * k),
    )
    sum_theorem = "TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum"
    bw_theorem = "TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim2_rank3"
    transitions = (
        CertificateTransitionSpec(
            "transition_sum", "sum-producer-sharded-k-rank-dim1", (activation,),
            (sum_output,), (0,), tuple(range(k)), sum_theorem,
        ),
        CertificateTransitionSpec(
            "transition_bw", "bw-sum-scalar-broadcast-dim2-k-rank",
            (gradient, activation), (bw_output,), (1,), tuple(range(k, 2 * k)), bw_theorem,
        ),
    )
    certificates = (
        KRankSumProducerCertificate(
            "sum-producer-sharded-k-rank-dim1", k, 2, full, shard, activation,
            sum_output, "sm:0:0", tuple(f"pm:{rank}:0" for rank in range(k)), sum_theorem,
        ),
        KRankBWSumCertificate(
            "bw-sum-scalar-broadcast-dim2-k-rank", k, 2, gradient, activation,
            bw_output, "sm:1:0", tuple(f"pm:{k + rank}:0" for rank in range(k)), bw_theorem,
        ),
    )
    chain = SimpleNamespace(relation_facts=records, states=states, segments=(segment,))
    relation = SimpleNamespace(
        dependent_chain_plan=chain, transition_specs=transitions, certificates=certificates,
    )
    sum_pm = [Node(rank, "FW_sum", [1000 + rank], [3000 + rank], []) for rank in range(k)]
    bw_pm = [Node(rank, "BW_sum", [900, 1000 + rank], [2000 + rank], []) for rank in range(k)]
    ir = SimpleNamespace(
        sm_nodes=[Node(0, "FW_sum", [100], [300], []), Node(0, "BW_sum", [900, 100], [200], [])],
        pm_nodes=[*sum_pm, *bw_pm], sm_graph_ref="SyntheticBWSum.smGraph",
        pm_graph_ref="SyntheticBWSum.pmGraph",
    )
    return ir, relation


@pytest.mark.parametrize("k", (2, 3))
def test_sum_bw_sum_compound_renderer_emits_dynamic_k(k):
    ir, relation = _compound_renderer_fixture(k)
    source = render_closed_sum_bw_sum_atomic_segment(ir, relation, "segment_000000")

    assert f"allGatherPrimDimN 2 {k}" in source
    assert f"fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum 2 {k}" in source
    assert "bw_sum_allGatherPrimDimN_dim2_rank3" in source
    assert "simpa only [List.length_cons, List.length_nil, List.map] using" in source
