from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import LineageGoal, Node
from trainverify.bridge_emitter.bw_sum_renderer import render_closed_k_rank_bw_sum_segment
from trainverify.bridge_emitter.bw_linear_dx_renderer import render_closed_k_rank_bw_linear_dx_segment
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.compound_rule_dispatch import select_bw_compound_renderer
from trainverify.bridge_emitter.sum_bw_sum_atomic_renderer import render_closed_sum_bw_sum_atomic_segment
from trainverify.bridge_emitter.relation_compiler import (
    CertificateTransitionSpec,
    ClosedDependentSegmentRecord,
    ClosedRelationFactRecord,
    ClosedRelationStateRecord,
    KRankBWSumCertificate,
    KRankBWLinearDxCertificate,
    KRankSumProducerCertificate,
    RelationCompositionError,
    RelationFactSpec,
    advance_k_rank_bw_linear_dx_frontiers,
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


def _bw_linear_dx_matcher_fixture(k: int):
    shard_width = 32
    full_gradient = (1, 8, shard_width * k)
    shard_gradient = (1, 8, shard_width)
    activation = (1, 8, 32)
    full_weight = (shard_width * k, 32)
    shard_weight = (shard_width, 32)
    output = activation
    sm = SimpleNamespace(
        step_id="sm:0:0", op="BW_linear", side="sm", rank=0,
        output_projection=".1",
        input_bindings=("sm:g:0", "sm:x:0", "init:700"),
        input_shapes=(full_gradient, activation, full_weight),
        output_shape=output, parameters=(),
    )
    pms = tuple(
        SimpleNamespace(
            step_id=f"pm:{rank}:0", op="BW_linear", side="pm", rank=rank,
            output_projection=".1",
            input_bindings=(f"pm:g:{rank}", "pm:x:shared", f"init:{701 + rank}"),
            input_shapes=(shard_gradient, activation, shard_weight),
            output_shape=output, parameters=(),
        )
        for rank in range(k)
    )
    plan = SimpleNamespace(steps=(sm, *pms))
    ir = SimpleNamespace(init_lineages={
        700: LineageGoal(
            700, list(full_weight),
            [(rank, 701 + rank) for rank in range(k)],
            [list(shard_weight) for _ in range(k)],
            gatherDim=0,
        )
    })
    frontier = (sm.step_id, *(step.step_id for step in pms))
    return plan, ir, frontier


@pytest.mark.parametrize("k", (3, 4))
def test_bw_linear_dx_row_reduction_matcher_derives_dynamic_rank_count(k):
    plan, ir, frontier = _bw_linear_dx_matcher_fixture(k)
    certs, _rewritten, _layouts = advance_k_rank_bw_linear_dx_frontiers(
        plan, ir, (frontier,), ("reduction",)
    )

    assert len(certs) == 1
    cert = certs[0]
    assert cert.rule_id == "bw-linear-dx-row-reduction-k-rank"
    assert cert.family == "row-reduction"
    assert cert.rank_count == k
    assert cert.lean_theorem == (
        "TrainVerify.Denote.bw_linear_dx_allGatherPrimDimN_dim2_rank3"
    )


def _bw_linear_dx_renderer_fixture(k: int):
    theorem = "TrainVerify.Denote.bw_linear_dx_allGatherPrimDimN_dim2_rank3"
    rule = "bw-linear-dx-row-reduction-k-rank"
    gradient = RelationFactSpec(
        "sharded", ("sm:g", *(f"pm:g:{rank}" for rank in range(k))), gather_dim=2
    )
    activation = RelationFactSpec("joined", ("sm:x",), joined_pm_step="pm:x")
    weight = RelationFactSpec(
        "sharded", ("init:300", *(f"init:{301 + rank}" for rank in range(k))),
        gather_dim=0,
    )
    output = RelationFactSpec(
        "reduction", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(k)))
    )
    full_gradient, shard_gradient = (1, 8, 32 * k), (1, 8, 32)
    full_weight, shard_weight = (32 * k, 32), (32, 32)
    records = (
        ClosedRelationFactRecord("fact_g", gradient, "sharded", 100,
            tuple(1000 + rank for rank in range(k)), None, None,
            full_gradient, shard_gradient, gather_dim=2),
        ClosedRelationFactRecord("fact_x", activation, "joined", 200, (), None, None,
            (1, 8, 32), (1, 8, 32), joined_pm_tid=2000),
        ClosedRelationFactRecord("fact_w", weight, "sharded", 300,
            tuple(3000 + rank for rank in range(k)), None, None,
            full_weight, shard_weight, gather_dim=0),
        ClosedRelationFactRecord("fact_out", output, "reduction", 400,
            tuple(4000 + rank for rank in range(k)), None, None,
            (1, 8, 32), (1, 8, 32)),
    )
    states = (
        ClosedRelationStateRecord("state_before", ("fact_g", "fact_x", "fact_w")),
        ClosedRelationStateRecord(
            "state_after", ("fact_g", "fact_x", "fact_w", "fact_out")
        ),
    )
    segment = ClosedDependentSegmentRecord(
        "segment_000000", "component_000000", "state_before", "state_after",
        ("transition_000000",), (0, 1), (0, k),
    )
    certificate = KRankBWLinearDxCertificate(
        rule, "row-reduction", k, "reduction", None,
        (gradient, activation, weight), output,
        "sm:0:0", tuple(f"pm:{rank}:0" for rank in range(k)), theorem,
    )
    transition = replace(
        CertificateTransitionSpec(
            "transition_000000", rule, tuple(sorted((gradient, activation, weight))), (output,),
            (0,), tuple(range(k)), theorem,
        ),
        certificate_digest=_typed_certificate_digest(certificate),
    )
    chain = SimpleNamespace(relation_facts=records, states=states, segments=(segment,))
    relation = SimpleNamespace(
        dependent_chain_plan=chain, transition_specs=(transition,),
        certificates=(certificate,),
    )
    ir = SimpleNamespace(
        sm_nodes=[Node(0, "BW_linear", [100, 200, 300], [400, 401], [])],
        pm_nodes=[
            Node(rank, "BW_linear", [1000 + rank, 2000, 3000 + rank],
                 [4000 + rank, 5000 + rank], [])
            for rank in range(k)
        ],
        sm_graph_ref="SyntheticBWLinearDx.smGraph",
        pm_graph_ref="SyntheticBWLinearDx.pmGraph",
    )
    return ir, relation


def _bw_linear_dx_witness_source(rendered: str) -> str:
    return f'''import denote.RelationCompiler
import denote.KRankBWLinearDx

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace SyntheticBWLinearDx

noncomputable section

def smGraph : GraphDecl := {{ numRanks := 1, nodes := [
  {{ rank := 0, op := "OpName.BW_linear", ins := [100, 200, 300], outs := [400, 401] }}
] }}
def pmGraph : GraphDecl := {{ numRanks := 3, nodes := [
  {{ rank := 0, op := "OpName.BW_linear", ins := [1000, 2000, 3000], outs := [4000, 5000] }},
  {{ rank := 1, op := "OpName.BW_linear", ins := [1001, 2000, 3001], outs := [4001, 5001] }},
  {{ rank := 2, op := "OpName.BW_linear", ins := [1002, 2000, 3002], outs := [4002, 5002] }}
] }}

def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002] 2 [1, 8, 96] [1, 8, 32]
def fact_x : RelationFact := .joined 200 2000 [1, 8, 32]
def fact_w : RelationFact := .sharded 300 [3000, 3001, 3002] 0 [96, 32] [32, 32]
def fact_out : RelationFact := .reduction 400 [4000, 4001, 4002] [1, 8, 32]
def state_before : RelationState where
  facts := [fact_g, fact_x, fact_w]
  nonempty := by decide
def state_after : RelationState where
  facts := [fact_g, fact_x, fact_w, fact_out]
  nonempty := by decide

{rendered}

#print axioms segment_000000

end
end SyntheticBWLinearDx
'''


def test_bw_linear_dx_row_reduction_renderer_emits_exact_k3_writer_frame():
    ir, relation = _bw_linear_dx_renderer_fixture(3)
    source = render_closed_k_rank_bw_linear_dx_segment(
        ir, relation, "segment_000000"
    )

    assert source.count("private theorem segment_000000_hPmWriter") == 3
    assert "segment_000000_hPmWriter2" in source
    assert "segment_000000_hPmWriter3" not in source
    assert "allGatherPrimDimN 2 3 0" in source
    assert "allGatherPrimDimN 0 3 0" in source
    assert "allReducePrim 3 0" in source
    assert "bw_linear_dx_allGatherPrimDimN_dim2_rank3" in source
    assert "bw_linear_dx_tp_split_dim2_4_g175" not in source
    witness = (
        Path(__file__).resolve().parents[2]
        / "trainverify/denote/GeneratedKRankBWLinearDxWitness.lean"
    )
    assert witness.read_text(encoding="utf-8") == _bw_linear_dx_witness_source(source)


def test_bw_linear_dx_dynamic_renderer_rejects_shape_outside_theorem_contract():
    ir, relation = _bw_linear_dx_renderer_fixture(3)
    records = list(relation.dependent_chain_plan.relation_facts)
    records[0] = replace(
        records[0], full_shape=(2, 4, 96), shard_shape=(2, 4, 32)
    )
    records[1] = replace(
        records[1], full_shape=(2, 4, 32), shard_shape=(2, 4, 32)
    )
    records[3] = replace(
        records[3], full_shape=(2, 4, 32), shard_shape=(2, 4, 32)
    )
    relation.dependent_chain_plan.relation_facts = tuple(records)

    with pytest.raises(ValueError, match="theorem shape contract"):
        render_closed_k_rank_bw_linear_dx_segment(ir, relation, "segment_000000")


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
