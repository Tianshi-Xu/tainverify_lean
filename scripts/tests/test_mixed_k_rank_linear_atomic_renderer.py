from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node


LOCAL_RULE = "linear-sharded-k-rank-dim1"
GATHER_RULE = "allgather-reconstruction-k-rank"
OUTPUT_RULE = "linear-output-sharded-k-rank"
LOCAL_THM = "TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm"
GATHER_THM = "TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather"
OUTPUT_THM = "TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm"


def _fixture(k=3):
    def sharded(source, sm_tid, pm_tids, full, shard, dim, fact_id):
        return rc.ClosedRelationFactRecord(
            fact_id, source, "sharded", sm_tid, tuple(pm_tids), None, None,
            full, shard, dim,
        )

    input_a_spec = rc.RelationFactSpec("sharded", ("init:100", *(f"init:{200+r}" for r in range(k))), gather_dim=1)
    input_b_spec = rc.RelationFactSpec("sharded", ("init:110", *(f"init:{210+r}" for r in range(k))), gather_dim=1)
    gather_in_spec = rc.RelationFactSpec("sharded", ("init:120", *(f"init:{220+r}" for r in range(k))), gather_dim=1)
    out_a_spec = rc.RelationFactSpec("sharded", ("sm:0:0", *(f"pm:{2*r}:0" for r in range(k))), gather_dim=1)
    out_b_pm = tuple(2*r+1 if r < k-1 else 2*r+2 for r in range(k))
    out_b_spec = rc.RelationFactSpec("sharded", ("sm:2:0", *(f"pm:{p}:0" for p in out_b_pm)), gather_dim=1)
    gather_pos = 2*k-1
    joined_spec = rc.RelationFactSpec("joined", ("init:120",), joined_pm_step=f"pm:{gather_pos}:0")
    output_start = 2*k+1
    final_spec = rc.RelationFactSpec("sharded", ("sm:1:0", *(f"pm:{output_start+r}:0" for r in range(k))), gather_dim=2)
    weight_spec = rc.RelationFactSpec("sharded", ("init:132", *(f"init:{232+r}" for r in range(k))), gather_dim=0)

    local_a = rc.KRankLocalRelationCertificate(
        LOCAL_RULE, "FW_linear", k, 1, input_a_spec, out_a_spec, "sm:0:0",
        tuple(f"pm:{2*r}:0" for r in range(k)), (130,), ((5, 5),), LOCAL_THM,
    )
    local_b = rc.KRankLocalRelationCertificate(
        LOCAL_RULE, "FW_linear", k, 1, input_b_spec, out_b_spec, "sm:2:0",
        tuple(f"pm:{p}:0" for p in out_b_pm), (131,), ((5, 5),), LOCAL_THM,
    )
    gather = rc.KRankAllGatherReconstructionCertificate(
        GATHER_RULE, k, 1, (2, 3*k, 5), (2, 3, 5), gather_in_spec,
        joined_spec, f"pm:{gather_pos}:0", GATHER_THM,
    )
    output = rc.KRankOutputShardedLinearCertificate(
        OUTPUT_RULE, k, 2, joined_spec, weight_spec, final_spec, "sm:1:0",
        tuple(f"pm:{output_start+r}:0" for r in range(k)),
        (2, 3*k, 5), (4*k, 5), (4, 5), (2, 3*k, 4*k), (2, 3*k, 4), OUTPUT_THM,
    )
    certs = (local_a, local_b, gather, output)
    transitions = rc.build_certificate_transition_specs(SimpleNamespace(), certs)

    input_a = sharded(input_a_spec, 100, range(200, 200+k), (2, 3*k, 5), (2, 3, 5), 1, "fact_input_a")
    input_b = sharded(input_b_spec, 110, range(210, 210+k), (2, 3*k, 5), (2, 3, 5), 1, "fact_input_b")
    gather_in = sharded(gather_in_spec, 120, range(220, 220+k), (2, 3*k, 5), (2, 3, 5), 1, "fact_gather_in")
    out_a = sharded(out_a_spec, 140, range(240, 240+k), (2, 3*k, 5), (2, 3, 5), 1, "fact_out_a")
    out_b = sharded(out_b_spec, 141, range(250, 250+k), (2, 3*k, 5), (2, 3, 5), 1, "fact_out_b")
    joined = rc.ClosedRelationFactRecord("fact_joined", joined_spec, "joined", 120, (), None, None, (2, 3*k, 5), (2, 3*k, 5), joined_pm_tid=260)
    weight = sharded(weight_spec, 132, range(232, 232+k), (4*k, 5), (4, 5), 0, "fact_weight")
    final = sharded(final_spec, 142, range(270, 270+k), (2, 3*k, 4*k), (2, 3*k, 4), 2, "fact_final")
    eq_a = rc.ClosedTensorEqFactRecord("eq_a", "sm", 130, "pm", 130)
    shape_a = rc.ClosedTensorShapeFactRecord("shape_a", "pm", 130, (5, 5), 130)
    eq_b = rc.ClosedTensorEqFactRecord("eq_b", "sm", 131, "pm", 131)
    shape_b = rc.ClosedTensorShapeFactRecord("shape_b", "pm", 131, (5, 5), 131)
    pre_ids = (input_a.fact_id, input_b.fact_id, gather_in.fact_id, weight.fact_id,
               eq_a.fact_id, shape_a.fact_id, eq_b.fact_id, shape_b.fact_id)
    post_ids = (out_a.fact_id, out_b.fact_id, final.fact_id)
    before = SimpleNamespace(state_id="state_pre", fact_ids=pre_ids)
    after = SimpleNamespace(state_id="state_post", fact_ids=post_ids)
    segment = SimpleNamespace(
        segment_id="segment_000059", transition_ids=tuple(t.transition_id for t in transitions),
        sm_range=(0, 3), pm_range=(0, 3*k+1),
        pre_state_id=before.state_id, post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, segments=(segment,), states=(before, after),
        relation_facts=(input_a, input_b, gather_in, weight, out_a, out_b, joined, final),
        authority_facts=(eq_a, shape_a, eq_b, shape_b),
    )
    sm_nodes = [
        Node(0, "FW_linear", [100, 130], [140], []),
        Node(0, "FW_linear", [120, 132], [142], []),
        Node(0, "FW_linear", [110, 131], [141], []),
    ]
    pm_nodes = []
    for rank in range(k):
        pm_nodes.append(Node(rank, "FW_linear", [200+rank, 130], [240+rank], []))
        if rank < k-1:
            pm_nodes.append(Node(rank, "FW_linear", [210+rank, 131], [250+rank], []))
    pm_nodes.append(Node(0, "AllGatherPrim", list(range(220, 220+k)), [260], [1]))
    pm_nodes.append(Node(k-1, "FW_linear", [210+k-1, 131], [250+k-1], []))
    pm_nodes.extend(Node(rank, "FW_linear", [260, 232+rank], [270+rank], []) for rank in range(k))
    ir = SimpleNamespace(
        sm_nodes=sm_nodes, pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="SyntheticMixedLinear.gSM", pm_graph_ref="SyntheticMixedLinear.gPM",
    )
    relation = SimpleNamespace(certificates=certs, transition_specs=transitions, dependent_chain_plan=chain)
    return ir, relation, segment


def test_mixed_linear_atomic_renderer_preserves_one_fold_per_axis_and_interleaving():
    ir, relation, segment = _fixture(3)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert source.count("foldl_faithful_middle_writer") == 13
    assert source.index("outs := [240]") < source.index("outs := [250]") < source.index("outs := [241]")
    assert source.index('op := "OpName.AllGatherPrim"') < source.index("outs := [252]") < source.index("outs := [270]")
    assert source.count("fw_linear_3d_allGatherPrimDimN_dim1_comm") == 2
    assert GATHER_THM in source and "fw_linear_3d_weight_allGatherPrimDimN_dim0_comm" in source
    assert "K := [pmStore 200, pmStore 201, pmStore 202].length" in source
    assert "rankCount = 3" not in source


@pytest.mark.parametrize("tamper", ("order", "role", "rank", "certificate", "footprint"))
def test_mixed_linear_atomic_renderer_rejects_tampering(tamper):
    ir, relation, segment = _fixture(3)
    if tamper == "order":
        ir.pm_nodes[0], ir.pm_nodes[1] = ir.pm_nodes[1], ir.pm_nodes[0]
    elif tamper == "role":
        ir.sm_nodes[0].ins = list(reversed(ir.sm_nodes[0].ins))
    elif tamper == "rank":
        ir.pm_nodes[2].rank = 2
    elif tamper == "certificate":
        relation.certificates = (replace(relation.certificates[0], external_tids=(999,)), *relation.certificates[1:])
    else:
        relation.transition_specs = (replace(relation.transition_specs[0], pm_node_indices=(0, 1, 2)), *relation.transition_specs[1:])
    with pytest.raises(ValueError):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def _witness(source):
    return f'''import denote.RelationCompiler
import denote.KRankLinearGather

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticMixedLinear
noncomputable section
set_option maxHeartbeats 1000000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [] }}
def fact_input_a : RelationFact := .sharded 100 [200,201,202] 1 [2,9,5] [2,3,5]
def fact_input_b : RelationFact := .sharded 110 [210,211,212] 1 [2,9,5] [2,3,5]
def fact_gather_in : RelationFact := .sharded 120 [220,221,222] 1 [2,9,5] [2,3,5]
def fact_weight : RelationFact := .sharded 132 [232,233,234] 0 [12,5] [4,5]
def eq_a : RelationFact := .tensorEq .sm 130 .pm 130
def shape_a : RelationFact := .tensorShape .pm 130 [5,5]
def eq_b : RelationFact := .tensorEq .sm 131 .pm 131
def shape_b : RelationFact := .tensorShape .pm 131 [5,5]
def fact_out_a : RelationFact := .sharded 140 [240,241,242] 1 [2,9,5] [2,3,5]
def fact_out_b : RelationFact := .sharded 141 [250,251,252] 1 [2,9,5] [2,3,5]
def fact_joined : RelationFact := .joined 120 260 [2,9,5]
def fact_final : RelationFact := .sharded 142 [270,271,272] 2 [2,9,12] [2,9,4]
def state_pre : RelationState where
  facts := [fact_input_a,fact_input_b,fact_gather_in,fact_weight,eq_a,shape_a,eq_b,shape_b]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out_a,fact_out_b,fact_joined,fact_final]
  nonempty := by decide
{source}
#print axioms segment_000059
end
end SyntheticMixedLinear
end TrainVerify.Denote
'''


def test_generated_mixed_linear_atomic_witness_is_exact_renderer_output():
    ir, relation, segment = _fixture(3)
    source = _witness(composer.render_closed_segment(ir, relation, segment.segment_id))
    path = Path(__file__).parents[2] / "trainverify/denote/GeneratedMixedKRankLinearAtomicWitness.lean"
    path.write_text(source, encoding="utf-8")
    assert path.read_text(encoding="utf-8") == source
    assert "sorry" not in source
