from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node

R_RULE = "linear-reduction-producer-k-rank"
R_THEOREM = "TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d"
G_RULE = "allgather-reconstruction-k-rank"
G_THEOREM = "TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather"


def _sharded(fid, source, sm_tid, pm_tids, full, shard, dim):
    return rc.ClosedRelationFactRecord(
        fid, source, "sharded", sm_tid, tuple(pm_tids), None, None,
        full, shard, dim,
    )


def _fixture(*, k=3, producer_count=2, reconstruct=True):
    assert k > 0 and producer_count > 0
    sm_nodes = []
    # Interleave producer rank blocks, with the optional collective between
    # rank zero and the remaining ranks. Transition tuple order is semantic;
    # these arrays retain graph authority order.
    pm_nodes = []
    positions = [[None] * k for _ in range(producer_count)]
    for producer in range(producer_count):
        positions[producer][0] = len(pm_nodes)
        pm_nodes.append(None)
    gather_position = None
    if reconstruct:
        gather_position = len(pm_nodes)
        pm_nodes.append(None)
    for rank in range(1, k):
        for producer in reversed(range(producer_count)):
            positions[producer][rank] = len(pm_nodes)
            pm_nodes.append(None)

    certs = []
    records = []
    pre_ids = []
    post_ids = []
    for producer in range(producer_count):
        activation_spec = rc.RelationFactSpec(
            "sharded",
            (f"init:{100 + producer}", *(f"init:{200 + producer * 10 + rank}" for rank in range(k))),
            gather_dim=2,
        )
        weight_spec = rc.RelationFactSpec(
            "sharded",
            (f"init:{300 + producer}", *(f"init:{400 + producer * 10 + rank}" for rank in range(k))),
            gather_dim=1,
        )
        output_spec = rc.RelationFactSpec(
            "reduction",
            (f"sm:{producer}:0", *(f"pm:{index}:0" for index in positions[producer])),
        )
        cert = rc.KRankReductionLinearProducerCertificate(
            R_RULE, k, 2, 1,
            (1, 6, 4 * k), (1, 6, 4), (9, 4 * k), (9, 4), (1, 6, 9),
            activation_spec, weight_spec, output_spec,
            f"sm:{producer}:0", tuple(f"pm:{index}:0" for index in positions[producer]),
            R_THEOREM,
        )
        certs.append(cert)
        activation = _sharded(
            f"activation_{producer}", activation_spec, 100 + producer,
            (200 + producer * 10 + rank for rank in range(k)),
            (1, 6, 4 * k), (1, 6, 4), 2,
        )
        weight = _sharded(
            f"weight_{producer}", weight_spec, 300 + producer,
            (400 + producer * 10 + rank for rank in range(k)),
            (9, 4 * k), (9, 4), 1,
        )
        output = rc.ClosedRelationFactRecord(
            f"output_{producer}", output_spec, "reduction", 500 + producer,
            tuple(600 + producer * 10 + rank for rank in range(k)), None, None,
            (1, 6, 9), (1, 6, 9),
        )
        records.extend((activation, weight, output))
        pre_ids.extend((activation.fact_id, weight.fact_id))
        post_ids.append(output.fact_id)
        sm_nodes.append(Node(0, "FW_linear", [activation.sm_tid, weight.sm_tid], [output.sm_tid], []))
        for rank, index in enumerate(positions[producer]):
            pm_nodes[index] = Node(
                rank, "FW_linear",
                [activation.pm_tids[rank], weight.pm_tids[rank]],
                [output.pm_tids[rank]], [],
            )

    if reconstruct:
        gather_pre_spec = rc.RelationFactSpec(
            "sharded", ("init:800", *(f"init:{810 + rank}" for rank in range(k))), gather_dim=1,
        )
        gather_post_spec = rc.RelationFactSpec("joined", ("init:800",), joined_pm_step=f"pm:{gather_position}:0")
        certs.append(rc.KRankAllGatherReconstructionCertificate(
            G_RULE, k, 1, (2, 5 * k), (2, 5), gather_pre_spec,
            gather_post_spec, f"pm:{gather_position}:0", G_THEOREM,
        ))
        gather_pre = _sharded(
            "gather_pre", gather_pre_spec, 800, (810 + rank for rank in range(k)),
            (2, 5 * k), (2, 5), 1,
        )
        gather_post = rc.ClosedRelationFactRecord(
            "gather_post", gather_post_spec, "joined", 800, (), None, None,
            (2, 5 * k), (2, 5 * k), joined_pm_tid=899,
        )
        records.extend((gather_pre, gather_post))
        pre_ids.append(gather_pre.fact_id)
        post_ids.append(gather_post.fact_id)
        pm_nodes[gather_position] = Node(0, "AllGatherPrim", list(gather_pre.pm_tids), [899], [1])

    transitions = rc.build_certificate_transition_specs(SimpleNamespace(), tuple(certs))
    before = SimpleNamespace(state_id="state_pre", fact_ids=tuple(pre_ids))
    after = SimpleNamespace(state_id="state_post", fact_ids=tuple(post_ids))
    segment = SimpleNamespace(
        segment_id="segment_atomic", transition_ids=tuple(item.transition_id for item in transitions),
        sm_range=(0, len(sm_nodes)), pm_range=(0, len(pm_nodes)),
        pre_state_id=before.state_id, post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, segments=(segment,), states=(before, after),
        relation_facts=tuple(records), authority_facts=(),
    )
    ir = SimpleNamespace(
        sm_nodes=sm_nodes, pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="SyntheticReductionTuple.gSM", pm_graph_ref="SyntheticReductionTuple.gPM",
    )
    relation = SimpleNamespace(
        certificates=tuple(certs), transition_specs=transitions, dependent_chain_plan=chain,
    )
    return ir, relation, segment


@pytest.mark.parametrize(
    ("k", "producer_count", "reconstruct"),
    ((2, 1, False), (3, 2, True), (4, 3, False)),
)
def test_generic_positive_reduction_tuple_optional_allgather_is_one_atomic_fold(k, producer_count, reconstruct):
    ir, relation, segment = _fixture(k=k, producer_count=producer_count, reconstruct=reconstruct)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert source.count(R_THEOREM) == producer_count
    assert source.count(G_THEOREM) == (1 if reconstruct else 0)
    assert source.count("foldl_faithful_middle_writer") == producer_count * (k + 1) + int(reconstruct)
    assert source.count("let rankCount") == producer_count + int(reconstruct)
    assert "singleton" not in source.lower()
    if reconstruct:
        assert source.index('op := "OpName.FW_linear"') < source.index('op := "OpName.AllGatherPrim"')
        assert source.index('op := "OpName.AllGatherPrim"') < source.rindex('op := "OpName.FW_linear"')


@pytest.mark.parametrize("tamper", ("family", "theorem", "role", "rank", "footprint", "state", "zero"))
def test_reduction_tuple_optional_allgather_rejects_tampered_authority(tamper):
    ir, relation, segment = _fixture()
    if tamper == "family":
        relation.transition_specs = (replace(relation.transition_specs[0], rule_id="other"), *relation.transition_specs[1:])
    elif tamper == "theorem":
        relation.transition_specs = (replace(relation.transition_specs[0], lean_theorem="wrong"), *relation.transition_specs[1:])
    elif tamper == "role":
        ir.pm_nodes[0].ins = list(reversed(ir.pm_nodes[0].ins))
    elif tamper == "rank":
        ir.pm_nodes[-1].rank = 0
    elif tamper == "footprint":
        relation.transition_specs = (replace(relation.transition_specs[0], pm_node_indices=(0, 1, 2)), *relation.transition_specs[1:])
    elif tamper == "state":
        relation.dependent_chain_plan.states = (
            relation.dependent_chain_plan.states[0],
            SimpleNamespace(state_id="state_post", fact_ids=relation.dependent_chain_plan.states[1].fact_ids + ("unknown",)),
        )
    else:
        relation.transition_specs = relation.transition_specs[-1:]
        relation.certificates = relation.certificates[-1:]
        segment.transition_ids = (relation.transition_specs[0].transition_id,)
    with pytest.raises(ValueError):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def test_reduction_tuple_exact_certificate_selector_ignores_unrelated_and_rejects_duplicate():
    ir, relation, segment = _fixture()
    baseline = composer.render_closed_segment(ir, relation, segment.segment_id)
    relation.certificates = (*relation.certificates, replace(
        relation.certificates[0],
        output_fact=rc.RelationFactSpec("reduction", ("sm:999:0",)),
    ))
    assert composer.render_closed_segment(ir, relation, segment.segment_id) == baseline
    relation.certificates = (*relation.certificates, relation.certificates[0])
    with pytest.raises(ValueError, match="exact"):
        composer.render_closed_segment(ir, relation, segment.segment_id)



def _witness_source(rendered):
    return f'''import denote.RelationCompiler
import denote.KRankLinearReduction

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticReductionTuple
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [] }}
def activation_0 : RelationFact := .sharded 100 [200,201,202] 2 [1,6,12] [1,6,4]
def weight_0 : RelationFact := .sharded 300 [400,401,402] 1 [9,12] [9,4]
def activation_1 : RelationFact := .sharded 101 [210,211,212] 2 [1,6,12] [1,6,4]
def weight_1 : RelationFact := .sharded 301 [410,411,412] 1 [9,12] [9,4]
def gather_pre : RelationFact := .sharded 800 [810,811,812] 1 [2,15] [2,5]
def output_0 : RelationFact := .reduction 500 [600,601,602] [1,6,9]
def output_1 : RelationFact := .reduction 501 [610,611,612] [1,6,9]
def gather_post : RelationFact := .joined 800 899 [2,15]
def state_pre : RelationState where
  facts := [activation_0,weight_0,activation_1,weight_1,gather_pre]
  nonempty := by decide
def state_post : RelationState where
  facts := [output_0,output_1,gather_post]
  nonempty := by decide

{rendered}
#print axioms segment_atomic
end
end SyntheticReductionTuple
end TrainVerify.Denote
'''


def test_generated_reduction_tuple_allgather_witness_is_exact_deterministic_renderer_output():
    ir, relation, segment = _fixture(k=3, producer_count=2, reconstruct=True)
    first = _witness_source(composer.render_closed_segment(ir, relation, segment.segment_id))
    second = _witness_source(composer.render_closed_segment(ir, relation, segment.segment_id))
    assert first == second
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedReductionLinearTupleAllGatherWitness.lean"
    assert witness.read_text(encoding="utf-8") == first
    assert "sorry" not in first
