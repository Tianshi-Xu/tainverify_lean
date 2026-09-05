from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node

REDUCTION_RULE = "linear-reduction-producer-k-rank"
OUTPUT_RULE = "linear-output-sharded-k-rank"
REDUCTION_THEOREM = "TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d"
OUTPUT_THEOREM = "TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm"


def _sharded(source, fact_id, sm_tid, pm_tids, full, shard, dim):
    return rc.ClosedRelationFactRecord(
        fact_id, source, "sharded", sm_tid, tuple(pm_tids), None, None,
        full, shard, dim,
    )


def _fixture(k=3, producer_count=2):
    assert k > 0 and producer_count > 0
    reduction_certs = []
    records = []
    pre_ids = []
    post_ids = []
    sm_nodes = []
    pm_nodes = []

    # Independent authority orders: all rank-0 producers, the output writers,
    # then the remaining producer writers interleaved by rank.
    producer_pm_positions = [[None] * k for _ in range(producer_count)]
    for producer in range(producer_count):
        producer_pm_positions[producer][0] = len(pm_nodes)
        pm_nodes.append(None)
    output_positions = []
    for rank in range(k):
        output_positions.append(len(pm_nodes))
        pm_nodes.append(None)
    for rank in range(1, k):
        for producer in range(producer_count):
            producer_pm_positions[producer][rank] = len(pm_nodes)
            pm_nodes.append(None)

    for producer in range(producer_count):
        activation_spec = rc.RelationFactSpec(
            "sharded",
            (f"init:{100 + producer}", *(f"init:{200 + 10 * producer + r}" for r in range(k))),
            gather_dim=2,
        )
        weight_spec = rc.RelationFactSpec(
            "sharded",
            (f"init:{300 + producer}", *(f"init:{400 + 10 * producer + r}" for r in range(k))),
            gather_dim=1,
        )
        output_spec = rc.RelationFactSpec(
            "reduction",
            (f"sm:{producer}:0", *(f"pm:{p}:0" for p in producer_pm_positions[producer])),
        )
        cert = rc.KRankReductionLinearProducerCertificate(
            REDUCTION_RULE, k, 2, 1,
            (1, 6, 4 * k), (1, 6, 4), (9, 4 * k), (9, 4), (1, 6, 9),
            activation_spec, weight_spec, output_spec, f"sm:{producer}:0",
            tuple(f"pm:{p}:0" for p in producer_pm_positions[producer]),
            REDUCTION_THEOREM,
        )
        reduction_certs.append(cert)
        activation = _sharded(
            activation_spec, f"fact_activation_{producer}", 100 + producer,
            range(200 + 10 * producer, 200 + 10 * producer + k),
            (1, 6, 4 * k), (1, 6, 4), 2,
        )
        weight = _sharded(
            weight_spec, f"fact_reduction_weight_{producer}", 300 + producer,
            range(400 + 10 * producer, 400 + 10 * producer + k),
            (9, 4 * k), (9, 4), 1,
        )
        output = rc.ClosedRelationFactRecord(
            f"fact_reduction_output_{producer}", output_spec, "reduction",
            500 + producer, tuple(600 + 10 * producer + r for r in range(k)),
            None, None, (1, 6, 9), (1, 6, 9),
        )
        records.extend((activation, weight, output))
        pre_ids.extend((activation.fact_id, weight.fact_id))
        post_ids.append(output.fact_id)
        sm_nodes.append(Node(0, "FW_linear", [activation.sm_tid, weight.sm_tid], [output.sm_tid], []))
        for rank, position in enumerate(producer_pm_positions[producer]):
            pm_nodes[position] = Node(
                rank, "FW_linear",
                [activation.pm_tids[rank], weight.pm_tids[rank]],
                [output.pm_tids[rank]], [],
            )

    joined_spec = rc.RelationFactSpec("joined", (f"init:{700}",), joined_pm_step="init:701")
    output_weight_spec = rc.RelationFactSpec(
        "sharded", ("init:702", *(f"init:{710 + r}" for r in range(k))), gather_dim=0,
    )
    final_spec = rc.RelationFactSpec(
        "sharded", (f"sm:{producer_count}:0", *(f"pm:{p}:0" for p in output_positions)), gather_dim=2,
    )
    output_cert = rc.KRankOutputShardedLinearCertificate(
        OUTPUT_RULE, k, 2, joined_spec, output_weight_spec, final_spec,
        f"sm:{producer_count}:0", tuple(f"pm:{p}:0" for p in output_positions),
        (1, 6, 4 * k), (15, 4 * k), (5, 4 * k), (1, 6, 15), (1, 6, 5), OUTPUT_THEOREM,
    )
    joined = rc.ClosedRelationFactRecord(
        "fact_joined", joined_spec, "joined", 700, (), None, None,
        (1, 6, 4 * k), (1, 6, 4 * k), joined_pm_tid=701,
    )
    output_weight = _sharded(
        output_weight_spec, "fact_output_weight", 702, range(710, 710 + k),
        (15, 4 * k), (5, 4 * k), 0,
    )
    final = _sharded(
        final_spec, "fact_final", 703, range(720, 720 + k),
        (1, 6, 15), (1, 6, 5), 2,
    )
    records.extend((joined, output_weight, final))
    pre_ids.extend((joined.fact_id, output_weight.fact_id))
    post_ids.append(final.fact_id)
    sm_nodes.append(Node(0, "FW_linear", [700, 702], [703], []))
    for rank, position in enumerate(output_positions):
        pm_nodes[position] = Node(rank, "FW_linear", [701, 710 + rank], [720 + rank], [])

    certs = (*reduction_certs, output_cert)
    transitions = rc.build_certificate_transition_specs(SimpleNamespace(), certs)
    before = SimpleNamespace(state_id="state_pre", fact_ids=tuple(pre_ids))
    after = SimpleNamespace(state_id="state_post", fact_ids=tuple(post_ids))
    segment = SimpleNamespace(
        segment_id="segment_atomic", transition_ids=tuple(t.transition_id for t in transitions),
        sm_range=(0, len(sm_nodes)), pm_range=(0, len(pm_nodes)),
        pre_state_id=before.state_id, post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, segments=(segment,), states=(before, after),
        relation_facts=tuple(records), authority_facts=(),
    )
    ir = SimpleNamespace(
        sm_nodes=sm_nodes, pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="SyntheticReductionOutput.gSM",
        pm_graph_ref="SyntheticReductionOutput.gPM",
    )
    relation = SimpleNamespace(
        certificates=certs, transition_specs=transitions,
        dependent_chain_plan=chain,
    )
    return ir, relation, segment


@pytest.mark.parametrize(("k", "producer_count"), ((2, 1), (3, 2)))
def test_atomic_reduction_output_renderer_is_dynamic_and_uses_one_fold_per_axis(k, producer_count):
    ir, relation, segment = _fixture(k, producer_count)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert source.count("foldl_faithful_middle_writer") == (producer_count + 1) * (k + 1)
    assert source.count(REDUCTION_THEOREM) == producer_count
    assert source.count(OUTPUT_THEOREM) == 1
    helper_lines = [
        line for line in source.splitlines()
        if "foldl_faithful_middle_writer" in line
        or "foldl_applyNodeDistributedFaithful_at_not_written" in line
    ]
    assert helper_lines
    assert all(" smNodes.take " not in line for line in helper_lines)
    assert all(" smNodes.drop " not in line for line in helper_lines)
    assert all(" pmNodes.take " not in line for line in helper_lines)
    assert all(" pmNodes.drop " not in line for line in helper_lines)
    assert "let rankCount0 := pmActivationTids0.length" in source
    assert f"rankCount = {k}" not in source
    assert source.index("outs := [600]") < source.index("outs := [720]")
    assert source.index("outs := [720]") < source.index("outs := [601]")


@pytest.mark.parametrize("tamper", ("family", "role", "rank", "footprint", "shape", "state"))
def test_atomic_reduction_output_renderer_rejects_malformed_or_tampered(tamper):
    ir, relation, segment = _fixture()
    if tamper == "family":
        relation.transition_specs = (*relation.transition_specs[:-1], replace(relation.transition_specs[-1], rule_id="other"))
    elif tamper == "role":
        ir.pm_nodes[0].ins = list(reversed(ir.pm_nodes[0].ins))
    elif tamper == "rank":
        ir.pm_nodes[3].rank = 0
    elif tamper == "footprint":
        relation.transition_specs = (replace(relation.transition_specs[0], pm_node_indices=(0, 1, 5)), *relation.transition_specs[1:])
    elif tamper == "shape":
        relation.certificates = (replace(relation.certificates[0], output_shape=(1, 6, 10)), *relation.certificates[1:])
    else:
        chain = relation.dependent_chain_plan
        bad_after = SimpleNamespace(
            state_id=chain.states[1].state_id,
            fact_ids=chain.states[1].fact_ids + ("unknown",),
        )
        chain.states = (chain.states[0], bad_after)
    with pytest.raises(ValueError):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def test_atomic_reduction_output_renderer_exact_selector_ignores_unrelated_and_rejects_duplicate():
    ir, relation, segment = _fixture()
    baseline = composer.render_closed_segment(ir, relation, segment.segment_id)
    unrelated = replace(relation.certificates[0], output_fact=rc.RelationFactSpec("reduction", ("sm:999:0",)))
    relation.certificates = (*relation.certificates, unrelated)
    assert composer.render_closed_segment(ir, relation, segment.segment_id) == baseline
    relation.certificates = (*relation.certificates, relation.certificates[0])
    with pytest.raises(ValueError, match="exact"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def test_atomic_reduction_output_renderer_rejects_zero_producers():
    ir, relation, segment = _fixture(producer_count=1)
    relation.transition_specs = relation.transition_specs[-1:]
    segment.transition_ids = (relation.transition_specs[0].transition_id,)
    relation.certificates = relation.certificates[-1:]
    from trainverify.bridge_emitter.mixed_reduction_linear_renderer import (
        render_closed_mixed_reduction_output_linear_segment,
    )
    with pytest.raises(ValueError, match="positive"):
        render_closed_mixed_reduction_output_linear_segment(
            ir, relation, segment.segment_id
        )



def _witness_source(rendered):
    return f'''import denote.RelationCompiler
import denote.KRankLinearReduction
import denote.KRankLinearGather

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticReductionOutput
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [] }}
def fact_activation_0 : RelationFact := .sharded 100 [200,201,202] 2 [1,6,12] [1,6,4]
def fact_reduction_weight_0 : RelationFact := .sharded 300 [400,401,402] 1 [9,12] [9,4]
def fact_activation_1 : RelationFact := .sharded 101 [210,211,212] 2 [1,6,12] [1,6,4]
def fact_reduction_weight_1 : RelationFact := .sharded 301 [410,411,412] 1 [9,12] [9,4]
def fact_joined : RelationFact := .joined 700 701 [1,6,12]
def fact_output_weight : RelationFact := .sharded 702 [710,711,712] 0 [15,12] [5,12]
def fact_reduction_output_0 : RelationFact := .reduction 500 [600,601,602] [1,6,9]
def fact_reduction_output_1 : RelationFact := .reduction 501 [610,611,612] [1,6,9]
def fact_final : RelationFact := .sharded 703 [720,721,722] 2 [1,6,15] [1,6,5]
def state_pre : RelationState where
  facts := [fact_activation_0,fact_reduction_weight_0,fact_activation_1,fact_reduction_weight_1,fact_joined,fact_output_weight]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_reduction_output_0,fact_reduction_output_1,fact_final]
  nonempty := by decide

{rendered}
#print axioms segment_atomic
end
end SyntheticReductionOutput
end TrainVerify.Denote
'''


def test_generated_atomic_reduction_output_witness_is_exact_renderer_output():
    ir, relation, segment = _fixture(k=3, producer_count=2)
    first = _witness_source(composer.render_closed_segment(ir, relation, segment.segment_id))
    second = _witness_source(composer.render_closed_segment(ir, relation, segment.segment_id))
    assert first == second
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedMixedReductionOutputLinearWitness.lean"
    assert witness.read_text(encoding="utf-8") == first
    assert "sorry" not in first
