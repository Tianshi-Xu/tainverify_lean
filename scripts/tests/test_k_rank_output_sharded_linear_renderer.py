from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node


def _closed_fixture(k=3):
    b, s, inner, local_out = 1, 5, 7, 11
    activation_shape = (b, s, inner)
    weight_full_shape = (local_out * k, inner)
    weight_shard_shape = (local_out, inner)
    output_full_shape = (b, s, local_out * k)
    output_shard_shape = (b, s, local_out)
    activation_fact = rc.RelationFactSpec(
        "joined", ("init:100",), joined_pm_step="init:200"
    )
    weight_fact = rc.RelationFactSpec(
        "sharded", ("init:101", *(f"init:{201 + rank}" for rank in range(k))),
        gather_dim=0,
    )
    output_fact = rc.RelationFactSpec(
        "sharded", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(k))),
        gather_dim=2,
    )
    theorem = "TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm"
    cert = rc.KRankOutputShardedLinearCertificate(
        rule_id="linear-output-sharded-k-rank",
        rank_count=k,
        output_gather_dim=2,
        activation_fact=activation_fact,
        weight_fact=weight_fact,
        output_fact=output_fact,
        sm_step_id="sm:0:0",
        pm_step_ids=tuple(f"pm:{rank}:0" for rank in range(k)),
        activation_shape=activation_shape,
        weight_full_shape=weight_full_shape,
        weight_shard_shape=weight_shard_shape,
        output_full_shape=output_full_shape,
        output_shard_shape=output_shard_shape,
        lean_theorem=theorem,
    )
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    activation = rc.ClosedRelationFactRecord(
        "fact_activation", activation_fact, "joined", 100, (), None, None,
        activation_shape, activation_shape, joined_pm_tid=200,
    )
    weight = rc.ClosedRelationFactRecord(
        "fact_weight", weight_fact, "sharded", 101,
        tuple(201 + rank for rank in range(k)), None, None,
        weight_full_shape, weight_shard_shape, 0,
    )
    output = rc.ClosedRelationFactRecord(
        "fact_output", output_fact, "sharded", 110,
        tuple(301 + rank for rank in range(k)), None, None,
        output_full_shape, output_shard_shape, 2,
    )
    before = SimpleNamespace(
        state_id="state_pre", fact_ids=(activation.fact_id, weight.fact_id)
    )
    after = SimpleNamespace(state_id="state_post", fact_ids=(output.fact_id,))
    segment = SimpleNamespace(
        segment_id="segment_000000", transition_ids=(transition.transition_id,),
        sm_range=(0, 1), pm_range=(0, k),
        pre_state_id=before.state_id, post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(activation, weight, output), authority_facts=(),
        states=(before, after), segments=(segment,),
    )
    sm_node = Node(0, "FW_linear", [100, 101], [110], [])
    pm_nodes = [
        Node(rank, "FW_linear", [200, 201 + rank], [301 + rank], [])
        for rank in range(k)
    ]
    ir = SimpleNamespace(
        sm_nodes=[sm_node], pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="SyntheticLinearOutput.gSM",
        pm_graph_ref="SyntheticLinearOutput.gPM",
    )
    relation = SimpleNamespace(
        certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain,
    )
    return ir, relation, segment, activation, weight, output


def test_closed_output_sharded_linear_replays_exact_dynamic_ordered_writers():
    ir, relation, segment, activation, weight, output = _closed_fixture(k=3)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source.count('op := "OpName.FW_linear"') == 4
    assert source.count("foldl_faithful_middle_writer") == 4
    assert source.count("applyNode_fw_linear_out") == 4
    assert "fw_linear_3d_weight_allGatherPrimDimN_dim0_comm" in source
    assert f"smStore {activation.sm_tid}" in source
    assert ", ".join(f"pmStore {tid}" for tid in weight.pm_tids) in source
    assert ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) in source
    assert "rankCount = 3" not in source
    assert source.count("simp only [List.length_cons, List.length_nil]") == 2


@pytest.mark.parametrize(
    ("target", "mutation", "message"),
    [
        ("writer", {"rank": 7}, "ordered ranks"),
        ("writer", {"params": [9]}, "no parameters"),
        ("writer", {"ins": [200]}, "binary"),
        ("writer", {"ins": [999, 202]}, "activation"),
        ("writer", {"ins": [200, 999]}, "weight"),
        ("writer", {"outs": [999]}, "output"),
        ("transition", {"sm_node_indices": (0, 1)}, "footprint"),
        ("segment", {"pm_range": (0, 2)}, "footprint"),
    ],
)
def test_closed_output_sharded_linear_rejects_tampered_authority(target, mutation, message):
    ir, relation, segment, *_ = _closed_fixture(k=3)
    if target == "writer":
        for key, value in mutation.items():
            setattr(ir.pm_nodes[1], key, value)
    elif target == "transition":
        relation.transition_specs = (replace(relation.transition_specs[0], **mutation),)
    else:
        for key, value in mutation.items():
            setattr(segment, key, value)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize("axis", ["rule", "theorem", "pre", "post", "class"])
def test_closed_output_sharded_linear_selector_rejects_each_inexact_axis(axis):
    ir, relation, segment, *_ = _closed_fixture(k=3)
    cert = relation.certificates[0]
    transition = relation.transition_specs[0]
    if axis == "rule":
        relation.certificates = (replace(cert, rule_id="wrong-rule"),)
    elif axis == "theorem":
        relation.certificates = (replace(cert, lean_theorem="Wrong.theorem"),)
    elif axis == "pre":
        relation.certificates = (replace(cert, activation_fact=rc.RelationFactSpec("joined", ("init:999",), joined_pm_step="init:200")),)
    elif axis == "post":
        relation.certificates = (replace(cert, output_fact=rc.RelationFactSpec("sharded", ("sm:9:0", *cert.pm_step_ids), gather_dim=2)),)
    else:
        relation.certificates = (SimpleNamespace(**cert.__dict__),)
    with pytest.raises(ValueError, match="exact typed certificate"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def test_closed_output_sharded_linear_selector_ignores_unrelated_but_rejects_duplicate():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    cert = relation.certificates[0]
    unrelated = replace(cert, rule_id="unrelated")
    relation.certificates = (unrelated, cert)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert "fw_linear_3d_weight_allGatherPrimDimN_dim0_comm" in source
    relation.certificates = (cert, cert)
    with pytest.raises(ValueError, match="exact typed certificate"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def test_closed_output_sharded_linear_rejects_certificate_shape_tamper():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    relation.certificates = (replace(relation.certificates[0], output_shard_shape=(1, 5, 99)),)
    with pytest.raises(ValueError, match="shapes disagree"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def _witness_source(rendered):
    return f'''import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticLinearOutput
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_linear", ins := [100, 101], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := "OpName.FW_linear", ins := [200, 201], outs := [301] }}, {{ rank := 1, op := "OpName.FW_linear", ins := [200, 202], outs := [302] }}, {{ rank := 2, op := "OpName.FW_linear", ins := [200, 203], outs := [303] }}] }}

def fact_activation : RelationFact := .joined 100 200 [1, 5, 7]
def fact_weight : RelationFact := .sharded 101 [201, 202, 203] 0 [33, 7] [11, 7]
def fact_output : RelationFact := .sharded 110 [301, 302, 303] 2 [1, 5, 33] [1, 5, 11]
def state_pre : RelationState where
  facts := [fact_activation, fact_weight]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_output]
  nonempty := by decide

{rendered}
#print axioms segment_000000
end
end SyntheticLinearOutput
end TrainVerify.Denote
'''


def test_generated_output_sharded_linear_witness_is_deterministic_renderer_output():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    first = _witness_source(composer.render_closed_segment(ir, relation, segment.segment_id))
    second = _witness_source(composer.render_closed_segment(ir, relation, segment.segment_id))
    assert first == second
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedKRankLinearOutputShardedWitness.lean"
    witness.write_text(first, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == first
    assert "sorry" not in first
    assert "#print axioms segment_000000" in first
