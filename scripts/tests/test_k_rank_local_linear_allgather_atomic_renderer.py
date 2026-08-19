from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter.composer import render_closed_segment
from trainverify.bridge_emitter.parser import Node
from trainverify.bridge_emitter import relation_compiler as rc


LOCAL_RULE = "linear-sharded-k-rank-dim1"
GATHER_RULE = "allgather-reconstruction-k-rank"
LOCAL_THEOREM = "TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm"
GATHER_THEOREM = "TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather"


def _fixture(*, k=3, count=2):
    assert k > 0 and count > 0
    full_in = (2, 3 * k, 5)
    shard_in = (2, 3, 5)
    full_out = (2, 3 * k, 7)
    shard_out = (2, 3, 7)

    # Deliberately orient the SM axis opposite to transition order.
    sm_nodes = []
    sm_positions = {}
    for group in reversed(range(count)):
        sm_positions[group] = len(sm_nodes)
        sm_nodes.append(Node(0, "FW_linear", [100 + group, 500 + group], [300 + group], []))

    # Deliberately interleave PM transition footprints by rank.  The gather
    # consumes local transition zero, while unrelated later writers may follow it.
    pm_nodes = []
    pm_positions = [[] for _ in range(count)]
    gather_position = None
    for rank in range(k):
        for group in range(count):
            pm_positions[group].append(len(pm_nodes))
            pm_nodes.append(Node(
                rank, "FW_linear", [200 + group * 10 + rank, 500 + group],
                [400 + group * 10 + rank], [],
            ))
            if rank == k - 1 and group == 0:
                gather_position = len(pm_nodes)
                pm_nodes.append(Node(
                    0, "AllGatherPrim", [400 + r for r in range(k)], [900], [1]
                ))
    assert gather_position is not None

    certificates = []
    relation_records = []
    authority_records = []
    local_outputs = []
    for group in range(count):
        pre = rc.RelationFactSpec(
            "sharded",
            (f"init:{100 + group}", *(f"init:{200 + group * 10 + rank}" for rank in range(k))),
            gather_dim=1,
        )
        post = rc.RelationFactSpec(
            "sharded",
            (f"sm:{sm_positions[group]}:0", *(f"pm:{position}:0" for position in pm_positions[group])),
            gather_dim=1,
        )
        cert = rc.KRankLocalRelationCertificate(
            LOCAL_RULE, "FW_linear", k, 1, pre, post,
            f"sm:{sm_positions[group]}:0",
            tuple(f"pm:{position}:0" for position in pm_positions[group]),
            (500 + group,), ((7, 5),), LOCAL_THEOREM,
        )
        certificates.append(cert)
        relation_records.extend((
            rc.ClosedRelationFactRecord(
                f"input_{group}", pre, "sharded", 100 + group,
                tuple(200 + group * 10 + rank for rank in range(k)),
                None, None, full_in, shard_in, 1,
            ),
            rc.ClosedRelationFactRecord(
                f"output_{group}", post, "sharded", 300 + group,
                tuple(400 + group * 10 + rank for rank in range(k)),
                None, None, full_out, shard_out, 1,
            ),
        ))
        local_outputs.append(post)
        authority_records.extend((
            rc.ClosedTensorEqFactRecord(
                f"weight_eq_{group}", "sm", 500 + group, "pm", 500 + group
            ),
            rc.ClosedTensorShapeFactRecord(
                f"weight_shape_{group}", "pm", 500 + group, (7, 5), 500 + group
            ),
        ))

    gather_post = rc.RelationFactSpec(
        "joined", (local_outputs[0].step_triple[0],), joined_pm_step=f"pm:{gather_position}:0"
    )
    certificates.append(rc.KRankAllGatherReconstructionCertificate(
        GATHER_RULE, k, 1, full_out, shard_out, local_outputs[0], gather_post,
        f"pm:{gather_position}:0", GATHER_THEOREM,
    ))
    relation_records.append(rc.ClosedRelationFactRecord(
        "joined", gather_post, "joined", 300, (), None, None,
        full_out, full_out, joined_pm_tid=900,
    ))

    transitions = rc.build_certificate_transition_specs(SimpleNamespace(), tuple(certificates))
    before_ids = tuple(
        [f"input_{group}" for group in range(count)]
        + [item.fact_id for item in authority_records]
    )
    # output_0 is consumed by the reconstruction; every other fresh output and
    # the joined terminal are published exactly.
    after_ids = tuple([f"output_{group}" for group in range(1, count)] + ["joined"])
    before = SimpleNamespace(state_id="state_pre", fact_ids=before_ids)
    after = SimpleNamespace(state_id="state_post", fact_ids=after_ids)
    segment = SimpleNamespace(
        segment_id="segment_generic", component_id="component",
        transition_ids=tuple(t.transition_id for t in transitions),
        sm_range=(0, len(sm_nodes)), pm_range=(0, len(pm_nodes)),
        pre_state_id=before.state_id, post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, segments=(segment,), states=(before, after),
        relation_facts=tuple(relation_records), authority_facts=tuple(authority_records),
        anchor_fact=SimpleNamespace(fact_id="anchor", side="sm", tid=100, shape=full_in),
    )
    ir = SimpleNamespace(
        sm_nodes=sm_nodes, pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph",
        pm_graph_ref="TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph",
    )
    relation = SimpleNamespace(
        certificates=tuple(certificates), transition_specs=transitions,
        dependent_chain_plan=chain,
    )
    return ir, relation, segment


def test_positive_local_linear_tuple_then_allgather_is_one_ordered_fold_per_axis():
    for count in (1, 2):
        ir, relation, segment = _fixture(k=3, count=count)
        source = render_closed_segment(ir, relation, segment.segment_id)
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1
        assert source.count(LOCAL_THEOREM) == count
        assert source.count(GATHER_THEOREM) == 1
        assert "rankCount = 3" not in source
        assert "K := [pmStore 200, pmStore 201, pmStore 202].length" in source
        assert "joined.Holds" in source
        assert all(f"output_{group}.Holds" in source for group in range(1, count))
        assert source.index("outs := [301]") < source.index("outs := [300]") if count == 2 else True
        assert source.index("outs := [400]") < source.index("outs := [410]") < source.index("outs := [401]") if count == 2 else True


@pytest.mark.parametrize(
    "tamper", [
        "transition-order", "sm-footprint", "pm-footprint", "sm-role", "pm-role",
        "pm-rank", "gather-input-order", "theorem", "duplicate-certificate", "state",
    ],
)
def test_local_linear_allgather_rejects_malformed_authority(tamper):
    ir, relation, segment = _fixture()
    if tamper == "transition-order":
        segment.transition_ids = tuple(reversed(segment.transition_ids))
    elif tamper == "sm-footprint":
        relation.transition_specs = (replace(relation.transition_specs[0], sm_node_indices=(0,)), *relation.transition_specs[1:])
    elif tamper == "pm-footprint":
        relation.transition_specs = (replace(relation.transition_specs[0], pm_node_indices=(0, 2)), *relation.transition_specs[1:])
    elif tamper == "sm-role":
        ir.sm_nodes[0].ins = list(reversed(ir.sm_nodes[0].ins))
    elif tamper == "pm-role":
        ir.pm_nodes[0].ins = list(reversed(ir.pm_nodes[0].ins))
    elif tamper == "pm-rank":
        ir.pm_nodes[0].rank = 2
    elif tamper == "gather-input-order":
        gather = next(node for node in ir.pm_nodes if node.op == "AllGatherPrim")
        gather.ins = list(reversed(gather.ins))
    elif tamper == "theorem":
        relation.transition_specs = (replace(relation.transition_specs[0], lean_theorem="wrong"), *relation.transition_specs[1:])
    elif tamper == "duplicate-certificate":
        relation.certificates += (relation.certificates[0],)
    else:
        relation.dependent_chain_plan.states[1].fact_ids += ("unproved",)
    with pytest.raises(ValueError):
        render_closed_segment(ir, relation, segment.segment_id)


def test_unrelated_same_family_certificate_does_not_change_rendered_bytes():
    ir, relation, segment = _fixture()
    expected = render_closed_segment(ir, relation, segment.segment_id)
    unrelated = replace(
        relation.certificates[0],
        input_fact=replace(relation.certificates[0].input_fact, gather_dim=0),
    )
    relation.certificates += (unrelated,)
    assert render_closed_segment(ir, relation, segment.segment_id) == expected


def test_generated_local_linear_allgather_witness_is_exact_renderer_output():
    from trainverify.bridge_emitter.composer import (
        _node_text, render_closed_relation_declarations,
    )

    ir, relation, segment = _fixture(k=3, count=2)
    namespace = "GeneratedKRankLocalLinearAllGatherAtomicWitness"
    rendered = render_closed_segment(ir, relation, segment.segment_id)
    declarations = render_closed_relation_declarations(
        relation.dependent_chain_plan, namespace
    )
    sm_nodes = "[" + ", ".join(_node_text(node) for node in ir.sm_nodes) + "]"
    pm_nodes = "[" + ", ".join(_node_text(node) for node in ir.pm_nodes) + "]"
    source = "\n".join((
        declarations,
        f"namespace TrainVerify.Denote.{namespace}",
        "noncomputable section",
        f"private def smGraph : GraphDecl := {{ numRanks := 1, nodes := {sm_nodes} }}",
        f"private def pmGraph : GraphDecl := {{ numRanks := 3, nodes := {pm_nodes} }}",
        rendered,
        f"#print axioms {segment.segment_id}",
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ))
    witness = Path(__file__).resolve().parents[2] / (
        "trainverify/denote/GeneratedKRankLocalLinearAllGatherAtomicWitness.lean"
    )
    witness.write_text(source, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == source
    assert "sorry" not in source and "False.elim" not in source
