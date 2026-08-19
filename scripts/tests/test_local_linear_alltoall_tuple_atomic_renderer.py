from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter.composer import render_closed_segment
from trainverify.bridge_emitter.parser import Node
from trainverify.bridge_emitter import relation_compiler as rc


LOCAL_RULE = "linear-sharded-k-rank-dim1"
A2A_RULE = "alltoall-k-rank-layout-transport"
LOCAL_THEOREM = "TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm"
A2A_THEOREM = "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"


def _fixture(*, k=3, local_count=2, a2a_count=2):
    assert k > 0 and local_count > 0 and a2a_count > 0
    sm_nodes = []
    sm_positions = {}
    for group in reversed(range(local_count)):
        sm_positions[group] = len(sm_nodes)
        sm_nodes.append(Node(0, "FW_linear", [100 + group, 500 + group], [300 + group], []))

    pm_nodes = []
    local_positions = [[] for _ in range(local_count)]
    a2a_positions = [[] for _ in range(a2a_count)]
    local_pm_tids = [tuple(200 + group * 10 + rank for rank in range(k)) for group in range(local_count)]
    local_out_tids = [tuple(400 + group * 10 + rank for rank in range(k)) for group in range(local_count)]
    a2a_out_tids = [tuple(800 + group * 10 + rank for rank in range(k)) for group in range(a2a_count)]
    # Rank-interleave all footprints.  Every AllToAll consumes a local output,
    # while the SM axis is deliberately reverse-oriented.
    for rank in range(k):
        for group in range(local_count):
            local_positions[group].append(len(pm_nodes))
            pm_nodes.append(Node(rank, "FW_linear", [local_pm_tids[group][rank], 500 + group], [local_out_tids[group][rank]], []))
    for rank in range(k):
        for group in range(a2a_count):
            producer = group % local_count
            a2a_positions[group].append(len(pm_nodes))
            pm_nodes.append(Node(rank, "AllToAllPrim", list(local_out_tids[producer]), [a2a_out_tids[group][rank]], [1, 2]))

    certs = []
    records = []
    authorities = []
    local_posts = []
    for group in range(local_count):
        pre = rc.RelationFactSpec("sharded", (f"init:{100 + group}", *(f"init:{tid}" for tid in local_pm_tids[group])), gather_dim=1)
        post = rc.RelationFactSpec("sharded", (f"sm:{sm_positions[group]}:0", *(f"pm:{i}:0" for i in local_positions[group])), gather_dim=1)
        certs.append(rc.KRankLocalRelationCertificate(
            LOCAL_RULE, "FW_linear", k, 1, pre, post,
            f"sm:{sm_positions[group]}:0", tuple(f"pm:{i}:0" for i in local_positions[group]),
            (500 + group,), ((7 * k, 5),), LOCAL_THEOREM,
        ))
        records.extend((
            rc.ClosedRelationFactRecord(f"local_in_{group}", pre, "sharded", 100 + group, local_pm_tids[group], None, None, (2, 3 * k, 5), (2, 3, 5), 1),
            rc.ClosedRelationFactRecord(f"local_out_{group}", post, "sharded", 300 + group, local_out_tids[group], None, None, (2, 3 * k, 7 * k), (2, 3, 7 * k), 1),
        ))
        authorities.extend((
            rc.ClosedTensorEqFactRecord(f"weight_eq_{group}", "sm", 500 + group, "pm", 500 + group),
            rc.ClosedTensorShapeFactRecord(f"weight_shape_{group}", "pm", 500 + group, (7 * k, 5), 500 + group),
        ))
        local_posts.append(post)

    for group in range(a2a_count):
        producer = group % local_count
        pre = local_posts[producer]
        post = rc.RelationFactSpec("sharded", (pre.step_triple[0], *(f"pm:{i}:0" for i in a2a_positions[group])), gather_dim=2)
        certs.append(rc.KRankAllToAllRelationCertificate(
            A2A_RULE, k, 1, 2, pre, post,
            tuple(f"pm:{i}:0" for i in a2a_positions[group]), A2A_THEOREM,
        ))
        records.append(rc.ClosedRelationFactRecord(
            f"a2a_out_{group}", post, "sharded", 300 + producer, a2a_out_tids[group],
            None, None, (2, 3 * k, 7 * k), (2, 3 * k, 7), 2,
        ))

    transitions = rc.build_certificate_transition_specs(SimpleNamespace(), tuple(certs))
    local_transitions = sorted(
        transitions[:local_count], key=lambda t: int(t.post_facts[0].step_triple[0].split(":")[1])
    )
    a2a_transitions = sorted(
        transitions[local_count:], key=lambda t: int(t.post_facts[0].step_triple[0].split(":")[1])
    )
    ordered_transitions = (*local_transitions, *a2a_transitions)
    before_ids = tuple(
        [f"local_in_{i}" for i in range(local_count)] + [a.fact_id for a in authorities]
    )
    after_ids = tuple(
        [f"local_out_{i}" for i in range(local_count)]
        + [f"a2a_out_{i}" for i in range(a2a_count)]
    )
    before = SimpleNamespace(state_id="state_pre", fact_ids=before_ids)
    after = SimpleNamespace(state_id="state_post", fact_ids=after_ids)
    segment = SimpleNamespace(
        segment_id="segment_generic", component_id="component",
        transition_ids=tuple(t.transition_id for t in ordered_transitions),
        sm_range=(0, len(sm_nodes)), pm_range=(0, len(pm_nodes)),
        pre_state_id=before.state_id, post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, segments=(segment,), states=(before, after),
        relation_facts=tuple(records), authority_facts=tuple(authorities),
        anchor_fact=SimpleNamespace(fact_id="anchor", side="sm", tid=100, shape=(2, 3 * k, 5)),
    )
    namespace = "GeneratedLocalLinearAllToAllTupleAtomicWitness"
    ir = SimpleNamespace(
        sm_nodes=sm_nodes, pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref=f"TrainVerify.Denote.{namespace}.smGraph",
        pm_graph_ref=f"TrainVerify.Denote.{namespace}.pmGraph",
    )
    relation = SimpleNamespace(certificates=tuple(certs), transition_specs=transitions, dependent_chain_plan=chain)
    return ir, relation, segment


def test_positive_local_linear_then_positive_alltoall_tuple_uses_one_fold_per_axis():
    for local_count, a2a_count in ((1, 2), (2, 1)):
        ir, relation, segment = _fixture(k=3, local_count=local_count, a2a_count=a2a_count)
        source = render_closed_segment(ir, relation, segment.segment_id)
        assert source.count("let smFinal :=") == 1
        assert source.count("let pmFinal :=") == 1
        assert source.count(LOCAL_THEOREM) == local_count
        assert source.count(A2A_THEOREM) == a2a_count
        assert all(f"a2a_out_{i}.Holds" in source for i in range(a2a_count))
        assert "rankCount = 3" not in source
        assert "outs := [301]" in source if local_count == 2 else True


@pytest.mark.parametrize("tamper", [
    "transition-order", "sm-footprint", "pm-footprint", "sm-role", "pm-role",
    "a2a-input-order", "a2a-rank", "theorem", "duplicate-certificate", "state",
])
def test_local_linear_alltoall_rejects_malformed_authority(tamper):
    ir, relation, segment = _fixture()
    if tamper == "transition-order":
        segment.transition_ids = tuple(reversed(segment.transition_ids))
    elif tamper == "sm-footprint":
        relation.transition_specs = (replace(relation.transition_specs[0], sm_node_indices=()), *relation.transition_specs[1:])
    elif tamper == "pm-footprint":
        relation.transition_specs = (replace(relation.transition_specs[0], pm_node_indices=relation.transition_specs[0].pm_node_indices[:-1]), *relation.transition_specs[1:])
    elif tamper == "sm-role":
        ir.sm_nodes[0].ins = list(reversed(ir.sm_nodes[0].ins))
    elif tamper == "pm-role":
        ir.pm_nodes[0].ins = list(reversed(ir.pm_nodes[0].ins))
    elif tamper == "a2a-input-order":
        next(node for node in ir.pm_nodes if node.op == "AllToAllPrim").ins.reverse()
    elif tamper == "a2a-rank":
        next(node for node in ir.pm_nodes if node.op == "AllToAllPrim").rank = 2
    elif tamper == "theorem":
        relation.transition_specs = (replace(relation.transition_specs[0], lean_theorem="wrong"), *relation.transition_specs[1:])
    elif tamper == "duplicate-certificate":
        relation.certificates += (relation.certificates[0],)
    else:
        relation.dependent_chain_plan.states[1].fact_ids += ("unproved",)
    with pytest.raises(ValueError):
        render_closed_segment(ir, relation, segment.segment_id)


def test_unrelated_same_family_certificate_is_byte_stable():
    ir, relation, segment = _fixture()
    expected = render_closed_segment(ir, relation, segment.segment_id)
    relation.certificates += (replace(relation.certificates[0], input_fact=replace(relation.certificates[0].input_fact, gather_dim=0)),)
    assert render_closed_segment(ir, relation, segment.segment_id) == expected


def test_generated_local_linear_alltoall_witness_is_exact_renderer_output():
    from trainverify.bridge_emitter.composer import _node_text, render_closed_relation_declarations
    ir, relation, segment = _fixture(k=3, local_count=2, a2a_count=2)
    namespace = "GeneratedLocalLinearAllToAllTupleAtomicWitness"
    rendered = render_closed_segment(ir, relation, segment.segment_id)
    declarations = render_closed_relation_declarations(relation.dependent_chain_plan, namespace)
    sm_nodes = "[" + ", ".join(_node_text(node) for node in ir.sm_nodes) + "]"
    pm_nodes = "[" + ", ".join(_node_text(node) for node in ir.pm_nodes) + "]"
    source = "\n".join((
        declarations,
        f"namespace TrainVerify.Denote.{namespace}", "noncomputable section",
        f"private def smGraph : GraphDecl := {{ numRanks := 1, nodes := {sm_nodes} }}",
        f"private def pmGraph : GraphDecl := {{ numRanks := 3, nodes := {pm_nodes} }}",
        rendered, f"#print axioms {segment.segment_id}", "end",
        f"end TrainVerify.Denote.{namespace}", "",
    ))
    witness = Path(__file__).resolve().parents[2] / "trainverify/denote/GeneratedLocalLinearAllToAllTupleAtomicWitness.lean"
    witness.write_text(source, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == source
    assert "sorry" not in source and "False.elim" not in source
