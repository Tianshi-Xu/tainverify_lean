from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter.composer import render_closed_segment
from trainverify.bridge_emitter.parser import Node
from trainverify.bridge_emitter.relation_compiler import (
    KRankAllGatherReconstructionCertificate,
    KRankAllToAllRelationCertificate,
    RelationFactSpec,
)


def _fixture(*, k=3, alltoall_count=2):
    assert k > 0 and alltoall_count > 0
    full_shape = (2, 3 * k, 5 * k)
    input_shape = (2, 3, 5 * k)
    output_shape = (2, 3 * k, 5)
    certificates = []
    transitions = []
    records = []
    pm_nodes = []
    blocks = []

    for group in range(alltoall_count):
        inputs = tuple(1000 + group * 100 + rank for rank in range(k))
        outputs = tuple(2000 + group * 100 + rank for rank in range(k))
        pre = RelationFactSpec(
            "sharded",
            (f"sm:{group}:0", *(f"pm:{10 + group * k + rank}:0" for rank in range(k))),
            gather_dim=1,
        )
        post_steps = tuple(f"pm:OUT:{group}:{rank}" for rank in range(k))
        post = RelationFactSpec(
            "sharded", (f"sm:{group}:0", *post_steps), gather_dim=2
        )
        cert = KRankAllToAllRelationCertificate(
            rule_id="alltoall-k-rank-layout-transport",
            rank_count=k,
            input_gather_dim=1,
            output_gather_dim=2,
            input_fact=pre,
            output_fact=post,
            pm_step_ids=post_steps,
            lean_theorem="TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn",
        )
        certificates.append(cert)
        transitions.append(SimpleNamespace(
            transition_id=f"a2a-{group}",
            rule_id=cert.rule_id,
            pre_facts=(pre,),
            post_facts=(post,),
            sm_node_indices=(),
            pm_node_indices=(),
            lean_theorem=cert.lean_theorem,
        ))
        records.extend((
            SimpleNamespace(
                fact_id=f"pre_{group}", source=pre, kind="sharded",
                sm_tid=10 + group, pm_tids=inputs, gather_dim=1,
                full_shape=full_shape, shard_shape=input_shape, joined_pm_tid=None,
            ),
            SimpleNamespace(
                fact_id=f"post_{group}", source=post, kind="sharded",
                sm_tid=10 + group, pm_tids=outputs, gather_dim=2,
                full_shape=full_shape, shard_shape=output_shape, joined_pm_tid=None,
            ),
        ))
        blocks.append((inputs, outputs, post_steps))

    gather_inputs = tuple(3000 + rank for rank in range(k))
    gather_pre = RelationFactSpec(
        "sharded", ("sm:g:0", *(f"pm:G:{rank}" for rank in range(k))),
        gather_dim=1,
    )
    gather_post = RelationFactSpec(
        "joined", ("sm:g:0",), joined_pm_step="pm:G:out"
    )
    gather_cert = KRankAllGatherReconstructionCertificate(
        rule_id="allgather-reconstruction-k-rank",
        rank_count=k,
        gather_dim=1,
        full_shape=full_shape,
        shard_shape=input_shape,
        input_fact=gather_pre,
        output_fact=gather_post,
        pm_allgather_step="pm:G:out",
        lean_theorem="TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather",
    )
    certificates.append(gather_cert)
    transitions.append(SimpleNamespace(
        transition_id="gather",
        rule_id=gather_cert.rule_id,
        pre_facts=(gather_pre,),
        post_facts=(gather_post,),
        sm_node_indices=(),
        pm_node_indices=(),
        lean_theorem=gather_cert.lean_theorem,
    ))
    records.extend((
        SimpleNamespace(
            fact_id="gather_pre", source=gather_pre, kind="sharded",
            sm_tid=99, pm_tids=gather_inputs, gather_dim=1,
            full_shape=full_shape, shard_shape=input_shape, joined_pm_tid=None,
        ),
        SimpleNamespace(
            fact_id="gather_post", source=gather_post, kind="joined",
            sm_tid=99, pm_tids=(), gather_dim=None,
            full_shape=full_shape, shard_shape=full_shape, joined_pm_tid=3999,
        ),
    ))

    # Interleave AllToAll blocks by rank and put the AllGather between rank-0
    # and later writers, matching the cross-transition authority cycle in Goal 1.
    node_transition = []
    for rank in range(k):
        for group, (inputs, outputs, steps) in enumerate(blocks):
            pm_nodes.append(Node(rank, "AllToAllPrim", list(inputs), [outputs[rank]], [1, 2]))
            node_transition.append((group, steps[rank]))
        if rank == 0:
            pm_nodes.append(Node(0, "AllGatherPrim", list(gather_inputs), [3999], [1]))
            node_transition.append((alltoall_count, "pm:G:out"))

    for index, (owner, step_id) in enumerate(node_transition):
        transitions[owner].pm_node_indices += (index,)
        cert = certificates[owner]
        if owner < alltoall_count:
            rank = cert.pm_step_ids.index(step_id)
            ids = list(cert.pm_step_ids)
            ids[rank] = f"pm:{index}:0"
            certificates[owner] = replace(cert, pm_step_ids=tuple(ids))
        else:
            certificates[owner] = replace(cert, pm_allgather_step=f"pm:{index}:0")

    # Synchronize certificate fact step identities with the exact transition
    # facts after assigning the concrete writer indices.
    for group in range(alltoall_count):
        cert = certificates[group]
        old_post = transitions[group].post_facts[0]
        new_post = replace(old_post, step_triple=(old_post.step_triple[0], *cert.pm_step_ids))
        certificates[group] = replace(cert, output_fact=new_post)
        transitions[group].post_facts = (new_post,)
        records[2 * group + 1].source = new_post
    gather_index = transitions[-1].pm_node_indices[0]
    old_gather_post = transitions[-1].post_facts[0]
    new_gather_post = replace(old_gather_post, joined_pm_step=f"pm:{gather_index}:0")
    certificates[-1] = replace(
        certificates[-1], output_fact=new_gather_post,
        pm_allgather_step=f"pm:{gather_index}:0",
    )
    transitions[-1].post_facts = (new_gather_post,)
    records[-1].source = new_gather_post

    pre_ids = tuple(f"pre_{group}" for group in range(alltoall_count)) + ("gather_pre",)
    post_ids = tuple(f"post_{group}" for group in range(alltoall_count)) + ("gather_post",)
    states = (
        SimpleNamespace(state_id="state_pre", fact_ids=("anchor", *pre_ids)),
        SimpleNamespace(state_id="state_post", fact_ids=("anchor", *post_ids)),
    )
    segment = SimpleNamespace(
        segment_id="segment_generic", component_id="component",
        pre_state_id="state_pre", post_state_id="state_post",
        transition_ids=tuple(t.transition_id for t in transitions),
        sm_range=(0, 0), pm_range=(0, len(pm_nodes)),
    )
    chain = SimpleNamespace(
        complete=True,
        relation_facts=tuple(records), authority_facts=(),
        anchor_fact=SimpleNamespace(fact_id="anchor", side="sm", tid=777, shape=(1,)),
        states=states, segments=(segment,),
    )
    relation = SimpleNamespace(
        certificates=tuple(certificates), transition_specs=tuple(transitions),
        dependent_chain_plan=chain,
    )
    ir = SimpleNamespace(
        sm_nodes=[], pm_nodes=pm_nodes, sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="TrainVerify.Denote.GeneratedKRankAllToAllAllGatherAtomicWitness.smGraph", pm_graph_ref="TrainVerify.Denote.GeneratedKRankAllToAllAllGatherAtomicWitness.pmGraph",
    )
    return ir, relation, segment


def test_generic_positive_alltoall_tuple_then_allgather_uses_one_pm_fold():
    for count in (1, 2):
        ir, relation, segment = _fixture(k=3, alltoall_count=count)
        source = render_closed_segment(ir, relation, segment.segment_id)
        assert source.count("let pmFinal :=") == 1
        assert source.count("let smFinal :=") == 1
        assert "smNodes : List NodeDecl := []" in source
        assert "rankCount = 3" not in source
        assert source.count("allGatherPrimDimN_allToAllPrimWithDims_ofFn") == count
        assert source.count("ShardedRel.to_joined_allGather") == 1
        assert all(f"post_{group}.Holds" in source for group in range(count))
        assert "gather_post.Holds" in source


def test_mixed_collective_renderer_rejects_duplicate_and_malformed_certificates():
    ir, relation, segment = _fixture()
    exact = relation.certificates[0]
    duplicate = SimpleNamespace(**{**relation.__dict__, "certificates": (*relation.certificates, exact)})
    with pytest.raises(ValueError, match="one exact typed certificate"):
        render_closed_segment(ir, duplicate, segment.segment_id)
    malformed = replace(exact, output_fact=replace(exact.output_fact, gather_dim=0))
    broken = SimpleNamespace(**{**relation.__dict__, "certificates": (malformed, *relation.certificates[1:])})
    with pytest.raises(ValueError, match="one exact typed certificate"):
        render_closed_segment(ir, broken, segment.segment_id)


@pytest.mark.parametrize("tamper", ["order", "footprint", "writer", "state"])
def test_mixed_collective_renderer_rejects_order_footprint_writer_and_state_tampering(tamper):
    ir, relation, segment = _fixture()
    if tamper == "order":
        segment.transition_ids = tuple(reversed(segment.transition_ids))
    elif tamper == "footprint":
        relation.transition_specs[0].pm_node_indices = relation.transition_specs[0].pm_node_indices[:-1]
    elif tamper == "writer":
        ir.pm_nodes[0].ins = list(reversed(ir.pm_nodes[0].ins))
    else:
        relation.dependent_chain_plan.states[1].fact_ids += ("unproved",)
    with pytest.raises(ValueError):
        render_closed_segment(ir, relation, segment.segment_id)


def test_generated_atomic_collective_witness_is_exact_renderer_output():
    from trainverify.bridge_emitter.composer import (
        _node_text, render_closed_relation_declarations,
    )
    ir, relation, segment = _fixture(k=3, alltoall_count=2)
    namespace = "GeneratedKRankAllToAllAllGatherAtomicWitness"
    rendered = render_closed_segment(ir, relation, segment.segment_id)
    declarations = render_closed_relation_declarations(
        relation.dependent_chain_plan, namespace
    )
    pm_nodes = "[" + ", ".join(_node_text(node) for node in ir.pm_nodes) + "]"
    source = "\n".join((
        declarations,
        f"namespace TrainVerify.Denote.{namespace}",
        "noncomputable section",
        "private def smGraph : GraphDecl := { numRanks := 1, nodes := [] }",
        f"private def pmGraph : GraphDecl := {{ numRanks := 3, nodes := {pm_nodes} }}",
        rendered,
        f"#print axioms {segment.segment_id}",
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ))
    witness = Path(__file__).resolve().parents[2] / (
        "trainverify/denote/GeneratedKRankAllToAllAllGatherAtomicWitness.lean"
    )
    witness.unlink(missing_ok=True)
    witness.write_text(source, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == source
    assert "sorry" not in source and "False.elim" not in source



def _alltoall_only_fixture(*, k=3, alltoall_count=2):
    ir, relation, segment = _fixture(k=k, alltoall_count=alltoall_count)
    gather_index = relation.transition_specs[-1].pm_node_indices[0]
    ir.pm_nodes.pop(gather_index)
    relation.certificates = relation.certificates[:-1]
    relation.transition_specs = relation.transition_specs[:-1]
    for cert_index, transition in enumerate(relation.transition_specs):
        transition.pm_node_indices = tuple(
            index - (index > gather_index) for index in transition.pm_node_indices
        )
        cert = relation.certificates[cert_index]
        new_steps = tuple(f"pm:{index}:0" for index in transition.pm_node_indices)
        new_post = replace(
            transition.post_facts[0],
            step_triple=(transition.post_facts[0].step_triple[0], *new_steps),
        )
        new_cert = replace(cert, output_fact=new_post, pm_step_ids=new_steps)
        relation.certificates = (
            *relation.certificates[:cert_index], new_cert,
            *relation.certificates[cert_index + 1:],
        )
        transition.post_facts = (new_post,)
        relation.dependent_chain_plan.relation_facts[2 * cert_index + 1].source = new_post
    relation.dependent_chain_plan.relation_facts = relation.dependent_chain_plan.relation_facts[:-2]
    relation.dependent_chain_plan.states[0].fact_ids = tuple(
        fact for fact in relation.dependent_chain_plan.states[0].fact_ids
        if fact != "gather_pre"
    )
    relation.dependent_chain_plan.states[1].fact_ids = tuple(
        fact for fact in relation.dependent_chain_plan.states[1].fact_ids
        if fact != "gather_post"
    )
    segment.transition_ids = segment.transition_ids[:-1]
    segment.pm_range = (0, len(ir.pm_nodes))
    namespace = "GeneratedKRankAllToAllTupleAtomicWitness"
    ir.sm_graph_ref = f"TrainVerify.Denote.{namespace}.smGraph"
    ir.pm_graph_ref = f"TrainVerify.Denote.{namespace}.pmGraph"
    return ir, relation, segment


def test_generic_positive_alltoall_tuple_without_reconstruction_uses_one_pm_fold():
    ir, relation, segment = _alltoall_only_fixture(k=3, alltoall_count=2)
    source = render_closed_segment(ir, relation, segment.segment_id)
    assert source.count("let pmFinal :=") == 1
    assert source.count("let smFinal :=") == 1
    assert "smNodes : List NodeDecl := []" in source
    assert "AllGatherPrim" not in source
    assert source.count("allGatherPrimDimN_allToAllPrimWithDims_ofFn") == 2
    assert "post_0.Holds" in source and "post_1.Holds" in source


def test_alltoall_tuple_rejects_transition_order_tampering():
    ir, relation, segment = _alltoall_only_fixture(k=3, alltoall_count=2)
    segment.transition_ids = tuple(reversed(segment.transition_ids))
    with pytest.raises(ValueError, match="transition order"):
        render_closed_segment(ir, relation, segment.segment_id)

def test_mixed_collective_renderer_supports_plan_top_level_import(monkeypatch):
    import importlib
    import sys

    bridge = Path(__file__).resolve().parents[2] / "trainverify/bridge_emitter"
    monkeypatch.syspath_prepend(str(bridge))
    sys.modules.pop("mixed_collective_renderer", None)
    module = importlib.import_module("mixed_collective_renderer")
    top_relation_compiler = importlib.import_module("relation_compiler")
    monkeypatch.setattr(
        top_relation_compiler,
        "KRankAllGatherReconstructionCertificate",
        KRankAllGatherReconstructionCertificate,
    )
    monkeypatch.setattr(
        top_relation_compiler,
        "KRankAllToAllRelationCertificate",
        KRankAllToAllRelationCertificate,
    )
    ir, relation, segment = _fixture()
    source = module.render_closed_k_rank_alltoall_allgather_segment(
        ir, relation, segment.segment_id
    )
    assert source.count("let pmFinal :=") == 1


def test_generated_alltoall_tuple_witness_is_exact_renderer_output():
    from trainverify.bridge_emitter.composer import (
        _node_text, render_closed_relation_declarations,
    )

    ir, relation, segment = _alltoall_only_fixture(k=3, alltoall_count=2)
    namespace = "GeneratedKRankAllToAllTupleAtomicWitness"
    rendered = render_closed_segment(ir, relation, segment.segment_id)
    declarations = render_closed_relation_declarations(
        relation.dependent_chain_plan, namespace
    )
    pm_nodes = "[" + ", ".join(_node_text(node) for node in ir.pm_nodes) + "]"
    source = "\n".join((
        declarations,
        f"namespace TrainVerify.Denote.{namespace}",
        "noncomputable section",
        "private def smGraph : GraphDecl := { numRanks := 1, nodes := [] }",
        f"private def pmGraph : GraphDecl := {{ numRanks := 3, nodes := {pm_nodes} }}",
        rendered,
        f"#print axioms {segment.segment_id}",
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ))
    witness = Path(__file__).resolve().parents[2] / (
        "trainverify/denote/GeneratedKRankAllToAllTupleAtomicWitness.lean"
    )
    witness.unlink(missing_ok=True)
    witness.write_text(source, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == source
    assert "sorry" not in source and "False.elim" not in source
