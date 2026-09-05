"""Ordinary contiguous prefix and K entry share one production relation DAG."""
from dataclasses import fields, replace
from pathlib import Path

import pytest

from scripts.tests.test_cp_k_entry import entry_ir, compile_entry
from trainverify.bridge_emitter import composer, parser, relation_compiler as rc
from trainverify.bridge_emitter.external_pre_fact_selector import select_unproduced_external_pre_facts
from trainverify.bridge_emitter.model_authority import ModelAuthorityIR, TargetQuery, materialize_target_ir
from trainverify.bridge_emitter.model_compiler import compile_shared_proof_dag, compile_shared_relation_dag
from trainverify.bridge_emitter.parser import LineageGoal, Node
from trainverify.bridge_emitter.proof_compiler import build_default_registry, compile_proof_plan


def prefix_ir(k=3, op="FW_maybe_shuffle", reordered=False, *, prefix_reordered=False):
    ir = entry_ir(k, op)
    ir.sm_nodes[0].ins[0] = 30
    for r, node in enumerate(ir.pm_nodes):
        node.ins[0] = 110+r
    ir.sm_nodes.insert(0, Node(0, "FW_contiguous", [10], [30], None))
    prefix = [Node(r, "FW_contiguous", [100+r], [110+r], None) for r in range(k)]
    if prefix_reordered:
        prefix = prefix[-1:] + prefix[:-1]
    if reordered:
        ir.pm_nodes = ir.pm_nodes[-1:] + ir.pm_nodes[:-1]
    ir.pm_nodes = prefix + ir.pm_nodes
    return ir


def shared_prefix(ir):
    k = ir.pm_num_ranks
    targets = {}
    for goal, lineage in enumerate((
        LineageGoal(30, [4*k, 2], [(r, 110+r) for r in range(k)], [[4, 2]]*k, 0),
        ir.lineage,
    )):
        payload = {f.name: getattr(ir, f.name) for f in fields(TargetQuery) if hasattr(ir, f.name)}
        payload.update(goal_id=goal, lineage=lineage, public_statement_digest="synthetic-prefix-entry", prereqs=tuple(ir.prereqs))
        targets[goal] = TargetQuery(**payload)
    payload = {f.name: getattr(ir, f.name) for f in fields(ModelAuthorityIR) if hasattr(ir, f.name)}
    model = ModelAuthorityIR(**payload, model_id="cp-k-prefix", root=__file__, targets=targets, aggregate=None)
    proof = compile_shared_proof_dag(model, build_default_registry())
    return model, compile_shared_relation_dag(model, proof)


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
@pytest.mark.parametrize("k", [3, 5])
@pytest.mark.parametrize("reordered,prefix_reordered", [(False, False), (True, False), (False, True), (True, True)])
def test_prefix_entry_share_exact_two_closed_segments(op, k, reordered, prefix_reordered):
    ir = prefix_ir(k, op, reordered, prefix_reordered=prefix_reordered)
    assert 30 not in ir.init_lineages
    assert not {30, *range(110, 110+k)} & {tid for tid, _ in ir.sm_shapes + ir.pm_shapes}
    model, dag = shared_prefix(ir)
    assert len(dag.certificates) == len(dag.transitions) == 2
    prefix_keys = dag.projections[0].certificate_keys
    entry_keys = dag.projections[1].certificate_keys
    assert len(prefix_keys) == 1 and len(entry_keys) == 2
    assert set(prefix_keys) < set(entry_keys)
    prefix_terminal = dag.projections[0].terminal_fact_key
    entry_terminal = dag.projections[1].terminal_fact_key
    assert prefix_terminal is not None and entry_terminal is not None
    assert dag.facts[prefix_terminal].layout == "sharded"
    assert dag.facts[entry_terminal].layout == "zigzag_k"
    relation = dag.global_relation
    assert relation is not None and relation.dependency_plan is not None
    chain = relation.dependent_chain_plan
    assert chain is not None
    assert chain.complete and len(chain.segments) == 2
    prefix = next(t for t in relation.transition_specs if t.rule_id == "contiguous-sharded-k-rank")
    entry = next(t for t in relation.transition_specs if t.rule_id != prefix.rule_id)
    assert prefix.post_facts == entry.pre_facts
    assert not set(entry.pre_facts) & select_unproduced_external_pre_facts(relation.transition_specs)
    assert dict(relation.dependency_plan.dependencies)[entry.transition_id] == (prefix.transition_id,)
    assert [s.sm_range for s in chain.segments] == [(0, 1), (1, 2)]
    assert [s.pm_range for s in chain.segments] == [(0, k), (k, 2*k)]
    assert prefix.sm_node_indices == (0,) and entry.sm_node_indices == (1,)
    assert prefix.pm_node_indices == tuple(range(k)) and entry.pm_node_indices == tuple(range(k, 2*k))
    target_ir = materialize_target_ir(model, 1)
    bodies = [composer.render_closed_segment(target_ir, relation, s.segment_id) for s in chain.segments]
    cert = next(c for c in relation.certificates if c.rule_id == prefix.rule_id)
    ordered_indices = tuple(next(i for i, n in enumerate(ir.pm_nodes[:k]) if n.rank == rank) for rank in range(k))
    assert cert.pm_step_ids == tuple(f"pm:{i}:0" for i in ordered_indices)
    segment_id = chain.segments[0].segment_id
    frame = ", ".join(composer._node_text(n) for n in ir.pm_nodes[:k])
    assert f"private def {segment_id}_pm_nodes : List NodeDecl := [{frame}]" in bodies[0]
    for rank, pos in enumerate(ordered_indices):
        assert f"pmNodes.take {pos} ++ [{segment_id}_pm_node_{rank}] ++ pmNodes.drop {pos + 1}" in bodies[0]
    assert bodies[0].count("foldl_faithful_middle_writer") == k + 1
    assert bodies[0].count("foldl_applyNodeDistributedFaithful_at_not_written") == k + 1
    assert "RelationState.Holds.fold_frame" in bodies[0]
    assert "ShardedRel.fw_contiguous" in bodies[0]
    assert "ZigzagKRel.of_sharded" in bodies[1]
    assert all("sorry" not in b and "axiom" not in b for b in bodies)
    with pytest.raises(ValueError, match="joined or ordered-sharded terminal"):
        composer.render_closed_public_theorem(target_ir, relation, "CPPrefixProof")


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
@pytest.mark.parametrize("mutation", [
    "missing_sm_prefix", "missing_pm_prefix", "wrong_prefix_input", "wrong_prefix_op",
    "mixed_target_op", "missing_last_writer", "missing_group", "reversed_group",
    "missing_metadata", "missing_packed", "wrong_tokens", "wrong_init_lineage",
])
def test_prefix_authority_mutations_fail_closed(op, mutation):
    ir = prefix_ir(op=op)
    if mutation == "missing_sm_prefix": ir.sm_nodes.pop(0)
    elif mutation == "missing_pm_prefix": ir.pm_nodes.pop(2)
    elif mutation == "wrong_prefix_input": ir.pm_nodes[2].ins[0] = 101
    elif mutation == "wrong_prefix_op": ir.pm_nodes[2].op = "FW_float"
    elif mutation == "mixed_target_op": ir.pm_nodes[-1].op = "BW_maybe_unshuffle" if op == "FW_maybe_shuffle" else "FW_maybe_shuffle"
    elif mutation == "missing_last_writer": ir.pm_nodes.pop()
    elif mutation == "missing_group": ir.pm_replica_groups = ()
    elif mutation == "reversed_group":
        group = ir.pm_replica_groups[0]
        ir.pm_replica_groups = (replace(group, members=tuple(reversed(group.members))),)
    elif mutation == "missing_metadata": ir.pm_input_value_classes = ()
    elif mutation == "missing_packed": ir.packed_cu_contracts = ()
    elif mutation == "wrong_tokens": ir.packed_cu_contracts = (replace(ir.packed_cu_contracts[0], total_tokens=18),)
    elif mutation == "wrong_init_lineage": ir.init_lineages[10].tps[2] = (2, 101)
    with pytest.raises((ValueError, rc.RelationCompositionError)):
        model, dag = shared_prefix(ir)
        relation = dag.global_relation
        assert relation is not None and relation.dependent_chain_plan is not None
        for segment in relation.dependent_chain_plan.segments:
            composer.render_closed_segment(materialize_target_ir(model, 1), relation, segment.segment_id)


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
def test_forged_intermediate_init_binding_is_not_prefix_authority(op):
    ir = prefix_ir(op=op)
    ir.init_lineages[30] = LineageGoal(30, [12, 2], [(r, 110+r) for r in range(3)], [[4, 2]]*3, 0)
    ir.sm_shapes.append((30, [12, 2]))
    ir.pm_shapes.extend((110+r, [4, 2]) for r in range(3))
    proof = compile_proof_plan(ir, build_default_registry())
    forged = replace(proof, steps=tuple(
        replace(s, input_bindings=(f"init:{s.input_tids[0]}", "init:90"))
        if s.step_id in proof.target_steps else s for s in proof.steps))
    with pytest.raises(rc.RelationCompositionError, match="producer authority"):
        rc.compile_k_shuffle_entry_boundary(ir, forged)


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
@pytest.mark.parametrize("mutation,message", [
    ("missing_init", "requires exact InitGoal source authority"),
    ("forged_shapes", "input producer authority mismatch"),
    ("gather_dim", "InitGoal gather dimension mismatch"),
])
def test_contiguous_init_authority_guards_independently(op, mutation, message):
    ir = prefix_ir(op=op)
    if mutation == "missing_init":
        ir.init_lineages.pop(10)
    elif mutation == "gather_dim":
        ir.init_lineages[10].gatherDim = 1
        ir.init_lineages[10].tsShape = [2, 12]
        ir.init_lineages[10].tpShapes = [[2, 4]] * 3
    proof = compile_proof_plan(ir, build_default_registry())
    frontier = tuple(s.step_id for s in proof.steps if s.op == "FW_contiguous")
    assert len(frontier) == 4
    if mutation == "forged_shapes":
        # Preserve the ordered init refs and gather dimension, but forge both
        # declared input/output shapes coherently in the supplied proof plan.
        proof = replace(proof, steps=tuple(
            replace(s, input_shapes=((18, 2) if s.side == "sm" else (6, 2),),
                    output_shape=(18, 2) if s.side == "sm" else (6, 2))
            if s.step_id in frontier else s for s in proof.steps))
    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_k_rank_contiguous_relation_frontiers(
            proof, (frontier,), ("sharded",), goal_ir=ir)


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
def test_k1_prefix_stays_outside_existing_contiguous_renderer(op):
    with pytest.raises(rc.RelationCompositionError, match="pre-fact has no producer"):
        compile_entry(prefix_ir(1, op))
    # The already-supported singleton K1 entry is unchanged.
    assert compile_entry(entry_ir(1, op))[1].dependent_chain_plan.complete


@pytest.mark.parametrize("op,name", [("FW_maybe_shuffle", "CPKPrefixFW.lean"), ("BW_maybe_unshuffle", "CPKPrefixBW.lean")])
@pytest.mark.parametrize("prefix_reordered", [False, True])
def test_exact_prefix_composed_witness(op, name, prefix_reordered):
    from scripts.tests.cp_k_entry_witness import witness_source
    if prefix_reordered:
        name = name.replace("Prefix", "PrefixReordered")
    source = witness_source(op, prefix=True, prefix_reordered=prefix_reordered)
    ir = prefix_ir(op=op, prefix_reordered=prefix_reordered)
    model, dag = shared_prefix(ir)
    relation = dag.global_relation
    assert relation is not None and relation.dependent_chain_plan is not None
    assert parser.parse_nodes(parser.extract_def_block(source, "smGraph")) == ir.sm_nodes
    assert parser.parse_nodes(parser.extract_def_block(source, "pmGraph")) == ir.pm_nodes
    for segment in relation.dependent_chain_plan.segments:
        assert composer.render_closed_segment(materialize_target_ir(model, 1), relation, segment.segment_id) in source
    assert "def composed" in source and "composed.sound" in source
    assert "ZigzagKRelationWitness.sharded_input" in source and "inhabitedOutput" in source
    assert "sorry" not in source and "axiom " not in source
    assert (Path(__file__).resolve().parent / "fixtures" / name).read_text() == source
