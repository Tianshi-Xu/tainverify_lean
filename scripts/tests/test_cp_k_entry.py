"""Independent CP entry authority; never borrows generated model graphs."""
from dataclasses import replace
import pytest
from trainverify.bridge_emitter.parser import (
    GoalIR, Node, LineageGoal, ReplicaGroup, ReplicaNodeRef,
    InputValueClass, PackedCuContract,
)
from trainverify.bridge_emitter.proof_compiler import compile_proof_plan, build_default_registry
from trainverify.bridge_emitter import relation_compiler as rc, composer


def entry_ir(k=3, op="FW_maybe_shuffle"):
    full, shard = [4*k, 2], [4, 2]
    sm = [Node(0, op, [10, 90], [20], [1, 0])]
    pm = [Node(r, op, [100+r, 90], [200+r], [k, r]) for r in range(k)]
    def group(nodes):
        return (ReplicaGroup(0, 0, op, tuple(ReplicaNodeRef(n.rank, n.outs[0]) for n in nodes)),)
    inputs = {
        10: LineageGoal(10, full, [(r,100+r) for r in range(k)], [shard]*k, 0),
        90: LineageGoal(90, [2], [(0,90)], [[2]]),
        91: LineageGoal(91, [2], [(0,91)], [[2]]),
    }
    return GoalIR(
        n=0, sm_nodes=sm, pm_nodes=pm,
        sm_shapes=[(10,full),(90,[2]),(91,[2])],
        pm_shapes=[(100+r,shard) for r in range(k)]+[(90,[2]),(91,[2])],
        lineage=LineageGoal(20,full,[(r,200+r) for r in range(k)],[shard]*k,0),
        prereqs=list(inputs), init_lineages=inputs, full_init_goal_ids=tuple(inputs),
        sm_graph_ref="CPEntry.smGraph", pm_graph_ref="CPEntry.pmGraph",
        sm_num_ranks=1, pm_num_ranks=k,
        sm_replica_groups=group(sm), pm_replica_groups=group(pm),
        sm_input_value_classes=(InputValueClass("cu",(90,91)),),
        pm_input_value_classes=(InputValueClass("cu",(90,91)),),
        packed_cu_contracts=(PackedCuContract("pm",91,4*k,k),),
        public_statement_uses_faithful_evaluator=True,
    )


def compile_entry(ir):
    proof = compile_proof_plan(ir, build_default_registry())
    if not proof.supported:
        raise rc.RelationCompositionError(str(proof.diagnostics))
    return proof, rc.compile_relation_plan(ir, proof)


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
def test_cp3_entry_reaches_real_closed_segment(op):
    ir = entry_ir(op=op)
    proof, relation = compile_entry(ir)
    assert relation.family == "cp-shuffle-k-entry-boundary"
    assert len(relation.certificates) == 1
    assert relation.certificates[0].input_step_triple == ("init:10","init:100","init:101","init:102")
    chain = relation.dependent_chain_plan
    assert chain is not None and chain.complete
    assert len(chain.segments) == 1
    post = next(f for f in chain.relation_facts if f.kind == "zigzag_k")
    assert post.pm_tids == (200,201,202)
    assert post.full_shape == (12,2) and post.shard_shape == (4,2)
    body = composer.render_closed_segment(ir, relation, chain.segments[0].segment_id)
    assert "ZigzagKRel.of_sharded" in body
    assert "CPEntry.smGraph" in body and "CPEntry.pmGraph" in body
    assert "sorry" not in body and "axiom" not in body
    assert ".zigzagK 20 [200, 201, 202] 90" in composer.render_closed_relation_declarations(chain, "CPEntryProof")


@pytest.mark.parametrize("k", [1,5])
@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
def test_positive_arbitrary_k(k, op):
    ir = entry_ir(k,op)
    _, relation = compile_entry(ir)
    chain = relation.dependent_chain_plan
    assert chain.complete
    body = composer.render_closed_segment(ir,relation,chain.segments[0].segment_id)
    assert "ZigzagKRel.of_sharded" in body
    assert body.count("let smFinal :=") == body.count("let pmFinal :=") == 1
    assert f"have hPm{k-1} : pmFinal {200+k-1}" in body


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
@pytest.mark.parametrize("mutation", [
    "missing_group_sm", "missing_group_pm", "missing_buddy", "duplicate_buddy", "reordered_buddies",
    "wrong_k", "wrong_rank", "wrong_shape", "wrong_tokens", "no_metadata_class", "cross_class",
    "no_metadata_lineage", "no_packed", "cross_packed", "wrong_input", "missing_last_writer",
])
def test_invalid_graph_authority_fails_closed(op, mutation):
    ir = entry_ir(op=op)
    group = ir.pm_replica_groups[0]
    if mutation == "missing_group_sm": ir.sm_replica_groups = ()
    elif mutation == "missing_group_pm": ir.pm_replica_groups = ()
    elif mutation == "missing_buddy": ir.pm_replica_groups = (replace(group,members=group.members[:-1]),)
    elif mutation == "duplicate_buddy": ir.pm_replica_groups = (replace(group,members=group.members[:2]+group.members[:1]),)
    elif mutation == "reordered_buddies": ir.pm_replica_groups = (replace(group,members=tuple(reversed(group.members))),)
    elif mutation == "wrong_k": ir.pm_nodes[-1].params[0] = 5
    elif mutation == "wrong_rank": ir.pm_nodes[-1].rank = 1
    elif mutation == "wrong_shape": ir.pm_shapes[2] = (102,[3,2])
    elif mutation == "wrong_tokens": ir.packed_cu_contracts = (PackedCuContract("pm",91,18,3),)
    elif mutation == "no_metadata_class": ir.pm_input_value_classes = ()
    elif mutation == "cross_class": ir.sm_input_value_classes = (InputValueClass("other",(90,91)),)
    elif mutation == "no_metadata_lineage": del ir.init_lineages[90]
    elif mutation == "no_packed": ir.packed_cu_contracts = ()
    elif mutation == "cross_packed": ir.pm_input_value_classes = (InputValueClass("cu",(90,)),InputValueClass("other",(91,)))
    elif mutation == "wrong_input": ir.pm_nodes[-1].ins[0] = 101
    elif mutation == "missing_last_writer": ir.pm_nodes.pop()
    with pytest.raises((rc.RelationCompositionError, ValueError)):
        proof, relation = compile_entry(ir)
        if relation.dependent_chain_plan is None:
            raise rc.RelationCompositionError("unresolved source")
        composer.render_closed_segment(ir,relation,relation.dependent_chain_plan.segments[0].segment_id)


@pytest.mark.parametrize("mutation", ["stale_digest", "rebind_buddies", "wrong_input_producer", "missing_packed", "wrong_region_k", "wrong_region_tokens", "missing_last_writer"])
def test_renderer_rechecks_authority(mutation):
    ir = entry_ir()
    proof, relation = compile_entry(ir)
    cert = relation.certificates[0]
    chain = relation.dependent_chain_plan
    segment = chain.segments[0]
    if mutation == "stale_digest":
        relation = replace(relation,certificates=(replace(cert,total_tokens=18),))
    elif mutation == "rebind_buddies":
        group = ir.pm_replica_groups[0]
        ir.pm_replica_groups = (replace(group,members=tuple(reversed(group.members))),)
        cert = replace(cert,pm_replica_members=tuple(reversed(cert.pm_replica_members)))
        transition = replace(relation.transition_specs[0],certificate_digest=composer._typed_certificate_digest(cert))
        relation = replace(relation,certificates=(cert,),transition_specs=(transition,))
    elif mutation == "wrong_input_producer":
        ir.pm_nodes[-1].ins[0] = 101
    elif mutation == "missing_packed":
        chain = replace(chain,authority_facts=tuple(a for a in chain.authority_facts if a.kind != "packed_cu"))
        relation = replace(relation,dependent_chain_plan=chain)
    elif mutation.startswith("wrong_region"):
        region = relation.zigzag_regions[0]
        region = replace(region,**({"num_ranks":5} if mutation.endswith("k") else {"total_tokens":18}))
        relation = replace(relation,zigzag_regions=(region,))
    elif mutation == "missing_last_writer":
        ir.pm_nodes.pop()
    with pytest.raises((ValueError,rc.RelationCompositionError)):
        composer.render_closed_segment(ir,relation,segment.segment_id)


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
def test_shared_consumers_reuse_one_entry_boundary(op):
    from dataclasses import fields
    from trainverify.bridge_emitter.model_authority import ModelAuthorityIR, TargetQuery, materialize_target_ir
    from trainverify.bridge_emitter.model_compiler import compile_shared_proof_dag, compile_shared_relation_dag
    ir = entry_ir(op=op)
    targets = {}
    for goal in (0,1):
        payload = {f.name:getattr(ir,f.name) for f in fields(TargetQuery) if hasattr(ir,f.name)}
        payload.update(goal_id=goal,public_statement_digest="synthetic-entry",prereqs=tuple(ir.prereqs))
        targets[goal] = TargetQuery(**payload)
    payload = {f.name:getattr(ir,f.name) for f in fields(ModelAuthorityIR) if hasattr(ir,f.name)}
    model = ModelAuthorityIR(**payload,model_id="cp3-entry",root=str(__file__),targets=targets,aggregate=None)
    dag = compile_shared_relation_dag(model,compile_shared_proof_dag(model,build_default_registry()))
    assert len(dag.certificates) == len(dag.transitions) == 1
    assert dag.projections[0].certificate_keys == dag.projections[1].certificate_keys
    relation = dag.global_relation
    assert relation is not None and relation.dependent_chain_plan.complete
    assert all(dag.facts[p.terminal_fact_key].layout == "zigzag_k" for p in dag.projections.values())
    body = composer.render_closed_segment(materialize_target_ir(model,0),relation,relation.dependent_chain_plan.segments[0].segment_id)
    assert "ZigzagKRel.of_sharded" in body


def test_semantic_rank_order_is_not_graph_index_order():
    ir = entry_ir()
    ir.pm_nodes = [ir.pm_nodes[2],ir.pm_nodes[0],ir.pm_nodes[1]]
    _, relation = compile_entry(ir)
    cert = relation.certificates[0]
    assert cert.output_step_triple == ("sm:0:0","pm:1:0","pm:2:0","pm:0:0")
    assert relation.transition_specs[0].pm_node_indices == (0,1,2)
    body = composer.render_closed_segment(ir,relation,relation.dependent_chain_plan.segments[0].segment_id)
    assert "have hPm2 : pmFinal 202" in body


def test_zigzag_boundary_cannot_discharge_ordinary_public_goal():
    ir = entry_ir()
    _, relation = compile_entry(ir)
    with pytest.raises(ValueError,match="joined or ordered-sharded terminal"):
        composer.render_closed_public_theorem(ir,relation,"CPEntryProof")


@pytest.mark.parametrize("op,name", [("FW_maybe_shuffle","CPKEntryFW.lean"),("BW_maybe_unshuffle","CPKEntryBW.lean")])
def test_exact_synthetic_graph_witness(op,name):
    from pathlib import Path
    from scripts.tests.cp_k_entry_witness import witness_source
    from trainverify.bridge_emitter import parser
    source = witness_source(op)
    ir = entry_ir(op=op)
    assert parser.parse_nodes(parser.extract_def_block(source,"smGraph")) == ir.sm_nodes
    assert parser.parse_nodes(parser.extract_def_block(source,"pmGraph")) == ir.pm_nodes
    assert "sorry" not in source and "axiom " not in source
    assert "ZigzagKRelationWitness.sharded_input" in source
    assert "inhabitedOutput" in source
    fixture = Path(__file__).resolve().parent / "fixtures" / name
    assert fixture.read_text() == source


def test_forged_plan_input_binding_is_rejected():
    ir = entry_ir()
    proof = compile_proof_plan(ir,build_default_registry())
    last = next(s for s in proof.steps if s.step_id == "pm:2:0")
    forged = replace(last,input_bindings=("init:101","init:90"))
    proof = replace(proof,steps=tuple(forged if s == last else s for s in proof.steps))
    with pytest.raises(rc.RelationCompositionError,match="producer"):
        rc.compile_k_shuffle_entry_boundary(ir,proof)


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
@pytest.mark.parametrize("field,value", [("total_tokens",18),("num_ranks",5),("metadata_source","other")])
def test_coordinated_metadata_payload_cannot_replace_graph_authority(op, field, value):
    ir = entry_ir(op=op)
    _, relation = compile_entry(ir)
    cert = replace(relation.certificates[0], **{field:value})
    region = replace(relation.zigzag_regions[0], **{field:value})
    chain = relation.dependent_chain_plan
    # Keep the forged certificate, digest, region and packed authority coherent.
    authority = tuple(replace(a, **{field:value})
                      if a.kind == "packed_cu" and field != "metadata_source" else a
                      for a in chain.authority_facts)
    transition = replace(relation.transition_specs[0],
                         certificate_digest=composer._typed_certificate_digest(cert))
    relation = replace(relation, certificates=(cert,), zigzag_regions=(region,),
                       transition_specs=(transition,),
                       dependent_chain_plan=replace(chain,authority_facts=authority))
    with pytest.raises(ValueError, match="certificate does not match graph authority"):
        composer.render_closed_segment(ir,relation,chain.segments[0].segment_id)


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
def test_cross_buddy_source_overwrite_has_no_ordinary_input_authority(op):
    ir = entry_ir(op=op)
    ir.pm_nodes[0].outs[0] = 101
    group = ir.pm_replica_groups[0]
    ir.pm_replica_groups = (replace(group,members=(ReplicaNodeRef(0,101),*group.members[1:])),)
    ir.lineage.tps[0] = (0,101)
    with pytest.raises(rc.RelationCompositionError,match="pre-fact has no producer"):
        compile_entry(ir)
