"""Actual entry/exit collective chain, without synthetic intermediate InitGoals."""
from dataclasses import fields, replace
import pytest
from scripts.tests.test_cp_k_entry import entry_ir, compile_entry
from trainverify.bridge_emitter import composer, relation_compiler as rc
from trainverify.bridge_emitter.parser import Node, LineageGoal, ReplicaGroup, ReplicaNodeRef


def exit_ir(k=3, op="FW_maybe_shuffle", reordered=True, entry_reordered=False):
    ir = entry_ir(k, op)
    exit_op = "FW_maybe_unshuffle" if op == "FW_maybe_shuffle" else "BW_maybe_shuffle"
    sm = Node(0, exit_op, [20, 90], [30], [1, 0])
    pm = [Node(r, exit_op, [200+r, 90], [300+r], [k, r]) for r in range(k)]
    def group(nodes):
        return ReplicaGroup(1, 0, exit_op, tuple(ReplicaNodeRef(n.rank, n.outs[0]) for n in nodes))
    ir.sm_replica_groups += (group([sm]),)
    ir.pm_replica_groups += (group(pm),)
    if entry_reordered:
        ir.pm_nodes = ir.pm_nodes[-1:] + ir.pm_nodes[:-1]
    ir.sm_nodes.append(sm)
    ir.pm_nodes += pm[-1:] + pm[:-1] if reordered else pm
    ir.lineage = LineageGoal(30, [4*k, 2], [(r,300+r) for r in range(k)], [[4,2]]*k, 0)
    return ir


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
def test_cp3_exit_composes_actual_entry(op):
    ir = exit_ir(op=op)
    _, relation = compile_entry(ir)
    chain = relation.dependent_chain_plan
    assert chain is not None and chain.complete
    assert len(relation.certificates) == len(chain.segments) == 2
    entry = next(c for c in relation.certificates if c.post_layout == "zigzag_k")
    exit = next(c for c in relation.certificates if c.pre_layout == "zigzag_k")
    assert entry.output_fact == exit.input_fact
    assert composer._closed_segment_family_imports((exit.rule_id,), (exit.lean_theorem,)) == ("denote.ZigzagKExit",)
    assert exit.output_fact.layout == "sharded" and exit.output_fact.gather_dim == 0
    assert exit.output_step_triple == ("sm:1:0", "pm:4:0", "pm:5:0", "pm:3:0")
    assert set(ir.init_lineages) == {10,90,91}
    bodies = [composer.render_closed_segment(ir, relation, s.segment_id) for s in chain.segments]
    assert "ZigzagKRel.of_sharded" in bodies[0]
    assert "to_sharded_unshuffle_single" in bodies[1]
    assert bodies[1].count("foldl_faithful_middle_writer") == 4
    assert "RelationState.Holds.fold_frame" in bodies[1]


@pytest.mark.parametrize("op,name", [("FW_maybe_shuffle","CPKExitFW.lean"),("BW_maybe_unshuffle","CPKExitBW.lean")])
def test_exact_exit_graph_and_public_witness(op,name):
    from pathlib import Path
    from scripts.tests.cp_k_entry_witness import witness_source
    from trainverify.bridge_emitter import parser
    source = witness_source(op, exit=True)
    ir = exit_ir(op=op)
    assert parser.parse_nodes(parser.extract_def_block(source,"smGraph")) == ir.sm_nodes
    assert parser.parse_nodes(parser.extract_def_block(source,"pmGraph")) == ir.pm_nodes
    assert "import denote.ZigzagKExit" in source
    assert "to_sharded_unshuffle_single" in source
    assert "ZigzagKRelationWitness.sharded_input" in source
    assert "theorem prove_goal_0_closed : CPEntry.exitStatement" in source
    assert "CoarseLineageHoldsWithInitDistributedFaithfulWithContract" in source
    assert "exact htarget.full_value" in source
    assert "inhabitedOutput" in source
    assert "theorem publicInputs" in source
    assert "theorem inhabitedPublicOutput : InitGoalHolds" in source
    assert "shapeEnvOfList smShapes" in source
    assert "gatherDim := some" not in source and "gatherDim := none" not in source
    assert "sorry" not in source and "axiom " not in source
    assert (Path(__file__).parent / "fixtures" / name).read_text() == source


def shared_exit(ir):
    from trainverify.bridge_emitter.model_authority import ModelAuthorityIR, TargetQuery
    from trainverify.bridge_emitter.model_compiler import compile_shared_proof_dag, compile_shared_relation_dag
    from trainverify.bridge_emitter.proof_compiler import build_default_registry
    targets = {}
    for goal, lineage in enumerate((entry_ir(ir.pm_num_ranks).lineage, ir.lineage)):
        payload = {f.name: getattr(ir, f.name) for f in fields(TargetQuery) if hasattr(ir, f.name)}
        payload.update(goal_id=goal, lineage=lineage, public_statement_digest="synthetic-entry-exit", prereqs=tuple(ir.prereqs))
        targets[goal] = TargetQuery(**payload)
    payload = {f.name: getattr(ir, f.name) for f in fields(ModelAuthorityIR) if hasattr(ir, f.name)}
    model = ModelAuthorityIR(**payload, model_id="cp-k-exit", root=__file__, targets=targets, aggregate=None)
    return model, compile_shared_relation_dag(model, compile_shared_proof_dag(model, build_default_registry()))


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
@pytest.mark.parametrize("k", [1,3,5])
@pytest.mark.parametrize("reordered,entry_reordered", [(False,False),(True,False),(False,True),(True,True)])
def test_shared_entry_exit_one_entry_dag(op,k,reordered,entry_reordered):
    from trainverify.bridge_emitter.external_pre_fact_selector import select_unproduced_external_pre_facts
    ir = exit_ir(k,op,reordered,entry_reordered)
    model, dag = shared_exit(ir)
    assert len(dag.certificates) == len(dag.transitions) == 2
    assert len(dag.projections[0].certificate_keys) == 1
    assert set(dag.projections[0].certificate_keys) < set(dag.projections[1].certificate_keys)
    assert dag.facts[dag.projections[0].terminal_fact_key].layout == "zigzag_k"
    assert dag.facts[dag.projections[1].terminal_fact_key].layout == "sharded"
    relation = dag.global_relation
    chain = relation.dependent_chain_plan
    assert chain.complete and len(chain.retained_target_fact_ids) == 2
    entry = next(t for t in relation.transition_specs if t.post_facts[0].layout == "zigzag_k")
    exit = next(t for t in relation.transition_specs if t.pre_facts[0].layout == "zigzag_k")
    assert entry.post_facts == exit.pre_facts
    assert exit.pre_facts[0] not in select_unproduced_external_pre_facts(relation.transition_specs)
    assert dict(relation.dependency_plan.dependencies)[exit.transition_id] == (entry.transition_id,)
    assert len(relation.zigzag_regions) == 1
    assert [s.pm_range for s in chain.segments] == [(0,k),(k,2*k)]
    assert all(f.kind != "zigzag_k" for f in chain.relation_facts if f.fact_id in chain.states[0].fact_ids)
    for segment in chain.segments:
        body = composer.render_closed_segment(ir,relation,segment.segment_id)
        assert "sorry" not in body and "axiom " not in body


@pytest.mark.parametrize("op", ["FW_maybe_shuffle", "BW_maybe_unshuffle"])
@pytest.mark.parametrize("mutation", ["cp_rank", "metadata", "packed_endpoint", "packed_rank", "odd", "zero", "groups", "alias", "metadata_clobber", "source_clobber", "output_clobber", "init_reseed"])
def test_exit_invalid_authority_fails_closed(op,mutation):
    from trainverify.bridge_emitter.parser import PackedCuContract, InputValueClass
    ir = exit_ir(op=op)
    exits = ir.pm_nodes[3:]
    if mutation == "cp_rank": exits[0].params[1] = 1  # rank=2 and shapes remain unchanged
    elif mutation == "metadata":
        ir.sm_shapes.append((92,[2])); ir.pm_shapes.append((92,[2]))
        ir.init_lineages[92] = LineageGoal(92,[2],[(0,92)],[[2]])
        ir.prereqs.append(92); ir.full_init_goal_ids += (92,)
        for side in ("sm", "pm"):
            setattr(ir, side+"_input_value_classes", getattr(ir,side+"_input_value_classes")+(InputValueClass("other",(92,)),))
        ir.packed_cu_contracts += (PackedCuContract("pm",92,12,3),)
        for n in [ir.sm_nodes[-1],*exits]: n.ins[1] = 92
    elif mutation.startswith("packed_"):
        ir.packed_cu_contracts = (PackedCuContract("pm",91,18 if mutation == "packed_endpoint" else 12,5 if mutation == "packed_rank" else 3),)
    elif mutation in {"odd", "zero"}:
        local = 3 if mutation == "odd" else 0
        ir.sm_shapes[0] = (10,[3*local,2])
        for r in range(3): ir.pm_shapes[r] = (100+r,[local,2])
        ir.init_lineages[10] = LineageGoal(10,[3*local,2],[(r,100+r) for r in range(3)],[[local,2]]*3,0)
        ir.lineage = LineageGoal(30,[3*local,2],[(r,300+r) for r in range(3)],[[local,2]]*3,0)
        ir.packed_cu_contracts = (PackedCuContract("pm",91,3*local,3),)
    elif mutation == "groups":
        ir.pm_replica_groups = (ir.pm_replica_groups[0],replace(ir.pm_replica_groups[1],members=tuple(reversed(ir.pm_replica_groups[1].members))))
    elif mutation == "alias": ir.pm_input_value_classes = (InputValueClass("cu",(90,)),InputValueClass("other",(91,)))
    elif mutation == "metadata_clobber": ir.pm_nodes.insert(3,Node(0,"FW_contiguous",[91],[90],None))
    elif mutation in {"source_clobber", "output_clobber"}:
        n = exits[0]
        n.outs[0] = 200 if mutation == "source_clobber" else 100
        g = ir.pm_replica_groups[1]
        ir.pm_replica_groups = (ir.pm_replica_groups[0],replace(g,members=tuple(ReplicaNodeRef(m.rank,n.outs[0]) if m.rank == 2 else m for m in g.members)))
        ir.lineage.tps[2] = (2,n.outs[0])
    elif mutation == "init_reseed":
        ir.sm_nodes = ir.sm_nodes[1:]; ir.pm_nodes = exits
        ir.sm_shapes.append((20,[12,2])); ir.pm_shapes += [(200+r,[4,2]) for r in range(3)]
        ir.init_lineages[20] = LineageGoal(20,[12,2],[(r,200+r) for r in range(3)],[[4,2]]*3,0)
        ir.prereqs.append(20); ir.full_init_goal_ids += (20,)
    with pytest.raises((ValueError,rc.RelationCompositionError)):
        _, relation = compile_entry(ir)
        assert relation.dependent_chain_plan is not None
        for s in relation.dependent_chain_plan.segments:
            composer.render_closed_segment(ir,relation,s.segment_id)


@pytest.mark.parametrize("mutation", ["region_alias", "live_alias"])
def test_exit_renderer_requires_entry_region_and_live_alias(mutation):
    ir = exit_ir()
    _, relation = compile_entry(ir)
    chain = relation.dependent_chain_plan
    exit_segment = chain.segments[-1]
    if mutation == "region_alias":
        relation = replace(relation, zigzag_regions=(
            replace(relation.zigzag_regions[0], alias_tids=()),))
        message = "metadata region authority"
    else:
        alias_ids = {a.fact_id for a in chain.authority_facts if a.kind == "tensor_eq"}
        chain = replace(chain, states=tuple(
            replace(s, fact_ids=tuple(f for f in s.fact_ids if f not in alias_ids))
            if s.state_id == exit_segment.pre_state_id else s for s in chain.states))
        relation = replace(relation, dependent_chain_plan=chain)
        message = "packed/alias authority not live"
    with pytest.raises(ValueError, match=message):
        composer.render_closed_segment(ir, relation, exit_segment.segment_id)


@pytest.mark.parametrize("mutation", ["cp_rank", "metadata", "packed", "region", "alias", "producer", "clobber"])
def test_exit_renderer_revalidates_coordinated_mutations(mutation):
    ir = exit_ir()
    _, relation = compile_entry(ir)
    chain = relation.dependent_chain_plan
    cert = next(c for c in relation.certificates if isinstance(c,rc.KRankUnshuffleExitCertificate))
    if mutation == "cp_rank": ir.pm_nodes[3].params[1] = 1
    elif mutation == "metadata": cert = replace(cert,node_metadata_tid=91)
    elif mutation == "packed":
        cert = replace(cert,total_tokens=18)
        chain = replace(chain,authority_facts=tuple(replace(a,total_tokens=18) if a.kind == "packed_cu" else a for a in chain.authority_facts))
        relation = replace(relation,dependent_chain_plan=chain,zigzag_regions=(replace(relation.zigzag_regions[0],total_tokens=18),))
    elif mutation == "region":
        relation = replace(relation,zigzag_regions=(replace(relation.zigzag_regions[0],num_ranks=5),))
        cert = replace(cert,num_ranks=5)
    elif mutation == "alias":
        chain = replace(chain,authority_facts=tuple(a for a in chain.authority_facts if a.kind != "tensor_eq"))
        relation = replace(relation,dependent_chain_plan=chain)
    elif mutation == "producer": ir.pm_nodes[3].ins[0] = 201
    elif mutation == "clobber": ir.pm_nodes[3].outs[0] = 200
    relation = replace(relation,certificates=tuple(cert if isinstance(c,rc.KRankUnshuffleExitCertificate) else c for c in relation.certificates),transition_specs=tuple(replace(t,certificate_digest=composer._typed_certificate_digest(cert)) if t.rule_id == cert.rule_id else t for t in relation.transition_specs))
    with pytest.raises((ValueError,rc.RelationCompositionError)):
        composer.render_closed_segment(ir,relation,chain.segments[-1].segment_id)
