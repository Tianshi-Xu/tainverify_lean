"""One CP3 compiler tracer: ordinary Q -> entry -> attention -> ordinary exit.

The six graph parameters encode Q/KV heads, QK/V channels, causal and window.
Default scale, zero dropout and no ALiBi are the restricted source interpretation
of this operator, not extra invented Node parameters. No intermediate InitGoal
is supplied, and no numerical/source witness substitutes for graph compilation.
"""
from dataclasses import fields, replace

import pytest

from scripts.tests.test_cp_k_entry import entry_ir
from trainverify.bridge_emitter import composer, parser
from trainverify.bridge_emitter.external_pre_fact_selector import (
    select_unproduced_external_pre_facts,
)
from trainverify.bridge_emitter.model_authority import ModelAuthorityIR, TargetQuery
from trainverify.bridge_emitter.model_compiler import (
    compile_shared_proof_dag,
    compile_shared_relation_dag,
)
from trainverify.bridge_emitter.proof_compiler import build_default_registry


def attention_ir(num_ranks=3):
    """Actual ordered CP3 buddies, GQA 2:1, local L=4, QK dim=2, V dim=3.

    Execution order [2,0,1] deliberately differs from semantic group order.
    K/V are separate ordinary dim-zero InitGoals; only Q passes through entry.
    Metadata 90 is shared by both attention operands and both boundaries, with
    the existing entry helper's public packed contract on its value alias 91.
    """
    ir = entry_ir(num_ranks)
    q_full, q_local = [4 * num_ranks, 2, 2], [4, 2, 2]
    ir.sm_shapes[0] = (10, q_full)
    ir.pm_shapes[:num_ranks] = [(100 + r, q_local) for r in range(num_ranks)]
    ir.init_lineages[10] = parser.LineageGoal(
        10, q_full, [(r, 100 + r) for r in range(num_ranks)], [q_local] * num_ranks, 0,
    )
    for tid, base, full, local in (
        (11, 110, [4 * num_ranks, 1, 2], [4, 1, 2]),
        (12, 120, [4 * num_ranks, 1, 3], [4, 1, 3]),
    ):
        ir.sm_shapes.append((tid, full))
        ir.pm_shapes.extend((base + r, local) for r in range(num_ranks))
        ir.init_lineages[tid] = parser.LineageGoal(
            tid, full, [(r, base + r) for r in range(num_ranks)], [local] * num_ranks, 0,
        )
    ir.prereqs = list(ir.init_lineages)
    ir.full_init_goal_ids = tuple(ir.prereqs)
    parameters = [2, 1, 2, 3, 1, 0]
    sm_attn = parser.Node(0, "FW_attn_zigzag", [20, 11, 12, 90, 90], [30], parameters)
    pm_attn = [
        parser.Node(r, "FW_attn_zigzag", [200 + r, 110 + r, 120 + r, 90, 90],
                    [300 + r], list(parameters))
        for r in range(num_ranks)
    ]
    sm_exit = parser.Node(0, "FW_maybe_unshuffle", [30, 90], [40], [1, 0])
    pm_exit = [
        parser.Node(r, "FW_maybe_unshuffle", [300 + r, 90], [400 + r], [num_ranks, r])
        for r in range(num_ranks)
    ]
    for cid, sm, pm in ((1, sm_attn, pm_attn), (2, sm_exit, pm_exit)):
        def group(nodes):
            return parser.ReplicaGroup(
                cid, 0, sm.op,
                tuple(parser.ReplicaNodeRef(n.rank, n.outs[0]) for n in nodes),
            )
        ir.sm_replica_groups += (group([sm]),)
        ir.pm_replica_groups += (group(pm),)
    ir.sm_nodes += [sm_attn, sm_exit]
    ir.pm_nodes = [ir.pm_nodes[r] for r in (num_ranks - 1, *range(num_ranks - 1))]
    ir.pm_nodes += [pm_attn[r] for r in (num_ranks - 1, *range(num_ranks - 1))]
    ir.pm_nodes += [pm_exit[r] for r in (num_ranks - 1, *range(num_ranks - 1))]
    ir.lineage = parser.LineageGoal(
        40, [4 * num_ranks, 2, 3], [(r, 400 + r) for r in range(num_ranks)], [[4, 2, 3]] * num_ranks, 0,
    )
    ir.sm_graph_ref = "CPKAttention.smGraph"
    ir.pm_graph_ref = "CPKAttention.pmGraph"
    return ir


def attention_model(ir):
    """Exit first: compile the maximal closure, then reuse its two prefixes."""
    num_ranks = ir.pm_num_ranks
    lineages = (
        ir.lineage,
        parser.LineageGoal(20, [4 * num_ranks, 2, 2], [(r, 200 + r) for r in range(num_ranks)],
                           [[4, 2, 2]] * num_ranks, 0),
        parser.LineageGoal(30, [4 * num_ranks, 2, 3], [(r, 300 + r) for r in range(num_ranks)],
                           [[4, 2, 3]] * num_ranks, 0),
    )
    targets = {}
    for goal_id, lineage in enumerate(lineages):
        payload = {f.name: getattr(ir, f.name) for f in fields(TargetQuery) if hasattr(ir, f.name)}
        payload.update(goal_id=goal_id, lineage=lineage, prereqs=tuple(ir.prereqs),
                       public_statement_digest=f"synthetic-cp3-attention-{goal_id}")
        targets[goal_id] = TargetQuery(**payload)
    payload = {f.name: getattr(ir, f.name) for f in fields(ModelAuthorityIR) if hasattr(ir, f.name)}
    return ModelAuthorityIR(**payload, model_id="cp3-k-attention", root=__file__,
                            targets=targets, aggregate=None)


def test_cp3_attention_public_fixture_matches_generator():
    from pathlib import Path
    from scripts.tests.cp_k_attention_witness import witness_source
    fixture = Path(__file__).with_name("fixtures") / "CPKAttentionFW.lean"
    assert fixture.read_text() == witness_source()


def _attention_segment():
    ir = attention_ir()
    model = attention_model(ir)
    relation = compile_shared_relation_dag(
        model, compile_shared_proof_dag(model, build_default_registry())).global_relation
    return ir, relation, relation.dependent_chain_plan.segments[1]


@pytest.mark.parametrize("kind", ["packed", "alias", "cross metadata"])
def test_attention_renderer_rejects_nonlive_metadata_authority(kind):
    ir, relation, segment = _attention_segment()
    chain = relation.dependent_chain_plan
    def wanted(a):
        if kind == "packed":
            return a.kind == "packed_cu"
        return a.kind == "tensor_eq" and a.left_side == ("pm" if kind == "alias" else "sm")
    authority = next(a for a in chain.authority_facts if wanted(a))
    states = tuple(replace(s, fact_ids=tuple(f for f in s.fact_ids if f != authority.fact_id))
                   if s.state_id in (segment.pre_state_id, segment.post_state_id) else s
                   for s in chain.states)
    corrupt = replace(relation, dependent_chain_plan=replace(chain, states=states))
    with pytest.raises(ValueError, match=kind + " authority not live"):
        composer.render_closed_segment(ir, corrupt, segment.segment_id)


def test_attention_renderer_rejects_region_alias_loss():
    ir, relation, segment = _attention_segment()
    corrupt = replace(relation, zigzag_regions=(replace(relation.zigzag_regions[0], alias_tids=()),))
    with pytest.raises(ValueError, match="metadata region authority mismatch"):
        composer.render_closed_segment(ir, corrupt, segment.segment_id)


def test_cp5_attention_complete_shared_dag():
    ir = attention_ir(5)
    model = attention_model(ir)
    dag = compile_shared_relation_dag(model, compile_shared_proof_dag(model, build_default_registry()))
    relation = dag.global_relation
    assert relation is not None and relation.dependent_chain_plan.complete
    assert len(dag.certificates) == 3
    assert [s.pm_range for s in relation.dependent_chain_plan.segments] == [(0, 5), (5, 10), (10, 15)]
    rendered = "\n".join(composer.render_closed_segment(ir, relation, s.segment_id)
                         for s in relation.dependent_chain_plan.segments)
    assert "sourceOutput_eq_collective" in rendered


def test_cp3_attention_complete_shared_dag_from_ordinary_inputs():
    ir = attention_ir()
    # Exercise existing graph syntax/parser before the real planner, not a mock.
    for side in ("sm", "pm"):
        nodes = getattr(ir, side + "_nodes")
        source = f"def {side}Graph : GraphDecl where\n  nodes := [" + ", ".join(
            composer._node_text(n) for n in nodes
        ) + "]\n"
        assert parser.parse_nodes(parser.extract_def_block(source, side + "Graph")) == nodes
    assert set(ir.init_lineages) == {10, 11, 12, 90, 91}
    assert not {20, 30, 40} & set(ir.init_lineages)
    model = attention_model(ir)
    proof_dag = compile_shared_proof_dag(model, build_default_registry())
    assert all(p.supported for p in proof_dag.plans.values())
    steps = {s.step_id: s for s in proof_dag.plans[0].steps}
    assert tuple((m.rank, m.primary_out_tid) for m in ir.pm_replica_groups[1].members) == (
        (0, 300), (1, 301), (2, 302),
    )
    assert steps["sm:1:0"].parameters == (2, 1, 2, 3, 1, 0)
    assert steps["sm:1:0"].input_bindings == (
        "sm:0:0", "init:11", "init:12", "init:90", "init:90",
    )
    for r, index in enumerate((4, 5, 3)):
        assert steps[f"pm:{index}:0"].input_bindings == (
            f"pm:{index - 3}:0", f"init:{110 + r}", f"init:{120 + r}",
            "init:90", "init:90",
        )
        assert steps[f"pm:{index}:0"].output_shape == (4, 2, 3)

    # Positive desired behavior. RED must be here, at attention normalization.
    dag = compile_shared_relation_dag(model, proof_dag)
    relation = dag.global_relation
    assert relation is not None
    chain = relation.dependent_chain_plan
    assert chain is not None and chain.complete
    assert len(dag.certificates) == len(dag.transitions) == len(chain.segments) == 3
    assert [s.pm_range for s in chain.segments] == [(0, 3), (3, 6), (6, 9)]
    assert len(chain.retained_target_fact_ids) == 3
    assert set(dag.projections[1].certificate_keys) < set(dag.projections[2].certificate_keys)
    assert set(dag.projections[2].certificate_keys) < set(dag.projections[0].certificate_keys)
    assert [dag.facts[dag.projections[i].terminal_fact_key].layout for i in (1, 2, 0)] == [
        "zigzag_k", "zigzag_k", "sharded",
    ]
    entry, attn, exit = (
        next(t for t in relation.transition_specs if t.post_facts[0].step_triple[0] == step)
        for step in ("sm:0:0", "sm:1:0", "sm:2:0")
    )
    assert entry.post_facts[0] in attn.pre_facts
    assert attn.post_facts == exit.pre_facts
    ordinary_kv = {f for f in attn.pre_facts if f.layout == "sharded"}
    assert {f.step_triple for f in ordinary_kv} == {
        ("init:11", "init:110", "init:111", "init:112"),
        ("init:12", "init:120", "init:121", "init:122"),
    }
    assert all(f.gather_dim == 0 for f in ordinary_kv)
    external = select_unproduced_external_pre_facts(relation.transition_specs)
    assert ordinary_kv <= set(external)
    assert entry.post_facts[0] not in external and attn.post_facts[0] not in external
    assert relation.dependency_plan is not None
    dependencies = dict(relation.dependency_plan.dependencies)
    assert dependencies[attn.transition_id] == (entry.transition_id,)
    assert dependencies[exit.transition_id] == (attn.transition_id,)
    assert len(relation.zigzag_regions) == 1
    region = relation.zigzag_regions[0]
    assert (region.metadata_source, region.contract_metadata_tid,
            region.total_tokens, region.num_ranks) == ("cu", 91, 12, 3)
    assert {entry.post_facts[0].step_triple, attn.post_facts[0].step_triple} <= set(region.frontier_triples)
    assert all(f.kind != "zigzag_k" for f in chain.relation_facts
               if f.fact_id in chain.states[0].fact_ids)
    rendered = "\n".join(composer.render_closed_segment(ir, relation, s.segment_id)
                         for s in chain.segments)
    assert "ZigzagKRel.of_sharded" in rendered
    assert "attn_zigzag_sharded_kv_single" in rendered
    assert "sourceOutput_eq_collective" in rendered
    assert "to_sharded_unshuffle_single" in rendered
    assert "sorry" not in rendered and "axiom " not in rendered


def _attention_plan(ir):
    from trainverify.bridge_emitter.proof_compiler import compile_proof_plan
    return compile_proof_plan(ir, build_default_registry())


def _advance_attention(ir, proof):
    from trainverify.bridge_emitter import relation_compiler as rc
    return rc.advance_k_rank_attention_frontiers(
        ir, proof, (("sm:1:0", "pm:4:0", "pm:5:0", "pm:3:0"),), ("zigzag_k",))


@pytest.mark.parametrize("mutation", [
    "missing_sm_group", "missing_pm_group", "reverse_group", "duplicate_buddy",
    "wrong_group_op", "foreign_metadata", "no_packed", "wrong_tokens", "no_value_class",
    "metadata_shape", "causal", "window", "extra_parameter", "nondivisible_gqa",
    "kv_lineage_order", "kv_not_public", "kv_replicated", "kv_wrong_axis",
])
def test_cp3_attention_rejects_graph_authority_mutations(mutation):
    from trainverify.bridge_emitter import relation_compiler as rc
    ir = attention_ir()
    group = ir.pm_replica_groups[1]
    if mutation == "missing_sm_group":
        ir.sm_replica_groups = (ir.sm_replica_groups[0], ir.sm_replica_groups[2])
    elif mutation == "missing_pm_group":
        ir.pm_replica_groups = (ir.pm_replica_groups[0], ir.pm_replica_groups[2])
    elif mutation in {"reverse_group", "duplicate_buddy", "wrong_group_op"}:
        change = (replace(group, members=tuple(reversed(group.members))) if mutation == "reverse_group"
                  else replace(group, members=(group.members[0],) * 3) if mutation == "duplicate_buddy"
                  else replace(group, irname="FW_maybe_shuffle"))
        ir.pm_replica_groups = (ir.pm_replica_groups[0], change, ir.pm_replica_groups[2])
    elif mutation == "foreign_metadata":
        for n in ir.sm_nodes + ir.pm_nodes:
            if n.op == "FW_attn_zigzag":
                n.ins[4] = 91
    elif mutation == "no_packed":
        ir.packed_cu_contracts = ()
    elif mutation == "wrong_tokens":
        ir.packed_cu_contracts = (replace(ir.packed_cu_contracts[0], total_tokens=24),)
    elif mutation == "no_value_class":
        ir.pm_input_value_classes = ()
    elif mutation == "metadata_shape":
        ir.init_lineages[90] = replace(ir.init_lineages[90], tsShape=[3], tpShapes=[[3]])
    elif mutation in {"causal", "window", "extra_parameter", "nondivisible_gqa"}:
        for n in ir.sm_nodes + ir.pm_nodes:
            if n.op == "FW_attn_zigzag":
                if mutation == "causal": n.params[4] = 0
                elif mutation == "window": n.params[5] = 1
                elif mutation == "extra_parameter": n.params.append(0)
                else: n.params[1] = 3
    elif mutation == "kv_lineage_order":
        ir.init_lineages[11] = replace(ir.init_lineages[11], tps=list(reversed(ir.init_lineages[11].tps)))
    elif mutation == "kv_not_public":
        ir.full_init_goal_ids = tuple(t for t in ir.full_init_goal_ids if t != 11)
    elif mutation == "kv_replicated":
        ir.init_lineages[11] = replace(ir.init_lineages[11], replicated=True)
    elif mutation == "kv_wrong_axis":
        ir.init_lineages[11] = replace(ir.init_lineages[11], gatherDim=1)
    with pytest.raises(rc.RelationCompositionError):
        _advance_attention(ir, _attention_plan(ir))


def test_cp3_attention_rejects_nondivisible_gqa_with_coherent_shapes():
    from trainverify.bridge_emitter import relation_compiler as rc
    ir = attention_ir()
    for tid, base, channels in ((11, 110, 2), (12, 120, 3)):
        full, local = [12, 3, channels], [4, 3, channels]
        ir.sm_shapes = [(t, full if t == tid else sh) for t, sh in ir.sm_shapes]
        ir.pm_shapes = [(t, local if base <= t < base + 3 else sh) for t, sh in ir.pm_shapes]
        ir.init_lineages[tid] = replace(ir.init_lineages[tid], tsShape=full, tpShapes=[local] * 3)
    for node in ir.sm_nodes + ir.pm_nodes:
        if node.op == "FW_attn_zigzag":
            node.params[1] = 3
    proof = _attention_plan(ir)
    assert proof.supported
    with pytest.raises(rc.RelationCompositionError, match="positive GQA dimensions"):
        _advance_attention(ir, proof)


@pytest.mark.parametrize("mutation", ["producer", "writer", "rank_order", "shape", "parameters"])
def test_cp3_attention_rejects_forged_plan(mutation):
    from trainverify.bridge_emitter import relation_compiler as rc
    ir = attention_ir()
    proof = _attention_plan(ir)
    step = next(s for s in proof.steps if s.step_id == "pm:4:0")
    if mutation == "producer":
        changed = replace(step, input_bindings=(step.input_bindings[0], "init:100", *step.input_bindings[2:]))
    elif mutation == "writer":
        changed = replace(step, output_tid=999)
    elif mutation == "rank_order":
        changed = replace(step, rank=1)
    elif mutation == "shape":
        changed = replace(step, output_shape=(4, 2, 2))
    else:
        changed = replace(step, parameters=(2, 1, 2, 3, 0, 0))
    forged = replace(proof, steps=tuple(changed if s.step_id == step.step_id else s for s in proof.steps))
    with pytest.raises(rc.RelationCompositionError):
        _advance_attention(ir, forged)


@pytest.mark.parametrize("source", ["q_init", "q_entry"])
def test_cp3_attention_rejects_k_reseed_even_when_shapes_match(source):
    from trainverify.bridge_emitter import relation_compiler as rc
    ir = attention_ir()
    # Equal Q/K heads ensure rejection is about authority, not a shape mismatch.
    full, local = [12, 1, 2], [4, 1, 2]
    ir.sm_shapes[0] = (10, full)
    ir.pm_shapes[:3] = [(100 + r, local) for r in range(3)]
    ir.init_lineages[10] = replace(ir.init_lineages[10], tsShape=full, tpShapes=[local] * 3)
    ir.lineage = replace(ir.lineage, tsShape=[12, 1, 3], tpShapes=[[4, 1, 3]] * 3)
    for n in ir.sm_nodes + ir.pm_nodes:
        if n.op == "FW_attn_zigzag":
            n.params[0] = 1
            n.ins[1] = (10 if n is ir.sm_nodes[1] else 100 + n.rank) if source == "q_init" else n.ins[0]
    proof = _attention_plan(ir)
    assert proof.supported
    with pytest.raises(rc.RelationCompositionError, match="K/V may not reseed Q|K/V must be ordinary external"):
        _advance_attention(ir, proof)


def test_cp3_attention_certificate_and_exit_render_without_attention_backend():
    from trainverify.bridge_emitter import relation_compiler as rc
    ir = attention_ir()
    proof = _attention_plan(ir)
    certs, frontiers, layouts = _advance_attention(ir, proof)
    assert len(certs) == 1
    cert = certs[0]
    assert cert.input_step_triples == frontiers
    assert layouts == ("zigzag_k", "sharded", "sharded")
    assert cert.parameters == (2, 1, 2, 3, 1, 0)
    assert cert.input_full_shapes == ((12, 2, 2), (12, 1, 2), (12, 1, 3))
    assert cert.full_shape == (12, 2, 3)
    relation = rc.compile_relation_plan(ir, proof)
    segment = relation.dependent_chain_plan.segments[-1]
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert "to_sharded_unshuffle_single" in rendered
    assert "[12, 2, 3] [4, 2, 3]" in rendered
