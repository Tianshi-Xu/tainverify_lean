"""One CP3 compiler tracer: ordinary Q -> entry -> attention -> ordinary exit.

The six graph parameters encode Q/KV heads, QK/V channels, causal and window.
Default scale, zero dropout and no ALiBi are the restricted source interpretation
of this operator, not extra invented Node parameters. No intermediate InitGoal
is supplied, and no numerical/source witness substitutes for graph compilation.
"""
from dataclasses import fields

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


def attention_ir():
    """Actual ordered CP3 buddies, GQA 2:1, local L=4, QK dim=2, V dim=3.

    Execution order [2,0,1] deliberately differs from semantic group order.
    K/V are separate ordinary dim-zero InitGoals; only Q passes through entry.
    Metadata 90 is shared by both attention operands and both boundaries, with
    the existing entry helper's public packed contract on its value alias 91.
    """
    ir = entry_ir(3)
    q_full, q_local = [12, 2, 2], [4, 2, 2]
    ir.sm_shapes[0] = (10, q_full)
    ir.pm_shapes[:3] = [(100 + r, q_local) for r in range(3)]
    ir.init_lineages[10] = parser.LineageGoal(
        10, q_full, [(r, 100 + r) for r in range(3)], [q_local] * 3, 0,
    )
    for tid, base, full, local in (
        (11, 110, [12, 1, 2], [4, 1, 2]),
        (12, 120, [12, 1, 3], [4, 1, 3]),
    ):
        ir.sm_shapes.append((tid, full))
        ir.pm_shapes.extend((base + r, local) for r in range(3))
        ir.init_lineages[tid] = parser.LineageGoal(
            tid, full, [(r, base + r) for r in range(3)], [local] * 3, 0,
        )
    ir.prereqs = list(ir.init_lineages)
    ir.full_init_goal_ids = tuple(ir.prereqs)
    parameters = [2, 1, 2, 3, 1, 0]
    sm_attn = parser.Node(0, "FW_attn_zigzag", [20, 11, 12, 90, 90], [30], parameters)
    pm_attn = [
        parser.Node(r, "FW_attn_zigzag", [200 + r, 110 + r, 120 + r, 90, 90],
                    [300 + r], list(parameters))
        for r in range(3)
    ]
    sm_exit = parser.Node(0, "FW_maybe_unshuffle", [30, 90], [40], [1, 0])
    pm_exit = [
        parser.Node(r, "FW_maybe_unshuffle", [300 + r, 90], [400 + r], [3, r])
        for r in range(3)
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
    ir.pm_nodes = [ir.pm_nodes[r] for r in (2, 0, 1)]
    ir.pm_nodes += [pm_attn[r] for r in (2, 0, 1)]
    ir.pm_nodes += [pm_exit[r] for r in (2, 0, 1)]
    ir.lineage = parser.LineageGoal(
        40, [12, 2, 3], [(r, 400 + r) for r in range(3)], [[4, 2, 3]] * 3, 0,
    )
    ir.sm_graph_ref = "CPKAttention.smGraph"
    ir.pm_graph_ref = "CPKAttention.pmGraph"
    return ir


def attention_model(ir):
    """Exit first: compile the maximal closure, then reuse its two prefixes."""
    lineages = (
        ir.lineage,
        parser.LineageGoal(20, [12, 2, 2], [(r, 200 + r) for r in range(3)],
                           [[4, 2, 2]] * 3, 0),
        parser.LineageGoal(30, [12, 2, 3], [(r, 300 + r) for r in range(3)],
                           [[4, 2, 3]] * 3, 0),
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
