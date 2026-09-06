"""Exact generated CP3 attention/public fixture; Lean execution is a separate gate."""
from dataclasses import replace
from pathlib import Path

from scripts.tests.test_cp_k_attention import attention_ir, attention_model
from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter.model_compiler import compile_shared_proof_dag, compile_shared_relation_dag
from trainverify.bridge_emitter.proof_compiler import build_default_registry


def witness_source():
    ir = attention_ir()
    namespace = "CPKAttention"
    proof_ns = "CPKAttentionProof"
    ir.init_goals_ref = namespace + ".initGoals"
    ir.lineage_ref = namespace + ".exitGoal"
    ir.public_statement_ref = namespace + ".exitStatement"
    ir.public_statement_contract_ref = namespace + ".externalContract"
    ir.sm_input_value_classes_ref = namespace + ".smInputValueClasses"
    ir.pm_input_value_classes_ref = namespace + ".pmInputValueClasses"
    model = attention_model(ir)
    dag = compile_shared_relation_dag(model, compile_shared_proof_dag(model, build_default_registry()))
    relation = dag.global_relation
    assert relation is not None and relation.dependent_chain_plan is not None
    target_key = dag.projections[0].terminal_fact_key
    assert target_key is not None
    source = dag.facts[target_key]
    target = next(f for f in relation.dependent_chain_plan.relation_facts if f.source == source)
    relation = replace(relation, dependent_chain_plan=replace(
        relation.dependent_chain_plan, terminal_target_fact_id=target.fact_id))
    chain = relation.dependent_chain_plan
    graph = ["open TrainVerify.Denote TrainVerify.Denote.RelationCompiler", f"namespace {namespace}", "noncomputable section"]
    for side in ("sm", "pm"):
        groups = []
        for group in getattr(ir, side + "_replica_groups"):
            members = ", ".join(f"{{ rank := {m.rank}, primaryOutTid := {m.primary_out_tid} }}" for m in group.members)
            groups.append(f'{{ logical := {{ cid := {group.cid}, mb := {group.mb}, irname := "{group.irname}" }}, members := [{members}] }}')
        graph += [f"def {side}Graph : GraphDecl where",
                  f"  numRanks := {getattr(ir, side + '_num_ranks')}",
                  "  nodes := [" + ", ".join(composer._node_text(n) for n in getattr(ir, side + "_nodes")) + "]",
                  f"  replicaGroups := [{', '.join(groups)}]",
                  f"def {side}Shapes : List (Tid × Shape) := [" + ", ".join(f"({tid}, {shape})" for tid, shape in getattr(ir, side + "_shapes")) + "]",
                  f"def {side}GraphInitEnv : ShapeEnv := shapeEnvOfList {side}Shapes",
                  f'def {side}InputValueClasses : List InputValueClass := [{{ source := "cu", tids := [90, 91] }}]']
    graph += [
        "abbrev q := ZigzagKAttentionWitness.q", "abbrev k := ZigzagKAttentionWitness.k",
        "def v : Tensor := Tensor.mkShape [12, 1, 3] (fun i => (3 * i.val + 2 : Nat))",
        "abbrev cu := ZigzagKAttentionWitness.cu", "abbrev sources := ZigzagKAttentionWitness.sources",
        "theorem q_sharded : ShardedRel q (sources q) 0 [12, 2, 2] [4, 2, 2] := ZigzagKAttentionWitness.q_sharded",
        "theorem k_sharded : ShardedRel k (sources k) 0 [12, 1, 2] [4, 1, 2] := ZigzagKAttentionWitness.k_sharded",
        "theorem v_sharded : ShardedRel v (sources v) 0 [12, 1, 3] [4, 1, 3] :=",
        "  ShardedRel.attention_chunks v 3 2 1 3 (by decide) rfl",
        "def initSM : Store := fun tid => if tid = 10 then q else if tid = 11 then k else if tid = 12 then v else cu",
        "def initPM : Store := fun tid =>",
        "  if tid = 100 then (sources q).getD 0 (zeroTensor []) else",
        "  if tid = 101 then (sources q).getD 1 (zeroTensor []) else",
        "  if tid = 102 then (sources q).getD 2 (zeroTensor []) else",
        "  if tid = 110 then (sources k).getD 0 (zeroTensor []) else",
        "  if tid = 111 then (sources k).getD 1 (zeroTensor []) else",
        "  if tid = 112 then (sources k).getD 2 (zeroTensor []) else",
        "  if tid = 120 then (sources v).getD 0 (zeroTensor []) else",
        "  if tid = 121 then (sources v).getD 1 (zeroTensor []) else",
        "  if tid = 122 then (sources v).getD 2 (zeroTensor []) else cu",
        "theorem packed : ZigzagCollective.PackedCuSeqlensWF cu 12 3 := by",
        "  have h := ZigzagKAttentionWitness.q_metadata",
        "  refine ⟨by decide, ZigzagAttentionSourceWitness.decode_cu, h.cu_starts_zero, h.cu_has_endpoint, h.monotone, h.divisible, ?_⟩",
        "  rw [ZigzagAttentionSourceWitness.decode_cu]", "  rfl",
    ]
    def lineage_text(g):
        pieces = ", ".join(f"{{ rank := {r}, tid := {tid} }}" for r, tid in g.tps)
        return f"{{ ts := {g.ts}, tsShape := {g.tsShape}, tps := [{pieces}], tpShapes := {g.tpShapes}, gatherDim := {0 if g.gatherDim is None else g.gatherDim} }}"
    graph += [*[f"def initGoal_{tid} : LineageGoal := {lineage_text(g)}" for tid, g in ir.init_lineages.items()],
              "def initGoals : List LineageGoal := [" + ", ".join(f"initGoal_{tid}" for tid in ir.init_lineages) + "]",
              f"def exitGoal : LineageGoal := {lineage_text(ir.lineage)}",
              "def externalContract (sm pm : Store) : Prop :=",
              "  InputValueClassesHold smInputValueClasses sm ∧",
              "  InputValueClassesHold pmInputValueClasses pm ∧",
              "  ZigzagCollective.PackedCuSeqlensWF (pm 91) 12 3",
              "def exitStatement : Prop :=",
              "  CoarseLineageHoldsWithInitDistributedFaithfulWithContract",
              "    smGraph pmGraph exitGoal smGraphInitEnv pmGraphInitEnv initGoals externalContract",
              "theorem publicInputs :",
              "    StoreShapesHold initSM smGraphInitEnv ∧ StoreShapesHold initPM pmGraphInitEnv ∧",
              "    InitGoalsHold 3 initGoals initSM initPM ∧ externalContract initSM initPM := by",
              "  refine ⟨?_, ?_, ?_, ?_⟩"]
    for side in ("sm", "pm"):
        count = len(getattr(ir, side + "_shapes"))
        graph += ["  · intro tid sh h",
                  "    have hm := shapeEnvOfList_mem_of_eq_some h",
                  f"    simp only [{side}Shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm",
                  "    rcases hm with " + " | ".join("⟨rfl, rfl⟩" for _ in range(count)),
                  "    all_goals rfl"]
    graph += ["  · intro g hg", "    simp only [initGoals, List.mem_cons, List.not_mem_nil, or_false] at hg",
              "    rcases hg with " + " | ".join("rfl" for _ in ir.init_lineages)]
    for tid in ir.init_lineages:
        if tid not in (10, 11, 12):
            graph += ["    · exact ⟨rfl, rfl, rfl⟩"]
            continue
        name = {10: "q", 11: "k", 12: "v"}[tid]
        chunks = [f"(chunkPrimDimN 0 3 {r} {name})" for r in range(3)]
        graph += ["    · refine ⟨rfl, rfl, ?_⟩",
                  "      rw [reconstructForGoal_of_not_replicated _ _ _ rfl]",
                  f"      change {name} = reconstructWithDim 0 3 0 [{', '.join(chunks)}]",
                  f"      rw [reconstructWithDim_cons_cons_nonscalar 0 3 0 {chunks[0]} {chunks[1]} [{chunks[2]}] (by decide)]",
                  f"      exact {name}_sharded.full_value"]
    graph += ["  · refine ⟨?_, ?_, packed⟩"]
    for side in ("sm", "pm"):
        graph += ["    · intro cls hcls tid htid",
                  f"      simp only [{side}InputValueClasses, List.mem_singleton] at hcls",
                  "      subst cls", "      simp only [List.mem_cons, List.not_mem_nil, or_false] at htid",
                  "      rcases htid with rfl | rfl <;> rfl"]
    graph += ["end", f"end {namespace}", ""]
    declarations = composer.render_closed_relation_declarations(chain, proof_ns)
    imports = "\n".join("import " + m for m in (
        "denote.InputValueClasses", "denote.GraphGears", "denote.ZigzagKAttentionWitness",
        "denote.ZigzagKAttention", "denote.ZigzagKAttentionRefinement", "denote.ZigzagKExit"))
    declarations = declarations.replace("import denote.RelationCompiler\n",
        "import denote.RelationCompiler\n" + imports + "\n" + "\n".join(graph) + "\n", 1)
    suffix = f"end\nend TrainVerify.Denote.{proof_ns}\n"
    assert declarations.endswith(suffix)
    declarations = declarations[:-len(suffix)]
    body = "\n".join(composer.render_closed_segment(ir, relation, s.segment_id) for s in chain.segments)
    assert len(chain.segments) == 3
    first, middle, last = (s.segment_id for s in chain.segments)
    body += "\n" + "\n".join([
        f"private def composed : ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {chain.initial_state_id} {chain.states[-1].state_id} where",
        f"  smNodes := {ir.sm_graph_ref}.nodes", f"  pmNodes := {ir.pm_graph_ref}.nodes",
        "  sound := by", "    intro sm pm h",
        f"    rw [show {ir.sm_graph_ref}.nodes = ({first}.smNodes ++ {middle}.smNodes) ++ {last}.smNodes by native_decide]",
        f"    rw [show {ir.pm_graph_ref}.nodes = ({first}.pmNodes ++ {middle}.pmNodes) ++ {last}.pmNodes by native_decide]",
        "    simp only [List.foldl_append]",
        f"    exact {last}.sound _ _ ({middle}.sound _ _ ({first}.sound sm pm h))", "",
    ])
    _, call_args, _ = composer._external_contract_arguments(ir)
    body += composer.render_closed_public_theorem(ir, relation, proof_ns, target_extraction_lines=(
        f"  have hpre := {proof_ns}_initial_state {call_args}",
        "  have h := composed.sound initSM initPM hpre",
        f"  exact h {chain.terminal_target_fact_id} (by native_decide)",
    ))
    body += f"""
#print axioms prove_goal_0_closed
#print axioms {namespace}.publicInputs

theorem inhabitedPublicOutput : InitGoalHolds 3 {namespace}.exitGoal
    (denoteGraphDistributedFaithful {ir.sm_graph_ref} {namespace}.initSM)
    (denoteGraphDistributedFaithful {ir.pm_graph_ref} {namespace}.initPM) :=
  prove_goal_0_closed {namespace}.initSM {namespace}.initPM {namespace}.publicInputs.1
    {namespace}.publicInputs.2.1 {namespace}.publicInputs.2.2.1 {namespace}.publicInputs.2.2.2
#print axioms inhabitedPublicOutput

"""
    return declarations + body + suffix


def conditional_source(num_ranks):
    """Exact K-rank graph closure, explicitly conditional on its initial state."""
    ir = attention_ir(num_ranks)
    model = attention_model(ir)
    dag = compile_shared_relation_dag(model, compile_shared_proof_dag(model, build_default_registry()))
    relation = dag.global_relation
    assert relation is not None and relation.dependent_chain_plan is not None
    chain = relation.dependent_chain_plan
    target_key = dag.projections[0].terminal_fact_key
    assert target_key is not None
    terminal_source = dag.facts[target_key]
    target = next(f for f in chain.relation_facts if f.source == terminal_source)
    namespace = "CPKAttentionConditionalProof"
    graph = ["open TrainVerify.Denote", "namespace CPKAttention"]
    for side in ("sm", "pm"):
        groups = []
        for group in getattr(ir, side + "_replica_groups"):
            members = ", ".join(f"{{ rank := {m.rank}, primaryOutTid := {m.primary_out_tid} }}" for m in group.members)
            groups.append(f'{{ logical := {{ cid := {group.cid}, mb := {group.mb}, irname := "{group.irname}" }}, members := [{members}] }}')
        graph += [f"def {side}Graph : GraphDecl where",
                  f"  numRanks := {getattr(ir, side + '_num_ranks')}",
                  "  nodes := [" + ", ".join(composer._node_text(n) for n in getattr(ir, side + "_nodes")) + "]",
                  f"  replicaGroups := [{', '.join(groups)}]"]
    graph += ["end CPKAttention", ""]
    declarations = composer.render_closed_relation_declarations(chain, namespace)
    declarations = declarations.replace("import denote.RelationCompiler\n",
        "import denote.RelationCompiler\nimport denote.ZigzagKAttentionRefinement\nimport denote.ZigzagKExit\n" + "\n".join(graph) + "\n", 1)
    suffix = f"end\nend TrainVerify.Denote.{namespace}\n"
    assert declarations.endswith(suffix)
    body = "\n".join(composer.render_closed_segment(ir, relation, s.segment_id) for s in chain.segments)
    first, middle, last = (s.segment_id for s in chain.segments)
    body += "\n" + "\n".join([
        f"theorem conditionalOutput (sm pm : Store) (h : {chain.initial_state_id}.Holds sm pm) :",
        f"    {target.fact_id}.Holds (denoteGraphDistributedFaithful CPKAttention.smGraph sm)",
        "      (denoteGraphDistributedFaithful CPKAttention.pmGraph pm) := by",
        "  unfold denoteGraphDistributedFaithful",
        f"  rw [show CPKAttention.smGraph.nodes = ({first}.smNodes ++ {middle}.smNodes) ++ {last}.smNodes by native_decide]",
        f"  rw [show CPKAttention.pmGraph.nodes = ({first}.pmNodes ++ {middle}.pmNodes) ++ {last}.pmNodes by native_decide]",
        "  simp only [List.foldl_append]",
        f"  exact ({last}.sound _ _ ({middle}.sound _ _ ({first}.sound sm pm h))) _ (by native_decide)",
        "#print axioms conditionalOutput", "",
    ])
    return declarations[:-len(suffix)] + body + suffix


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(witness_source())
    print(args.output)
