"""Generate exact CP3 compiler witnesses; parent alone runs Lean on the output."""
from pathlib import Path
from scripts.tests.test_cp_k_entry import entry_ir, compile_entry
from trainverify.bridge_emitter import composer


def witness_source(op, *, prefix=False, prefix_reordered=False, exit=False):
    if exit and (prefix or prefix_reordered):
        raise ValueError("exit witness has no contiguous prefix")
    if exit:
        from dataclasses import replace
        from scripts.tests.test_cp_k_exit import exit_ir, shared_exit
        ir = exit_ir(op=op)
        _, dag = shared_exit(ir)
        relation = dag.global_relation
        target_source = dag.facts[dag.projections[1].terminal_fact_key]
        target = next(f for f in relation.dependent_chain_plan.relation_facts if f.source == target_source)
        relation = replace(relation, dependent_chain_plan=replace(
            relation.dependent_chain_plan, terminal_target_fact_id=target.fact_id))
        ir.init_goals_ref = "CPEntry.initGoals"
        ir.lineage_ref = "CPEntry.exitGoal"
        ir.public_statement_ref = "CPEntry.exitStatement"
        ir.public_statement_contract_ref = "CPEntry.externalContract"
        ir.sm_input_value_classes_ref = "CPEntry.smInputValueClasses"
        ir.pm_input_value_classes_ref = "CPEntry.pmInputValueClasses"
    elif prefix:
        from scripts.tests.test_cp_k_prefix import prefix_ir, shared_prefix
        from trainverify.bridge_emitter.model_authority import materialize_target_ir
        model, dag = shared_prefix(prefix_ir(op=op, prefix_reordered=prefix_reordered))
        ir = materialize_target_ir(model, 1)
        relation = dag.global_relation
    else:
        ir = entry_ir(op=op)
        _, relation = compile_entry(ir)
    chain = relation.dependent_chain_plan
    segment = chain.segments[0]
    graph_lines = ["open TrainVerify.Denote", "namespace CPEntry", "noncomputable section"]
    for side in ("sm", "pm"):
        nodes = getattr(ir, side + "_nodes")
        groups = getattr(ir, side + "_replica_groups")
        node_text = ", ".join(composer._node_text(n) for n in nodes)
        group_text = []
        for g in groups:
            members = ", ".join(f"{{ rank := {m.rank}, primaryOutTid := {m.primary_out_tid} }}" for m in g.members)
            group_text.append(f'{{ logical := {{ cid := {g.cid}, mb := {g.mb}, irname := "{g.irname}" }}, members := [{members}] }}')
        graph_lines += [f"def {side}Graph : GraphDecl where", f"  numRanks := {getattr(ir,side+'_num_ranks')}", f"  nodes := [{node_text}]", f"  replicaGroups := [{', '.join(group_text)}]"]
        shape_text = ", ".join(f"({tid}, {shape})" for tid,shape in getattr(ir,side+"_shapes"))
        graph_lines += [f"def {side}Shapes : List (Tid × Shape) := [{shape_text}]",
                        f'def {side}InputValueClasses : List InputValueClass := [{{ source := "cu", tids := [90, 91] }}]']
    w = "TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness"
    graph_lines += [
        f"def initSM : Store := fun tid => if tid = 10 then {w}.full else {w}.cu",
        f"def initPM : Store := fun tid => if tid = 100 then {w}.source 0 else if tid = 101 then {w}.source 1 else if tid = 102 then {w}.source 2 else {w}.cu",
        f"theorem packed : ZigzagCollective.PackedCuSeqlensWF ({w}.cu) 12 3 := by",
        f"  have h := {w}.cu_wf",
        f"  refine ⟨by decide, {w}.decode_cu, h.cu_starts_zero, h.cu_has_endpoint, h.monotone, h.divisible, ?_⟩",
        f"  rw [{w}.decode_cu]", "  rfl", "end", "end CPEntry", "",
    ]
    if exit:
        def lineage_text(g):
            pieces = ", ".join(f"{{ rank := {rank}, tid := {tid} }}" for rank, tid in g.tps)
            dim = 0 if g.gatherDim is None else g.gatherDim
            return f"{{ ts := {g.ts}, tsShape := {g.tsShape}, tps := [{pieces}], tpShapes := {g.tpShapes}, gatherDim := {dim} }}"
        public_graph = [
            "namespace CPEntry", "noncomputable section",
            "def smGraphInitEnv : ShapeEnv := shapeEnvOfList smShapes",
            "def pmGraphInitEnv : ShapeEnv := shapeEnvOfList pmShapes",
            *[f"def initGoal_{tid} : LineageGoal := {lineage_text(g)}" for tid,g in ir.init_lineages.items()],
            "def initGoals : List LineageGoal := [initGoal_10, initGoal_90, initGoal_91]",
            f"def exitGoal : LineageGoal := {lineage_text(ir.lineage)}",
            "def externalContract (initSM initPM : Store) : Prop :=",
            "  InputValueClassesHold smInputValueClasses initSM ∧",
            "  InputValueClassesHold pmInputValueClasses initPM ∧",
            "  ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3",
            "def exitStatement : Prop :=",
            "  CoarseLineageHoldsWithInitDistributedFaithfulWithContract",
            "    smGraph pmGraph exitGoal smGraphInitEnv pmGraphInitEnv initGoals externalContract",
            "end", "end CPEntry", "",
        ]
        graph_lines += public_graph
    declarations = composer.render_closed_relation_declarations(chain,"CPEntryProof")
    declarations = declarations.replace("import denote.RelationCompiler\n", "import denote.RelationCompiler\nimport denote.InputValueClasses\nimport denote.ZigzagKRelationWitness\n" + ("import denote.ZigzagKExit\n" if exit else "") + "\n" + "\n".join(graph_lines) + "\n", 1)
    suffix = "end\nend TrainVerify.Denote.CPEntryProof\n"
    assert declarations.endswith(suffix)
    declarations = declarations[:-len(suffix)]
    body = composer.render_closed_segment(ir,relation,segment.segment_id)
    sound_name = segment.segment_id
    if prefix or exit:
        assert len(chain.segments) == 2
        second = chain.segments[1]
        body += "\n" + composer.render_closed_segment(ir, relation, second.segment_id)
        body += "\n" + "\n".join([
            f"private def composed : ClosedDepSegmentCertificate CPEntry.smGraph CPEntry.pmGraph {chain.initial_state_id} {chain.states[-1].state_id} where",
            "  smNodes := CPEntry.smGraph.nodes", "  pmNodes := CPEntry.pmGraph.nodes",
            "  sound := by", "    intro sm pm h",
            f"    rw [show CPEntry.smGraph.nodes = {segment.segment_id}.smNodes ++ {second.segment_id}.smNodes by native_decide]",
            f"    rw [show CPEntry.pmGraph.nodes = {segment.segment_id}.pmNodes ++ {second.segment_id}.pmNodes by native_decide]",
            "    rw [List.foldl_append, List.foldl_append]",
            f"    exact {second.segment_id}.sound _ _ ({segment.segment_id}.sound sm pm h)",
        ]) + "\n"
        sound_name = "composed"
    if exit:
        _, call_args, _ = composer._external_contract_arguments(ir)
        body += "\n" + composer.render_closed_public_theorem(
            ir, relation, "CPEntryProof",
            target_extraction_lines=(
                f"  have hpre := CPEntryProof_initial_state {call_args}",
                "  have h := composed.sound initSM initPM hpre",
                f"  exact h {chain.terminal_target_fact_id} (by native_decide)",
            ))
        body += "\n#print axioms prove_goal_0_closed\n"
    initial = [f"theorem inhabitedInput : {chain.initial_state_id}.Holds CPEntry.initSM CPEntry.initPM := by",
               "  intro fact hfact",
               f"  change fact ∈ {list(chain.states[0].fact_ids)} at hfact".replace("'", ""),
               "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfact",
               "  rcases hfact with " + " | ".join("rfl" for _ in chain.states[0].fact_ids)]
    records = {f.fact_id:f for f in (*chain.relation_facts,*chain.authority_facts,chain.anchor_fact)}
    for fid in chain.states[0].fact_ids:
        f = records[fid]
        if f.kind == "sharded": initial += [f"  · exact {w}.sharded_input"]
        elif f.kind == "tensor_shape": initial += [f"  · exact {w}.sharded_input.full_shape"]
        elif f.kind == "packed_cu": initial += ["  · exact CPEntry.packed"]
        elif f.kind == "tensor_eq": initial += ["  · rfl"]
        else: raise ValueError(f.kind)
    initial += [
        f"theorem inhabitedOutput : {chain.terminal_target_fact_id}.Holds",
        "    (smGraph.nodes.foldl (applyNodeDistributedFaithful smGraph) initSM)",
        "    (pmGraph.nodes.foldl (applyNodeDistributedFaithful pmGraph) initPM) := by",
        f"  have h := {sound_name}.sound CPEntry.initSM CPEntry.initPM inhabitedInput",
        f"  exact h {chain.terminal_target_fact_id} (by native_decide)",
        "#print axioms inhabitedOutput", "",
    ]
    if exit:
        initial += """
open ZigzagKRelationWitness in
theorem publicInputs :
    StoreShapesHold CPEntry.initSM CPEntry.smGraphInitEnv ∧
    StoreShapesHold CPEntry.initPM CPEntry.pmGraphInitEnv ∧
    InitGoalsHold 3 CPEntry.initGoals CPEntry.initSM CPEntry.initPM ∧
    CPEntry.externalContract CPEntry.initSM CPEntry.initPM := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tid sh h
    simp [CPEntry.smGraphInitEnv, CPEntry.smShapes, shapeEnvOfList, List.find?] at h
    by_cases h10 : 10 = tid <;> by_cases h90 : 90 = tid <;> by_cases h91 : 91 = tid <;>
      simp_all [CPEntry.initSM, sharded_input.full_shape, cu, Tensor.mkShape, eq_comm]
  · intro tid sh h
    simp [CPEntry.pmGraphInitEnv, CPEntry.pmShapes, shapeEnvOfList, List.find?] at h
    by_cases h100 : 100 = tid <;> by_cases h101 : 101 = tid <;> by_cases h102 : 102 = tid <;>
      by_cases h90 : 90 = tid <;> by_cases h91 : 91 = tid <;>
      simp_all [CPEntry.initPM, source, cu, Tensor.mkShape, eq_comm]
  · intro g hg
    simp only [CPEntry.initGoals, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · refine ⟨sharded_input.full_shape, rfl, ?_⟩
      rw [reconstructForGoal_of_not_replicated _ _ _ rfl]
      change full = reconstructWithDim 0 3 0 [source 0, source 1, source 2]
      rw [reconstructWithDim_cons_cons_nonscalar 0 3 0 (source 0) (source 1) [source 2] (by decide)]
      rfl
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · refine ⟨?_, ?_, CPEntry.packed⟩
    · intro c hc tid ht
      simp only [CPEntry.smInputValueClasses, List.mem_singleton] at hc
      subst c
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> rfl
    · intro c hc tid ht
      simp only [CPEntry.pmInputValueClasses, List.mem_singleton] at hc
      subst c
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> rfl

theorem inhabitedPublicOutput : InitGoalHolds 3 CPEntry.exitGoal
    (denoteGraphDistributedFaithful CPEntry.smGraph CPEntry.initSM)
    (denoteGraphDistributedFaithful CPEntry.pmGraph CPEntry.initPM) :=
  prove_goal_0_closed CPEntry.initSM CPEntry.initPM publicInputs.1
    publicInputs.2.1 publicInputs.2.2.1 publicInputs.2.2.2
#print axioms publicInputs
#print axioms inhabitedPublicOutput
""".splitlines() + [""]
    return declarations + body + "\nopen CPEntry\n" + "\n".join(initial) + suffix


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--prefix", action="store_true", help="emit shared contiguous-prefix/entry witnesses")
    parser.add_argument("--exit", action="store_true", help="emit shared entry/exit witnesses with public gather")
    parser.add_argument("--prefix-reordered", action="store_true", help="execute prefix ranks in order [2, 0, 1]")
    args = parser.parse_args()
    if args.exit and (args.prefix or args.prefix_reordered):
        parser.error("--exit cannot be combined with prefix options")
    if args.prefix_reordered and not args.prefix:
        parser.error("--prefix-reordered requires --prefix")
    if not args.output_dir.is_absolute():
        parser.error("--output-dir must be absolute")
    args.output_dir.mkdir(parents=True,exist_ok=True)
    for op, name in (("FW_maybe_shuffle","CPKEntryFW.lean"),("BW_maybe_unshuffle","CPKEntryBW.lean")):
        if args.prefix:
            name = name.replace("Entry", "Prefix")
        if args.prefix_reordered:
            name = name.replace("Prefix", "PrefixReordered")
        if args.exit:
            name = name.replace("Entry", "Exit")
        path = args.output_dir / name
        path.write_text(witness_source(op, prefix=args.prefix, prefix_reordered=args.prefix_reordered, exit=args.exit))
        print(path)
