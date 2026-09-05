"""Generate exact CP3 compiler witnesses; parent alone runs Lean on the output."""
from pathlib import Path
from scripts.tests.test_cp_k_entry import entry_ir, compile_entry
from trainverify.bridge_emitter import composer


def witness_source(op, *, prefix=False, prefix_reordered=False):
    if prefix:
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
    declarations = composer.render_closed_relation_declarations(chain,"CPEntryProof")
    declarations = declarations.replace("import denote.RelationCompiler\n", "import denote.RelationCompiler\nimport denote.InputValueClasses\nimport denote.ZigzagKRelationWitness\n\n" + "\n".join(graph_lines) + "\n", 1)
    suffix = "end\nend TrainVerify.Denote.CPEntryProof\n"
    assert declarations.endswith(suffix)
    declarations = declarations[:-len(suffix)]
    body = composer.render_closed_segment(ir,relation,segment.segment_id)
    sound_name = segment.segment_id
    if prefix:
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
    return declarations + body + "\nopen CPEntry\n" + "\n".join(initial) + suffix


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--prefix", action="store_true", help="emit shared contiguous-prefix/entry witnesses")
    parser.add_argument("--prefix-reordered", action="store_true", help="execute prefix ranks in order [2, 0, 1]")
    args = parser.parse_args()
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
        path = args.output_dir / name
        path.write_text(witness_source(op, prefix=args.prefix, prefix_reordered=args.prefix_reordered))
        print(path)
