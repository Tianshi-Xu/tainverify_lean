"""Shared single-output frame renderer for column-sharded BW_linear dX/dW."""
from __future__ import annotations


def render_closed_k_rank_bw_linear_dx_column_segment(ir, relation, segment_id: str) -> str:
    return _render_column_single_output(ir, relation, segment_id, dw=False)


def render_closed_k_rank_bw_linear_dw_column_segment(ir, relation, segment_id: str) -> str:
    return _render_column_single_output(ir, relation, segment_id, dw=True)


def _render_column_single_output(ir, relation, segment_id: str, *, dw: bool) -> str:
    projection_index = 1 if dw else 0
    projection = ".2" if dw else ".1"
    output_dim = 1 if dw else 2
    derivative = "dw" if dw else "dx"
    try:
        from .composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from .relation_compiler import get_closed_rule_spec
    except ImportError:
        from composer import (
            _node_text, _render_mixed_final_value, _select_exact_typed_certificate,
            _shape_text,
        )
        from relation_compiler import get_closed_rule_spec

    rule_spec = get_closed_rule_spec(
        "bw-linear-dw-input-column-sharded-k-rank" if dw else "bw-linear-dx-column-sharded-k-rank"
    )
    def input_facts(cert):
        return (cert.gradient_fact, cert.activation_fact, cert.weight_fact) if dw else cert.input_facts
    view_rule_spec = get_closed_rule_spec("bw-view-joined")
    rule = rule_spec.rule_id
    chain = relation.dependent_chain_plan
    segment = next((item for item in chain.segments if item.segment_id == segment_id), None)
    if segment is None or len(segment.transition_ids) not in (1, 2):
        raise ValueError("BW_linear column dX requires one transition and optional joined view")
    transition_map = {item.transition_id: item for item in relation.transition_specs}
    segment_transitions = tuple(transition_map[item] for item in segment.transition_ids)
    transition = next((item for item in segment_transitions if item.rule_id == rule), None)
    view_transition = next((item for item in segment_transitions if item.rule_id == view_rule_spec.rule_id), None)
    if transition is None or (len(segment_transitions) == 2 and view_transition is None):
        raise ValueError("BW_linear column dX transition authority is missing")
    if transition.lean_theorem not in rule_spec.lean_theorems:
        raise ValueError("BW_linear column dX theorem identity is unsupported")
    theorem = transition.lean_theorem
    certificate = _select_exact_typed_certificate(
        relation, transition, rule, theorem, rule_spec.certificate_type,
        lambda cert: (tuple(sorted(input_facts(cert))), (cert.output_fact,)),
    )
    if not dw and (certificate.family != "column-sharded" or len(certificate.input_facts) != 3):
        raise ValueError("BW_linear column dX certificate family/arity mismatch")
    view_certificate = None
    if view_transition is not None:
        view_certificate = _select_exact_typed_certificate(
            relation, view_transition, view_rule_spec.rule_id,
            view_rule_spec.lean_theorems[0],
            view_rule_spec.certificate_type,
            lambda cert: ((cert.input_fact,), (cert.output_fact,)),
        )
    records = {item.source: item for item in chain.relation_facts}
    try:
        gradient, activation, weight = (
            records[source] for source in input_facts(certificate)
        )
        output = records[certificate.output_fact]
        view_input = records[view_certificate.input_fact] if view_certificate else None
        view_output = records[view_certificate.output_fact] if view_certificate else None
    except KeyError as exc:
        raise ValueError("BW_linear column dX fact is not materialized") from exc
    states = {item.state_id: item for item in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    required={gradient.fact_id,activation.fact_id,weight.fact_id};fresh={output.fact_id}
    if view_input is not None: required.add(view_input.fact_id);fresh.add(view_output.fact_id)
    if not required <= set(before.fact_ids) or not fresh <= set(after.fact_ids):
        raise ValueError("BW_linear column dX pre/post facts are not live")
    if not set(after.fact_ids) <= (fresh | set(before.fact_ids)):
        raise ValueError("BW_linear column dX post-state introduces an unproved fact")
    k = len(output.pm_tids)
    column_dx_shape_spec(gradient, activation, weight, output, k, dw=dw)
    if certificate.rank_count != k:
        raise ValueError("BW_linear column derivative rank count mismatch")
    if dw:
        if certificate.output_fact.layout != "sharded" or certificate.output_fact.gather_dim != 1:
            raise ValueError("BW_linear column dW output descriptor mismatch")
    elif certificate.output_layout != "sharded" or certificate.gather_dim != 2:
        raise ValueError("BW_linear column dX output descriptor mismatch")

    if len(transition.sm_node_indices) != 1 or len(transition.pm_node_indices) != k:
        raise ValueError("BW_linear column dX footprint is not exact 1+K")
    sm_start, sm_end = segment.sm_range; pm_start, pm_end = segment.pm_range
    if (not set(transition.sm_node_indices) <= set(range(sm_start, sm_end))
            or not set(transition.pm_node_indices) <= set(range(pm_start, pm_end))):
        raise ValueError("BW_linear column dX writers are outside the complete frame")
    sm_frame = list(ir.sm_nodes[sm_start:sm_end]); pm_frame = list(ir.pm_nodes[pm_start:pm_end])
    sm_node = ir.sm_nodes[transition.sm_node_indices[0]]
    pm_nodes = tuple(ir.pm_nodes[index] for index in transition.pm_node_indices)
    if (certificate.sm_step_id != f"sm:{transition.sm_node_indices[0]}:{projection_index}"
            or certificate.pm_step_ids
               != tuple(f"pm:{index}:{projection_index}" for index in transition.pm_node_indices)):
        raise ValueError("BW_linear column dX certificate footprint was tampered")
    if (sm_node.rank != 0 or sm_node.op != "BW_linear" or sm_node.params
            or len(sm_node.ins) != 3 or len(sm_node.outs) != 2
            or tuple(sm_node.ins) != (gradient.sm_tid, activation.sm_tid, weight.sm_tid)
            or sm_node.outs[projection_index] != output.sm_tid):
        raise ValueError("BW_linear column dX SM writer roles are not exact")
    if tuple(node.rank for node in pm_nodes) != tuple(range(k)):
        raise ValueError("BW_linear column dX PM ranks are not ordered")
    for rank, node in enumerate(pm_nodes):
        if (node.op != "BW_linear" or node.params or len(node.ins) != 3
                or len(node.outs) != 2
                or tuple(node.ins) != (
                    gradient.joined_pm_tid, activation.pm_tids[rank], weight.pm_tids[rank],
                )
                or node.outs[projection_index] != output.pm_tids[rank]):
            raise ValueError("BW_linear column dX PM writer roles/order are not exact")
    view_sm_node=view_pm_node=None
    if view_transition is not None:
        if (view_input.kind!="joined" or view_output.kind!="joined"
                or view_input.full_shape!=tuple(view_certificate.input_shape)
                or view_output.full_shape!=tuple(view_certificate.target_shape)
                or view_certificate.sm_step_id!=f"sm:{view_transition.sm_node_indices[0]}:0"
                or view_certificate.pm_step_id!=f"pm:{view_transition.pm_node_indices[0]}:0"):
            raise ValueError("BW_linear column/view metadata mismatch")
        view_sm_node=ir.sm_nodes[view_transition.sm_node_indices[0]]
        view_pm_node=ir.pm_nodes[view_transition.pm_node_indices[0]]
        for node in (view_sm_node,view_pm_node):
            if (node.op!="BW_view" or node.ins[0] not in (view_input.sm_tid,view_input.joined_pm_tid)
                    or node.outs[0] not in (view_output.sm_tid,view_output.joined_pm_tid)):
                raise ValueError("BW_linear column/view writer mismatch")

    sm_nodes_name, pm_nodes_name = f"{segment_id}_sm_nodes", f"{segment_id}_pm_nodes"
    sm_final_name, pm_final_name = f"{segment_id}_sm_final", f"{segment_id}_pm_final"
    lines = [
        "set_option maxHeartbeats 500000 in",
        f"private def {sm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in sm_frame)}]",
        f"private def {pm_nodes_name} : List NodeDecl := [{', '.join(_node_text(n) for n in pm_frame)}]",
        f"private def {sm_final_name} (store : Store) : Store :=",
        f"  {sm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.sm_graph_ref}) store",
        f"private def {pm_final_name} (store : Store) : Store :=",
        f"  {pm_nodes_name}.foldl (applyNodeDistributedFaithful {ir.pm_graph_ref}) store", "",
    ]

    def writer(name, graph, initial, final_name, nodes_name, frame, position, node):
        theorem_name = f"{segment_id}_{name}"; final = f"({final_name} {initial})"
        expression = (
            f"(bw_linear ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]}) "
            f"({{store}} {node.ins[2]})){projection}"
        )
        lines.extend([
            f"private theorem {theorem_name} ({initial} : Store) :",
            f"    {final} {node.outs[projection_index]} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial} := by",
            f"    unfold {final_name}", "    rfl",
        ])
        helper = _render_mixed_final_value(
            name="hout", graph=graph, initial_store=initial, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=frame,
            position=position, output_tid=node.outs[projection_index], input_tids=tuple(node.ins),
            written_tids={tid for item in frame for tid in item.outs},
            expression=expression,
            apply_lines=[
                "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
                "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
                "(hattn := by native_decide)]",
                "simp [applyNodeDistributed, applyNodeRingAttn]",
                f"exact applyNode_bw_linear_{'snd' if dw else 'fst'}_out {graph} t {node.rank} "
                f"{node.ins[0]} {node.ins[1]} {node.ins[2]} "
                f"{node.outs[0]} {node.outs[1]} (by native_decide)",
            ],
        )
        lines.extend(item[2:] if item.startswith("  ") else item for item in helper)
        lines.extend(["  exact hout", ""]); return theorem_name

    sm_helper = writer("hSmWriter", ir.sm_graph_ref, "smStore", sm_final_name,
                       sm_nodes_name, sm_frame, transition.sm_node_indices[0]-sm_start, sm_node)
    pm_helpers = tuple(
        writer(f"hPmWriter{rank}", ir.pm_graph_ref, "pmStore", pm_final_name,
               pm_nodes_name, pm_frame, index-pm_start, node)
        for rank, (index,node) in enumerate(zip(transition.pm_node_indices, pm_nodes))
    )
    view_sm_helper=view_pm_helper=None
    if view_transition is not None:
        def view_writer(name,graph,initial,final_name,nodes_name,frame,position,node):
            theorem_name=f"{segment_id}_{name}";final=f"({final_name} {initial})";shape=_shape_text(list(view_certificate.target_shape));expr=f"fw_view {shape} ({{store}} {node.ins[0]})"
            lines.extend([f"private theorem {theorem_name}({initial}:Store):{final} {node.outs[0]}={expr.format(store=final)}:=by",f"  have hfinal:{final}={nodes_name}.foldl (applyNodeDistributedFaithful {graph}) {initial}:=by unfold {final_name};rfl"])
            helper=_render_mixed_final_value(name="hout",graph=graph,initial_store=initial,final_store=final,final_equality="hfinal",nodes_name=nodes_name,nodes=frame,position=position,output_tid=node.outs[0],input_tids=(node.ins[0],),written_tids={tid for item in frame for tid in item.outs},expression=expr,apply_lines=["rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]","simp [applyNodeDistributed,applyNodeRingAttn]",f"exact applyNode_bw_view_out {graph} t {node.rank} {node.params[0]} {_shape_text(node.params[1:])} {node.ins[0]} {node.ins[1]} {node.outs[0]}"])
            lines.extend(item[2:] if item.startswith("  ") else item for item in helper);lines.extend(["  exact hout",""]);return theorem_name
        view_sm_helper=view_writer("hViewSm",ir.sm_graph_ref,"smStore",sm_final_name,sm_nodes_name,sm_frame,view_transition.sm_node_indices[0]-sm_start,view_sm_node)
        view_pm_helper=view_writer("hViewPm",ir.pm_graph_ref,"pmStore",pm_final_name,pm_nodes_name,pm_frame,view_transition.pm_node_indices[0]-pm_start,view_pm_node)
    lines.extend([
        f"private theorem {segment_id}_{derivative}_shape (g x w : Tensor) (o i : Nat)",
        "    (hg : g.shape = [1,8,o]) (hx : x.shape = [1,8,i])",
        f"    (hw : w.shape = [o,i]) : (bw_linear g x w){projection}.shape = {'[o,i]' if dw else '[1,8,i]'} :=",
        f"  bw_linear_3d_{'snd' if dw else 'fst'}_shape 1 8 o i g x w hg hx hw", "",
    ])
    xlist = "[" + ", ".join(f"pmFinal {tid}" for tid in activation.pm_tids) + "]"
    wlist = "[" + ", ".join(f"pmFinal {tid}" for tid in weight.pm_tids) + "]"
    olist = "[" + ", ".join(f"pmFinal {tid}" for tid in output.pm_tids) + "]"
    afull,ashard = (_shape_text(list(x)) for x in (activation.full_shape,activation.shard_shape))
    wfull,wshard = (_shape_text(list(x)) for x in (weight.full_shape,weight.shard_shape))
    ofull,oshard = (_shape_text(list(x)) for x in (output.full_shape,output.shard_shape))
    lines.extend([
        "set_option maxHeartbeats 500000 in",
        f"private theorem {segment_id}_sound (smStore pmStore : Store)",
        f"    (hstate : {before.state_id}.Holds smStore pmStore) :",
        f"    {after.state_id}.Holds ({sm_final_name} smStore) ({pm_final_name} pmStore) := by",
        f"    let smFinal := {sm_final_name} smStore", f"    let pmFinal := {pm_final_name} pmStore",
        f"    have hframe : {before.state_id}.Holds smFinal pmFinal := by",
        f"      unfold smFinal pmFinal {sm_final_name} {pm_final_name}",
        f"      apply RelationState.Holds.fold_frame {sm_nodes_name} {pm_nodes_name} smStore pmStore hstate",
        "      · native_decide", "      · native_decide", "      · native_decide", "      · native_decide",
        f"    have hg : {gradient.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change smFinal {gradient.sm_tid} = pmFinal {gradient.joined_pm_tid} ∧",
        f"      (smFinal {gradient.sm_tid}).shape = {_shape_text(list(gradient.full_shape))} ∧",
        f"      (pmFinal {gradient.joined_pm_tid}).shape = {_shape_text(list(gradient.full_shape))} at hg",
        f"    have hx : {activation.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {activation.sm_tid}) {xlist} 2 {afull} {ashard} at hx",
        f"    have hw : {weight.fact_id}.Holds smFinal pmFinal := hframe _ (by native_decide)",
        f"    change ShardedRel (smFinal {weight.sm_tid}) {wlist} 1 {wfull} {wshard} at hw",
        f"    have hxValue : smFinal {activation.sm_tid} = allGatherPrimDimN 2 {k} 0 {xlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hx.full_value",
        f"    have hwValue : smFinal {weight.sm_tid} = allGatherPrimDimN 1 {k} 0 {wlist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hw.full_value",
        f"    have hSmWriter : smFinal {output.sm_tid} =",
        f"        (bw_linear (smFinal {sm_node.ins[0]}) (smFinal {sm_node.ins[1]}) (smFinal {sm_node.ins[2]})){projection} :=",
        f"      {sm_helper} smStore",
    ])
    if view_transition is not None:
        target_shape=_shape_text(list(view_certificate.target_shape));input_shape=_shape_text(list(view_certificate.input_shape))
        lines.extend([f"    have hvi:{view_input.fact_id}.Holds smFinal pmFinal:=hframe _ (by native_decide)",f"    have hvs:={view_sm_helper} smStore",f"    have hvp:={view_pm_helper} pmStore",f"    change smFinal {view_output.sm_tid}=fw_view {target_shape} (smFinal {view_input.sm_tid}) at hvs",f"    change pmFinal {view_output.joined_pm_tid}=fw_view {target_shape} (pmFinal {view_input.joined_pm_tid}) at hvp",f"    have houtView:{view_output.fact_id}.Holds smFinal pmFinal:=by",f"      change smFinal {view_output.sm_tid}=pmFinal {view_output.joined_pm_tid}∧_∧_","      rw [hvs,hvp]",f"      exact JoinedRel.fw_view {target_shape} {input_shape} hvi"])
    for rank,(helper,node) in enumerate(zip(pm_helpers,pm_nodes)):
        lines.extend([
            f"    have hPmWriter{rank} : pmFinal {output.pm_tids[rank]} =",
            f"        (bw_linear (pmFinal {node.ins[0]}) (pmFinal {node.ins[1]}) (pmFinal {node.ins[2]})){projection} :=",
            f"      {helper} pmStore",
            f"    have hxShape{rank} := hx.shard_shapes (pmFinal {activation.pm_tids[rank]}) (by simp)",
            f"    have hwShape{rank} := hw.shard_shapes (pmFinal {weight.pm_tids[rank]}) (by simp)",
            f"    have hOutShape{rank} : (pmFinal {output.pm_tids[rank]}).shape = {oshard} := by",
            f"      rw [hPmWriter{rank}]",
            f"      exact {segment_id}_{derivative}_shape _ _ _ {gradient.full_shape[2]} {activation.shard_shape[2]} hg.2.2 hxShape{rank} hwShape{rank}",
        ])
    if dw:
        try:
            from .bw_linear_column_dual_renderer import render_dynamic_column_dw_commute
        except ImportError:
            from bw_linear_column_dual_renderer import render_dynamic_column_dw_commute
        hcomm_lines = [line.replace("hDwComm", "hcomm") for line in
                       render_dynamic_column_dw_commute(theorem, gradient, activation, weight)]
        value_rewrites = "hSmWriter, hg.1, hxValue, hwValue, hcomm"
    else:
        hcomm_lines = render_dynamic_column_commute(theorem, gradient, activation, weight)
        value_rewrites = "hSmWriter, hg.1, hwValue, hcomm"
    lines.extend([
        *hcomm_lines,
        f"    have hOutValue : smFinal {output.sm_tid} = allGatherPrimDimN {output_dim} {k} 0 {olist} := by",
        f"      rw [{value_rewrites}]",
        "      rw [" + ", ".join(f"← hPmWriter{rank}" for rank in range(k)) + "]",
        f"    have hOutValueList : smFinal {output.sm_tid} =",
        f"        allGatherPrimDimN {output_dim} {olist}.length 0 {olist} := by",
        "      simpa only [List.length_cons, List.length_nil] using hOutValue",
        f"    have hFullShape : (smFinal {output.sm_tid}).shape = {ofull} := by",
        "      rw [hSmWriter]",
        f"      exact {segment_id}_{derivative}_shape _ _ _ {gradient.full_shape[2]} {activation.full_shape[2]} hg.2.1 hx.full_shape hw.full_shape",
        f"    have hout : {output.fact_id}.Holds smFinal pmFinal := by",
        f"      change ShardedRel (smFinal {output.sm_tid}) {olist} {output_dim} {ofull} {oshard}",
        "      refine {", "        full_value := hOutValueList",
        "        full_shape := hFullShape", "        shards_nonempty := by simp",
        "        gather_dim_lt := by decide", "        shard_shapes := ?_",
        "        shape_contract := by",
        "          simp only [List.length_cons, List.length_nil]",
        "          native_decide", "      }",
        "      intro shard hmem",
        "      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem",
        "      rcases hmem with " + " | ".join(f"h{rank}" for rank in range(k)),
    ])
    for rank in range(k):
        lines.extend(["      · subst shard", f"        exact hOutShape{rank}"])
    publication=[output.fact_id]+([view_output.fact_id] if view_output else []);pub_list="["+", ".join(publication)+"]";fresh_lines=(["      rcases fresh with rfl | rfl","      · exact hout","      · exact houtView"] if view_output else ["      rcases fresh with rfl","      exact hout"])
    lines.extend([
        "    intro fact hfact",
        f"    have covered : fact ∈ {pub_list} ++ {before.state_id}.facts := by",
        f"      exact (show {after.state_id}.facts ⊆ {pub_list} ++ {before.state_id}.facts by native_decide) hfact",
        "    simp only [List.mem_append] at covered", "    rcases covered with fresh | old",
        "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
        *fresh_lines, "    · exact hframe fact old", "",
        "set_option maxRecDepth 8192 in",
        f"private def {segment_id} :",
        f"    ClosedDepSegmentCertificate {ir.sm_graph_ref} {ir.pm_graph_ref} {before.state_id} {after.state_id} where",
        f"  smNodes := {sm_nodes_name}", f"  pmNodes := {pm_nodes_name}",
        "  sound := by", "    intro smStore pmStore hstate",
        f"    exact {segment_id}_sound smStore pmStore hstate", "",
    ])
    return "\n".join(lines)


def render_dynamic_column_commute(theorem, gradient, activation, weight):
    """Common list ABI for singleton and shared dX/dW column frames."""
    xs="["+", ".join(f"pmFinal {t}" for t in activation.pm_tids)+"]"
    ws="["+", ".join(f"pmFinal {t}" for t in weight.pm_tids)+"]"
    return [f"    have hcomm := {theorem} (pmFinal {gradient.joined_pm_tid})",
            f"      (smFinal {activation.sm_tid}) {xs} {ws} {gradient.full_shape[2]} {activation.shard_shape[2]} (by decide) (by decide)",
            "      (by simp) (by simp) hg.2.2 hx.full_shape hx.shard_shapes hw.shard_shapes",
            "    simp only [List.length_cons, List.length_nil, List.zipWith_cons_cons, List.zipWith_nil_left] at hcomm"]


def column_dx_shape_spec(gradient, activation, weight, output, k, *, dw=False):
    """Validate shared column roles and the selected dX/dW output contract."""
    if (k < 1 or len(gradient.full_shape) != 3 or gradient.full_shape[:2] != (1,8)
            or len(activation.shard_shape) != 3 or activation.shard_shape[:2] != (1,8)):
        raise ValueError("column dX tensor ranks or row shape are unsupported")
    o,d=gradient.full_shape[2],activation.shard_shape[2]
    expected_output=((o,d*k),(o,d)) if dw else ((1,8,d*k),(1,8,d))
    if (o <= 0 or d <= 0 or gradient.kind != "joined" or gradient.pm_tids != ()
            or gradient.joined_pm_tid is None
            or activation.kind != "sharded" or activation.gather_dim != 2
            or activation.full_shape != (1,8,d*k) or len(activation.pm_tids) != k
            or weight.kind != "sharded" or weight.gather_dim != 1
            or weight.full_shape != (o,d*k) or weight.shard_shape != (o,d)
            or len(weight.pm_tids) != k
            or output.kind != "sharded" or output.gather_dim != (1 if dw else 2)
            or (output.full_shape,output.shard_shape) != expected_output
            or len(output.pm_tids) != k):
        raise ValueError("column dX role shapes/layouts are inconsistent")
    return {"gradient": (1,8,o), "activation": ((1,8,d*k),(1,8,d)),
            "weight": ((o,d*k),(o,d)), "output": expected_output}
