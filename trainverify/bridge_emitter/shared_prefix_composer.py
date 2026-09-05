"""Compose one shared prefix with exact target-local terminal projections."""
from __future__ import annotations

from dataclasses import replace
import re


def compose_shared_prefix_bundle(
    model, relation_dag, namespace: str, module_prefix: str, *,
    max_source_bytes: int, aggregate_theorem_name: str | None,
):
    from .composer import (
        _closed_bundle_module_footer,
        _closed_bundle_module_header,
        _closed_bundle_relation_blocks,
        _closed_segment_family_imports,
        _external_contract_arguments,
        _node_text,
        _promote_closed_segment,
        _validate_closed_bundle,
        compose_closed_dependent_bundle,
        render_closed_external_initial_state,
        render_closed_public_theorem,
        render_closed_segment,
        render_public_aggregate,
    )
    from .model_authority import materialize_target_ir
    from .model_compiler import (
        materialize_shared_prefix_relation_plan,
        materialize_target_relation_plan,
        materialize_terminal_projection_plan,
    )

    projections = sorted(
        relation_dag.projections.values(),
        key=lambda item: (-len(item.transition_keys), item.goal_id),
    )
    if len(projections) < 2:
        raise ValueError("shared-prefix composition requires at least two projections")
    left, right = projections[:2]
    overlap = len(set(left.transition_keys) & set(right.transition_keys))
    if overlap * 10 < 9 * min(len(left.transition_keys), len(right.transition_keys)):
        raise ValueError("largest projections do not have a reusable shared prefix")

    prefix_relation = materialize_shared_prefix_relation_plan(
        model, relation_dag.proof_dag, relation_dag, left.goal_id, right.goal_id
    )
    prefix_chain = prefix_relation.dependent_chain_plan
    if prefix_chain is None or not prefix_chain.complete:
        raise ValueError("shared prefix is incomplete")
    right_ir = materialize_target_ir(model, right.goal_id)
    prefix_ir = replace(
        right_ir,
        sm_nodes=right_ir.sm_nodes[:prefix_chain.expected_sm_node_count],
        pm_nodes=right_ir.pm_nodes[:prefix_chain.expected_pm_node_count],
    )
    bundle = compose_closed_dependent_bundle(
        prefix_ir,
        prefix_relation,
        namespace,
        module_prefix,
        max_source_bytes=max_source_bytes,
        include_public=False,
        require_full_graph=False,
    )
    prefix_chain_source = bundle.pop("Chain.lean")
    bundle["PrefixChain.lean"] = prefix_chain_source
    prefix_state_modules = [
        f"{module_prefix}.{path[:-5]}" for path in bundle if path.startswith("States")
    ]
    prefix_known_facts = {
        *(item.fact_id for item in prefix_chain.relation_facts),
        *(item.fact_id for item in prefix_chain.authority_facts),
        prefix_chain.anchor_fact.fact_id,
    }
    prefix_known_states = {item.state_id for item in prefix_chain.states}

    terminal_data = {}
    emitted_terminal_fact_ids = set()
    previous_terminal_defs = []
    for goal_id in (left.goal_id, right.goal_id):
        ir, relation = materialize_terminal_projection_plan(
            model, relation_dag.proof_dag, relation_dag, prefix_relation, goal_id
        )
        chain = relation.dependent_chain_plan
        assert chain is not None
        post_fact_ids = {
            item.fact_id for item in chain.relation_facts
            if item.fact_id not in prefix_known_facts
        }
        new_authority_ids = {
            item.fact_id for item in chain.authority_facts
            if item.fact_id not in prefix_known_facts
        }
        fact_blocks, _state_blocks = _closed_bundle_relation_blocks(chain, namespace)
        wanted_fact_ids = (post_fact_ids | new_authority_ids) - emitted_terminal_fact_ids
        selected_blocks = []
        for block in fact_blocks:
            match = re.match(r"def\s+([A-Za-z0-9_]+)\s*:", block)
            if match and match.group(1) in wanted_fact_ids:
                selected_blocks.append(block)
        authority_by_id = {item.fact_id: item for item in chain.authority_facts}
        for fact_id in sorted(wanted_fact_ids):
            fact = authority_by_id.get(fact_id)
            if fact is None:
                continue
            helper = f"{fact_id}_holds_of_read"
            if fact.kind == "tensor_shape":
                store = "smStore" if fact.side == "sm" else "pmStore"
                shape = "[" + ", ".join(str(value) for value in fact.shape) + "]"
                premise = f"({store} {fact.tid}).shape = {shape}"
            elif fact.kind == "tensor_eq":
                left_store = "smStore" if fact.left_side == "sm" else "pmStore"
                right_store = "smStore" if fact.right_side == "sm" else "pmStore"
                premise = f"{left_store} {fact.left_tid} = {right_store} {fact.right_tid}"
            elif fact.kind == "label_bound":
                store = "smStore" if fact.side == "sm" else "pmStore"
                premise = (
                    f"∀ l < {fact.length}, scalarToNat "
                    f"(valAt ({store} {fact.tid}) l) < {fact.upper_bound}"
                )
            else:
                raise ValueError(f"unsupported terminal authority helper: {fact!r}")
            selected_blocks.append(
                f"theorem {helper} (smStore pmStore : Store)\n"
                f"    (h : {premise}) : {fact_id}.Holds smStore pmStore := by\n"
                f"  simpa only [{fact_id}, RelationFact.Holds, StoreSide.read] using h"
            )
        pre = chain.states[0]
        post = chain.states[1]
        prefix_final = prefix_chain.states[-1]
        if pre.state_id == prefix_final.state_id:
            pre_block = None
            pre_facts_expr = pre.state_id + ".facts"
        else:
            terminal_only = [fact for fact in pre.fact_ids if fact not in prefix_final.fact_ids]
            if not terminal_only:
                raise ValueError(f"target {goal_id} terminal pre-state has no explicit delta")
            additions = ", ".join(terminal_only)
            pre_block = (
                f"def {pre.state_id} : RelationState where\n"
                f"  facts := {prefix_final.state_id}.facts ++ [{additions}]\n"
                "  nonempty := by decide"
            )
            pre_facts_expr = pre.state_id + ".facts"
        post_only = [fact for fact in post.fact_ids if fact not in pre.fact_ids]
        if not post_only:
            raise ValueError(f"target {goal_id} terminal post-state has no produced fact")
        post_block = (
            f"def {post.state_id} : RelationState where\n"
            f"  facts := {pre_facts_expr} ++ [{', '.join(post_only)}]\n"
            "  nonempty := by decide"
        )
        declaration_body = "\n\n".join([
            *selected_blocks,
            *([pre_block] if pre_block else []),
            post_block,
        ])
        defs_path = f"Target{goal_id}TerminalDefs.lean"
        defs_module = f"{module_prefix}.Target{goal_id}TerminalDefs"
        defs_source = _closed_bundle_module_header(
            f"target {goal_id} terminal facts and states",
            [*prefix_state_modules, *previous_terminal_defs, ir.public_statement_module],
            namespace,
        ) + declaration_body + _closed_bundle_module_footer(namespace)
        bundle[defs_path] = defs_source.encode()
        emitted_terminal_fact_ids.update(wanted_fact_ids)
        previous_terminal_defs.append(defs_module)

        segment = chain.segments[0]
        raw = render_closed_segment(ir, relation, segment.segment_id)
        promoted = _promote_closed_segment(segment.segment_id, raw)
        sm_nodes_text = "[" + ", ".join(_node_text(node) for node in ir.sm_nodes) + "]"
        pm_nodes_text = "[" + ", ".join(_node_text(node) for node in ir.pm_nodes) + "]"
        promoted += (
            f"\ntheorem {segment.segment_id}_sm_nodes_exact :\n"
            f"    {segment.segment_id}.smNodes = {sm_nodes_text} := by rfl\n\n"
            f"theorem {segment.segment_id}_pm_nodes_exact :\n"
            f"    {segment.segment_id}.pmNodes = {pm_nodes_text} := by rfl\n"
        )
        family = tuple(item.rule_id for item in relation.transition_specs)
        terminal_path = f"Target{goal_id}Segment001123.lean"
        terminal_module = f"{module_prefix}.Target{goal_id}Segment001123"
        terminal_source = _closed_bundle_module_header(
            f"target {goal_id} terminal projection",
            [
                ir.public_statement_module,
                *prefix_state_modules,
                defs_module,
                *_closed_segment_family_imports(
                    family, tuple(item.lean_theorem for item in relation.transition_specs)
                ),
            ],
            namespace,
        ) + promoted + _closed_bundle_module_footer(namespace)
        bundle[terminal_path] = terminal_source.encode()
        terminal_data[goal_id] = (ir, relation, terminal_module)

    prefix_bound_keys = {
        (item.side, item.tid, item.length, item.upper_bound)
        for item in prefix_chain.authority_facts if item.kind == "label_bound"
    }

    def prefix_contract_ir(ir):
        return replace(
            ir,
            tensor_value_bound_contracts=tuple(
                contract for contract in ir.tensor_value_bound_contracts
                if (contract.side, contract.tid, contract.length, contract.upper_bound)
                in prefix_bound_keys
            ),
        )

    public_parts = []
    prefix_initial_names = {}
    for goal_id in (left.goal_id, right.goal_id):
        ir = materialize_target_ir(model, goal_id)
        prefix_ir_contract = prefix_contract_ir(ir)
        initial_namespace = f"{namespace}Goal{goal_id}Prefix"
        public_parts.append(
            render_closed_external_initial_state(
                prefix_ir_contract, prefix_relation, initial_namespace
            ).rstrip()
        )
        prefix_initial_names[goal_id] = f"{initial_namespace}_initial_state"

    prefix_chain_name = f"{namespace}_chain"
    for goal_id in (left.goal_id, right.goal_id):
        full_ir = materialize_target_ir(model, goal_id)
        terminal_ir, terminal_relation, _terminal_module = terminal_data[goal_id]
        terminal_chain = terminal_relation.dependent_chain_plan
        assert terminal_chain is not None
        terminal_segment = terminal_chain.segments[0]
        _, full_call_args, _ = _external_contract_arguments(full_ir)
        prefix_ir_contract = prefix_contract_ir(full_ir)
        _, prefix_call_args, _ = _external_contract_arguments(prefix_ir_contract)
        prefix_sm = (
            f"{prefix_chain_name}.smNodes.foldl "
            f"(applyNodeDistributedFaithful {full_ir.sm_graph_ref}) initSM"
        )
        prefix_pm = (
            f"{prefix_chain_name}.pmNodes.foldl "
            f"(applyNodeDistributedFaithful {full_ir.pm_graph_ref}) initPM"
        )
        prefix_sm_nodes = (
            f"{full_ir.sm_graph_ref}.nodes.take {prefix_chain.expected_sm_node_count}"
        )
        prefix_pm_nodes = (
            f"{full_ir.pm_graph_ref}.nodes.take {prefix_chain.expected_pm_node_count}"
        )
        extraction = [
            f"  have hprefixPre := {prefix_initial_names[goal_id]} {prefix_call_args}",
            f"  have hprefix := {prefix_chain_name}.sound initSM initPM hprefixPre",
        ]
        pre = terminal_chain.states[0]
        prefix_final = prefix_chain.states[-1]
        if pre.state_id == prefix_final.state_id:
            extraction.append("  have hterminalPre := hprefix")
        else:
            extra_ids = [fact for fact in pre.fact_ids if fact not in prefix_final.fact_ids]
            if not extra_ids:
                raise ValueError(f"target {goal_id} terminal extension is empty")
            authority_by_id = {item.fact_id: item for item in terminal_chain.authority_facts}
            authority_names = []
            generated_ns = full_ir.lineage_ref.rsplit(".", 1)[0]
            for index, extra_id in enumerate(extra_ids):
                extra = authority_by_id.get(extra_id)
                if extra is None:
                    raise ValueError(f"target {goal_id} terminal extension is not authority: {extra_id}")
                proof_name = f"hTerminalAuthority{index}"
                authority_names.append(proof_name)
                if extra.kind == "tensor_shape":
                    graph = full_ir.sm_graph_ref if extra.side == "sm" else full_ir.pm_graph_ref
                    store = "initSM" if extra.side == "sm" else "initPM"
                    prefix_store = prefix_sm if extra.side == "sm" else prefix_pm
                    shape = "[" + ", ".join(str(value) for value in extra.shape) + "]"
                    hypothesis = "hSM" if extra.side == "sm" else "hPM"
                    extraction.extend([
                        f"  have hTerminalRead{index} : ({prefix_store}) {extra.tid} = {store} {extra.tid} := by",
                        f"    rw [{prefix_chain_name}_{'sm_nodes' if extra.side == 'sm' else 'pm_nodes'}]",
                        f"    exact foldl_applyNodeDistributedFaithful_at_not_written {graph}",
                        f"      ({prefix_sm_nodes if extra.side == 'sm' else prefix_pm_nodes}) {store} {extra.tid} (by native_decide) (by native_decide)",
                        f"  have {proof_name} : {extra_id}.Holds ({prefix_sm}) ({prefix_pm}) := by",
                        f"    apply {extra_id}_holds_of_read",
                        f"    rw [hTerminalRead{index}]",
                        f"    exact {hypothesis} {extra.tid} {shape} (by native_decide)",
                    ])
                elif extra.kind == "label_bound":
                    bound_indices = [
                        index for index, contract in enumerate(full_ir.tensor_value_bound_contracts)
                        if (contract.side, contract.tid, contract.length, contract.upper_bound)
                        == (extra.side, extra.tid, extra.length, extra.upper_bound)
                    ]
                    if len(bound_indices) != 1:
                        raise ValueError(
                            f"target {goal_id} label-bound authority lacks one exact caller contract"
                        )
                    bound_name = f"hBound_{bound_indices[0]}"
                    extraction.extend([
                        f"  have hTerminalRead{index} : ({prefix_pm}) {extra.tid} = initPM {extra.tid} := by",
                        f"    rw [{prefix_chain_name}_pm_nodes]",
                        f"    exact foldl_applyNodeDistributedFaithful_at_not_written {full_ir.pm_graph_ref}",
                        f"      ({prefix_pm_nodes}) initPM {extra.tid} (by native_decide) (by native_decide)",
                        f"  have {proof_name} : {extra_id}.Holds ({prefix_sm}) ({prefix_pm}) := by",
                        f"    apply {extra_id}_holds_of_read",
                        f"    rw [hTerminalRead{index}]",
                        f"    exact {bound_name}",
                    ])
                elif extra.kind == "tensor_eq" and (extra.left_side, extra.right_side) == ("sm", "pm"):
                    goal = f"{generated_ns}.initGoal_{extra.left_tid}"
                    extraction.extend([
                        f"  have hTerminalSmRead{index} : ({prefix_sm}) {extra.left_tid} = initSM {extra.left_tid} := by",
                        f"    rw [{prefix_chain_name}_sm_nodes]",
                        f"    exact foldl_applyNodeDistributedFaithful_at_not_written {full_ir.sm_graph_ref}",
                        f"      ({prefix_sm_nodes}) initSM {extra.left_tid} (by native_decide) (by native_decide)",
                        f"  have hTerminalPmRead{index} : ({prefix_pm}) {extra.right_tid} = initPM {extra.right_tid} := by",
                        f"    rw [{prefix_chain_name}_pm_nodes]",
                        f"    exact foldl_applyNodeDistributedFaithful_at_not_written {full_ir.pm_graph_ref}",
                        f"      ({prefix_pm_nodes}) initPM {extra.right_tid} (by native_decide) (by native_decide)",
                        f"  have hTerminalInitEq{index} : initSM {extra.left_tid} = initPM {extra.right_tid} := by",
                        f"    have hi := hInit {goal} (by native_decide)",
                        f"    exact InitGoalHolds.singleton_value_eq {full_ir.pm_graph_ref}.numRanks {goal} initSM initPM",
                        f"      {{ rank := 0, tid := {extra.right_tid} }} hi rfl",
                        f"  have {proof_name} : {extra_id}.Holds ({prefix_sm}) ({prefix_pm}) := by",
                        f"    apply {extra_id}_holds_of_read",
                        f"    rw [hTerminalSmRead{index}, hTerminalPmRead{index}]",
                        f"    exact hTerminalInitEq{index}",
                    ])
                else:
                    raise ValueError(
                        f"target {goal_id} terminal authority transport unsupported: {extra!r}"
                    )
            extraction.extend([
                f"  have hterminalPre : {pre.state_id}.Holds ({prefix_sm}) ({prefix_pm}) := by",
                "    intro fact hfact",
                f"    change fact ∈ {prefix_final.state_id}.facts ++ [{', '.join(extra_ids)}] at hfact",
                "    rcases List.mem_append.mp hfact with old | hfact",
                "    · exact hprefix fact old",
                "    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfact",
            ])
            for index, proof_name in enumerate(authority_names[:-1]):
                extraction.extend([
                    "      rcases hfact with rfl | hfact",
                    f"      · exact {proof_name}",
                ])
            extraction.extend([
                "      subst fact",
                f"      exact {authority_names[-1]}",
            ])
        target_id = terminal_chain.terminal_target_fact_id
        extraction.extend([
            f"  have hterminal := {terminal_segment.segment_id}.sound ({prefix_sm}) ({prefix_pm}) hterminalPre",
            f"  have htarget := hterminal {target_id} (by native_decide)",
            f"  have hSmNodes : {prefix_chain_name}.smNodes ++ {terminal_segment.segment_id}.smNodes = {full_ir.sm_graph_ref}.nodes := by",
            f"    rw [{prefix_chain_name}_sm_nodes]",
            f"    rw [{terminal_segment.segment_id}_sm_nodes_exact]",
            "    native_decide",
            f"  have hPmNodes : {prefix_chain_name}.pmNodes ++ {terminal_segment.segment_id}.pmNodes = {full_ir.pm_graph_ref}.nodes := by",
            f"    rw [{prefix_chain_name}_pm_nodes]",
            f"    rw [{terminal_segment.segment_id}_pm_nodes_exact]",
            "    native_decide",
            "  unfold denoteGraphDistributedFaithful",
            "  rw [← hSmNodes, ← hPmNodes]",
            "  simpa only [List.foldl_append] using htarget",
        ])
        public_parts.append(render_closed_public_theorem(
            full_ir,
            terminal_relation,
            namespace,
            declaration_prefix=f"{namespace}_goal_{goal_id}",
            include_external=False,
            target_extraction_lines=tuple(extraction),
        ).rstrip())

    expected_segments = len(prefix_chain.segments) + 2
    public_imports = [
        f"{module_prefix}.PrefixChain",
        *(data[2] for data in terminal_data.values()),
    ]
    for goal_id in model.targets:
        if goal_id in terminal_data:
            continue
        ir = materialize_target_ir(model, goal_id)
        projected = materialize_target_relation_plan(
            model, relation_dag.proof_dag, relation_dag, goal_id
        )
        local_namespace = f"{namespace}Target{goal_id}"
        local_prefix = f"{module_prefix}.Target{goal_id}"
        local = compose_closed_dependent_bundle(
            ir, projected, local_namespace, local_prefix,
            max_source_bytes=max_source_bytes,
        )
        expected_segments += len(projected.dependent_chain_plan.segments)
        for relative, payload in local.items():
            flattened = f"Target{goal_id}{relative}"
            source = payload.decode().replace(local_prefix + ".", local_prefix)
            bundle[flattened] = source.encode()
        public_imports.append(f"{module_prefix}.Target{goal_id}Public")
        public_parts.extend([
            f"theorem prove_goal_{goal_id}_closed : {ir.public_statement_ref} := by",
            f"  exact TrainVerify.Denote.{local_namespace}.prove_goal_{goal_id}_closed",
        ])

    for query in model.targets.values():
        if query.public_statement_module not in public_imports:
            public_imports.append(query.public_statement_module)
    public_source = _closed_bundle_module_header(
        "shared-prefix exact target projections", public_imports, namespace
    ) + "\n\n".join(public_parts) + _closed_bundle_module_footer(namespace)
    bundle["Public.lean"] = public_source.encode()
    if model.aggregate is not None:
        if aggregate_theorem_name is None:
            raise ValueError("complete aggregate authority requires an aggregate theorem name")
        main_source = _closed_bundle_module_header(
            "exact whole-model public aggregate",
            [f"{module_prefix}.Public", model.aggregate.statement_module],
            namespace,
        ) + render_public_aggregate(model, aggregate_theorem_name).rstrip() + _closed_bundle_module_footer(namespace)
        bundle["Main.lean"] = main_source.encode()
    _validate_closed_bundle(bundle, module_prefix, max_source_bytes, expected_segments)
    return bundle
