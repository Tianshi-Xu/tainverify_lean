"""Whole-model proof planning and content-addressed target projections."""
from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass, replace

from .external_pre_fact_selector import select_unproduced_external_pre_facts
from .model_authority import ModelAuthorityIR, materialize_target_ir
from .proof_compiler import (
    CertificateStep, Diagnostic, ProofPlan, RuleRegistry, compile_proof_plan,
)
from .relation_compiler import (
    CertificateTransitionSpec, ClosedDependentChainPlan,
    ClosedDependentSegmentRecord, ClosedRelationStateRecord,
    RelationFactSpec, RelationPlan,
    build_atomic_schedule, build_closed_dependent_chain_plan,
    build_exact_node_coverage_plan, build_transition_dependency_plan,
    compile_relation_plan,
)


@dataclass(frozen=True)
class TargetProofProjection:
    goal_id: int
    graph_authority_key: str
    target_steps: tuple[str, ...]
    ancestry_steps: tuple[str, ...]
    diagnostics: tuple[Diagnostic, ...]
    projection_digest: str


@dataclass(frozen=True)
class SharedProofDAG:
    model_id: str
    steps: dict[str, CertificateStep]
    projections: dict[int, TargetProofProjection]
    authority_digest: str
    plans: dict[int, ProofPlan]


@dataclass(frozen=True)
class TargetRelationProjection:
    goal_id: int
    graph_authority_key: str
    family: str
    terminal_rule_id: str
    fact_keys: tuple[str, ...]
    certificate_keys: tuple[str, ...]
    transition_keys: tuple[str, ...]
    unresolved_frontiers: tuple[tuple[str, ...], ...]
    unresolved_side_conditions: tuple[object, ...]
    closure_key: str | None
    terminal_fact_key: str | None


@dataclass(frozen=True)
class SharedRelationClosure:
    closure_key: str
    representative_goal_id: int
    relation: RelationPlan


@dataclass(frozen=True)
class SharedRelationDAG:
    model_id: str
    facts: dict[str, RelationFactSpec]
    certificates: dict[str, object]
    transitions: dict[str, CertificateTransitionSpec]
    projections: dict[int, TargetRelationProjection]
    closures: dict[str, SharedRelationClosure]
    transition_certificate_keys: dict[str, str]
    authority_digest: str
    global_relation: RelationPlan | None
    proof_dag: SharedProofDAG


def _canonical(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def _step_payload(step: CertificateStep) -> dict:
    return asdict(step)


def _adapter_payload(graph) -> dict:
    return {side + "_adapter_communications": [asdict(record) for record in getattr(graph, side + "_adapter_communications")]
            for side in ("sm", "pm") if getattr(graph, side + "_adapter_communications") is not None}


def _query_payload(query) -> dict:
    payload = asdict(query)
    for side in ("sm", "pm"):
        if payload[side + "_adapter_communications"] is None:
            del payload[side + "_adapter_communications"]
    return payload


def _authority_digest(model: ModelAuthorityIR) -> str:
    payload = {
        "model_id": model.model_id,
        "sm_graph_ref": model.sm_graph_ref,
        "pm_graph_ref": model.pm_graph_ref,
        "sm_num_ranks": model.sm_num_ranks,
        "pm_num_ranks": model.pm_num_ranks,
        "sm_nodes": [asdict(node) for node in model.sm_nodes],
        "pm_nodes": [asdict(node) for node in model.pm_nodes],
        "sm_shapes": model.sm_shapes,
        "pm_shapes": model.pm_shapes,
        "sm_replica_groups": [asdict(group) for group in model.sm_replica_groups],
        "pm_replica_groups": [asdict(group) for group in model.pm_replica_groups],
        "targets": [
            {"goal_id": goal_id, "query": _query_payload(query)}
            for goal_id, query in model.targets.items()
        ],
        "aggregate": None if model.aggregate is None else asdict(model.aggregate),
    }
    payload.update(_adapter_payload(model))
    if model.parallel_authority is not None:
        from .parallel_authority import parallel_authority_payload
        payload["parallel_authority"] = parallel_authority_payload(model.parallel_authority)
    return hashlib.sha256(_canonical(payload)).hexdigest()


def compile_shared_proof_dag(
    model: ModelAuthorityIR, registry: RuleRegistry
) -> SharedProofDAG:
    """Compile target projections and hash-cons identical graph certificate steps.

    This first whole-model slice preserves the existing proven single-target
    planner as an adapter. Shared authority is parsed once; step identities are
    globally stable ``side:node:output`` IDs and conflicting payloads fail
    closed instead of being silently overwritten.
    """
    from .adapter_communication import validate_model_adapter_communications
    validate_model_adapter_communications(model)
    graph_keys = {
        goal_id: _content_key("target-graph-authority", {
            "sm_graph_ref": query.sm_graph_ref,
            "pm_graph_ref": query.pm_graph_ref,
            "sm_num_ranks": query.sm_num_ranks,
            "pm_num_ranks": query.pm_num_ranks,
            "sm_nodes": [asdict(node) for node in query.sm_nodes],
            "pm_nodes": [asdict(node) for node in query.pm_nodes],
            "sm_shapes": query.sm_shapes,
            "pm_shapes": query.pm_shapes,
            "sm_replica_groups": [asdict(group) for group in query.sm_replica_groups],
            "pm_replica_groups": [asdict(group) for group in query.pm_replica_groups],
            **_adapter_payload(query),
        })
        for goal_id, query in model.targets.items()
    }
    multiple_graphs = len(set(graph_keys.values())) > 1
    steps: dict[str, CertificateStep] = {}
    projections: dict[int, TargetProofProjection] = {}
    plans: dict[int, ProofPlan] = {}
    for goal_id in model.targets:
        ir = materialize_target_ir(model, goal_id)
        proof = compile_proof_plan(ir, registry)
        if not proof.supported:
            details = "; ".join(
                f"{item.code.value}: {item.message}" for item in proof.diagnostics
            )
            raise ValueError(f"model target {goal_id} is unsupported: {details}")
        plans[goal_id] = proof
        graph_key = graph_keys[goal_id]
        def shared_step_key(step_id: str) -> str:
            return f"{graph_key}:{step_id}" if multiple_graphs else step_id

        ancestry = tuple(shared_step_key(step.step_id) for step in proof.steps)
        for step in proof.steps:
            key = shared_step_key(step.step_id)
            existing = steps.get(key)
            if existing is not None and _step_payload(existing) != _step_payload(step):
                raise ValueError(
                    f"conflicting shared certificate step identity {key} "
                    f"between model targets"
                )
            steps.setdefault(key, step)
        projection_payload = {
            "goal_id": goal_id,
            "graph_authority_key": graph_key,
            "target_steps": tuple(shared_step_key(item) for item in proof.target_steps),
            "ancestry_steps": ancestry,
            "steps": [_step_payload(step) for step in proof.steps],
            "diagnostics": [asdict(item) for item in proof.diagnostics],
        }
        projections[goal_id] = TargetProofProjection(
            goal_id=goal_id,
            graph_authority_key=graph_key,
            target_steps=tuple(shared_step_key(item) for item in proof.target_steps),
            ancestry_steps=ancestry,
            diagnostics=proof.diagnostics,
            projection_digest=hashlib.sha256(_canonical(projection_payload)).hexdigest(),
        )
    return SharedProofDAG(
        model_id=model.model_id,
        steps=steps,
        projections=projections,
        authority_digest=_authority_digest(model),
        plans=plans,
    )


def _content_key(kind: str, payload) -> str:
    return hashlib.sha256(_canonical({"kind": kind, "payload": payload})).hexdigest()


def _target_relation_fact(proof: ProofPlan) -> RelationFactSpec | None:
    if getattr(proof.relation.kind, "value", proof.relation.kind) != "gather":
        return None
    by_step = {step.step_id: step for step in proof.steps}
    if (len(proof.target_steps) != 3 and proof.target_steps
            and all(ref in by_step for ref in proof.target_steps)
            and {by_step[ref].op for ref in proof.target_steps} in
                ({"FW_maybe_shuffle"}, {"BW_maybe_unshuffle"}, {"FW_attn_zigzag"})):
        return RelationFactSpec("zigzag_k", tuple(proof.target_steps))
    joined = (
        len(proof.target_steps) == 2
        and len(proof.relation.pm_pieces) == 1
        and tuple(by_step[proof.target_steps[0]].output_shape)
        == tuple(by_step[proof.target_steps[1]].output_shape)
    )
    if joined:
        return RelationFactSpec(
            "joined", (proof.target_steps[0],), joined_pm_step=proof.target_steps[1]
        )
    return RelationFactSpec(
        "sharded", tuple(proof.target_steps), gather_dim=int(proof.relation.gather_dim)
    )


def _compiled_terminal_relation_fact(relation: RelationPlan) -> RelationFactSpec:
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("compiled relation has no complete terminal chain")
    matches = tuple(
        item.source for item in chain.relation_facts
        if item.fact_id == chain.terminal_target_fact_id
    )
    if len(matches) != 1:
        raise ValueError("compiled relation terminal fact is not unique")
    return matches[0]


def _build_global_relation_plan(
    model: ModelAuthorityIR,
    proof_dag: SharedProofDAG,
    transitions: dict[str, CertificateTransitionSpec],
    certificates: dict[str, object],
    transition_certificate_keys: dict[str, str],
    projections: dict[int, TargetRelationProjection],
    closures: dict[str, SharedRelationClosure],
    facts: dict[str, RelationFactSpec],
) -> RelationPlan:
    """Rebuild one authority-ordered relation chain from the content-addressed union."""
    representative = max(
        projections.values(),
        key=lambda item: (len(item.transition_keys), -item.goal_id),
    )
    if representative.terminal_fact_key is None:
        raise ValueError("global relation representative lacks a terminal fact")
    ordered_keys = tuple(sorted(transitions))
    global_transitions = tuple(
        replace(transitions[key], transition_id=f"shared_transition_{index:06d}")
        for index, key in enumerate(ordered_keys)
    )
    global_certificates = tuple(
        certificates[key] for key in sorted(certificates)
    )

    merged_init_lineages = {}
    full_init_goal_ids = set()
    for query in model.targets.values():
        full_init_goal_ids.update(query.full_init_goal_ids)
        for tid, lineage in query.init_lineages.items():
            previous = merged_init_lineages.get(tid)
            if previous is not None and previous != lineage:
                raise ValueError(f"conflicting whole-model InitGoal lineage for tid {tid}")
            merged_init_lineages[tid] = lineage
    global_ir = replace(
        materialize_target_ir(model, representative.goal_id),
        init_lineages=merged_init_lineages,
        full_init_goal_ids=tuple(sorted(full_init_goal_ids)),
    )
    global_proof = replace(
        proof_dag.plans[representative.goal_id],
        steps=tuple(proof_dag.steps.values()),
    )
    external = select_unproduced_external_pre_facts(global_transitions)
    coverage = build_exact_node_coverage_plan(global_ir, global_transitions)
    dependency = build_transition_dependency_plan(
        global_transitions, external_pre_facts=external
    )
    schedule = build_atomic_schedule(
        global_ir, global_transitions, external_pre_facts=external
    )

    synchronized = {}
    zigzag_regions = {}
    for closure in closures.values():
        for item in closure.relation.synchronized_steps:
            synchronized.setdefault(_content_key("synchronized-step", asdict(item)), item)
        for item in closure.relation.zigzag_regions:
            zigzag_regions.setdefault(_content_key("zigzag-region", asdict(item)), item)
    base = RelationPlan(
        family="shared-whole-model",
        terminal_rule_id=representative.terminal_rule_id,
        synchronized_steps=tuple(synchronized[key] for key in sorted(synchronized)),
        certificates=global_certificates,
        unresolved_frontiers=(),
        unresolved_layouts=(),
        unresolved_side_conditions=(),
        zigzag_regions=tuple(zigzag_regions[key] for key in sorted(zigzag_regions)),
        transition_specs=global_transitions,
        coverage_plan=coverage,
        dependency_plan=dependency,
        atomic_schedule=schedule,
    )
    protected = tuple(
        facts[item.terminal_fact_key]
        for item in projections.values()
        if item.terminal_fact_key is not None
    )
    primary = facts[representative.terminal_fact_key]
    return replace(
        base,
        dependent_chain_plan=build_closed_dependent_chain_plan(
            global_ir,
            global_proof,
            base,
            protected_sources=protected,
            primary_target_source=primary,
        ),
    )


def materialize_target_relation_plan(
    model: ModelAuthorityIR,
    proof_dag: SharedProofDAG,
    relation_dag: SharedRelationDAG,
    goal_id: int,
    *,
    transition_keys: tuple[str, ...] | None = None,
    primary_target: RelationFactSpec | None = None,
    protected_targets: tuple[RelationFactSpec, ...] | None = None,
    proof_override: ProofPlan | None = None,
    ir_override=None,
    retain_all_authority: bool = False,
) -> RelationPlan:
    """Rebuild one exact target projection without unrelated target authority."""
    try:
        projection = relation_dag.projections[goal_id]
        proof = proof_override or proof_dag.plans[goal_id]
    except KeyError as exc:
        raise ValueError(f"unknown target relation projection {goal_id}") from exc
    if projection.terminal_fact_key is None:
        raise ValueError(f"target {goal_id} relation projection lacks a terminal fact")
    ordered_keys = tuple(sorted(
        projection.transition_keys if transition_keys is None else transition_keys
    ))
    selected = tuple(
        replace(relation_dag.transitions[key], transition_id=f"projected_transition_{index:06d}")
        for index, key in enumerate(ordered_keys)
    )
    selected_certificate_keys = tuple(sorted({
        relation_dag.transition_certificate_keys[key]
        for key in ordered_keys
        if key in relation_dag.transition_certificate_keys
    }))
    selected_certificates = tuple(
        relation_dag.certificates[key] for key in selected_certificate_keys
    )
    ir = materialize_target_ir(model, goal_id) if ir_override is None else ir_override
    external = select_unproduced_external_pre_facts(selected)
    coverage = build_exact_node_coverage_plan(ir, selected)
    dependency = build_transition_dependency_plan(selected, external_pre_facts=external)
    schedule = build_atomic_schedule(ir, selected, external_pre_facts=external)
    synchronized = {}
    zigzag_regions = {}
    for closure in relation_dag.closures.values():
        for item in closure.relation.synchronized_steps:
            synchronized.setdefault(_content_key("synchronized-step", asdict(item)), item)
        for item in closure.relation.zigzag_regions:
            zigzag_regions.setdefault(_content_key("zigzag-region", asdict(item)), item)
    base = RelationPlan(
        family=f"shared-target-{goal_id}",
        terminal_rule_id=projection.terminal_rule_id,
        synchronized_steps=tuple(synchronized[key] for key in sorted(synchronized)),
        certificates=selected_certificates,
        unresolved_frontiers=(),
        unresolved_layouts=(),
        unresolved_side_conditions=(),
        zigzag_regions=tuple(zigzag_regions[key] for key in sorted(zigzag_regions)),
        authority_region_ids=tuple(
            item.region_id for item in zigzag_regions.values()
        ) if ir.packed_cu_contracts else (),
        transition_specs=selected,
        coverage_plan=coverage,
        dependency_plan=dependency,
        atomic_schedule=schedule,
    )
    primary = (
        relation_dag.facts[projection.terminal_fact_key]
        if primary_target is None else primary_target
    )
    return replace(
        base,
        dependent_chain_plan=build_closed_dependent_chain_plan(
            ir,
            proof,
            base,
            protected_sources=(primary,) if protected_targets is None else protected_targets,
            primary_target_source=primary,
            retain_all_authority=retain_all_authority,
        ),
    )


def materialize_shared_prefix_relation_plan(
    model: ModelAuthorityIR,
    proof_dag: SharedProofDAG,
    relation_dag: SharedRelationDAG,
    left_goal_id: int,
    right_goal_id: int,
) -> RelationPlan:
    """Build shared ancestry once, excluding both target terminal transitions."""
    terminal_keys = set()
    terminal_transitions = []
    for goal_id in (left_goal_id, right_goal_id):
        projection = relation_dag.projections[goal_id]
        if projection.terminal_fact_key is None:
            raise ValueError(f"target {goal_id} lacks a terminal relation fact")
        target = relation_dag.facts[projection.terminal_fact_key]
        matches = [
            key for key in projection.transition_keys
            if target in relation_dag.transitions[key].post_facts
        ]
        if len(matches) != 1:
            raise ValueError(f"target {goal_id} terminal transition is not unique")
        terminal_keys.add(matches[0])
        terminal_transitions.append(relation_dag.transitions[matches[0]])
    shared_keys = tuple(sorted(
        (set(relation_dag.projections[left_goal_id].transition_keys)
         | set(relation_dag.projections[right_goal_id].transition_keys))
        - terminal_keys
    ))
    produced = {
        fact: key
        for key in shared_keys
        for fact in relation_dag.transitions[key].post_facts
    }
    primary_candidates = [
        fact for transition in terminal_transitions for fact in transition.pre_facts
        if fact in produced
    ]
    if not primary_candidates:
        raise ValueError("shared prefix has no produced terminal-precondition fact")
    representative_proof = replace(
        proof_dag.plans[left_goal_id],
        steps=tuple(proof_dag.steps.values()),
    )
    full_ir = materialize_target_ir(model, right_goal_id)
    selected_transitions = tuple(relation_dag.transitions[key] for key in shared_keys)
    sm_end = max(index for item in selected_transitions for index in item.sm_node_indices) + 1
    pm_end = max(index for item in selected_transitions for index in item.pm_node_indices) + 1
    prefix_ir = replace(
        full_ir,
        sm_nodes=full_ir.sm_nodes[:sm_end],
        pm_nodes=full_ir.pm_nodes[:pm_end],
    )
    return materialize_target_relation_plan(
        model,
        proof_dag,
        relation_dag,
        right_goal_id,
        transition_keys=shared_keys,
        primary_target=primary_candidates[0],
        protected_targets=tuple(dict.fromkeys(primary_candidates)),
        proof_override=representative_proof,
        ir_override=prefix_ir,
        retain_all_authority=True,
    )


def materialize_terminal_projection_plan(
    model: ModelAuthorityIR,
    proof_dag: SharedProofDAG,
    relation_dag: SharedRelationDAG,
    prefix_relation: RelationPlan,
    goal_id: int,
):
    """Build one local terminal frame over retained shared-prefix facts."""
    full = materialize_target_relation_plan(model, proof_dag, relation_dag, goal_id)
    full_chain = full.dependent_chain_plan
    prefix_chain = prefix_relation.dependent_chain_plan
    if full_chain is None or prefix_chain is None:
        raise ValueError("terminal projection requires complete prefix and target chains")
    terminal_segment = full_chain.segments[-1]
    if len(terminal_segment.transition_ids) != 1:
        raise ValueError(f"target {goal_id} terminal component is not singleton")
    terminal_id = terminal_segment.transition_ids[0]
    transition = next(item for item in full.transition_specs if item.transition_id == terminal_id)
    sm_start, sm_end = terminal_segment.sm_range
    pm_start, pm_end = terminal_segment.pm_range
    full_ir = materialize_target_ir(model, goal_id)
    terminal_ir = replace(
        full_ir,
        sm_nodes=full_ir.sm_nodes[sm_start:sm_end],
        pm_nodes=full_ir.pm_nodes[pm_start:pm_end],
    )
    rebased = replace(
        transition,
        transition_id=f"terminal_transition_goal_{goal_id}",
        sm_node_indices=tuple(index - sm_start for index in transition.sm_node_indices),
        pm_node_indices=tuple(index - pm_start for index in transition.pm_node_indices),
    )
    prefix_records = {item.source: item for item in prefix_chain.relation_facts}
    full_records = {item.source: item for item in full_chain.relation_facts}
    missing_pre = [source for source in rebased.pre_facts if source not in prefix_records]
    if missing_pre:
        raise ValueError(f"target {goal_id} terminal pre-facts are absent from shared prefix: {missing_pre!r}")
    post_records = tuple(
        replace(full_records[source], fact_id=f"fact_goal_{goal_id}_terminal_{index}")
        for index, source in enumerate(rebased.post_facts)
    )
    def authority_key(item):
        payload = asdict(item)
        payload.pop("fact_id", None)
        return (type(item).__name__, _canonical(payload))

    def required_by_terminal(item):
        for requirement in rebased.authority_requirements:
            if item.kind == "tensor_eq" and requirement.kind == "tensor_eq":
                if (requirement.sides == (item.left_side, item.right_side)
                        and requirement.tids == (item.left_tid, item.right_tid)):
                    return True
            elif item.kind == "tensor_shape" and requirement.kind == "tensor_shape":
                if (requirement.sides == (item.side,)
                        and requirement.tids == (item.tid,)
                        and requirement.shape == item.shape):
                    return True
            elif item.kind == "label_bound" and requirement.kind == "label_bound":
                if (requirement.sides == (item.side,)
                        and requirement.tids == (item.tid,)
                        and requirement.length == item.length
                        and requirement.upper_bound == item.upper_bound):
                    return True
        return False

    prefix_authority_by_key = {
        authority_key(item): item for item in prefix_chain.authority_facts
    }
    new_authority = []
    terminal_authority_ids = []
    prefix_final_ids = set(prefix_chain.states[-1].fact_ids)
    for item in full_chain.authority_facts:
        if not required_by_terminal(item):
            continue
        key = authority_key(item)
        selected_item = prefix_authority_by_key.get(key, item)
        if selected_item.fact_id not in prefix_final_ids:
            terminal_authority_ids.append(selected_item.fact_id)
        if key not in prefix_authority_by_key:
            new_authority.append(item)
    extra_authority = tuple(new_authority)
    pre_state = prefix_chain.states[-1]
    if terminal_authority_ids:
        pre_state = ClosedRelationStateRecord(
            f"state_goal_{goal_id}_terminal_pre",
            tuple(dict.fromkeys((*pre_state.fact_ids, *terminal_authority_ids))),
        )
    post_state = ClosedRelationStateRecord(
        f"state_goal_{goal_id}_terminal_post",
        tuple(dict.fromkeys((*pre_state.fact_ids, *(item.fact_id for item in post_records)))),
    )
    segment = ClosedDependentSegmentRecord(
        segment_id=f"segment_goal_{goal_id}_terminal",
        component_id=f"terminal_component_goal_{goal_id}",
        pre_state_id=pre_state.state_id,
        post_state_id=post_state.state_id,
        transition_ids=(rebased.transition_id,),
        sm_range=(0, sm_end - sm_start),
        pm_range=(0, pm_end - pm_start),
    )
    chain = ClosedDependentChainPlan(
        relation_facts=tuple((*prefix_chain.relation_facts, *post_records)),
        authority_facts=tuple((*prefix_chain.authority_facts, *extra_authority)),
        anchor_fact=prefix_chain.anchor_fact,
        states=(pre_state, post_state),
        segments=(segment,),
        initial_state_id=pre_state.state_id,
        terminal_state_id=post_state.state_id,
        terminal_target_fact_id=post_records[0].fact_id,
        retained_target_fact_ids=tuple(item.fact_id for item in post_records),
        expected_sm_node_count=sm_end - sm_start,
        expected_pm_node_count=pm_end - pm_start,
    )
    terminal_relation = replace(
        full,
        transition_specs=(rebased,),
        certificates=tuple(
            certificate for certificate in full.certificates
            if hashlib.sha256(_canonical({
                "type": type(certificate).__name__, "fields": asdict(certificate),
            })).hexdigest() == rebased.certificate_digest
        ),
        dependent_chain_plan=chain,
        coverage_plan=None,
        dependency_plan=None,
        atomic_schedule=None,
    )
    if not chain.complete or len(terminal_relation.certificates) != 1:
        raise ValueError(f"target {goal_id} terminal projection is incomplete")
    return terminal_ir, terminal_relation


def compile_shared_relation_dag(
    model: ModelAuthorityIR, proof_dag: SharedProofDAG
) -> SharedRelationDAG:
    """Compile maximal relation closures once and project target-local sub-DAGs."""
    from .adapter_communication import validate_model_adapter_communications
    validate_model_adapter_communications(model)
    if model.parallel_authority is not None:
        from .parallel_authority import validate_model_parallel_authority
        validate_model_parallel_authority(model)
    if proof_dag.authority_digest != _authority_digest(model):
        raise ValueError("shared proof authority mismatch: recompile after changing graph/configuration authority")
    if tuple(proof_dag.projections) != tuple(model.targets):
        raise ValueError("shared proof projections do not exactly cover model targets")
    facts: dict[str, RelationFactSpec] = {}
    certificates: dict[str, object] = {}
    transitions: dict[str, CertificateTransitionSpec] = {}
    projections: dict[int, TargetRelationProjection] = {}
    closures: dict[str, SharedRelationClosure] = {}
    producer: dict[tuple[str, RelationFactSpec], str] = {}
    producer_closure: dict[tuple[str, RelationFactSpec], str] = {}
    certificate_by_transition: dict[str, str] = {}

    def register_relation(goal_id, relation):
        graph_key = proof_dag.projections[goal_id].graph_authority_key
        local_transition_keys = []
        local_post_facts = []
        local_certificates_by_digest = {}
        for certificate in relation.certificates:
            certificate_key = _content_key(
                f"certificate:{type(certificate).__name__}", asdict(certificate)
            )
            existing_certificate = certificates.get(certificate_key)
            if existing_certificate is not None and existing_certificate != certificate:
                raise ValueError(f"certificate digest collision at target {goal_id}")
            certificates.setdefault(certificate_key, certificate)
            certificate_digest = hashlib.sha256(_canonical({
                "type": type(certificate).__name__,
                "fields": asdict(certificate),
            })).hexdigest()
            previous_key = local_certificates_by_digest.get(certificate_digest)
            if previous_key is not None and previous_key != certificate_key:
                raise ValueError(f"certificate authority digest collision at target {goal_id}")
            local_certificates_by_digest[certificate_digest] = certificate_key

        for transition in relation.transition_specs:
            payload = asdict(transition)
            payload.pop("transition_id", None)
            transition_key = _content_key(
                "transition", {"graph_authority_key": graph_key, "transition": payload}
            )
            existing_transition = transitions.get(transition_key)
            if existing_transition is not None:
                existing_payload = asdict(existing_transition)
                existing_payload.pop("transition_id", None)
                if existing_payload != payload:
                    raise ValueError(f"transition digest collision at target {goal_id}")
            transitions.setdefault(transition_key, transition)
            local_transition_keys.append(transition_key)
            if transition.certificate_digest:
                certificate_key = local_certificates_by_digest.get(
                    transition.certificate_digest
                )
                if certificate_key is None:
                    raise ValueError(
                        f"transition certificate digest is unbound at target {goal_id}"
                    )
                previous_certificate = certificate_by_transition.get(transition_key)
                if previous_certificate is not None and previous_certificate != certificate_key:
                    raise ValueError(
                        f"transition has conflicting certificates at target {goal_id}"
                    )
                certificate_by_transition[transition_key] = certificate_key

            for fact in (*transition.pre_facts, *transition.post_facts):
                fact_key = _content_key("relation-fact", {
                    "graph_authority_key": graph_key,
                    "fact": asdict(fact),
                })
                existing_fact = facts.get(fact_key)
                if existing_fact is not None and existing_fact != fact:
                    raise ValueError(f"relation fact digest collision at target {goal_id}")
                facts.setdefault(fact_key, fact)
            for fact in transition.post_facts:
                scoped_fact = (graph_key, fact)
                previous = producer.get(scoped_fact)
                if previous is not None and previous != transition_key:
                    raise ValueError(f"relation fact has conflicting producers at target {goal_id}")
                producer[scoped_fact] = transition_key
                local_post_facts.append(fact)

        closure_payload = {
            "graph_authority_key": graph_key,
            "transition_keys": sorted(set(local_transition_keys)),
            "dependent_chain_plan": asdict(relation.dependent_chain_plan),
        }
        closure_key = _content_key("relation-closure", closure_payload)
        existing_closure = closures.get(closure_key)
        if existing_closure is not None and existing_closure.relation != relation:
            raise ValueError(f"relation closure digest collision at target {goal_id}")
        closures.setdefault(
            closure_key,
            SharedRelationClosure(
                closure_key=closure_key,
                representative_goal_id=goal_id,
                relation=relation,
            ),
        )
        for fact in local_post_facts:
            producer_closure.setdefault((graph_key, fact), closure_key)
        return closure_key

    def project(goal_id: int, target: RelationFactSpec, family: str, terminal_rule_id: str):
        graph_key = proof_dag.projections[goal_id].graph_authority_key
        pending = [target]
        seen_facts = set()
        transition_keys = set()
        certificate_keys = set()
        while pending:
            fact = pending.pop()
            if fact in seen_facts:
                continue
            seen_facts.add(fact)
            transition_key = producer.get((graph_key, fact))
            if transition_key is None:
                continue
            if transition_key in transition_keys:
                continue
            transition_keys.add(transition_key)
            certificate_key = certificate_by_transition.get(transition_key)
            if certificate_key is not None:
                certificate_keys.add(certificate_key)
            pending.extend(transitions[transition_key].pre_facts)
        fact_keys = tuple(sorted(
            _content_key("relation-fact", {
                "graph_authority_key": graph_key,
                "fact": asdict(fact),
            }) for fact in seen_facts
        ))
        projections[goal_id] = TargetRelationProjection(
            goal_id=goal_id,
            graph_authority_key=graph_key,
            family=family,
            terminal_rule_id=terminal_rule_id,
            fact_keys=fact_keys,
            certificate_keys=tuple(sorted(certificate_keys)),
            transition_keys=tuple(sorted(transition_keys)),
            unresolved_frontiers=(),
            unresolved_side_conditions=(),
            closure_key=producer_closure.get((graph_key, target)),
            terminal_fact_key=_content_key("relation-fact", {
                "graph_authority_key": graph_key,
                "fact": asdict(target),
            }),
        )

    compile_order = sorted(
        proof_dag.plans.items(), key=lambda item: (-len(item[1].steps), item[0])
    )
    for goal_id, proof in compile_order:
        graph_key = proof_dag.projections[goal_id].graph_authority_key
        target = _target_relation_fact(proof)
        if target is None:
            ir = materialize_target_ir(model, goal_id)
            try:
                relation = compile_relation_plan(ir, proof)
            except Exception as exc:
                raise ValueError(
                    f"target {goal_id} relation closure failed: {type(exc).__name__}: {exc}"
                ) from exc
            if relation.unresolved_frontiers or relation.unresolved_side_conditions:
                raise ValueError(
                    f"target {goal_id} relation closure is unresolved: "
                    f"frontiers={relation.unresolved_frontiers}, "
                    f"side_conditions={relation.unresolved_side_conditions}"
                )
            register_relation(goal_id, relation)
            target = _target_relation_fact(proof)
            if target is None:
                raise ValueError(f"target {goal_id} has no projectable relation fact")
        relation = None
        if (graph_key, target) not in producer:
            ir = materialize_target_ir(model, goal_id)
            try:
                relation = compile_relation_plan(ir, proof)
            except Exception as exc:
                raise ValueError(
                    f"target {goal_id} relation closure failed: {type(exc).__name__}: {exc}"
                ) from exc
            if relation.unresolved_frontiers or relation.unresolved_side_conditions:
                raise ValueError(
                    f"target {goal_id} relation closure is unresolved: "
                    f"frontiers={relation.unresolved_frontiers}, "
                    f"side_conditions={relation.unresolved_side_conditions}"
                )
            register_relation(goal_id, relation)
            if (graph_key, target) not in producer:
                target = _compiled_terminal_relation_fact(relation)
        if (graph_key, target) not in producer:
            raise ValueError(f"target {goal_id} relation closure did not produce target fact")
        project(
            goal_id, target,
            relation.family if relation is not None else "shared-projection",
            relation.terminal_rule_id if relation is not None else "shared-projection",
        )

    ordered_projections = {goal_id: projections[goal_id] for goal_id in model.targets}
    for closure_key, closure in tuple(closures.items()):
        protected = tuple(
            facts[projection.terminal_fact_key]
            for projection in ordered_projections.values()
            if projection.closure_key == closure_key
            and projection.terminal_fact_key is not None
        )
        representative = closure.representative_goal_id
        rebuilt_chain = build_closed_dependent_chain_plan(
            materialize_target_ir(model, representative),
            proof_dag.plans[representative],
            closure.relation,
            protected_sources=protected,
        )
        closures[closure_key] = replace(
            closure,
            relation=replace(closure.relation, dependent_chain_plan=rebuilt_chain),
        )
    transition_certificate_keys = {
        key: certificate_by_transition[key]
        for key in sorted(certificate_by_transition)
    }
    graph_keys = {
        projection.graph_authority_key for projection in ordered_projections.values()
    }
    global_relation = None
    if len(graph_keys) == 1:
        global_relation = _build_global_relation_plan(
            model,
            proof_dag,
            transitions,
            certificates,
            transition_certificate_keys,
            ordered_projections,
            closures,
            facts,
        )
    return SharedRelationDAG(
        model_id=model.model_id,
        facts=facts,
        certificates=certificates,
        transitions=transitions,
        projections=ordered_projections,
        closures=closures,
        transition_certificate_keys=transition_certificate_keys,
        authority_digest=proof_dag.authority_digest,
        global_relation=global_relation,
        proof_dag=proof_dag,
    )
