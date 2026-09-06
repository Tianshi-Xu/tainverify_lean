"""Whole-model authority parsing with lightweight per-target projections.

This module is an additive compatibility layer: existing single-Goal compilers
still consume ``GoalIR``, while the shared graph authority is parsed once and
materialized as target-specific views without reparsing graph nodes/shapes.
"""
from __future__ import annotations

import hashlib
import os
import re
from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .parallel_authority import ParallelGraphAuthority

from . import parser as p


@dataclass(frozen=True)
class TargetQuery:
    goal_id: int
    sm_nodes: list[p.Node]
    pm_nodes: list[p.Node]
    sm_shapes: list[tuple[int, list[int]]]
    pm_shapes: list[tuple[int, list[int]]]
    sm_graph_ref: str
    pm_graph_ref: str
    sm_num_ranks: int
    pm_num_ranks: int
    sm_replica_groups: tuple[p.ReplicaGroup, ...]
    pm_replica_groups: tuple[p.ReplicaGroup, ...]
    lineage: p.LineageGoal
    prereqs: tuple[int, ...]
    public_statement_module: str
    public_statement_ref: str
    public_statement_digest: str
    public_statement_uses_contract_wrapper: bool
    public_statement_contract_ref: str
    public_statement_uses_faithful_evaluator: bool
    lineage_ref: str
    init_goals_ref: str
    packed_cu_contracts: tuple[p.PackedCuContract, ...]
    tensor_value_bound_contracts: tuple[p.TensorValueBoundContract, ...]
    sm_input_value_classes: tuple[p.InputValueClass, ...]
    pm_input_value_classes: tuple[p.InputValueClass, ...]
    sm_input_value_classes_ref: str
    pm_input_value_classes_ref: str
    init_lineages: dict[int, p.LineageGoal]
    full_init_goal_ids: tuple[int, ...]
    sm_adapter_communications: tuple[p.AdapterCommunication, ...] | None = None
    pm_adapter_communications: tuple[p.AdapterCommunication, ...] | None = None


@dataclass(frozen=True)
class PublicAggregateAuthority:
    form: str
    statement_module: str
    statement_ref: str
    statement_digest: str
    goals_ref: str
    goal_chunk_refs: tuple[str, ...]
    ordered_target_chunks: tuple[tuple[int, ...], ...]
    ordered_target_ids: tuple[int, ...]
    ordered_lineage_refs: tuple[str, ...]


@dataclass(frozen=True)
class ModelAuthorityIR:
    model_id: str
    root: str
    sm_nodes: list[p.Node]
    pm_nodes: list[p.Node]
    sm_shapes: list[tuple[int, list[int]]]
    pm_shapes: list[tuple[int, list[int]]]
    sm_graph_ref: str
    pm_graph_ref: str
    sm_num_ranks: int
    pm_num_ranks: int
    sm_replica_groups: tuple[p.ReplicaGroup, ...]
    pm_replica_groups: tuple[p.ReplicaGroup, ...]
    targets: dict[int, TargetQuery]
    aggregate: PublicAggregateAuthority | None
    parallel_authority: ParallelGraphAuthority | None = None
    sm_adapter_communications: tuple[p.AdapterCommunication, ...] | None = None
    pm_adapter_communications: tuple[p.AdapterCommunication, ...] | None = None


@dataclass(frozen=True)
class PublicStatementEntry:
    text: str
    module: str
    name: str


@dataclass(frozen=True)
class PublicStatementInventory:
    entries: dict[int, PublicStatementEntry]
    goal_texts: dict[int, str]


def _parse_public_aggregate(
    gen_text: str,
    gen_module: str,
    target_ids: tuple[int, ...],
) -> PublicAggregateAuthority | None:
    """Bind a complete target inventory to the generated aggregate authority."""
    if not re.search(r"(?m)^\s*def\s+all_goals_stmt\s*:", gen_text):
        return None
    goals_block = p.extract_def_block(gen_text, "goals")
    chunk_names = re.findall(r"\bgoalChunk_\d+\b", goals_block)
    if chunk_names:
        chunk_lineage_names = tuple(
            tuple(re.findall(
                r"\bgoal_\d+\b", p.extract_def_block(gen_text, chunk_name)
            ))
            for chunk_name in chunk_names
        )
    else:
        chunk_lineage_names = (tuple(re.findall(r"\bgoal_\d+\b", goals_block)),)
    lineage_names = [name for chunk in chunk_lineage_names for name in chunk]
    ordered_ids = tuple(int(name.removeprefix("goal_")) for name in lineage_names)
    if len(ordered_ids) != len(set(ordered_ids)):
        raise ValueError("aggregate goals authority contains duplicate targets")
    if ordered_ids != target_ids:
        return None
    return PublicAggregateAuthority(
        form="lineage-list",
        statement_module=gen_module,
        statement_ref=p._qualified_definition_name("all_goals_stmt", gen_text),
        statement_digest=hashlib.sha256(
            p.extract_def_block(gen_text, "all_goals_stmt").encode("utf-8")
        ).hexdigest(),
        goals_ref=p._qualified_definition_name("goals", gen_text),
        goal_chunk_refs=tuple(
            p._qualified_definition_name(name, gen_text) for name in chunk_names
        ),
        ordered_target_chunks=tuple(
            tuple(int(name.removeprefix("goal_")) for name in chunk)
            for chunk in chunk_lineage_names
        ),
        ordered_target_ids=ordered_ids,
        ordered_lineage_refs=tuple(
            p._qualified_definition_name(name, gen_text) for name in lineage_names
        ),
    )


def _parse_exact_public_aggregate(
    root: str,
    target_ids: tuple[int, ...],
    inventory: PublicStatementInventory,
) -> PublicAggregateAuthority | None:
    path = os.path.join(root, p.DENOTE_DIR, "AllGoalsFull.lean")
    if not os.path.isfile(path):
        return None
    with open(path, encoding="utf-8") as handle:
        text = handle.read()
    block = p.extract_def_block(text, "all_goals_stmt_full")
    statement_names = tuple(
        re.findall(r"\bgoal_\d+_stmt(?:_full)?\b", block)
    )
    ordered_ids = tuple(
        int(re.search(r"goal_(\d+)_stmt", name).group(1))
        for name in statement_names
    )
    if ordered_ids != target_ids:
        raise ValueError(
            "exact public aggregate target order differs from requested inventory"
        )
    expected_names = tuple(inventory.entries[n].name for n in target_ids)
    if statement_names != expected_names:
        raise ValueError(
            "exact public aggregate does not name the selected statements"
        )
    module = f"{p.MOD_PREFIX}.AllGoalsFull"
    return PublicAggregateAuthority(
        form="conjunction",
        statement_module=module,
        statement_ref=p._qualified_definition_name("all_goals_stmt_full", text),
        statement_digest=hashlib.sha256(block.encode("utf-8")).hexdigest(),
        goals_ref="",
        goal_chunk_refs=(),
        ordered_target_chunks=(target_ids,),
        ordered_target_ids=target_ids,
        ordered_lineage_refs=tuple(
            p._qualified_definition_name(
                inventory.entries[n].name, inventory.entries[n].text
            )
            for n in target_ids
        ),
    )


def _build_public_statement_inventory(
    root: str, target_ids: tuple[int, ...], gen_text: str
) -> PublicStatementInventory:
    """Scan the statement corpus once and preserve unique-full/fallback semantics."""
    wanted = set(target_ids)
    goal_dir = os.path.join(root, p.DENOTE_DIR)
    gen_path = os.path.abspath(os.path.join(root, p.GEN_DIR, p.GEN_FILE))
    relative = p.GEN_DIR.removeprefix("trainverify/").strip("/").replace("/", ".")
    gen_module = relative + "." + os.path.splitext(p.GEN_FILE)[0]
    full: dict[int, list[PublicStatementEntry]] = {n: [] for n in target_ids}
    goal_texts: dict[int, str] = {}
    for filename in sorted(os.listdir(goal_dir)):
        if not filename.endswith(".lean"):
            continue
        path = os.path.join(goal_dir, filename)
        if os.path.abspath(path) == gen_path:
            text = gen_text
        else:
            with open(path, encoding="utf-8") as handle:
                text = handle.read()
        goal_match = re.fullmatch(r"Goal_(\d+)\.lean", filename)
        if goal_match and int(goal_match.group(1)) in wanted:
            goal_texts[int(goal_match.group(1))] = text
        module = (gen_module if os.path.abspath(path) == gen_path else
                  p.MOD_PREFIX + "." + os.path.splitext(filename)[0])
        for match in re.finditer(r"(?m)^\s*def\s+goal_(\d+)_stmt_full\s*:", text):
            n = int(match.group(1))
            if n in wanted:
                full[n].append(PublicStatementEntry(text, module, f"goal_{n}_stmt_full"))

    legacy = {
        int(match.group(1))
        for match in re.finditer(r"(?m)^\s*def\s+goal_(\d+)_stmt\s*:", gen_text)
    }
    entries = {}
    for n in target_ids:
        candidates = full[n]
        if len(candidates) > 1:
            raise ValueError(
                f"expected exactly one exported goal_{n}_stmt_full definition, "
                f"found {len(candidates)}"
            )
        if candidates:
            entries[n] = candidates[0]
        elif n in legacy:
            entries[n] = PublicStatementEntry(gen_text, gen_module, f"goal_{n}_stmt")
            goal_texts[n] = gen_text
        else:
            raise ValueError(
                f"expected exactly one exported goal_{n}_stmt_full definition, found 0"
            )
    return PublicStatementInventory(entries=entries, goal_texts=goal_texts)


def _query_from_ir(ir: p.GoalIR, public_statement_digest: str) -> TargetQuery:
    return TargetQuery(
        goal_id=ir.n,
        sm_nodes=ir.sm_nodes,
        pm_nodes=ir.pm_nodes,
        sm_shapes=ir.sm_shapes,
        pm_shapes=ir.pm_shapes,
        sm_graph_ref=ir.sm_graph_ref,
        pm_graph_ref=ir.pm_graph_ref,
        sm_num_ranks=ir.sm_num_ranks,
        pm_num_ranks=ir.pm_num_ranks,
        sm_replica_groups=ir.sm_replica_groups,
        pm_replica_groups=ir.pm_replica_groups,
        lineage=ir.lineage,
        prereqs=tuple(ir.prereqs),
        public_statement_module=ir.public_statement_module,
        public_statement_ref=ir.public_statement_ref,
        public_statement_digest=public_statement_digest,
        public_statement_uses_contract_wrapper=ir.public_statement_uses_contract_wrapper,
        public_statement_contract_ref=ir.public_statement_contract_ref,
        public_statement_uses_faithful_evaluator=ir.public_statement_uses_faithful_evaluator,
        lineage_ref=ir.lineage_ref,
        init_goals_ref=ir.init_goals_ref,
        packed_cu_contracts=ir.packed_cu_contracts,
        tensor_value_bound_contracts=ir.tensor_value_bound_contracts,
        sm_input_value_classes=ir.sm_input_value_classes,
        pm_input_value_classes=ir.pm_input_value_classes,
        sm_input_value_classes_ref=ir.sm_input_value_classes_ref,
        pm_input_value_classes_ref=ir.pm_input_value_classes_ref,
        init_lineages=dict(ir.init_lineages),
        full_init_goal_ids=ir.full_init_goal_ids,
        sm_adapter_communications=ir.sm_adapter_communications,
        pm_adapter_communications=ir.pm_adapter_communications,
    )


def _parse_target_query(
    model: ModelAuthorityIR,
    n: int,
    gen_text: str,
    inventory: PublicStatementInventory,
    shared_query: TargetQuery,
) -> TargetQuery:
    try:
        goal_text = inventory.goal_texts[n]
        entry = inventory.entries[n]
    except KeyError as exc:
        raise ValueError(f"target {n} is missing from the parser corpus") from exc
    (
        statement_text, public_statement_module, sm_graph_ref, pm_graph_ref,
        _sm_name, _pm_name, _sm_shapes_name, _pm_shapes_name, statement_name,
    ) = p._public_scope_from_statement(entry.text, entry.module, entry.name)
    sources = tuple(dict.fromkeys((goal_text, statement_text, gen_text)))
    resolved_sm = p._qualified_definition_name(sm_graph_ref, *sources)
    resolved_pm = p._qualified_definition_name(pm_graph_ref, *sources)
    if (resolved_sm, resolved_pm) != (model.sm_graph_ref, model.pm_graph_ref):
        target_ir = p.load_goal_ir(n, model.root)
        if (target_ir.sm_graph_ref, target_ir.pm_graph_ref) != (resolved_sm, resolved_pm):
            raise ValueError(f"target {n} parser resolved inconsistent graph authority")
        statement_block = p.extract_def_block(statement_text, statement_name)
        if target_ir.public_statement_ref != p._qualified_definition_name(
            statement_name, statement_text
        ):
            raise ValueError(f"target {n} parser resolved inconsistent public statement")
        return _query_from_ir(
            target_ir, hashlib.sha256(statement_block.encode("utf-8")).hexdigest()
        )
    scope_text = goal_text + "\n" + statement_text
    packed = p.parse_packed_cu_contracts(statement_text, *sources)
    bounds = p.parse_tensor_value_bound_contracts(statement_text, *sources)
    sm_classes = p.parse_input_value_classes(
        *sources,
        name="smInputValueClasses",
        required="smInputValueClasses" in statement_text,
    )
    pm_classes = p.parse_input_value_classes(
        *sources,
        name="pmInputValueClasses",
        required="pmInputValueClasses" in statement_text,
    )
    init_goals_name = p.parse_full_init_goals_name(statement_text, n)
    init_goals_ref = p._qualified_definition_name(init_goals_name, *sources)
    if init_goals_ref == shared_query.init_goals_ref:
        full_init_ids = shared_query.full_init_goal_ids
        init_lineages = dict(shared_query.init_lineages)
    else:
        full_init_ids = p.parse_full_init_goal_ids(scope_text, gen_text, n)
        needed_init_tids = {int(tid) for node in model.sm_nodes for tid in node.ins}
        init_lineages = {
            tid: p.parse_lineage_block(
                p.extract_def_block(gen_text, f"initGoal_{tid}"), f"initGoal_{tid}"
            )
            for tid in sorted(needed_init_tids & set(full_init_ids))
        }
    statement_block = p.extract_def_block(statement_text, statement_name)
    return TargetQuery(
        goal_id=n,
        sm_nodes=model.sm_nodes,
        pm_nodes=model.pm_nodes,
        sm_shapes=model.sm_shapes,
        pm_shapes=model.pm_shapes,
        sm_graph_ref=model.sm_graph_ref,
        pm_graph_ref=model.pm_graph_ref,
        sm_num_ranks=model.sm_num_ranks,
        pm_num_ranks=model.pm_num_ranks,
        sm_replica_groups=model.sm_replica_groups,
        pm_replica_groups=model.pm_replica_groups,
        lineage=p.parse_lineage(gen_text, n),
        prereqs=tuple(p.parse_prereqs(scope_text, n)),
        public_statement_module=public_statement_module,
        public_statement_ref=p._qualified_definition_name(statement_name, statement_text),
        public_statement_digest=hashlib.sha256(
            statement_block.encode("utf-8")
        ).hexdigest(),
        public_statement_uses_contract_wrapper=(
            "CoarseLineageHoldsWithInitDistributedFaithfulWithContract" in statement_block
        ),
        public_statement_contract_ref=p.parse_public_statement_contract_ref(statement_text, n),
        public_statement_uses_faithful_evaluator=(
            "CoarseLineageHoldsWithInitDistributedFaithful" in statement_block
        ),
        lineage_ref=p._qualified_definition_name(f"goal_{n}", *sources),
        init_goals_ref=init_goals_ref,
        packed_cu_contracts=packed,
        tensor_value_bound_contracts=bounds,
        sm_input_value_classes=sm_classes,
        pm_input_value_classes=pm_classes,
        sm_input_value_classes_ref=p.parse_input_value_classes_ref(
            statement_text, n, "sm", *sources
        ),
        pm_input_value_classes_ref=p.parse_input_value_classes_ref(
            statement_text, n, "pm", *sources
        ),
        init_lineages=init_lineages,
        full_init_goal_ids=full_init_ids,
        sm_adapter_communications=model.sm_adapter_communications,
        pm_adapter_communications=model.pm_adapter_communications,
    )


def load_model_authority(
    target_ids: tuple[int, ...] | list[int], root: str, *, model_id: str,
    allow_partial: bool = False,
) -> ModelAuthorityIR:
    ids = tuple(int(n) for n in target_ids)
    if not ids:
        raise ValueError("model target inventory must be nonempty")
    if len(ids) != len(set(ids)):
        raise ValueError("model target inventory must contain unique IDs")
    base = p.load_goal_ir(ids[0], root)
    model = ModelAuthorityIR(
        model_id=model_id,
        root=root,
        sm_nodes=base.sm_nodes,
        pm_nodes=base.pm_nodes,
        sm_shapes=base.sm_shapes,
        pm_shapes=base.pm_shapes,
        sm_graph_ref=base.sm_graph_ref,
        pm_graph_ref=base.pm_graph_ref,
        sm_num_ranks=base.sm_num_ranks,
        pm_num_ranks=base.pm_num_ranks,
        sm_replica_groups=base.sm_replica_groups,
        pm_replica_groups=base.pm_replica_groups,
        sm_adapter_communications=base.sm_adapter_communications,
        pm_adapter_communications=base.pm_adapter_communications,
        targets={},
        aggregate=None,
    )
    gen_path = os.path.join(root, p.GEN_DIR, p.GEN_FILE)
    with open(gen_path, encoding="utf-8") as handle:
        gen_text = handle.read()
    inventory = _build_public_statement_inventory(root, ids, gen_text)
    base_entry = inventory.entries[ids[0]]
    base_statement = p.extract_def_block(base_entry.text, base_entry.name)
    shared_query = _query_from_ir(
        base, hashlib.sha256(base_statement.encode("utf-8")).hexdigest()
    )
    targets = {ids[0]: shared_query}
    for n in ids[1:]:
        targets[n] = _parse_target_query(model, n, gen_text, inventory, shared_query)
    object.__setattr__(model, "targets", targets)
    gen_relative = p.GEN_DIR.removeprefix("trainverify/").strip("/").replace("/", ".")
    gen_module = gen_relative + "." + os.path.splitext(p.GEN_FILE)[0]
    if allow_partial:
        aggregate = None
    else:
        legacy = _parse_public_aggregate(gen_text, gen_module, ids)
        legacy_matches_targets = legacy is not None and all(
            inventory.entries[n].module == gen_module
            and inventory.entries[n].name == f"goal_{n}_stmt"
            for n in ids
        )
        try:
            aggregate = _parse_exact_public_aggregate(root, ids, inventory)
        except ValueError as exc:
            if ("target order differs" not in str(exc)) or not legacy_matches_targets:
                raise
            aggregate = legacy
        if aggregate is None and legacy_matches_targets:
            aggregate = legacy
        if aggregate is None:
            raise ValueError(
                "whole-model authority requires a complete aggregate whose ordered "
                "targets exactly match the requested inventory; pass allow_partial=True "
                "only for diagnostic projections"
            )
    object.__setattr__(model, "aggregate", aggregate)
    return model


def bind_parallel_authority(model: ModelAuthorityIR, topology, *, graph_scope: str, scale_unit: int = 0) -> ModelAuthorityIR:
    """Attach one source topology to all projections, without inferring subgroups."""
    from .parallel_authority import bind_model
    return bind_model(model, topology, graph_scope=graph_scope, scale_unit=scale_unit)


def materialize_target_ir(model: ModelAuthorityIR, goal_id: int) -> p.GoalIR:
    from .adapter_communication import validate_model_adapter_communications
    validate_model_adapter_communications(model)
    if model.parallel_authority is not None:
        from .parallel_authority import validate_model_parallel_authority
        validate_model_parallel_authority(model)
    try:
        query = model.targets[goal_id]
    except KeyError as exc:
        raise ValueError(f"unknown model target {goal_id}") from exc
    return p.GoalIR(
        n=query.goal_id,
        sm_nodes=query.sm_nodes,
        pm_nodes=query.pm_nodes,
        sm_shapes=query.sm_shapes,
        pm_shapes=query.pm_shapes,
        lineage=query.lineage,
        prereqs=list(query.prereqs),
        sm_graph_ref=query.sm_graph_ref,
        pm_graph_ref=query.pm_graph_ref,
        public_statement_module=query.public_statement_module,
        public_statement_ref=query.public_statement_ref,
        public_statement_uses_contract_wrapper=query.public_statement_uses_contract_wrapper,
        public_statement_contract_ref=query.public_statement_contract_ref,
        public_statement_uses_faithful_evaluator=query.public_statement_uses_faithful_evaluator,
        lineage_ref=query.lineage_ref,
        init_goals_ref=query.init_goals_ref,
        sm_num_ranks=query.sm_num_ranks,
        pm_num_ranks=query.pm_num_ranks,
        sm_replica_groups=query.sm_replica_groups,
        pm_replica_groups=query.pm_replica_groups,
        packed_cu_contracts=query.packed_cu_contracts,
        tensor_value_bound_contracts=query.tensor_value_bound_contracts,
        sm_input_value_classes=query.sm_input_value_classes,
        pm_input_value_classes=query.pm_input_value_classes,
        sm_input_value_classes_ref=query.sm_input_value_classes_ref,
        pm_input_value_classes_ref=query.pm_input_value_classes_ref,
        init_lineages=dict(query.init_lineages),
        full_init_goal_ids=query.full_init_goal_ids,
        parallel_authority=model.parallel_authority,
        sm_adapter_communications=query.sm_adapter_communications,
        pm_adapter_communications=query.pm_adapter_communications,
    )
