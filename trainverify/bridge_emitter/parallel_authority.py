"""Bind source-derived topology to the existing graph authority.

Replica groups describe logical replicas, not necessarily communication groups.
This adapter admits their use as communication groups only when their *ordered*
members equal the source configuration's group for every participating rank.
It never splits a replica group to manufacture missing communication authority.
This is graph/plan scope, not a GPU capture or proof of runtime DP/ZeRO/PP.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass, replace

from trainverify.parallel_topology import ParallelTopology, validate_topology
from .parser import AdapterCommunication, ReplicaNodeRef
from .adapter_communication import ADAPTER_COLLECTIVES, validate_adapter_communications


# Roles of the fixed source-derived custom operators, not inferred from shapes.
_SOURCE_ROLES = {
    **{f"{direction}_{op}": "cp" for direction in ("FW", "BW")
       for op in ("maybe_shuffle", "maybe_unshuffle", "attn_zigzag", "attn_sliding_window")},
    **{f"{direction}_all2all_moe_gmm": "ep" for direction in ("FW", "BW")},
}
_GENERIC_COLLECTIVES = ADAPTER_COLLECTIVES


class ParallelAuthorityError(ValueError):
    def __init__(self, code: str, detail: str):
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


@dataclass(frozen=True)
class GraphCommunication:
    node: ReplicaNodeRef
    role: str
    members: tuple[ReplicaNodeRef, ...]


@dataclass(frozen=True)
class ParallelGraphAuthority:
    topology: ParallelTopology
    graph_scope: str
    rank_map: tuple[int, ...]
    communications: tuple[GraphCommunication, ...]
    evidence_kind: str = "source-checked-replica-group-projection"
    adapters: tuple[AdapterCommunication, ...] | None = None
    sm_adapters: tuple[AdapterCommunication, ...] | None = None


def parallel_authority_payload(authority: ParallelGraphAuthority) -> dict:
    """Keep legacy identities/bytes when adapter capture is absent, not empty."""
    payload = asdict(authority)
    for name in ("adapters", "sm_adapters"):
        if payload.get(name) is None:
            payload.pop(name, None)
    return payload


def _communications(graph) -> tuple[GraphCommunication, ...]:
    result = []
    for node in graph.pm_nodes:
        role = _SOURCE_ROLES.get(node.op)
        if role is None:
            if node.op in _GENERIC_COLLECTIVES and graph.pm_adapter_communications is None:
                raise ParallelAuthorityError("missing-collective-role", f"{node.op} rank {node.rank}: capture the communication role; shape/replica count is insufficient")
            continue
        if not node.outs:
            raise ParallelAuthorityError("missing-node-identity", f"{node.op} has no primary output")
        ref = ReplicaNodeRef(node.rank, node.outs[0])
        groups = [g for g in graph.pm_replica_groups if ref in g.members]
        if len(groups) != 1:
            raise ParallelAuthorityError("missing-communication-authority", f"{node.op} {ref}: expected one explicit ordered replica group")
        result.append(GraphCommunication(ref, role, groups[0].members))
    return tuple(result)


def validate_graph_authority(graph, authority: ParallelGraphAuthority) -> None:
    validate_topology(authority.topology)
    config = authority.topology.config
    mapping = authority.rank_map
    if type(mapping) is not tuple or any(type(rank) is not int for rank in mapping):
        raise ParallelAuthorityError("invalid-rank-map", "rank_map must be an ordered tuple of integer ranks, not booleans")
    if authority.evidence_kind != "source-checked-replica-group-projection":
        raise ParallelAuthorityError("invalid-evidence-kind", "this adapter only checks existing explicit replica groups")
    if authority.graph_scope == "plan":
        allowed = tuple(g.members for g in authority.topology.groups_for("scale_unit"))
        if mapping not in allowed or graph.pm_num_ranks != config.plan_ngpus:
            raise ParallelAuthorityError("graph-rank-scope-mismatch", "plan graph must map, in order, to one entire source scale unit")
    elif authority.graph_scope == "runtime":
        if mapping != tuple(range(config.runtime_ngpus)) or graph.pm_num_ranks != config.runtime_ngpus:
            raise ParallelAuthorityError("graph-rank-scope-mismatch", "runtime graph must cover every runtime rank in order")
    else:
        raise ParallelAuthorityError("graph-rank-scope-mismatch", "graph_scope must be explicitly plan or runtime")
    if config.pipeline_stages != 1:
        raise ParallelAuthorityError("missing-pipeline-placement", "pipeline stages require captured stage placement; a stage count is not placement authority")
    if any(type(n.rank) is not int or not 0 <= n.rank < len(mapping) for n in graph.pm_nodes):
        raise ParallelAuthorityError("invalid-node-rank", "PM node rank is outside the graph rank space")
    if authority.adapters != graph.pm_adapter_communications or authority.sm_adapters != graph.sm_adapter_communications:
        raise ParallelAuthorityError("adapter-binding-mismatch", "adapter capture changed after topology binding")
    validate_adapter_communications(graph, "sm")
    validate_adapter_communications(graph, "pm")
    actual = _communications(graph)
    if authority.communications != actual:
        raise ParallelAuthorityError("communication-binding-mismatch", "stored communication projection differs from actual graph writers/groups/roles")
    by_ref = {}
    for node in graph.pm_nodes:
        if node.outs:
            by_ref.setdefault(ReplicaNodeRef(node.rank, node.outs[0]), []).append(node)
    for binding in actual:
        nodes = by_ref.get(binding.node, ())
        if len(nodes) != 1:
            raise ParallelAuthorityError("ambiguous-node-identity", str(binding.node))
        node = nodes[0]
        runtime_rank = mapping[node.rank]
        expected = authority.topology.group_for_rank(binding.role, runtime_rank).members
        if any(type(m.rank) is not int or not 0 <= m.rank < len(mapping) for m in binding.members):
            raise ParallelAuthorityError("invalid-member-rank", str(binding.node))
        observed = tuple(mapping[m.rank] for m in binding.members)
        if observed != expected:
            raise ParallelAuthorityError("communication-group-mismatch", f"{node.op} {binding.node}: source {binding.role} expects {expected}, graph replicas map to {observed}; capture subgroup communication separately, do not reinterpret all logical replicas as buddies")
        for member in binding.members:
            peers = by_ref.get(member, ())
            if len(peers) != 1 or peers[0].op != node.op:
                raise ParallelAuthorityError("communication-writer-mismatch", f"{binding.node}: {member} is not the same source operator")
        local_rank = expected.index(runtime_rank)
        if node.op.endswith(("maybe_shuffle", "maybe_unshuffle")) and tuple(node.params or ()) != (len(expected), local_rank):
            raise ParallelAuthorityError("source-rank-parameter-mismatch", f"{node.op} {binding.node}: expected group-local parameters {(len(expected), local_rank)}, got {node.params}")
        if len(expected) != graph.pm_num_ranks or local_rank != node.rank:
            raise ParallelAuthorityError("unsupported-group-local-proof", f"{node.op} {binding.node}: communication authority is consistent, but existing proof backend assumes whole-graph ranks; group size {len(expected)}, local rank {local_rank}, graph size {graph.pm_num_ranks}")


def validate_ir_parallel_authority(ir) -> None:
    if ir.parallel_authority is not None:
        validate_graph_authority(ir, ir.parallel_authority)


def validate_model_parallel_authority(model) -> None:
    if model.parallel_authority is None:
        return
    validate_graph_authority(model, model.parallel_authority)
    fields = ("sm_graph_ref", "pm_graph_ref", "sm_num_ranks", "pm_num_ranks", "sm_nodes", "pm_nodes", "sm_shapes", "pm_shapes", "sm_replica_groups", "pm_replica_groups", "sm_adapter_communications", "pm_adapter_communications")
    for target, query in model.targets.items():
        if any(getattr(query, f) != getattr(model, f) for f in fields):
            raise ParallelAuthorityError("target-graph-authority-mismatch", f"target {target} is not a projection of the topology-bound shared graph")
        validate_adapter_communications(query, "sm")
        validate_adapter_communications(query, "pm")


def bind_model(model, topology: ParallelTopology, *, graph_scope: str, scale_unit: int = 0):
    validate_topology(topology)
    if type(scale_unit) is not int or scale_unit < 0:
        raise ParallelAuthorityError("graph-rank-scope-mismatch", "scale_unit must be a nonnegative integer")
    units = topology.groups_for("scale_unit")
    if graph_scope == "plan" and scale_unit < len(units):
        rank_map = units[scale_unit].members
    elif graph_scope == "runtime" and scale_unit == 0:
        rank_map = tuple(range(topology.config.runtime_ngpus))
    else:
        raise ParallelAuthorityError("graph-rank-scope-mismatch", "invalid scope/scale-unit selection")
    authority = ParallelGraphAuthority(topology, graph_scope, rank_map, _communications(model),
                                       adapters=model.pm_adapter_communications,
                                       sm_adapters=model.sm_adapter_communications)
    bound = replace(model, parallel_authority=authority)
    validate_model_parallel_authority(bound)
    return bound
