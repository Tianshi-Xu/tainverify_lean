"""Check literal adapter communication capture against graph reads and writers.

This does not infer a CP/EP role. Adapter groups come from the source primitive's
ranks argument. Current evaluator/proof backends still require whole-graph ranks.
"""
from __future__ import annotations

from .parser import AdapterCommunication

ADAPTER_COLLECTIVES = frozenset(("AllToAllPrim", "AllGatherPrim", "AllReducePrim", "ReduceScatterPrim"))


def validate_model_adapter_communications(model) -> None:
    for side in ("sm", "pm"):
        validate_adapter_communications(model, side)
        for target, query in model.targets.items():
            if (getattr(query, side + "_graph_ref") == getattr(model, side + "_graph_ref")
                    and getattr(query, side + "_adapter_communications") != getattr(model, side + "_adapter_communications")):
                raise ValueError(f"target {target} adapter authority differs from shared graph")
            validate_adapter_communications(query, side)


def _initial_owners(graph, side):
    owners = {}
    if side == "sm" or getattr(graph, side + "_num_ranks") == 1:
        return {tid: {0} for tid, _shape in getattr(graph, side + "_shapes")}
    queries = [graph] if hasattr(graph, "init_lineages") else list(graph.targets.values())
    for query in queries:
        for lineage in query.init_lineages.values():
            for rank, tid in lineage.tps:
                owners.setdefault(tid, set()).add(rank)
    return owners


def validate_adapter_communications(graph, side: str) -> None:
    records = getattr(graph, side + "_adapter_communications")
    if records is None:
        return  # Legacy capture: no claim of adapter communication authority.
    if type(records) is not tuple:
        raise ValueError("invalid adapter communication record collection")
    nodes = getattr(graph, side + "_nodes")
    count = getattr(graph, side + "_num_ranks")
    indexed = {}
    for record in records:
        if type(record) is not AdapterCommunication or record.op not in ADAPTER_COLLECTIVES:
            raise ValueError("invalid adapter communication record/operator")
        if type(record.ranks) is not tuple or type(record.inputs) is not tuple:
            raise ValueError("adapter ranks and inputs must be tuples")
        if any(type(pair) is not tuple or len(pair) != 2 for pair in record.inputs):
            raise ValueError("invalid adapter input ownership pairs")
        values = (record.rank, record.primary_out_tid, *record.ranks, *(x for pair in record.inputs for x in pair))
        if any(type(x) is not int or x < 0 for x in values):
            raise ValueError("adapter rank/tid must be natural integers")
        key = (record.rank, record.primary_out_tid)
        if key in indexed:
            raise ValueError("duplicate adapter communication identity")
        if not record.ranks or len(set(record.ranks)) != len(record.ranks) or record.rank not in record.ranks:
            raise ValueError("invalid adapter communication group")
        if any(rank >= count for rank in record.ranks):
            raise ValueError("adapter communication rank outside graph scope")
        if tuple(rank for rank, _tid in record.inputs) != record.ranks:
            raise ValueError("adapter input rank order differs from captured communication order")
        indexed[key] = record
    expected_keys = [(n.rank, n.outs[0]) for n in nodes if n.op in ADAPTER_COLLECTIVES and n.outs]
    if len(expected_keys) != len(set(expected_keys)):
        raise ValueError("ambiguous adapter graph writer identity")
    if set(expected_keys) != set(indexed):
        raise ValueError("adapter communication inventory does not exactly cover graph primitives")
    owners = _initial_owners(graph, side)
    for node in nodes:
        if node.op in ADAPTER_COLLECTIVES:
            if not node.outs:
                raise ValueError("adapter graph writer has no primary output")
            record = indexed[(node.rank, node.outs[0])]
            if record.op != node.op or tuple(tid for _rank, tid in record.inputs) != tuple(node.ins):
                raise ValueError("adapter communication operator/input bindings differ from actual graph")
            for rank, tid in record.inputs:
                if rank not in owners.get(tid, ()):
                    raise ValueError(f"adapter input ownership mismatch: rank {rank}, tid {tid}; use the actual preceding writer or explicit initial lineage")
            if record.ranks != tuple(range(count)):
                raise ValueError("unsupported-group-local-proof: adapter ranks are not the whole ordered graph rank space")
        # Ownership follows the actual execution schedule, not a future/last writer.
        for tid in node.outs:
            owners[tid] = {node.rank}
