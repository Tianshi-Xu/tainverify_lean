"""Source-derived one-world interleaving, not equivalence to the old raw fold.

Call after runtime_world._authenticate. Raw source ordinals remain identities.
Only per-rank control and exact fullref producer dependencies constrain execution.
External leaves are inventoried, never initialized by this scheduling pass.
"""
import heapq


def _dependencies(view):
    nodes = view.nodes()
    if tuple(nodes) != view._runtime_original_nodes or nodes != list(view.source.nodes()):
        raise ValueError('schedule raw source sequence mismatch')
    world = view.W.runtime_ndevs
    if type(world) is not int or world <= 0 or world != view._runtime_world_size:
        raise ValueError('schedule world mismatch')
    registered = set(view.tensors())
    if len(registered) != len(view.tensors()):
        raise ValueError('schedule duplicate tensor inventory')
    predecessors = [set() for _ in nodes]
    ranks = {}; writers = {}; inputs = []
    for i, n in enumerate(nodes):
        if type(n.rank) is not int or not 0 <= n.rank < world:
            raise ValueError('schedule invalid rank')
        sequence = ranks.setdefault(n.rank, [])
        if sequence: predecessors[i].add(sequence[-1])
        sequence.append(i)
        for method in ('node_inputs', 'node_outputs'):
            tensors = getattr(view, method)(n)
            refs = []
            for t in tensors:
                if t not in registered: raise ValueError('schedule missing fullref inventory')
                ref = tuple(view.source_tensor(t))
                if (len(ref) != 5 or ref[0] != n[0]
                        or any(type(x) is not int for x in ref[1:])
                        or ref[3] < 0 or ref[4] < 0):
                    raise ValueError('schedule invalid world/fullref')
                refs.append(ref)
            if refs != [tuple(t) for t in getattr(view.source, method)(n)]:
                raise ValueError('schedule ordered source ports mismatch')
            if method == 'node_inputs':
                inputs.extend((i, port, t, ref) for port, (t, ref) in enumerate(zip(tensors, refs)))
            else:
                for ref in refs:
                    if ref in writers: raise ValueError(f'schedule duplicate fullref writer: {ref}')
                    if ref[1] != n.rank: raise ValueError('schedule output rank mismatch')
                    writers[ref] = i
    external = {}; reads = []
    for i, port, t, ref in inputs:
        if ref in writers:
            writer = writers[ref]
            if writer == i:
                raise ValueError(f'schedule self-read: source={i} port={port} fullref={ref}')
            predecessors[i].add(writer)
            reads.append((writer, i, port, ref))
        else:
            if t.tid not in external:
                external[t.tid] = dict(tid=t.tid, ref=list(ref),
                    source_is_initialized=bool(view.is_initialized(t)),
                    initial_value_proved=False, readers=[])
            external[t.tid]['readers'].append(dict(source_index=i, port=port))
    return predecessors, ranks, reads, [external[t] for t in sorted(external)]


def validate(view, execution_to_source):
    """Reject incomplete, repeated, forged, or dependency-illegal permutations."""
    predecessors, ranks, reads, external = _dependencies(view)
    order = list(execution_to_source)
    if (any(type(i) is not int for i in order) or len(order) != len(predecessors)
            or set(order) != set(range(len(predecessors)))):
        raise ValueError('schedule must contain every source node exactly once')
    positions = [0] * len(order)
    for j, i in enumerate(order): positions[i] = j
    for rank, source in ranks.items():
        if [i for i in order if view.nodes()[i].rank == rank] != source:
            raise ValueError(f'schedule per-rank control order mismatch: rank={rank}')
    for writer, reader, port, ref in reads:
        if positions[writer] >= positions[reader]:
            raise ValueError(f'schedule read-before-writer: reader={reader} port={port} writer={writer} fullref={ref}')
    return dict(execution_to_source=order, source_to_execution=positions,
                per_rank_source_indices={str(r): seq for r, seq in ranks.items()},
                dataflow_reads=len(reads), external_leaves=external,
                external_initial_values_proved=False,
                dependency_order_validated=True)


def build(view):
    """Stable Kahn ordering with source ordinal as the only ready-node key."""
    predecessors, _, _, _ = _dependencies(view)
    successors = [[] for _ in predecessors]
    pending = [len(ps) for ps in predecessors]
    for reader, ps in enumerate(predecessors):
        for writer in ps: successors[writer].append(reader)
    ready = [i for i, count in enumerate(pending) if count == 0]
    heapq.heapify(ready)
    order = []
    while ready:
        writer = heapq.heappop(ready)
        order.append(writer)
        for reader in successors[writer]:
            pending[reader] -= 1
            if pending[reader] == 0: heapq.heappush(ready, reader)
    if len(order) != len(pending):
        # Follow remaining predecessor edges to give an actual closed cycle,
        # not merely a list of downstream nodes blocked by the cycle.
        node = next(i for i, count in enumerate(pending) if count)
        path = []; seen = {}
        while node not in seen:
            seen[node] = len(path); path.append(node)
            node = min(p for p in predecessors[node] if pending[p])
        cycle = path[seen[node]:] + [node]
        raise ValueError(f'schedule dependency cycle (reader -> predecessor source indices): {cycle}')
    return validate(view, order)
