"""Source-only embedding route census, not a value proof or a new lineage.

``census`` takes the original lowered worlds, complete original typed lineage
sequence, and live _TraceValidation. It reuses full-world source authentication.
DTOs are descriptions only and must never be accepted back as authority.
"""
from dataclasses import dataclass, replace

from Verdict.runtime_lineage import (
    Endpoint, Role, _Index, _TraceValidation, _same_typed, op, trace,
)


@dataclass(frozen=True)
class Port:
    endpoint: Endpoint
    parent_name: str
    parent_shape: tuple
    bounds: tuple
    value_part: tuple


@dataclass(frozen=True)
class Step:
    node: tuple
    op: str
    inputs: tuple[Port, ...]
    outputs: tuple[Port, ...]
    source_writer: str | None = None
    ranks: tuple = ()
    local_index: int | None = None
    chunk_axis: int | None = None
    gather_axis: int | None = None
    split_axis: int | None = None
    peers: tuple = ()


@dataclass(frozen=True)
class RankRoute:
    rank: int
    loader: Port
    chunk: Step | None
    embedding: Step
    exchange: Step | None
    output: Port


@dataclass(frozen=True)
class EmbeddingRoute:
    unit: int
    positions: tuple
    batch_key: tuple
    parameter_key: tuple
    global_embedding: Step
    ranks: tuple[RankRoute, ...]


@dataclass(frozen=True)
class Unavailable:
    global_node: tuple
    unit: int
    reason: str


@dataclass(frozen=True)
class Census:
    routes: tuple[EmbeddingRoute, ...]
    unavailable: tuple[Unavailable, ...]
    proof_admissible: bool = False
    public_complete: bool = False
    kernel_value_proved: bool = False
    torch_refinement: bool = False


class _Unavailable(Exception):
    pass


def _port(index, ref):
    m = index.meta[tuple(ref)]
    if (type(m[0]) is not str or not m[0] or len(m[1]) != len(m[2])
            or any(type(d) is not int or d <= 0 for d in m[1])
            or any(len(b) != 2 or any(type(x) is not int for x in b)
                   or not 0 <= b[0] < b[1] <= d for b, d in zip(m[2], m[1]))
            or any(type(x) is not int for x in m[3])):
        raise ValueError('malformed raw parent/bounds identity')
    return Port(index.endpoint(ref), m[0], m[1], m[2], m[3])


def _step(index, cell):
    return Step(tuple(cell.node), op(cell),
                tuple(_port(index, t) for t in cell.inputs),
                tuple(_port(index, t) for t in cell.outputs))


def _path(index, pc, loader):
    ref = tuple(pc.inputs[0])
    if ref == loader:
        return True, None
    node = index.writers.get(ref)
    if node is None or str(index.view.node_opname(node)).split('.')[-1] != 'ChunkPrim':
        return False, None
    inputs = index.view.node_inputs(node)
    return (len(inputs) == 1 and tuple(index.view.source_tensor(inputs[0])) == loader), node


def _embedding(global_step, local, positions):
    x, w = local.inputs
    if len(local.outputs) != 1 or len(w.parent_shape) != 2:
        raise _Unavailable('unsupported embedding output/weight rank')
    y, = local.outputs
    for gp, pp, parameter in zip((*global_step.inputs, *global_step.outputs), (x, w, y), (False, True, False)):
        expected = gp.parent_shape if parameter else (len(positions), *gp.parent_shape[1:])
        if pp.parent_name != gp.parent_name or pp.parent_shape != expected:
            raise ValueError('raw embedding parent identity/layout mismatch')
        if gp.value_part != (0, 1) or pp.value_part != (0, 1):
            raise _Unavailable('unsupported embedding value partition')
    if w.bounds[0] != (0, w.parent_shape[0]) or y.bounds != (*x.bounds, w.bounds[1]):
        raise _Unavailable('unsupported embedding placement')


def _chunk(index, node, loader, output, ranks):
    scope = index.view.chunk_scopes[node]
    if scope.ranks != ranks or not 0 < scope.dim < len(loader.parent_shape):
        raise _Unavailable('unsupported Chunk unit/axis layout')
    if loader.bounds != tuple((0, d) for d in loader.parent_shape):
        raise _Unavailable('unsupported sharded loader before Chunk')
    dim, k, j = scope.dim, len(scope.ranks), scope.local_index
    bounds = list(loader.bounds)
    size = (bounds[dim][1] - bounds[dim][0]) // k
    bounds[dim] = (j * size, (j + 1) * size)
    if (output.parent_name != loader.parent_name or output.parent_shape != loader.parent_shape
            or output.bounds != tuple(bounds) or output.value_part != loader.value_part):
        raise ValueError('raw Chunk-to-embedding metadata mismatch')
    return Step(tuple(node), 'ChunkPrim', (loader,), (output,), scope.source_writer,
                scope.ranks, scope.local_index, chunk_axis=dim)


def _exchanges(index, local):
    """AllToAllSourceFaithful: split sender on odim, concatenate on idim.

    Axes come from authenticated effective source scopes (including FW/BW),
    NOT raw parameter-position guesses. Output bounds are transport-derived;
    no missing adapter IR metadata is invented or used as identity authority.
    """
    ranks = tuple(r.rank for r in local)
    outputs = tuple(r.embedding.outputs[0] for r in local)
    expected = tuple(p.endpoint.tid for p in outputs)
    result = []
    for route in local:
        if route.chunk is None:
            raise _Unavailable('unsupported mixed direct/Chunk route')
        matches = [s for s in index.view.collective_scopes.values()
                   if s.op == 'AllToAllPrim' and s.node.rank == route.rank
                   and route.embedding.outputs[0].endpoint.tid in s.input_tids]
        if not matches:
            raise _Unavailable('missing embedding AllToAll consumer')
        if len(matches) != 1:
            raise ValueError('ambiguous embedding AllToAll consumer')
        scope, = matches
        if scope.ranks != ranks:
            raise _Unavailable('unsupported AllToAll cross-unit/subgroup layout')
        if scope.input_tids != expected:
            raise ValueError('AllToAll ordered peers differ from embedding source pair')
        gather, split = scope.params
        if gather != route.chunk.chunk_axis or split != len(outputs[0].bounds) - 1:
            raise _Unavailable('unsupported AllToAll embedding axes')
        whole = outputs[0].parent_shape
        bounds = list(outputs[0].bounds)
        end = 0
        for port in outputs:
            if (port.parent_name != outputs[0].parent_name or port.parent_shape != whole
                    or port.bounds[gather][0] != end
                    or any(b != (0, whole[i]) for i, b in enumerate(port.bounds) if i != gather)):
                raise _Unavailable('unsupported ordered embedding sender partition')
            end = port.bounds[gather][1]
        if end != whole[gather]:
            raise _Unavailable('incomplete embedding sender partition')
        bounds[gather] = (0, end)
        width = whole[split] // len(ranks)
        bounds[split] = (scope.local_index * width, (scope.local_index + 1) * width)
        out, = index.view.node_outputs(scope.node)
        endpoint = index.endpoint(index.view.source_tensor(out))
        if endpoint.shape != tuple(b-a for a, b in bounds):
            raise ValueError('AllToAll derived bounds/shape mismatch')
        port = Port(endpoint, outputs[0].parent_name, whole, tuple(bounds), (0, 1))
        step = Step(tuple(scope.node), 'AllToAllPrim', outputs, (port,), scope.source_writer,
                    scope.ranks, scope.local_index, gather_axis=gather, split_axis=split,
                    peers=tuple(zip(scope.ranks, scope.input_tids)))
        result.append(replace(route, exchange=step, output=port))
    return result


def census(sm, pm, lineages, validation):
    """Ordered global-source-node / DP-unit census; malformed authority raises.

    Unsupported routes are explicit ``unavailable`` entries (never guessed by
    equal shapes). Existing batch and parameter keys are target fullrefs.
    """
    from Verdict import graph_to_lean as c
    from Verdict.runtime_world import _authenticate

    if type(validation) is not _TraceValidation:
        raise ValueError('missing live trace authority')
    raw_sm, raw_pm, _, batch, _, _ = validation._inputs
    for label, view, raw_cells in (('s', sm, raw_sm), ('p', pm, raw_pm)):
        # Validate independent raw identities BEFORE dict lookup/equality in
        # trace/_Index: bools must not alias integer owners, phases or versions.
        for cell in raw_cells:
            node = tuple(cell.node)
            if (len(node) != 5 or type(node[0]) is not str or node[0] != label
                    or any(type(x) is not int for x in node[1:4])
                    or type(node[4]) is not str or not node[4]
                    or type(cell.rank) is not int or node[1] != cell.rank
                    or not 0 <= cell.rank < view.W.runtime_ndevs):
                raise ValueError('malformed raw node/owner identity')
            for field in ('inputs', 'outputs'):
                for port in getattr(cell, field):
                    ref = tuple(port)
                    if (len(ref) != 5 or type(ref[0]) is not str or ref[0] != label
                            or any(type(x) is not int for x in ref[1:])
                            or not 0 <= ref[1] < view.W.runtime_ndevs
                            or (field == 'outputs' and ref[1] != cell.rank)):
                        raise ValueError('malformed raw port/owner identity')
        for tensor in view.tensors():
            ref = tuple(view.source_tensor(tensor))
            if (len(ref) != 5 or type(ref[0]) is not str or ref[0] != label
                    or any(type(x) is not int for x in ref[1:])):
                raise ValueError('malformed original fullref identity')
    canonical, _, current = trace(sm, pm, *validation._inputs)
    if not _same_typed(lineages, canonical) or not _same_typed(dict(validation), dict(current)):
        raise ValueError('lineage/validation differs from original raw/batch authority')
    _authenticate(sm, raw_sm, c)
    _authenticate(pm, raw_pm, c)
    for view in (sm, pm):
        for name in ('chunk_scopes', 'collective_scopes'):
            for scope in getattr(view, name, {}).values():
                axes = (scope.dim,) if name == 'chunk_scopes' else scope.params
                tids = (scope.input_tid, scope.output_tid) if name == 'chunk_scopes' else (*scope.input_tids, scope.output_tid)
                if (any(type(x) is not int for x in (*scope.ranks, scope.local_index, *axes, *tids))
                        or scope.proof_admissible is not False):
                    raise ValueError('malformed source scope identity')
    si, pi = _Index(sm, raw_sm), _Index(pm, raw_pm)
    keyed = {l.target.ref: l for l in lineages}
    routes, missing = [], []
    for sc in raw_sm:
        if op(sc) != 'FW_embedding':
            continue
        for unit in batch['config']['units']:
            try:
                if len(sc.inputs) != 2 or len(sc.outputs) != 1:
                    raise _Unavailable('unsupported global embedding arity')
                bl = keyed.get(tuple(sc.inputs[0]))
                wl = keyed.get(tuple(sc.inputs[1]))
                if bl is None or bl.role != Role.BATCH or wl is None or wl.role != Role.PARAMETER:
                    raise _Unavailable('missing existing loader/parameter lineage key')
                bu = next(u for u in bl.units if u.unit == unit['unit'])
                wu = next(u for u in wl.units if u.unit == unit['unit'])
                local = []
                for bp, wp in zip(bu.pieces, wu.pieces, strict=True):
                    matches = [pc for pc in raw_pm if op(pc) == 'FW_embedding'
                               and len(pc.inputs) == 2 and pc.rank == bp.endpoint.ref[1]
                               and _path(pi, pc, bp.endpoint.ref)[0]
                               and tuple(pc.inputs[1]) == wp.endpoint.ref]
                    if not matches:
                        raise _Unavailable('unsupported loader-to-embedding path')
                    if len(matches) != 1:
                        raise ValueError('ambiguous original embedding source pair')
                    pc, = matches
                    if pc.ir.signature != sc.ir.signature or dict(pc.kwargs) != dict(sc.kwargs):
                        raise ValueError('raw embedding signature/kwargs mismatch')
                    step = _step(pi, pc)
                    _embedding(_step(si, sc), step, unit['positions'])
                    if (pc.kwargs.get('padding_idx') is not None or pc.kwargs.get('start') != 0
                            or pc.kwargs.get('stop') != step.inputs[1].parent_shape[0]):
                        raise _Unavailable('unsupported embedding offset/padding')
                    loader = _port(pi, bp.endpoint.ref)
                    _, node = _path(pi, pc, bp.endpoint.ref)
                    chunk = None if node is None else _chunk(pi, node, loader, step.inputs[0], tuple(unit['ranks']))
                    local.append(RankRoute(pc.rank, loader, chunk, step, None, step.outputs[0]))
                if any(r.chunk is not None for r in local):
                    local = _exchanges(pi, local)
                routes.append(EmbeddingRoute(unit['unit'], tuple(unit['positions']),
                    bl.target.ref, wl.target.ref, _step(si, sc), tuple(local)))
            except _Unavailable as exc:
                missing.append(Unavailable(tuple(sc.node), unit['unit'], str(exc)))
    return Census(tuple(routes), tuple(missing))
