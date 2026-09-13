"""Bare original backward collective reads, with freshly reloaded source authority.

The callable authenticates each fullref-selected producer; its equations are not
spliced into this fragment. Composition and kernel checking belong to callers.
No serialized snapshot, shape coincidence, or caller-supplied equation is source
proof authority. Source files are trusted local capture inputs, never uploads.
"""
from copy import copy
from dataclasses import asdict
import importlib

from Verdict import graph_to_lean as compiler, runtime_schedule
from Verdict.runtime_backward_linear_reads import _writer
from Verdict.runtime_lineage import _same_typed

_FLAGS = ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement')
_FIELDS = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')


def _require(condition, reason):
    if not condition:
        raise ValueError('bw-collective ' + reason)


def _one(rows, reason):
    rows = list(rows)
    _require(len(rows) == 1, reason)
    return rows[0]


def _ref(ref):
    return dict(zip(_FIELDS, ref, strict=True))


def _ports(view, cell, fresh):
    """Compare expanded edges and independent pre-export local IR metadata."""
    node = cell.node
    _require(_same_typed(cell.kwargs, fresh.kwargs)
             and _same_typed(view.node_kwargs(node), fresh.kwargs)
             and cell.opname.name == fresh.opname.name
             and str(view.node_opname(node)).split('.')[-1] == fresh.opname.name,
             'raw/lowered opcode or kwargs mismatch')
    for side in ('inputs', 'outputs'):
        tensors = getattr(view, 'node_' + side)(node)
        refs = [tuple(r) for r in getattr(fresh, side)]
        _require(_same_typed([tuple(r) for r in getattr(cell, side)], refs)
                 and _same_typed([tuple(view.source_tensor(t)) for t in tensors], refs),
                 'ordered original fullref mismatch')
        field = '_' + side[:-1] + '_irs'
        irs, originals = getattr(cell, field), getattr(fresh, field)
        def metadata(ir):
            return (ir.tid, tuple(ir.shape), ir.parent.tid, tuple(ir.parent.shape),
                    tuple(tuple(x) for x in ir.indmap), tuple(ir.valmap),
                    ir.is_grad(), ir.is_param())
        _require(_same_typed([metadata(ir) for ir in irs], [metadata(ir) for ir in originals]),
                 'raw original IR shape/layout mismatch')
        # Fused collective inputs retain only the local pre-fusion IR metadata.
        local = [t for t in tensors if t.rank == cell.rank] if len(originals) == 1 else tensors
        _require(len(local) == len(originals)
                 and _same_typed([tuple(view.tensor_shape(t)) for t in local],
                                 [tuple(ir.shape) for ir in originals]),
                 'lowered original shape mismatch')


def _fresh(view, cells, snapshot):
    source = snapshot.get('source', {})
    _require(all(source.get(k) for k in ('capture', 'rank_code_directory'))
             and all(hasattr(snapshot, k) for k in ('raw_cells', 'raw_writers', 'raw_rank_sources')),
             'fresh capture/raw source authority required')
    fresh = compiler._load_chunk_source(source['capture'], source['rank_code_directory'])
    _require(_same_typed(snapshot.raw_rank_sources, fresh.raw_rank_sources)
             and _same_typed(snapshot.raw_writers, fresh.raw_writers),
             'fresh raw writer/generated body authority mismatch')
    nodes = view.nodes()
    inventory = [tuple(c.node) for c in fresh.raw_cells]
    _require(_same_typed([tuple(n) for n in nodes], inventory)
             and _same_typed([tuple(c.node) for c in cells], inventory),
             'original source node inventory mismatch')
    # Explicitly guard Python bool/int equality and lowered-ID aliasing.
    tensors = view.tensors()
    refs = [tuple(view.source_tensor(t)) for t in tensors]
    ids = [t.tid for t in tensors]
    _require(all(type(tid) is int and tid >= 0 for tid in ids)
             and len(set(ids)) == len(ids) and len(set(refs)) == len(refs)
             and all(len(r) == 5 and all(type(v) is int for v in r[1:]) for r in refs),
             'typed injective fullref/lowered index mismatch')
    # Rebinding a private view neither repairs nor mutates a corrupted caller scope.
    checked = copy(view)
    compiler.attach_collective_scopes(checked, fresh)
    _require(_same_typed({n: asdict(s) for n, s in getattr(view, 'collective_scopes', {}).items()},
                         {n: asdict(s) for n, s in checked.collective_scopes.items()}),
             'fresh ordered scope/effective params/local index mismatch')
    return fresh, checked


def render_read(view, cells, snapshot, source_index, order, label, producer_reader, output_port):
    """Authenticate ordered original peers and emit one bare AG/AA/RS equality."""
    _require(label in ('sm', 'pm') and type(source_index) is int
             and 0 <= source_index < len(cells), 'invalid world/source index')
    _require(type(output_port) is int and output_port >= 0, 'invalid producer output port')
    module_name = getattr(producer_reader, '__module__', '')
    _require(module_name.startswith('Verdict.runtime_backward_')
             and module_name.endswith('_reads')
             and getattr(producer_reader, '__name__', '') == 'render_read'
             and getattr(importlib.import_module(module_name), 'render_read', None) is producer_reader,
             'certified producer renderer required, not a supplied row/equation')
    cell = cells[source_index]
    _require(cell.node.wtype == {'sm': 's', 'pm': 'p'}[label], 'source owner/world mismatch')
    _require(cell.opname.name in ('AllGatherPrim', 'AllToAllPrim', 'ReduceScatterPrim'),
             'unsupported original backward collective')
    fresh, checked = _fresh(view, cells, snapshot)
    validated = runtime_schedule.validate(view, order['execution_to_source'])
    _require(_same_typed(order.get('source_to_execution'), validated['source_to_execution']),
             'source/execution inverse mismatch')
    seq = list(order['execution_to_source']); k = seq.index(source_index)
    scope = checked.collective_scopes[cell.node]
    writer = _one((w for w in fresh['writers'] if w['export_id'] == scope.source_writer), 'source writer missing/ambiguous')
    peers = writer['adapter']['peer_writers']
    ranks = list(scope.ranks)
    inputs = view.node_inputs(cell.node); output, = view.node_outputs(cell.node)
    refs = [list(view.source_tensor(t)) for t in inputs]
    ids = [t.tid for t in inputs]
    if cell.opname.name == 'ReduceScatterPrim':
        # Runtime SUM of each sender's destination chunk equals chunk(SUM)
        # only on this equal, positive, divisible source-shape domain.
        dim, = scope.params
        shape = tuple(scope.input_shape)
        outshape = tuple(view.tensor_shape(output))
        _require(ranks and len(set(ranks)) == len(ranks) and len(inputs) == len(ranks)
                 and all(type(r) is int and 0 <= r < view.W.runtime_ndevs for r in ranks)
                 and _same_typed(tuple(t.rank for t in inputs), scope.ranks)
                 and _same_typed(tuple(ids), scope.input_tids)
                 and _same_typed(output.tid, scope.output_tid)
                 and _same_typed(scope.local_index, ranks.index(cell.rank)),
                 'ordered reduce-scatter peers/output/local index mismatch')
        _require(shape and type(dim) is int and 0 <= dim < len(shape)
                 and all(type(d) is int and d > 0 for d in (*shape, *outshape))
                 and all(_same_typed(tuple(view.tensor_shape(t)), shape) for t in inputs)
                 and shape[dim] % len(ranks) == 0,
                 'positive divisible same reduce-scatter peer shapes required')
        expected = list(shape); expected[dim] //= len(ranks)
        _require(_same_typed(list(outshape), expected), 'reduce-scatter output shape mismatch')
    predecessors = []
    for tensor, ref in zip(inputs, refs, strict=True):
        j, producer = _one(((j, c) for j, c in enumerate(cells)
            if any(_same_typed(tuple(r), tuple(ref)) for r in c.outputs)),
            'original peer producer missing/ambiguous')
        _require(output_port < len(producer.outputs)
                 and _same_typed(tuple(producer.outputs[output_port]), tuple(ref)),
                 'selected producer output port mismatch')
        _ports(view, producer, fresh.raw_cells[j])
        text, row = producer_reader(view, cells, snapshot, j, order, label)
        fresh_text, authenticated = producer_reader(checked, fresh.raw_cells, fresh, j, order, label)
        _require(_same_typed(row, authenticated) and text == fresh_text,
                 'fresh producer row mismatch')
        _require(row.get('world') == label and row.get('source_index') == j
                 and row.get('execution_index') == validated['source_to_execution'][j]
                 and row.get('bw_writer') == _writer(fresh, fresh.raw_cells, j)
                 and _same_typed(row.get('input_tids'), [t.tid for t in view.node_inputs(producer.node)])
                 and _same_typed(row.get('output_tids'), [t.tid for t in view.node_outputs(producer.node)])
                 and _same_typed(row.get('input_refs'), [list(r) for r in producer.inputs])
                 and _same_typed(row.get('output_refs'), [list(r) for r in producer.outputs])
                 and all(row.get(flag) is False for flag in _FLAGS)
                 and len(row.get('theorems', [])) == len(producer.outputs),
                 'authenticated producer row/ports mismatch')
        _require(row['output_tids'][output_port] == tensor.tid, 'producer lowered output mismatch')
        predecessors.append(row)
    _require(len(peers) == len(ranks), 'incomplete ordered peer writers')
    fields = ('idim', 'odim') if cell.opname.name == 'AllToAllPrim' else ('dim',)
    for rank, wid, predecessor in zip(ranks, peers, predecessors, strict=True):
        original = _one((w for w in fresh['writers'] if w['export_id'] == wid), 'fresh peer writer missing/ambiguous')
        ref = original['ref']
        identity = (ref['world'], ref['runtime_rank'], ref['microbatch'],
                    ref['source_cid'], original['source_irname'])
        j = _one((j for j, c in enumerate(cells) if _same_typed(tuple(c.node), identity)),
                 'original collective peer missing/ambiguous')
        peer = cells[j]; peer_scope = checked.collective_scopes[peer.node]
        _require(peer.rank == rank, 'ordered collective peer rank mismatch')
        _ports(view, peer, fresh.raw_cells[j])
        _require(_writer(snapshot, cells, j) == wid, 'original peer writer/export/call mismatch')
        actual = _one((w for w in snapshot['writers'] if w['export_id'] == wid), 'peer source writer missing/ambiguous')
        _require(_same_typed(actual, original), 'fresh collective writer/context mismatch')
        ctx = original['adapter'].get('backward_context', {})
        backward = ctx.get('runtime', {}).get('backward', {})
        params = backward.get('kwargs', {})
        _require(ctx.get('status') == 'structurally-bound' and ctx.get('gradient_value_proved') is False
                 and backward.get('op') == cell.opname.name and backward.get('tensor') == 'output-gradient'
                 and _same_typed(params.get('ranks'), ranks)
                 and set(params) == {'ranks', *fields}, 'authenticated backward context required')
        dims = [params[f] for f in fields]
        _require(all(type(d) is int for d in dims), 'typed backward dimensions required')
        dims = [d + len(scope.input_shape) if d < 0 else d for d in dims]
        _require(_same_typed(tuple(dims), scope.params)
                 and _same_typed(peer_scope.ranks, scope.ranks)
                 and _same_typed(peer_scope.input_tids, scope.input_tids)
                 and _same_typed(peer_scope.params, scope.params)
                 and peer_scope.local_index == ranks.index(rank), 'ordered peer effective scope mismatch')
        local = _ref(refs[ranks.index(rank)])
        outref = _ref(view.source_tensor(view.node_outputs(peer.node)[0]))
        _require(_same_typed(ctx.get('output_gradient'), [local])
                 and _same_typed(ctx.get('input_gradient'), [outref])
                 and _same_typed(ctx.get('gradient_read_points'), [dict(ref=local, writer=predecessor['bw_writer'])]),
                 'peer backward gradient fullref/read point mismatch')
    nodes = view.nodes()
    _require(not any(set(ids) & {t.tid for t in view.node_outputs(nodes[j])} for j in seq[k:]),
             'peer operand overwritten in complete execution suffix')
    _require(not any(output.tid in {t.tid for t in view.node_outputs(nodes[j])} for j in seq[k+1:]),
             'output overwritten in complete execution suffix')
    name = f'backwardCollective_{label}_{source_index}_read'; req = f'{label}InputRequests'
    operands = f'(({ids} : List Tid).map t)'
    if cell.opname.name == 'AllGatherPrim':
        dim, = scope.params
        value = f'allGatherPrimDimN {dim} {len(ranks)} {scope.local_index}'
        law = 'SourceAllGatherRead.allGather_value_of_split'
    elif cell.opname.name == 'AllToAllPrim':
        idim, odim = scope.params
        value = f'AllToAllSourceFaithful.tensor {len(ranks)} {scope.local_index} {idim} {odim}'
        law = 'SourcePrimitiveRead.allToAll_value_of_split'
    else:
        dim, = scope.params
        value = f'chunkPrimDimN {dim} {len(ranks)} {scope.local_index}'
        operands = f'(tensorSum {operands})'
        law = 'SourceReduceScatterRead.reduceScatter_value_of_split'
    args = f'{cell.rank} {ranks} {ids} {output.tid} ' + ' '.join(map(str, scope.params))
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
             f'    t {output.tid} = {value} {operands} := by',
             f'  apply {law} {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
             f'    {req} ({req}.take {k}) ({req}.drop {k+1}) {label}Node_{source_index}',
             f'    {args} s t rfl ?_ rfl ?_ h', '  · calc',
             f'      {req} = {req}.take {k} ++ {req}.drop {k} := (List.take_append_drop {k} {req}).symm',
             '      _ = _ := rfl',
             f'  · change ∀ tid ∈ ({ids} : List Tid), ∀ row ∈ {req}.drop {k}, tid ∉ row.1.outs',
             '    decide', f'#print axioms {name}']
    return '\n'.join(proof) + '\n', dict(world=label, source_index=source_index, execution_index=k,
        opname=cell.opname.name, ranks=ranks, local_index=scope.local_index, input_tids=ids,
        input_refs=refs, output_tid=output.tid, output_ref=list(view.source_tensor(output)),
        params=list(scope.params), raw_params=[cell.kwargs[f] for f in fields],
        theorems=[name], predecessors=predecessors, source_writer=scope.source_writer,
        input_shapes=[list(view.tensor_shape(t)) for t in inputs], output_shape=list(view.tensor_shape(output)),
        output_port=output_port, operand_nonwrite_source_indices=seq[k:],
        **{flag: False for flag in _FLAGS})
