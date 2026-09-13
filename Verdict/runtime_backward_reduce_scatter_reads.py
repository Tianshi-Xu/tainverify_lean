"""Original BW_linear dX -> source-scoped ReduceScatter final-store reads.

This fragment consumes the existing BW_linear dX theorem, not a new SM/PM
value equality. nnScaler AllGatherReduceScatter.backward uses ctx._dim and
ctx._ranks; its reduce_scatter chunks each sender then performs SUM. Equal,
positive, divisible shapes make that the chunk of tensorSum modeled here.
Successful SourceScopedEval execution alone does NOT establish these source
shape/peer contracts. Fresh capture attachment and the checks below do.
"""
from Verdict import graph_to_lean as compiler, runtime_backward_linear_reads as linear
from Verdict import runtime_schedule
from Verdict.runtime_lineage import _same_typed


def _one(rows, reason):
    rows = list(rows)
    if len(rows) != 1:
        raise ValueError('bw-reduce-scatter ' + reason)
    return rows[0]


def _consumer(cells, gradient):
    cell = _one((c for c in cells if c.rank == gradient.rank and gradient in c.inputs),
                'local dX consumer missing/ambiguous')
    if cell.opname.name != 'ReduceScatterPrim':
        raise ValueError('bw-reduce-scatter direct dX consumer required')
    return cell


def _ref(ref):
    return dict(zip(('world', 'runtime_rank', 'microbatch', 'source_tid', 'version'), ref, strict=True))


def _read(view, cells, snapshot, order, index, selected):
    _, local = linear.render_read(view, cells, snapshot, index, order, 'pm')
    bw = cells[index]
    cell = _consumer(cells, bw.outputs[0])
    nodes = view.nodes(); i = nodes.index(cell.node)
    scope = view.collective_scopes[cell.node]
    writer = _one((w for w in snapshot['writers'] if w['export_id'] == scope.source_writer),
                  'original collective writer missing/ambiguous')
    adapter = writer['adapter']; ctx = adapter.get('backward_context', {})
    raw_kwargs = dict(cell.kwargs)
    if raw_kwargs.get('__consts') == []:
        del raw_kwargs['__consts']
    if (str(view.node_opname(cell.node)).split('.')[-1] != cell.opname.name
            or not _same_typed(view.node_kwargs(cell.node), cell.kwargs)
            or not _same_typed(raw_kwargs, writer['adapter_kwargs'])):
        raise ValueError('bw-reduce-scatter current original opcode/raw kwargs mismatch')
    if linear._writer(snapshot, cells, i) != scope.source_writer:
        raise ValueError('bw-reduce-scatter original collective writer mismatch')
    inputs = view.node_inputs(cell.node); output, = view.node_outputs(cell.node)
    ranks = list(scope.ranks); ids = [t.tid for t in inputs]
    if (scope.op != 'ReduceScatterPrim' or scope.node != cell.node
            or not _same_typed(tuple(t.rank for t in inputs), scope.ranks)
            or not _same_typed(tuple(ids), scope.input_tids)
            or not _same_typed(output.tid, scope.output_tid)
            or not _same_typed(scope.local_index, ranks.index(cell.rank))):
        raise ValueError('bw-reduce-scatter ordered peers/output/local index mismatch')
    if (ctx.get('status') != 'structurally-bound' or ctx.get('gradient_value_proved') is not False
            or ctx['runtime']['backward']['op'] != 'ReduceScatterPrim'):
        raise ValueError('bw-reduce-scatter original backward runtime context required')
    runtime_kwargs = ctx['runtime']['backward']['kwargs']
    shape = tuple(view.tensor_shape(inputs[0])); outshape = tuple(view.tensor_shape(output))
    dim = runtime_kwargs['dim']
    if type(dim) is not int:
        raise ValueError('bw-reduce-scatter strict effective dim required')
    dim = dim + len(shape) if dim < 0 else dim
    if (not _same_typed(scope.params, (dim,)) or not _same_typed(runtime_kwargs['ranks'], ranks)):
        raise ValueError('bw-reduce-scatter effective backward dim/group mismatch')
    if (not ranks or len(set(ranks)) != len(ranks) or len(inputs) != len(ranks)
            or any(type(r) is not int or not 0 <= r < view.W.runtime_ndevs for r in ranks)
            or not shape or not 0 <= dim < len(shape)
            or any(type(d) is not int or d <= 0 for d in (*shape, *outshape))
            or any(not _same_typed(tuple(view.tensor_shape(t)), shape) for t in inputs)
            or not _same_typed(scope.input_shape, shape) or shape[dim] % len(ranks)):
        raise ValueError('bw-reduce-scatter positive divisible same peer shapes required')
    expected = list(shape); expected[dim] //= len(ranks)
    if not _same_typed(list(outshape), expected):
        raise ValueError('bw-reduce-scatter output shape mismatch')
    localref = _ref(bw.outputs[0]); outref = _ref(view.source_tensor(output))
    if (not _same_typed(ctx['output_gradient'], [localref])
            or not _same_typed(ctx['input_gradient'], [outref])
            or not _same_typed(ctx['gradient_read_points'], [dict(ref=localref, writer=local['bw_writer'])])):
        raise ValueError('bw-reduce-scatter original local gradient read point mismatch')
    contributions = []; values = []; points = []
    for tensor in inputs:
        fullref = view.source_tensor(tensor)
        pi, producer = _one(((j,c) for j,c in enumerate(cells) if fullref in c.outputs),
                            'ordered dX producer missing/ambiguous')
        if (pi not in selected or producer.opname.name != 'BW_linear'
                or not _same_typed(tuple(producer.outputs[0]), tuple(fullref))):
            raise ValueError('bw-reduce-scatter complete selected original dX outputs required')
        _, row = linear.render_read(view, cells, snapshot, pi, order, 'pm')
        peer_cell = _consumer(cells, fullref); peer_scope = view.collective_scopes[peer_cell.node]
        if (not _same_typed(peer_scope.ranks, scope.ranks)
                or not _same_typed(peer_scope.input_tids, scope.input_tids)
                or not _same_typed(peer_scope.params, scope.params)):
            raise ValueError('bw-reduce-scatter peer consumer group/dim mismatch')
        points.append(dict(ref=_ref(fullref), writer=row['bw_writer']))
        g,x,w = row['input_tids']
        values.append(f'(bw_linear (t {g}) (t {x}) (t {w})).1')
        contributions.append(dict(source_index=pi, gradient_ref=list(fullref),
                                  gradient_tid=tensor.tid, theorem=row['theorems'][0]))
    if not _same_typed(adapter['read_points'], points):
        raise ValueError('bw-reduce-scatter ordered original dX read points mismatch')
    runtime_schedule.validate(view, order['execution_to_source'])
    sequence = order['execution_to_source']; k = sequence.index(i)
    for j in sequence[k:]:
        if set(ids) & {t.tid for t in view.node_outputs(nodes[j])}:
            raise ValueError('bw-reduce-scatter peer overwritten in selected/complete execution suffix')
    name = f'backwardReduceScatter_pm_{i}'
    value = f'chunkPrimDimN {dim} {len(ranks)} {scope.local_index}'
    proof = [f'theorem {name}_read (s t : Store) (h : pmDenoteWithInputs s = some t) :',
        f'    t {output.tid} = {value} (tensorSum ({ids}.map t)) := by',
        '  apply SourceReduceScatterRead.reduceScatter_value_of_split pmGraph pmScope pmPeers pmGraph.nodes',
        f'    pmInputRequests (pmInputRequests.take {k}) (pmInputRequests.drop {k+1}) pmNode_{i}',
        f'    {cell.rank} {ranks} {ids} {output.tid} {dim} s t rfl ?_ rfl ?_ h',
        '  · calc',
        f'      pmInputRequests = pmInputRequests.take {k} ++ pmInputRequests.drop {k} := (List.take_append_drop {k} pmInputRequests).symm',
        '      _ = _ := rfl',
        f'  · change ∀ tid ∈ ({ids} : List Tid), ∀ row ∈ pmInputRequests.drop {k}, tid ∉ row.1.outs',
        '    decide', f'#print axioms {name}_read',
        f'theorem {name}_dx (s t : Store) (h : pmDenoteWithInputs s = some t) :',
        f'    t {output.tid} = {value} (tensorSum [' + ', '.join(values) + ']) := by',
        f'  rw [{name}_read s t h]',
        '  simp only [List.map_cons, List.map_nil]',
        '  rw [' + ', '.join(p['theorem']+' s t h' for p in contributions) + ']',
        f'#print axioms {name}_dx']
    return '\n'.join(proof)+'\n', dict(source_index=i, execution_index=k, node=list(cell.node),
        rank=cell.rank, ranks=ranks, local_index=scope.local_index, params=[dim],
        raw_kwargs=dict(cell.kwargs), backward_context_status=ctx['status'],
        runtime_backward=ctx['runtime']['backward'], source_writer=scope.source_writer,
        input_tids=ids, input_ranks=[t.rank for t in inputs], input_shape=list(shape),
        output_tid=output.tid, output_shape=list(outshape), output_ref=list(view.source_tensor(output)),
        contributions=contributions, theorems=[name+'_read', name+'_dx'],
        operand_nonwrite_source_indices=sequence[k:])


def render(worlds, indices, capture_path, rank_code_directory):
    """Freshly reload the original collective authority on every invocation."""
    view,cells,_,order,label = worlds[1]
    if (label != 'pm' or not indices or any(type(i) is not int or not 0 <= i < len(cells) for i in indices)
            or len(set(indices)) != len(indices)):
        raise ValueError('bw-reduce-scatter unique original linear projection required')
    snapshot = compiler._load_chunk_source(capture_path, rank_code_directory)
    compiler.attach_collective_scopes(view, snapshot)
    proofs = []; rows = []; seen = set()
    for index in indices:
        text,row = _read(view, cells, snapshot, order, index, indices)
        if row['source_index'] in seen:
            raise ValueError('bw-reduce-scatter duplicate collective projection')
        seen.add(row['source_index']); proofs.append(text); rows.append(row)
    return ''.join(proofs), dict(reads=rows, proof_admissible=False, kernel_value_proved=False,
        public_complete=False, torch_refinement=False, sm_pm_dx_equal=False)
