"""Retain the original reverse residual branch through faithful AllToAll.

Runtime autograd context supplies the effective backward dimensions. Raw cell
kwargs describe its paired forward primitive and must not select the BW tensor.
"""
from Verdict import graph_to_lean as compiler, runtime_schedule
from Verdict import runtime_backward_add_consumers as add_consumers
from Verdict import runtime_backward_add_reads as add_reads
from Verdict.runtime_backward_linear_reads import _writer
from Verdict.runtime_lineage import _same_typed


def _one(rows, reason):
    rows = list(rows)
    if len(rows) != 1: raise ValueError('bw-residual-exchange ' + reason)
    return rows[0]


def _read(view, cells, snapshot, order, prior, add_row):
    producer = cells[add_row['source_index']]
    _, fresh = add_reads.render_read(view, cells, snapshot, add_row['source_index'], order, 'pm')
    if not _same_typed(fresh, add_row):
        raise ValueError('bw-residual-exchange original predecessor mismatch')
    ref = producer.outputs[0]
    consumer = _one((c for c in cells if c.rank == producer.rank and ref in c.inputs),
                    'local retained residual consumer missing/ambiguous')
    if consumer.opname.name != 'AllToAllPrim':
        raise ValueError('bw-residual-exchange expected original reverse AllToAll')
    nodes = view.nodes(); i = nodes.index(consumer.node)
    scope = view.collective_scopes[consumer.node]
    writer = _one((w for w in snapshot['writers'] if w['export_id'] == scope.source_writer), 'writer missing/ambiguous')
    ctx = writer['adapter'].get('backward_context', {})
    if (ctx.get('status') != 'structurally-bound' or ctx.get('gradient_value_proved') is not False
            or ctx['runtime']['backward']['op'] != 'AllToAllPrim'
            or not _same_typed(ctx['runtime']['backward']['kwargs'],
                              dict(idim=scope.params[0], odim=scope.params[1], ranks=list(scope.ranks)))):
        raise ValueError('bw-residual-exchange authenticated backward context required')
    if _writer(snapshot, cells, i) != scope.source_writer:
        raise ValueError('bw-residual-exchange original collective writer mismatch')
    inputs = view.node_inputs(consumer.node); output, = view.node_outputs(consumer.node)
    if (not _same_typed(tuple(t.tid for t in inputs), scope.input_tids)
            or not _same_typed(tuple(t.rank for t in inputs), scope.ranks)
            or output.tid != scope.output_tid or scope.local_index != list(scope.ranks).index(consumer.rank)):
        raise ValueError('bw-residual-exchange ordered peer/output/local index mismatch')
    predecessors = []
    for tensor in inputs:
        original = list(view.source_tensor(tensor))
        row = _one((p['add_read'] for p in prior['reads'] if p['world'] == 'pm'
                    and _same_typed(p['add_read']['output_refs'][0], original)),
                   'ordered retained-branch contribution missing/ambiguous')
        _, authenticated = add_reads.render_read(view, cells, snapshot, row['source_index'], order, 'pm')
        if not _same_typed(authenticated, row):
            raise ValueError('bw-residual-exchange fresh peer source binding mismatch')
        predecessors.append(row)
    fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
    local = dict(zip(fields, ref, strict=True))
    outref = dict(zip(fields, view.source_tensor(output), strict=True))
    if (not _same_typed(ctx['output_gradient'], [local])
            or not _same_typed(ctx['input_gradient'], [outref])
            or not _same_typed(ctx['gradient_read_points'], [dict(ref=local, writer=add_row['bw_writer'])])):
        raise ValueError('bw-residual-exchange original backward gradient read point mismatch')
    runtime_schedule.validate(view, order['execution_to_source'])
    sequence = order['execution_to_source']; k = sequence.index(i)
    ids = [t.tid for t in inputs]
    if any(set(ids) & {t.tid for t in view.node_outputs(nodes[j])} for j in sequence[k:]):
        raise ValueError('bw-residual-exchange peer overwritten in full suffix')
    rs = list(scope.ranks); idim, odim = scope.params
    name = f'backwardResidualExchange_pm_{i}'
    value = f'AllToAllSourceFaithful.tensor {len(rs)} {scope.local_index} {idim} {odim}'
    contributions = ['(bw_add2 ' + ' '.join(f'(t {tid})' for tid in p['input_tids']) + ').1' for p in predecessors]
    proof = [f'theorem {name}_read (s t : Store) (h : pmDenoteWithInputs s = some t) :',
             f'    t {output.tid} = {value} ({ids}.map t) := by',
             '  apply SourcePrimitiveRead.allToAll_value_of_split pmGraph pmScope pmPeers pmGraph.nodes',
             f'    pmInputRequests (pmInputRequests.take {k}) (pmInputRequests.drop {k+1}) pmNode_{i}',
             f'    {consumer.rank} {rs} {ids} {output.tid} {idim} {odim} s t rfl ?_ rfl ?_ h',
             '  · calc', f'      pmInputRequests = pmInputRequests.take {k} ++ pmInputRequests.drop {k} := (List.take_append_drop {k} pmInputRequests).symm',
             '      _ = _ := rfl',
             f'  · change ∀ tid ∈ ({ids} : List Tid), ∀ row ∈ pmInputRequests.drop {k}, tid ∉ row.1.outs',
             '    decide', f'#print axioms {name}_read',
             f'theorem {name}_contributions (s t : Store) (h : pmDenoteWithInputs s = some t) :',
             f'    t {output.tid} = {value} [' + ', '.join(contributions) + '] := by',
             f'  rw [{name}_read s t h]', '  simp only [List.map_cons, List.map_nil]',
             '  rw [' + ', '.join(p['theorems'][0] + ' s t h' for p in predecessors) + ']',
             f'#print axioms {name}_contributions']
    return '\n'.join(proof) + '\n', dict(source_index=i, execution_index=k, ranks=rs,
        input_tids=ids, output_tid=output.tid, output_ref=list(view.source_tensor(output)),
        params=list(scope.params), raw_params=[consumer.kwargs['idim'], consumer.kwargs['odim']],
        predecessors=[p['theorems'][0] for p in predecessors],
        theorems=[name+'_read', name+'_contributions'], backward_context_status=ctx['status'])


def render(worlds, capture, rank_code):
    _, prior = add_consumers.render(worlds)
    view, cells, _, order, label = worlds[1]
    if label != 'pm': raise ValueError('bw-residual-exchange original PM world required')
    snapshot = compiler._load_chunk_source(capture, rank_code)
    compiler.attach_collective_scopes(view, snapshot)
    proof, rows = [], []
    for p in prior['reads']:
        if p['world'] != 'pm': continue
        text, row = _read(view, cells, snapshot, order, prior, p['add_read'])
        proof.append(text); rows.append(row)
    return ''.join(proof), dict(reads=rows, proof_admissible=False, kernel_value_proved=False,
                               public_complete=False, torch_refinement=False)
