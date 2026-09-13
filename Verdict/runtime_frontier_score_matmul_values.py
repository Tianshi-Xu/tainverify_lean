"""First ready ORIGINAL ordered Q/K score matmul frontier, UNCOMPILED.

Only new binary reads and complete conditional unit facts are emitted. The
original division and AA(1,3) are inventoried, never proved or consumed. Parent
owns capture, imports, assembly, kernel and joint closure; no refinement claim.
"""
from Verdict import runtime_frontier_middle_exchange_values as predecessor
from Verdict import runtime_matmul_values as backend
from Verdict import runtime_div_values as division
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build

_post = predecessor.predecessor
_transpose = _post.predecessor
_view = predecessor._view


def render(sm, pm, lineages, validation, bound, execution_order):
    """One public predecessor render, with the identical six caller objects."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError, ZeroDivisionError) as exc:
        raise ValueError(f'malformed frontier score-matmul original source: {exc}') from exc


def _frontiers(sm, pm, si, pi, lineages, validation, bound, order, closed):
    """Peel candidate history, then reconstruct each original stage in order.

    K's SM source_step stays the second transpose while its PM source is now
    AA(2,1). Neither it nor replicated V can be fed to an earlier-state gate as
    though it were that gate's sharded input. Only the common view boundary is
    peeled; its independent source-derived whole-branch/DP/carry inventory is
    checked by the head constructor. All later names, descriptors, read suffixes
    and classifications are reconstructed, never seeded from candidate facts.
    """
    views = []
    for row in closed['frontier_units']:
        current = row; seen = set()
        while op(si.raw[tuple(current['source_step']['node'])]) != 'FW_multiref':
            if id(current) in seen: raise ValueError('score-matmul cyclic candidate history')
            seen.add(id(current))
            if (op(si.raw[tuple(current['source_step']['node'])]) == 'FW_view'
                    and all(op(pi.raw[tuple(s['node'])]) == 'FW_view' for s in current['local_steps'])):
                break
            current = current['input_frontier']
        views.append(current)
    selected = [i for i,r in enumerate(views) if op(si.raw[tuple(r['source_step']['node'])])=='FW_view']
    candidate = dict(frontier_units=views, units=[views[i] for i in selected],
        consumed_frontier_indices=selected, retained_units=[r for i,r in enumerate(views) if i not in selected],
        deferred_units=[])
    _, head = predecessor._head._render(sm,pm,lineages,validation,bound,order,candidate)
    _, first = _transpose._render(sm,pm,lineages,validation,bound,order,head)
    _, post = _post._render(sm,pm,lineages,validation,bound,order,first)
    _, expected = predecessor._render(sm,pm,lineages,validation,bound,order,post)
    if not _same_typed(closed,expected):
        raise ValueError('score-matmul complete original middle/post/head/view/history/frontier mismatch')
    return closed['frontier_units']


def _ordinary_raw(index, cell, kind, signature, arity):
    """No Port casts before original types, edge parents and scopes pass."""
    node = _view.source.residual._identity(index, cell)
    actual_signature = getattr(getattr(cell,'ir',None),'signature',None)
    if (op(cell)!=kind or type(actual_signature) is not str or actual_signature!=signature
            or len(cell.inputs)!=arity or len(cell.outputs)!=1
            or cell._input_irs is None or len(cell._input_irs)!=arity
            or cell._output_irs is None or len(cell._output_irs)!=1
            or any(node in getattr(index.view,k,{}) for k in ('collective_scopes','chunk_scopes','wred_scopes'))):
        raise ValueError('score-matmul original callable/arity/metadata/global scope mismatch')
    for refs,irs in ((cell.inputs,cell._input_irs),(cell.outputs,cell._output_irs)):
        for ref,ir in zip(refs,irs,strict=True):
            _view._raw(ir,4)
            if not _same_typed(ir.tid,ref[3]) or not _same_typed(tuple(ir.valmap),(0,1)):
                raise ValueError('score-matmul original full tensor/value identity mismatch')
    ports = [_transpose._producer(index,r) for r in cell.inputs]
    for p,ir in zip(ports,cell._input_irs,strict=True): _view._edge(index,p,ir)
    return ports


def _matmul(index, cell, operands):
    ports = _ordinary_raw(index,cell,'FW_matmul','torch.matmul',2)
    kwargs = dict(cell.kwargs); consts = kwargs.pop('__consts',[])
    if kwargs or not _same_typed(consts,[]) or not _same_typed(tuple(ports),tuple(operands)):
        raise ValueError('score-matmul original kwargs/ordered complete operands mismatch')
    return backend._matmul(index, cell, operands)


def _read(index, label, step, order):
    cell = index.raw[step.node]
    actual = _matmul(index,cell,step.inputs)
    if (label not in ('sm','pm') or tuple(cell.node)[0] != {'sm':'s','pm':'p'}[label]
            or not _same_typed(actual,step) or not _same_typed(order,build(index.view))):
        raise ValueError('score-matmul original fresh step/full schedule mismatch')
    _, auth = backend._consumer(index, actual.inputs[0], order)
    proof, row = backend._read(index.view, label, actual, order)
    row.update(source_signature=cell.ir.signature,
        source_writer=auth['source_writer'], writer_ref=auth.get('writer_ref'),
        input_metadata='present', output_metadata='present')
    return proof, row


def _ready(groups):
    return bool(groups) and all(len(cs)==1 and op(cs[0])=='FW_matmul' for cs in groups)


def _classification(original_carry, groups):
    """Carry identity has already passed the independent original inventory."""
    if original_carry: return 'retained'
    return 'ready' if _ready(groups) else 'deferred'


def _unit(si, pi, left, right, global_, locals_, names, join):
    """Authenticate the ordered binary join before the unchanged six-arg law."""
    if (not _same_typed(_matmul(si,si.raw[global_.node],global_.inputs),global_)
            or not _same_typed([s.node[1] for s in locals_],left['ranks'])
            or not _same_typed(left['ranks'],right['ranks'])
            or not _same_typed([list(p.endpoint.ref) for p in global_.inputs],
                              [left['sm_output_ref'],right['sm_output_ref']])):
        raise ValueError('score-matmul original ordered global operands/rank cover mismatch')
    parent = si.raw[global_.node]._output_irs[0].parent.tid
    for j,step in enumerate(locals_):
        if (not _same_typed(_matmul(pi,pi.raw[step.node],step.inputs),step)
                or not _same_typed([list(p.endpoint.ref) for p in step.inputs],
                                  [left['pm_output_refs'][j],right['pm_output_refs'][j]])
                or not _same_typed(pi.raw[step.node]._output_irs[0].parent.tid,parent)):
            raise ValueError('score-matmul original local operand/peer/output parent mismatch')
    for k,row in enumerate((left,right)):
        predecessor.backend._contract(row,global_.inputs[k],[s.inputs[k] for s in locals_])
    pair=[left['frontier_index'],right['frontier_index']]
    expected=dict(frontier_indices=pair,emitted_at_frontier_index=min(pair),unit=left['unit'],ranks=left['ranks'],
        sm_input_refs=[list(p.endpoint.ref) for p in global_.inputs],
        pm_ordered_input_refs=[[list(p.endpoint.ref) for p in s.inputs] for s in locals_],
        sm_node=list(global_.node),pm_nodes=[list(s.node) for s in locals_])
    if len(set(pair))!=2 or not _same_typed(join,expected):
        raise ValueError('score-matmul complete original ordered join mismatch')
    return backend._unit(left,right,global_,locals_,names,join)


def _successor(index, cell):
    """Authenticate downstream edges but emit no division or AA value read."""
    if op(cell) != 'FW_div':
        return _post._successor(index, cell)
    producer, = _ordinary_raw(index,cell,'FW_div','torch.div',1)
    step, auth = division._div(index, cell, producer)
    return dict(node=list(step.node), op=step.op, source_signature=cell.ir.signature,
        source_inputs=[list(r) for r in cell.inputs], source_outputs=[list(r) for r in cell.outputs],
        input_shapes=[list(p.endpoint.shape) for p in step.inputs],
        output_shapes=[list(p.endpoint.shape) for p in step.outputs], value_proved=False, **auth)


def _census(si, pi, g, ps):
    groups = [_view.column._consumers(si, [g]), *[_view.column._consumers(pi, [p]) for p in ps]]
    peers = _view.column._consumers(pi, ps)
    return dict(observed_consumer_ops=[[op(c) for c in cells] for cells in groups],
        sm_consumers=[list(c.node) for c in groups[0]], pm_consumers=[list(c.node) for c in peers],
        downstream_consumers=[*[_successor(si,c) for c in groups[0]], *[_successor(pi,c) for c in peers]])


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order, dict(sm=build(sm), pm=build(pm))):
        raise ValueError('score-matmul complete typed execution/inverse order mismatch')
    si, pi = (_Index(v,raw) for v,raw in zip((sm,pm),validation._inputs[:2],strict=True))
    old = _frontiers(sm, pm, si, pi, lineages, validation, bound, order, closed)
    entries = []; lookup = {}
    for i, row in enumerate(old):
        g = _transpose._producer(si, row['sm_output_ref'])
        ps = [_transpose._producer(pi, ref) for ref in row['pm_output_refs']]
        predecessor.backend._contract(row, g, ps)
        key = (g.endpoint.ref, row['unit'], tuple(row['ranks']))
        if key in lookup: raise ValueError('score-matmul duplicate original frontier identity')
        lookup[key] = i
        groups = [_view.column._consumers(si,[g]), *[_view.column._consumers(pi,[p]) for p in ps]]
        entries.append((g,ps,groups))
    proofs, reads, units, result, retained, deferred, joins = [], [], [], [], [], [], []
    consumed = set(); names = {}; seen = {}; completed = set()
    for i, row in enumerate(old):
        if i in consumed: continue
        g, ps, groups = entries[i]
        classification = _classification(op(si.raw[tuple(row['source_step']['node'])])=='FW_multiref',groups)
        if classification=='retained':
            result.append(row); retained.append(row); continue
        if classification=='deferred':
            deferred.append(dict(frontier_index=i, unit=row['unit'], source_boundary=row,
                reason='unavailable-or-unsupported-original-consumer', value_proved=False))
            result.append(row); continue
        gc, gr = backend._consumer(si,g,order['sm'])
        consumers = [backend._consumer(pi,p,order['pm']) for p in ps]
        keys = [(tuple(ref),row['unit'],tuple(row['ranks'])) for ref in gc.inputs]
        missing = [list(k[0]) for k in keys if k not in lookup]
        if missing:
            if any(not _same_typed(r['port_positions'],gr['port_positions']) for _,r in consumers):
                raise ValueError('score-matmul deferred original ordered port correspondence mismatch')
            deferred.append(dict(frontier_index=i, unit=row['unit'], source_boundary=row,
                global_first_consumer=gr, first_consumers=[r for _,r in consumers],
                missing_operand_refs=missing, reason='first-original-FW_matmul-missing-operand', value_proved=False))
            result.append(row); continue
        pair = [lookup[k] for k in keys]
        if len(pair)!=2 or len(set(pair))!=2 or any(j in consumed for j in pair):
            raise ValueError('score-matmul overlapping original operand coverage')
        if row['unit'] in completed:
            deferred.append(dict(frontier_index=i, unit=row['unit'], source_boundary=row,
                reason='after-first-ready-original-score-matmul', value_proved=False))
            result.append(row); continue
        if any(len(entries[j][2][0])!=1 or tuple(entries[j][2][0][0].node)!=tuple(gc.node) for j in pair):
            raise ValueError('score-matmul paired original SM first consumer mismatch')
        left, right = [old[j] for j in pair]
        global_ = _matmul(si, gc, [entries[j][0] for j in pair])
        locals_ = []
        for r in range(len(ps)):
            cells = [entries[j][2][r+1] for j in pair]
            if any(len(cs)!=1 for cs in cells) or tuple(cells[0][0].node)!=tuple(cells[1][0].node):
                raise ValueError('score-matmul paired original PM first consumer mismatch')
            locals_.append(_matmul(pi,cells[0][0],[entries[j][1][r] for j in pair]))
        join = dict(frontier_indices=pair, emitted_at_frontier_index=i, unit=row['unit'], ranks=row['ranks'],
            sm_input_refs=[list(p.endpoint.ref) for p in global_.inputs],
            pm_ordered_input_refs=[[list(p.endpoint.ref) for p in s.inputs] for s in locals_],
            sm_node=list(global_.node), pm_nodes=[list(s.node) for s in locals_])
        for index,label,step in [(si,'sm',global_), *((pi,'pm',s) for s in locals_)]:
            if step.node in seen:
                if label!='sm' or not _same_typed(seen[step.node],step):
                    raise ValueError('score-matmul duplicate/nonidentical original read')
                continue
            proof, read = _read(index,label,step,order[label])
            name = read['theorem'].replace('matmulRead_','frontierScoreMatmulRead_')
            proofs.extend(s.replace(read['theorem'],name) for s in proof)
            read.update(theorem=name,unit=row['unit'],frontier_index=i)
            reads.append(read); names[step.node]=name; seen[step.node]=step
        proof, fresh = _unit(si,pi,left,right,global_,locals_,names,join)
        name = fresh['theorem'].replace('matmulUnitFacts_','frontierScoreMatmulUnitFacts_')
        proofs.extend(s.replace(fresh['theorem'],name) for s in proof)
        fresh.update(theorem=name,facts_theorem=name,input_frontiers=[left,right],
            input_refs=join['pm_ordered_input_refs'],source_output_slot=0,slot=0,
            pm_output_slots=[0 for _ in locals_],output_gather_axis=1,frontier_index=i,
            deferred_stage='after-first-ready-score-matmul: division and AA(1,3) values unproved')
        fresh.update(_census(si,pi,global_.outputs[0],[s.outputs[0] for s in locals_]))
        units.append(fresh); result.append(fresh); joins.append(join)
        consumed.update(pair); completed.add(row['unit'])
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, aggregate costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld','noncomputable section','set_option maxHeartbeats 500000',
        *proofs,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return text, dict(status='source-frontier-score-matmul-values-emitted-uncompiled',reads=reads,units=units,
        frontier_units=result,retained_units=retained,deferred_units=deferred,ordered_joins=joins,
        consumed_frontier_indices=sorted(consumed),lean_bytes=len(text.encode()),
        cost_scope='score matmul fragment only; excludes predecessors, frame and imports',
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
