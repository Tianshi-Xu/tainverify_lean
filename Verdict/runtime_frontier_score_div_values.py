"""Current mixed score division, conditional and UNCOMPILED.

Only original scalar reads and complete unit facts are emitted. No canonical
attachment, downstream exchange/softmax, successful run or Torch claim.
"""
from Verdict import runtime_frontier_score_exchange_values as predecessor
from Verdict import runtime_div_values as backend
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build

_score = predecessor.predecessor
_view = predecessor._view
_transpose = predecessor._transpose


def render(sm, pm, lineages, validation, bound, execution_order):
    """Exactly one public predecessor call, preserving all six identities."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError, ZeroDivisionError) as exc:
        raise ValueError(f'malformed frontier score-div original source: {exc}') from exc


def _history_identity(si, pi, row, owners):
    """Cheap source-derived necessary checks before expensive full rebuilding.

    This is NOT acceptance: _frontiers still rebuilds and compares the entire
    original receipt. In particular, valid-looking earlier aliases cannot use
    these name/endpoint checks as a substitute for the root carry inventory.
    """
    from Verdict.runtime_embedding_units import _one
    owner = _one((o for o in owners if _same_typed(o['unit'],row['unit'])),
        'score-div original history DP owner missing/ambiguous')
    if not _same_typed((row['ranks'],row['positions']),(owner['ranks'],owner['positions'])):
        raise ValueError('score-div original history owner/rank/position mismatch')
    local_steps=row['local_steps']
    if not _same_typed([s['node'][1] for s in local_steps],owner['ranks']):
        raise ValueError('score-div original history complete ordered peer cover required')
    for index,step in [(si,row['source_step']),*[(pi,s) for s in local_steps]]:
        cell=index.raw[tuple(step['node'])]
        _view.source.residual._identity(index,cell)
        for key in ('inputs','outputs'):
            refs=[tuple(p['endpoint']['ref']) for p in step[key]]
            if not _same_typed(refs,[tuple(r) for r in getattr(cell,key)]):
                raise ValueError('score-div original history complete ordered source ports mismatch')
    cell=si.raw[tuple(row['source_step']['node'])]
    g=_transpose._producer(si,row['sm_output_ref'])
    slot=_one((i for i,r in enumerate(cell.outputs) if _same_typed(tuple(r),g.endpoint.ref)),
        'score-div original history SM output slot missing/ambiguous')
    kind=op(cell); local=[op(pi.raw[tuple(s['node'])]) for s in local_steps]
    if kind!='FW_multiref':
        ps=[_transpose._producer(pi,ref) for ref in row['pm_output_refs']]
        backend.middle._contract(row,g,ps)
    if kind=='FW_multiref':
        prefix='frontierAliasFacts'; suffix=''
    elif kind=='FW_matmul':
        prefix='frontierScoreExchangeUnitFacts' if all(k=='AllToAllPrim' for k in local) else 'frontierScoreMatmulUnitFacts'
        suffix=''
        if all(k=='FW_matmul' for k in local):
            join=row['ordered_join']
            if (not _same_typed(join['sm_input_refs'],[list(r) for r in cell.inputs])
                    or not _same_typed(join['pm_ordered_input_refs'],
                        [[list(r) for r in pi.raw[tuple(s['node'])].inputs] for s in local_steps])):
                raise ValueError('score-div original binary ordered join mismatch')
    elif kind=='FW_view':
        prefix='frontierProjectionViewUnitFacts' if all(k=='FW_view' for k in local) else 'frontierHeadExchangeUnitFacts'
        suffix=f'_slot{slot}'
    elif kind=='FW_transpose':
        if all(k=='AllToAllPrim' for k in local):
            prefix='frontierMiddleExchangeUnitFacts'
        elif all(k=='AllGatherPrim' for k in local):
            prefix='frontierPostTransposeUnitFacts'
        else:
            params,status=backend._ordinary(si.view,cell.node,backend.compiler._get_node_params)
            if status is not None:
                raise ValueError('score-div original history transpose params unsupported')
            prefix='frontierProjectionTransposeUnitFacts' if _same_typed(params,[1,2]) else 'frontierPostTransposeUnitFacts'
        suffix=f'_slot{slot}'
    else:
        raise ValueError('score-div unsupported original history boundary')
    expected=f'{prefix}_{g.endpoint.tid}_{owner["unit"]}{suffix}'
    if not _same_typed((row['facts_theorem'],row['theorem'],row['source_output_slot']),(expected,expected,slot)):
        raise ValueError('score-div original complete fact identity mismatch')


def _frontiers(sm, pm, si, pi, lineages, validation, bound, order, closed):
    """Rebuild from original view/fork authority, not candidate fact strings.

    Exchange keeps the SM matmul descriptor but has a UNARY history. Peel it
    before expanding the original Q-first/K-second binary ordered join. The
    head gate independently derives the full V/carry/DP inventory and names.
    """
    views = []
    def peel(row, active):
        if id(row) in active:
            raise ValueError('score-div cyclic candidate history')
        active = active | {id(row)}
        _history_identity(si,pi,row,validation._inputs[3]['config']['units'])
        kind = op(si.raw[tuple(row['source_step']['node'])])
        local = [op(pi.raw[tuple(s['node'])]) for s in row['local_steps']]
        if kind == 'FW_matmul' and local and all(k == 'AllToAllPrim' for k in local):
            peel(row['input_frontier'], active)
        elif kind == 'FW_matmul':
            if len(row['input_frontiers']) != 2:
                raise ValueError('score-div complete binary history required')
            for operand in row['input_frontiers']:
                peel(operand, active)
        elif kind == 'FW_multiref' or (kind == 'FW_view' and all(k == 'FW_view' for k in local)):
            views.append(row)
        else:
            peel(row['input_frontier'], active)
    for row in closed['frontier_units']:
        peel(row, set())
    selected = [i for i,r in enumerate(views) if op(si.raw[tuple(r['source_step']['node'])]) == 'FW_view']
    candidate = dict(frontier_units=views, units=[views[i] for i in selected],
        consumed_frontier_indices=selected, retained_units=[r for i,r in enumerate(views) if i not in selected],
        deferred_units=[])
    for stage in (predecessor._head, _transpose, _score._post, _score.predecessor, _score, predecessor):
        _, candidate = stage._render(sm,pm,lineages,validation,bound,order,candidate)
    if not _same_typed(closed,candidate):
        raise ValueError('score-div complete original binary/history/frontier mismatch')
    return closed['frontier_units']


def _div(index, cell, producer):
    ports = _score._ordinary_raw(index,cell,'FW_div','torch.div',1)
    if not _same_typed(ports,[producer]):
        raise ValueError('score-div complete original producer mismatch')
    return backend._div(index,cell,producer)


def _read(index, label, step, order):
    actual, auth = _div(index,index.raw[step.node],step.inputs[0])
    if (label not in ('sm','pm') or step.node[0] != {'sm':'s','pm':'p'}[label]
            or not _same_typed(actual,step) or not _same_typed(order,build(index.view))):
        raise ValueError('score-div fresh step/full execution order mismatch')
    proof, row = backend._read(index.view,label,actual,order)
    row.update(auth,source_signature=index.raw[step.node].ir.signature)
    return proof,row


def _classification(carry, groups):
    if carry:
        return 'retained'
    ready = bool(groups) and all(len(cs)==1 and op(cs[0])=='FW_div' for cs in groups)
    if not ready and any(op(cell)=='FW_div' for cells in groups for cell in cells):
        raise ValueError('score-div incomplete/mixed/duplicate original division consumer cover')
    return 'ready' if ready else 'deferred'


def _unit(si, pi, old, global_, locals_, names, c):
    ga, auth = _div(si,si.raw[global_.node],global_.inputs[0])
    if (not _same_typed(ga,global_) or not _same_typed(auth['scalar_nat'],c)
            or not _same_typed([s.node[1] for s in locals_],old['ranks'])
            or len({s.node for s in locals_}) != len(locals_)
            or not _same_typed(list(global_.inputs[0].endpoint.ref),old['sm_output_ref'])
            or not _same_typed([list(s.inputs[0].endpoint.ref) for s in locals_],old['pm_output_refs'])):
        raise ValueError('score-div original ordered peer/global/scalar cover mismatch')
    for step in locals_:
        actual, local = _div(pi,pi.raw[step.node],step.inputs[0])
        if (not _same_typed(actual,step) or not _same_typed(local['scalar_nat'],c)
                or not _same_typed(pi.raw[step.node]._output_irs[0].parent.tid,
                                   si.raw[global_.node]._output_irs[0].parent.tid)):
            raise ValueError('score-div original local step/scalar/output parent mismatch')
    for index,step in [(si,global_),*[(pi,s) for s in locals_]]:
        cells = _view.column._consumers(index,[step.inputs[0]])
        if not _same_typed([tuple(cell.node) for cell in cells],[step.node]):
            raise ValueError('score-div complete original first-consumer cover mismatch')
    backend.middle._contract(old,global_.inputs[0],[s.inputs[0] for s in locals_])
    return backend._unit(old,global_,locals_,names,c)


def _successor(index, cell):
    """Inventory AA(3,2) directly; no old AA(3,1) backend or new value law."""
    if op(cell) != 'AllToAllPrim':
        return _score._successor(index,cell)
    node = _view.source.residual._identity(index,cell)
    ports = [_transpose._producer(index,r) for r in cell.inputs]
    ranks = tuple(p.endpoint.ref[1] for p in ports)
    signature = getattr(getattr(cell,'ir',None),'signature',None)
    if (signature != 'nnscaler.runtime.adapter.nn.alltoall_alltoall' or type(signature) is not str
            or len(ranks)<2 or len(set(ranks))!=len(ranks) or cell.rank not in ranks
            or any(node in getattr(index.view,k,{}) for k in ('chunk_scopes','wred_scopes'))):
        raise ValueError('score-div next exchange original callable/peer/scope mismatch')
    j=ranks.index(cell.rank); scope=index.view.collective_scopes[node]
    kw=dict(cell.kwargs); consts=kw.pop('__consts',[])
    if (not _same_typed(kw,dict(idim=3,odim=2,ranks=list(ranks))) or not _same_typed(consts,[])
            or not _same_typed(scope.params,(3,2)) or len(cell.outputs)!=1):
        raise ValueError('score-div next exchange original AA(3,2) required')
    # Generic source-only rank-four admission, not a route-specific value adapter.
    _view._outgoing(index,ports)
    out=cell._output_irs[0]; _view._raw(out,4)
    parent=index.raw[ports[0].endpoint.writer]._output_irs[0].parent.tid
    if (not _same_typed(out.parent.tid,parent)
            or any(not _same_typed(index.raw[p.endpoint.writer]._output_irs[0].parent.tid,parent) for p in ports)
            or not _same_typed(scope.output_tid,index.endpoint(cell.outputs[0]).tid)):
        raise ValueError('score-div next exchange original output/peer parent mismatch')
    shape=list(ports[j].endpoint.shape); shape[3]*=len(ports)
    if shape[2]%len(ports):
        raise ValueError('score-div next exchange nonintegral split')
    shape[2]//=len(ports)
    if not _same_typed(tuple(shape),tuple(out.shape)):
        raise ValueError('score-div next exchange input-derived output shape mismatch')
    return dict(node=list(node),op=op(cell),axes=[3,2],source_signature=signature,source_kwargs=dict(cell.kwargs),
        source_inputs=[list(r) for r in cell.inputs],source_outputs=[list(r) for r in cell.outputs],
        input_shapes=[list(p.endpoint.shape) for p in ports],output_shapes=[shape],value_proved=False,
        source_writer=scope.source_writer,input_metadata='local-only' if len(cell._input_irs)==1 else 'all-peers')


def _census(si,pi,g,ps):
    groups=[_view.column._consumers(si,[g]),*[_view.column._consumers(pi,[p]) for p in ps]]
    peers=_view.column._consumers(pi,ps)
    return dict(observed_consumer_ops=[[op(c) for c in cs] for cs in groups],
        sm_consumers=[list(c.node) for c in groups[0]],pm_consumers=[list(c.node) for c in peers],
        downstream_consumers=[*[_successor(si,c) for c in groups[0]],*[_successor(pi,c) for c in peers]])


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order,dict(sm=build(sm),pm=build(pm))):
        raise ValueError('score-div complete typed execution/inverse order mismatch')
    si,pi = (_Index(v,raw) for v,raw in zip((sm,pm),validation._inputs[:2],strict=True))
    old = _frontiers(sm,pm,si,pi,lineages,validation,bound,order,closed)
    proofs,reads,units,result,retained,deferred,consumed = [],[],[],[],[],[],[]
    seen={}; names={}
    for i,row in enumerate(old):
        g = _transpose._producer(si,row['sm_output_ref'])
        ps = [_transpose._producer(pi,r) for r in row['pm_output_refs']]
        groups = [_view.column._consumers(si,[g]), *[_view.column._consumers(pi,[p]) for p in ps]]
        classification = _classification(op(si.raw[tuple(row['source_step']['node'])])=='FW_multiref',groups)
        if classification == 'retained':
            result.append(row); retained.append(row); continue
        backend.middle._contract(row,g,ps)
        if classification == 'deferred':
            result.append(row)
            deferred.append(dict(frontier_index=i,unit=row['unit'],source_boundary=row,
                reason='unavailable-or-unsupported-original-consumer',value_proved=False))
            continue
        global_,ga = _div(si,groups[0][0],g)
        pairs = [_div(pi,cs[0],p) for cs,p in zip(groups[1:],ps,strict=True)]
        if row['layout'] != 'sharded' or not _same_typed(row['gather_axis'],3):
            raise ValueError('score-div requires complete original axis3 predecessor')
        locals_ = [s for s,_ in pairs]
        for index,label,step in [(si,'sm',global_), *[(pi,'pm',s) for s in locals_]]:
            if step.node in seen:
                if label!='sm' or not _same_typed(seen[step.node],step):
                    raise ValueError('score-div duplicate/cross-DP original source')
                continue
            proof,read = _read(index,label,step,order[label])
            name = read['theorem'].replace('divRead_','frontierScoreDivRead_')
            proofs.extend(s.replace(read['theorem'],name) for s in proof)
            read.update(theorem=name,unit=row['unit'],frontier_index=i)
            reads.append(read); names[step.node]=name; seen[step.node]=step
        proof,fresh = _unit(si,pi,row,global_,locals_,names,ga['scalar_nat'])
        name = fresh['theorem'].replace('divUnitFacts_','frontierScoreDivUnitFacts_')
        proofs.extend(s.replace(fresh['theorem'],name) for s in proof)
        shape=list(global_.outputs[0].endpoint.shape)
        local_shape=list(locals_[0].outputs[0].endpoint.shape)
        fresh.update(theorem=name,facts_theorem=name,input_frontier=row,predecessor_facts=row['facts_theorem'],
            global_shape=shape,local_shape=local_shape,
            dimensions=dict(D=row['dimensions']['D'],T=len(locals_),**dict(zip(('B','H','Q','C'),local_shape))),
            source_output_slot=0,slot=0,pm_output_slots=[0 for _ in locals_],frontier_index=i,
            deferred_stage='after-score-div: original next exchange and softmax values unproved')
        fresh.update(_census(si,pi,global_.outputs[0],[s.outputs[0] for s in locals_]))
        units.append(fresh); result.append(fresh); consumed.append(i)
    text='\n'.join(['-- UNCOMPILED: parent owns exact imports, assembly, budget and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld','noncomputable section','set_option maxHeartbeats 500000',
        *proofs,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return text,dict(status='source-frontier-score-div-values-emitted-uncompiled',reads=reads,units=units,
        frontier_units=result,retained_units=retained,deferred_units=deferred,consumed_frontier_indices=consumed,
        lean_bytes=len(text.encode()),cost_scope='score division fragment only; excludes predecessors, frame and imports',
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
