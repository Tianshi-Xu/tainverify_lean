"""Mixed original second-transpose/AllGather values, UNCOMPILED.

Q matmuls are explicitly deferred; residual forks remain intact. Only the new
fragment is emitted. Parent owns assembly, actual capture and kernel closure.
"""
from Verdict import runtime_frontier_projection_transpose_values as predecessor
from Verdict import runtime_post_transpose_values as backend
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build
from Verdict.runtime_embedding_units import _one


_view = predecessor._view
_head = predecessor.predecessor


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh predecessor, exactly once, with precisely the SAME six objects."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError, ZeroDivisionError) as exc:
        raise ValueError(f'malformed frontier post-transpose original source: {exc}') from exc


def _frontiers(sm, pm, si, pi, lineages, validation, bound, order, closed):
    # Peel candidate history only; regenerate its authority from original source.
    # A transpose output is NOT a HEAD-AA input record. The view gate also
    # independently expands the original carry fork, catching coherent deletion
    # and substitution with an earlier genuine same-shaped residual skip.
    views = []
    for row in closed['frontier_units']:
        kind = op(si.raw[tuple(row['source_step']['node'])])
        if kind == 'FW_multiref': views.append(row)
        elif kind == 'FW_transpose': views.append(row['input_frontier']['input_frontier'])
        else: raise ValueError('post-transpose original transpose/retained fork required')
    selected = [i for i,r in enumerate(views) if op(si.raw[tuple(r['source_step']['node'])]) == 'FW_view']
    candidate = dict(frontier_units=views, units=[views[i] for i in selected],
        consumed_frontier_indices=selected, retained_units=[r for i,r in enumerate(views) if i not in selected],
        deferred_units=[])
    _, head = _head._render(sm, pm, lineages, validation, bound, order, candidate)
    _, expected = predecessor._render(sm, pm, lineages, validation, bound, order, head)
    if not _same_typed(closed, expected):
        raise ValueError('post-transpose complete original transpose/head/view/history/frontier mismatch')
    result = []
    for row in closed['frontier_units']:
        if op(si.raw[tuple(row['source_step']['node'])]) == 'FW_multiref':
            g = _view.frontier._output(si, row['source_step'], row['sm_output_ref'])
            ps = [_view.frontier._output(pi, s, ref) for s,ref in zip(row['local_steps'],row['pm_output_refs'],strict=True)]
        else:
            g = predecessor._producer(si,row['sm_output_ref'])
            ps = [predecessor._producer(pi,ref) for ref in row['pm_output_refs']]
            backend.transpose._contract(row,g,ps)
        result.append((row,g,ps))
    return result


def _transpose(index, cell, producer):
    if any(cell.node in getattr(index.view,k,{}) for k in ('collective_scopes','chunk_scopes','wred_scopes')):
        raise ValueError('post-transpose conflicting original transpose scope')
    predecessor._successor(index,cell)  # strict present raw rank-four edge metadata
    signature = getattr(getattr(cell,'ir',None),'signature',None)
    if type(signature) is not str or signature != 'torch.transpose':
        raise ValueError('post-transpose original function must be torch.transpose')
    # backend normalizes only for comparison: original negative kwargs survive.
    return backend._transpose(index,cell,producer)


def _boundary(index, cell, ports, ranks, j):
    predecessor._successor(index,cell)
    actual_ports = [predecessor._producer(index,ref) for ref in cell.inputs]
    if not _same_typed(tuple(ports),tuple(actual_ports)):
        raise ValueError('post-transpose complete original ordered peer descriptors mismatch')
    # nn.allgather_reducescatter -> AllGatherReduceScatter.forward ->
    # all_gather(itensor, dim, ranks), with reduce_scatter only in backward.
    signature = getattr(getattr(cell,'ir',None),'signature',None)
    if type(signature) is not str or signature != 'nnscaler.runtime.adapter.nn.allgather_reducescatter':
        raise ValueError('post-transpose original AllGather callable mismatch')
    if op(cell) != 'AllGatherPrim':
        raise ValueError('post-transpose only original AllGather is consumable')
    step, coverage = backend._boundary(index,cell,ports,ranks,j)
    return step, dict(coverage,producer_metadata='all-peers',input_parent_identity=coverage['input_metadata'])


def _read(index, label, step, order):
    if step.op == 'FW_transpose':
        actual = _transpose(index,index.raw[step.node],step.inputs[0])
        coverage = dict(input_metadata='present',output_metadata='present')
    elif step.op == 'AllGatherPrim':
        actual, coverage = _boundary(index,index.raw[step.node],step.inputs,step.ranks,step.local_index)
    else: raise ValueError('post-transpose unsupported original read')
    if not _same_typed(actual,step) or not _same_typed(order,build(index.view)):
        raise ValueError('post-transpose read original step/full schedule mismatch')
    proof,row = backend._read(index.view,label,actual,order)
    row.update(coverage,source_signature=index.raw[step.node].ir.signature)
    return proof,row


def _successor(index, cell):
    """Inventory only; in particular never emit the next AA2,1 value read."""
    if op(cell) != 'AllToAllPrim':
        return predecessor._successor(index,cell)
    ports=[predecessor._producer(index,r) for r in cell.inputs]
    ranks=[p.endpoint.ref[1] for p in ports]
    if cell.rank not in ranks:
        raise ValueError('post-transpose downstream receiver not in ordered peers')
    step,_,meta=_head._boundary(index,cell,ports,ranks,ranks.index(cell.rank))
    return dict(node=list(step.node),op=step.op,source_kwargs=dict(cell.kwargs),
        source_signature=cell.ir.signature,source_inputs=[list(r) for r in cell.inputs],
        source_outputs=[list(r) for r in cell.outputs],input_shapes=[list(p.endpoint.shape) for p in ports],
        output_shapes=[list(p.endpoint.shape) for p in step.outputs],value_proved=False,**meta)


def _census(si, pi, g, ps):
    groups=[_view.column._consumers(si,[g]),*[_view.column._consumers(pi,[p]) for p in ps]]
    peers=_view.column._consumers(pi,ps)
    return dict(observed_consumer_ops=[[op(c) for c in cells] for cells in groups],
        sm_consumers=[list(c.node) for c in groups[0]],pm_consumers=[list(c.node) for c in peers],
        downstream_consumers=[*[_successor(si,c) for c in groups[0]],*[_successor(pi,c) for c in peers]])


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order,dict(sm=build(sm),pm=build(pm))):
        raise ValueError('post-transpose complete typed execution/inverse order mismatch')
    si,pi = (_Index(v,raw) for v,raw in zip((sm,pm),validation._inputs[:2],strict=True))
    authenticated = _frontiers(sm,pm,si,pi,lineages,validation,bound,order,closed)
    proofs,reads,units,result,retained,deferred,consumed = [],[],[],[],[],[],[]
    names={}; seen={}
    def emit(index,label,step,i,old):
        if step.node in seen:
            if label != 'sm' or not _same_typed(seen[step.node],step):
                raise ValueError('post-transpose duplicate/cross-unit original operation')
            return
        proof,read = _read(index,label,step,order[label])
        name=read['theorem'].replace('postTransposeRead_','frontierPostTransposeRead_')
        proofs.extend(s.replace(read['theorem'],name) for s in proof)
        read.update(theorem=name,frontier_index=i,unit=old['unit'])
        reads.append(read); names[step.node]=name; seen[step.node]=step
    for i,(old,g,ps) in enumerate(authenticated):
        if op(si.raw[tuple(old['source_step']['node'])]) == 'FW_multiref':
            result.append(old); retained.append(old); continue
        if len(ps)<=1: raise ValueError('post-transpose actual TP>1 source family required')
        globals_ = _view.column._consumers(si,[g])
        locals_ = _view.column._consumers(pi,ps)
        kinds={op(c) for c in locals_}
        if len(globals_)!=1 or len(locals_)!=len(ps) or len(kinds)!=1:
            raise ValueError('post-transpose complete unmixed original consumer cover required')
        kind=next(iter(kinds)); global_step=None
        if kind=='FW_matmul' and op(globals_[0])=='FW_matmul':
            _census(si,pi,g,ps)
            result.append(old); deferred.append(old); continue
        if kind=='FW_transpose':
            global_step=_transpose(si,globals_[0],g)
            emit(si,'sm',global_step,i,old)
        elif kind!='AllGatherPrim' or op(globals_[0])!='FW_matmul':
            raise ValueError('post-transpose unsupported original mixed frontier')
        steps=[]
        for j,rank in enumerate(old['ranks']):
            cell=_one((c for c in locals_ if _same_typed(c.rank,rank)), 'post-transpose receiver missing/ambiguous')
            if kind=='FW_transpose':
                step=_transpose(pi,cell,ps[j])
                if not _same_typed(pi.raw[step.node]._output_irs[0].parent.tid,si.raw[global_step.node]._output_irs[0].parent.tid):
                    raise ValueError('post-transpose original SM/PM output parent mismatch')
            else: step,_=_boundary(pi,cell,ps,old['ranks'],j)
            emit(pi,'pm',step,i,old); steps.append(step)
        proof,fresh=backend._unit(old,g,global_step,ps,steps,names)
        gy=global_step.outputs[0] if global_step else g
        name=f'frontierPostTransposeUnitFacts_{gy.endpoint.tid}_{old["unit"]}_slot0'
        proofs.extend(s.replace(fresh['theorem'],name) for s in proof)
        row=dict(old); row.update(fresh)
        shape=list(steps[0].outputs[0].endpoint.shape)
        row.update(theorem=name,facts_theorem=name,source_output_slot=0,slot=0,
            pm_output_slots=[0 for _ in steps],input_refs=[list(p.endpoint.ref) for p in ps],
            input_frontier=old,predecessor_facts=old['facts_theorem'],frontier_index=i,
            dimensions=dict(D=old['dimensions']['D'],T=len(ps),**dict(zip(('B','S','H','C'),shape))),
            axes=[2,3] if kind=='FW_transpose' else None,output_gather_axis=fresh['gather_axis'],
            deferred_stage='after-post-transpose: original successors inventoried, values unproved')
        row.update(_census(si,pi,gy,[s.outputs[0] for s in steps]))
        units.append(row); result.append(row); consumed.append(i)
    text='\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, aggregate costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld','noncomputable section','set_option maxHeartbeats 500000',
        *proofs,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return text,dict(status='source-frontier-post-transpose-values-emitted-uncompiled',reads=reads,units=units,
        frontier_units=result,retained_units=retained,deferred_units=deferred,consumed_frontier_indices=consumed,
        lean_bytes=len(text.encode()),cost_scope='mixed post-transpose fragment only; excludes predecessors, frame and imports',
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
