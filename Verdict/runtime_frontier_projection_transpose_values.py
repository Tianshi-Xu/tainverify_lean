"""Original projection transpose(1,2) values, UNCOMPILED.

Only the new transpose fragment is emitted. Parent owns original capture,
imports, assembly, aggregate costs and kernel closure. No successor value proof.
"""
from Verdict import runtime_frontier_head_exchange_values as predecessor
from Verdict import runtime_transpose_values as transpose
from Verdict import runtime_query_transpose_values as query
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build
from Verdict.runtime_embedding_units import _one


_view = predecessor.predecessor


def render(sm, pm, lineages, validation, bound, execution_order):
    """Exactly one fresh predecessor call with precisely the SAME six inputs."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError, ZeroDivisionError) as exc:
        raise ValueError(f'malformed projection-transpose original source: {exc}') from exc


def _frontiers(sm, pm, si, pi, lineages, validation, bound, order, closed):
    # AA OUTPUT DTOs are not FW-view outputs. Peel exactly one stage, then run
    # the existing raw-bound view/history/fork-inventory and AA read constructors.
    # This is not a second predecessor render and introduces no proof premises.
    rows = closed['frontier_units']
    views = [r if op(si.raw[tuple(r['source_step']['node'])]) == 'FW_multiref'
             else r['input_frontier'] for r in rows]
    selected = [i for i,r in enumerate(views) if op(si.raw[tuple(r['source_step']['node'])]) == 'FW_view']
    prior = dict(frontier_units=views, units=[views[i] for i in selected],
        consumed_frontier_indices=selected, retained_units=[r for i,r in enumerate(views) if i not in selected],
        deferred_units=[])
    _, expected = predecessor._render(sm, pm, lineages, validation, bound, order, prior)
    if not _same_typed(closed, expected):
        raise ValueError('projection-transpose complete original head/view/history/frontier mismatch')
    result = []
    for old in rows:
        if op(si.raw[tuple(old['source_step']['node'])]) == 'FW_multiref':
            g = _view.frontier._output(si, old['source_step'], old['sm_output_ref'])
            ps = [_view.frontier._output(pi, s, r) for s,r in zip(old['local_steps'],old['pm_output_refs'],strict=True)]
        else:
            g = predecessor.middle._output(si, old['source_step'])
            ps = [predecessor.middle._output(pi, s) for s in old['local_steps']]
        result.append((old,g,ps))
    return result


def _transpose(index, cell, producer):
    node = _view.source.residual._identity(index, cell)
    signature = getattr(getattr(cell, 'ir', None), 'signature', None)
    if type(signature) is not str or signature != 'torch.transpose':
        raise ValueError('projection-transpose original function must be torch.transpose')
    if (op(cell) != 'FW_transpose' or len(cell.inputs) != 1 or len(cell.outputs) != 1
            or cell._input_irs is None or len(cell._input_irs) != 1
            or cell._output_irs is None or len(cell._output_irs) != 1
            or any(node in getattr(index.view,k,{}) for k in ('collective_scopes','chunk_scopes','wred_scopes'))):
        raise ValueError('projection-transpose original arity/metadata/scope mismatch')
    kwargs=dict(cell.kwargs); consts=kwargs.pop('__consts',[])
    if not _same_typed(kwargs,dict(dim0=1,dim1=2)) or not _same_typed(consts,[]):
        raise ValueError('projection-transpose original typed axes/kwargs mismatch')
    for ref,ir in ((cell.inputs[0],cell._input_irs[0]),(cell.outputs[0],cell._output_irs[0])):
        _view._raw(ir,4)
        if not _same_typed(ir.tid,ref[3]) or not _same_typed(tuple(ir.valmap),(0,1)):
            raise ValueError('projection-transpose original tensor identity/full value mismatch')
    _view._edge(index,producer,cell._input_irs[0])
    return transpose._transpose(index,cell,producer)


def _read(index, label, step, order):
    # Read entry points also recheck live function and raw metadata, not only
    # normalized opcode/params. No casts precede this stage-local guard.
    actual = _transpose(index,index.raw[step.node],step.inputs[0])
    if not _same_typed(actual,step) or not _same_typed(order,build(index.view)):
        raise ValueError('projection-transpose read original step/schedule mismatch')
    return transpose._read(index.view,label,actual,order)


def _producer(index, ref):
    cell = index.raw[tuple(index.writers[tuple(ref)])]
    _view.source.residual._identity(index,cell)
    slot = _one((j for j,r in enumerate(cell.outputs) if _same_typed(tuple(r),tuple(ref))),
        'projection-transpose successor producer slot missing/ambiguous')
    if cell._output_irs is None or len(cell._output_irs) != len(cell.outputs):
        raise ValueError('projection-transpose successor complete producer metadata required')
    ir = cell._output_irs[slot]
    _view._raw(ir,len(index.endpoint(ref).shape))
    if not _same_typed(ir.tid,ref[3]):
        raise ValueError('projection-transpose successor original producer tensor identity mismatch')
    return _view.projection.post._port(index,ref,ir)


def _successor(index, cell):
    """Source-only edge inventory: no successor read or value theorem emitted."""
    node = _view.source.residual._identity(index,cell)
    inputs = [_producer(index,r) for r in cell.inputs]
    irs, outs = cell._input_irs, cell._output_irs
    if (not inputs or irs is None or outs is None or len(outs) != len(cell.outputs)
            or not outs or any(len(p.endpoint.shape) != 4 for p in inputs)):
        raise ValueError('projection-transpose successor complete rank-four metadata required')
    expected = inputs; coverage = 'present'
    if op(cell) == 'AllGatherPrim':
        ranks = tuple(p.endpoint.ref[1] for p in inputs)
        if len(set(ranks)) != len(ranks) or cell.rank not in ranks:
            raise ValueError('projection-transpose successor ordered distinct gather peers required')
        j = ranks.index(cell.rank); axis = cell.kwargs.get('dim')
        kw = dict(cell.kwargs); rawranks = kw.pop('ranks',None); consts = kw.pop('__consts',[])
        scope = index.view.collective_scopes[node]
        writer = _one((w for w in index.view._collective_source['writers'] if _same_typed(
            (w['ref']['world'],w['ref']['runtime_rank'],w['ref']['microbatch'],w['ref']['source_cid'],w['source_irname']),tuple(node))),
            'projection-transpose successor gather writer missing/ambiguous')
        if (type(axis) is not int or not 0 <= axis < 4 or not _same_typed(kw,dict(dim=axis))
                or not _same_typed(consts,[]) or type(rawranks) not in (list,tuple)
                or not _same_typed(tuple(rawranks),ranks) or scope.op != op(cell)
                or not scope.source_writer or scope.source_writer != writer['export_id']
                or not _same_typed(scope.ranks,ranks) or not _same_typed(scope.local_index,j)
                or not _same_typed(scope.params,(axis,))
                or not _same_typed(scope.input_tids,tuple(p.endpoint.tid for p in inputs))
                or not _same_typed(scope.input_shape,inputs[j].endpoint.shape)
                or len(outs) != 1
                or not _same_typed(scope.output_tid,index.endpoint(cell.outputs[0]).tid)
                or any(node in getattr(index.view,k,{}) for k in ('chunk_scopes','wred_scopes'))):
            raise ValueError('projection-transpose successor original gather scope/axis/peers mismatch')
        first=inputs[0]; parent=predecessor._original(index,first).parent.tid; end=0
        for rank,p in zip(ranks,inputs,strict=True):
            if (p.endpoint.ref[:3] != (node[0],rank,node[2]) or p.parent_shape != first.parent_shape
                    or p.parent_name != first.parent_name or p.endpoint.shape != first.endpoint.shape
                    or p.value_part != (0,1) or p.bounds[axis][0] != end
                    or any(b != (0,d) for k,(b,d) in enumerate(zip(p.bounds,p.parent_shape,strict=True)) if k != axis)
                    or not _same_typed(predecessor._original(index,p).parent.tid,parent)):
                raise ValueError('projection-transpose successor complete gather partition/parent mismatch')
            end=p.bounds[axis][1]
        if end != first.parent_shape[axis] or len(irs) not in (1,len(inputs)):
            raise ValueError('projection-transpose successor complete gather cover/metadata required')
        expected = [inputs[j]] if len(irs)==1 else inputs
        coverage = 'local-only' if len(irs)==1 and len(inputs)>1 else 'all-peers'
        _view._raw(outs[0],4)
        y = _view.projection.post._port(index,cell.outputs[0],outs[0])
        if (not _same_typed(outs[0].parent.tid,parent) or y.parent_shape != first.parent_shape
                or y.parent_name != first.parent_name or y.bounds != tuple((0,d) for d in first.parent_shape)
                or y.endpoint.shape != first.parent_shape or y.value_part != (0,1)):
            raise ValueError('projection-transpose successor gather output metadata mismatch')
    elif (op(cell) not in ('FW_matmul','FW_transpose')
            or node in getattr(index.view,'collective_scopes',{})):
        raise ValueError('projection-transpose unsupported original successor')
    if len(irs) != len(expected):
        raise ValueError('projection-transpose successor complete input metadata required')
    for p,ir in zip(expected,irs,strict=True): _view._edge(index,p,ir)
    for ref,ir in zip(cell.outputs,outs,strict=True):
        _view._raw(ir,len(index.endpoint(ref).shape))
        y = _view.projection.post._port(index,ref,ir)
        if (not _same_typed(ir.tid,ref[3]) or y.endpoint.writer != tuple(node)
                or y.endpoint.ref[:3] != tuple(node)[:3]):
            raise ValueError('projection-transpose successor output identity mismatch')
    return dict(node=list(node),op=op(cell),source_kwargs=dict(cell.kwargs),
        source_signature=getattr(getattr(cell,'ir',None),'signature',None),
        source_inputs=[list(r) for r in cell.inputs],source_outputs=[list(r) for r in cell.outputs],
        input_shapes=[list(p.endpoint.shape) for p in inputs],output_shapes=[list(ir.shape) for ir in outs],
        input_metadata=coverage,producer_metadata='all-peers' if op(cell)=='AllGatherPrim' else 'all-inputs',
        input_parent_identity=coverage,output_metadata='present',value_proved=False)


def _census(si,pi,g,ps):
    groups = [_view.column._consumers(si,[g]),*[_view.column._consumers(pi,[p]) for p in ps]]
    peers = _view.column._consumers(pi,ps)
    return dict(observed_consumer_ops=[[op(c) for c in cells] for cells in groups],
        sm_consumers=[list(c.node) for c in groups[0]],pm_consumers=[list(c.node) for c in peers],
        downstream_consumers=[*[_successor(si,c) for c in groups[0]],*[_successor(pi,c) for c in peers]])


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order, dict(sm=build(sm), pm=build(pm))):
        raise ValueError('projection-transpose complete typed execution/inverse order mismatch')
    si, pi = (_Index(v,raw) for v,raw in zip((sm,pm),validation._inputs[:2],strict=True))
    authenticated = _frontiers(sm,pm,si,pi,lineages,validation,bound,order,closed)
    proofs, reads, units, result, retained, consumed = [], [], [], [], [], []
    names = {}; seen = {}
    for i,(old,g,ps) in enumerate(authenticated):
        if op(si.raw[tuple(old['source_step']['node'])]) == 'FW_multiref':
            result.append(old); retained.append(old); continue
        global_ = _transpose(si,_view.view._consumer(si,g),g)
        locals_ = [_transpose(pi,_view.view._consumer(pi,p),p) for p in ps]
        parent = si.raw[global_.node]._output_irs[0].parent.tid
        if any(not _same_typed(pi.raw[s.node]._output_irs[0].parent.tid,parent) for s in locals_):
            raise ValueError('projection-transpose original SM/PM output parent mismatch')
        for index,label,step in [(si,'sm',global_),*((pi,'pm',s) for s in locals_)]:
            if step.node in seen:
                if label != 'sm' or not _same_typed(seen[step.node],step):
                    raise ValueError('projection-transpose duplicate/cross-unit original operation')
                continue
            proof,read = _read(index,label,step,order[label])
            name = read['theorem'].replace('transposeRead_','frontierProjectionTransposeRead_')
            proofs.extend(s.replace(read['theorem'],name) for s in proof)
            read.update(theorem=name,frontier_index=i,unit=old['unit'])
            reads.append(read); names[step.node]=name; seen[step.node]=step
        backend = query if old['gather_axis'] == 2 else transpose
        proof,fresh = backend._unit(old,global_,locals_,names)
        name = f'frontierProjectionTransposeUnitFacts_{global_.outputs[0].endpoint.tid}_{old["unit"]}_slot0'
        proofs.extend(s.replace(fresh['theorem'],name) for s in proof)
        row = dict(old); row.update(fresh)
        shape = list(locals_[0].outputs[0].endpoint.shape)
        row.update(theorem=name,facts_theorem=name,source_output_slot=0,slot=0,
            family=global_.op,input_refs=[list(s.inputs[0].endpoint.ref) for s in locals_],
            pm_output_slots=[0 for _ in locals_],input_frontier=old,predecessor_facts=old['facts_theorem'],
            dimensions=dict(D=old['dimensions']['D'],T=len(ps),**dict(zip(('B','S','H','C'),shape))),
            output_gather_axis=fresh['gather_axis'],frontier_index=i,
            deferred_stage='after-projection-transpose: original successors inventoried, values unproved')
        row.update(_census(si,pi,global_.outputs[0],[s.outputs[0] for s in locals_]))
        units.append(row); result.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, aggregate costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld','noncomputable section','set_option maxHeartbeats 500000',
        *proofs,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return text,dict(status='source-frontier-projection-transpose-values-emitted-uncompiled',reads=reads,units=units,
        frontier_units=result,retained_units=retained,deferred_units=[],consumed_frontier_indices=consumed,
        lean_bytes=len(text.encode()),cost_scope='projection transpose fragment only; excludes predecessors, frame and imports',
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
