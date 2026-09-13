"""Fresh sequence AllGather -> output-row linear source facts, UNCOMPILED.

Only complete supported consumer covers advance. Existing input-linear and skip
facts remain in order; no caller DTO, invented alias, output premise or new math.
Parent owns canonical assembly, aggregate budget and the kernel gate.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_input_linear_values as predecessor
from Verdict import runtime_frontier_sequence_alias_values as sequence
from Verdict import runtime_frontier_alias_exchange_values as source
from Verdict import runtime_frontier_layernorm_values as frontier
from Verdict import runtime_projection_values as projection
from Verdict import runtime_add_values as adds
from Verdict import runtime_middle_exchange_values as middle
from Verdict.runtime_embedding_position_units import _list
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import Role, _Index, _same_typed, op
from Verdict.runtime_schedule import build


def _linear(index, activation):
    cell = _one(sequence._consumers(index,[activation]),
                'gathered-linear complete unique original consumer required')
    node = source.residual._identity(index,cell)
    signature = getattr(getattr(cell,'ir',None),'signature',None)
    if type(signature) is not str or signature != 'torch.nn.functional.linear':
        raise ValueError('gathered-linear original function must be torch.nn.functional.linear')
    if (op(cell) != 'FW_linear' or len(cell.inputs) != 2 or len(cell.outputs) != 1
            or len(cell._input_irs) != 2 or len(cell._output_irs) != 1
            or any(node in getattr(index.view,k,{}) for k in ('collective_scopes','chunk_scopes','wred_scopes'))
            or set(cell.kwargs)-{'bias','__consts'} or cell.kwargs.get('bias') is not None
            or not _same_typed(cell.kwargs.get('__consts',[]),[])):
        raise ValueError('gathered-linear original op/arity/scope/kwargs mismatch')
    source._raw(cell._input_irs[0]); source._raw(cell._output_irs[0])
    predecessor._matrix(cell._input_irs[1])
    source._edge(index,activation,cell._input_irs[0])
    ref = tuple(cell.inputs[1]); parent = cell._input_irs[1].parent.tid
    # Every occurrence is gated before the canonical binder or Port conversion.
    for other in index.raw.values():
        if ref not in map(tuple,other.inputs): continue
        source.residual._identity(index,other)
        irs = getattr(other,'_input_irs',None)
        if irs is None or len(irs) != len(other.inputs):
            raise ValueError('gathered-linear complete weight occurrence metadata required')
        for r,ir in zip(other.inputs,irs,strict=True):
            if tuple(r) != ref: continue
            predecessor._matrix(ir)
            if not _same_typed(ir.parent.tid,parent):
                raise ValueError('gathered-linear original weight occurrence parent mismatch')
    step = projection._linear(index,activation)
    if any(p.endpoint.ref[:3] != tuple(node)[:3] for p in (step.inputs[0],*step.outputs)):
        raise ValueError('gathered-linear original activation/output owner mismatch')
    return step


def _producer(index,ref):
    cell = index.raw[tuple(index.writers[tuple(ref)])]
    source.residual._identity(index,cell)
    return _one((p for p in source._ports(index,cell,'outputs') if p.endpoint.ref == tuple(ref)),
                'gathered-linear original producer missing/ambiguous')


def _descriptor(index,descriptor,ranks):
    """Rebuild complete old boundaries, including mixed-rank linear/RS IR."""
    cell = index.raw[tuple(descriptor['node'])]
    source.residual._identity(index,cell)
    if op(cell) == 'FW_multiref':
        ins = source._ports(index,cell,'inputs'); source._ports(index,cell,'outputs')
        if len(ins) != 1: raise ValueError('gathered-linear predecessor alias arity')
        source._edge(index,ins[0],cell._input_irs[0])
        step = projection.post._next(index,ins[0])
    elif op(cell) == 'FW_linear':
        # Previous global input-column linear has full weight and contraction.
        step = _linear(index,_producer(index,cell.inputs[0]))
    elif op(cell) == 'ReduceScatterPrim':
        ports = [_producer(index,r) for r in cell.inputs]
        # Validate each real partial linear with the existing column adapter.
        for j,p in enumerate(ports):
            partial = index.raw[p.endpoint.writer]
            predecessor._linear(index,_producer(index,partial.inputs[0]),(j,len(ranks)))
        step,_ = predecessor._scatter(index,cell,ports,ranks,ranks.index(cell.rank))
    elif op(cell) == 'AllToAllPrim':
        ports = [_producer(index,r) for r in cell.inputs]
        step,_ = predecessor.exchange._boundary(index,cell,ports,ranks,ranks.index(cell.rank))
    else:
        raise ValueError('gathered-linear unsupported predecessor descriptor')
    if not _same_typed(asdict(step),descriptor):
        raise ValueError('gathered-linear complete original predecessor descriptor mismatch')
    return step


def _frontiers(si,pi,closed,owners):
    frontier._cover(closed,owners)
    rows = closed['frontier_units']; units = closed['units']
    if (not _same_typed([r['frontier_index'] for r in units],closed['consumed_frontier_indices'])
            or any(not _same_typed(rows[r['frontier_index']],r) for r in units)
            or [r['unit'] for r in rows] != sorted(r['unit'] for r in rows)):
        raise ValueError('gathered-linear complete ordered input-linear boundary required')
    for retained in closed['retained_units']:
        if not any(_same_typed(retained,r) for r in rows):
            raise ValueError('gathered-linear original retained frontier omitted')
    authenticated = []; groups = {}; retained = []
    for old in rows:
        g = frontier._output(si,old['source_step'],old['sm_output_ref'])
        ps = [frontier._output(pi,s,r) for s,r in zip(old['local_steps'],old['pm_output_refs'],strict=True)]
        global_ = _descriptor(si,old['source_step'],old['ranks'])
        locals_ = [_descriptor(pi,s,old['ranks']) for s in old['local_steps']]
        middle._contract(old,g,ps)
        B,S,H = old['local_shape']; u = old['unit']; slot = old['source_output_slot']
        if (not _same_typed(old['dimensions'],dict(D=len(owners),T=len(ps),B=B,S=S,H=H))
                or type(slot) is not int or not 0 <= slot < len(global_.outputs)
                or not _same_typed(global_.outputs[slot],g)
                or ('slot' in old and not _same_typed(old['slot'],slot))
                or not _same_typed(old['sm_output_tid'],g.endpoint.tid)
                or not _same_typed(old['pm_output_tids'],[p.endpoint.tid for p in ps])):
            raise ValueError('gathered-linear strong predecessor dimensions/slot mismatch')
        parent = source._original(si,g).parent.tid
        if any(not _same_typed(source._original(pi,p).parent.tid,parent) for p in ps):
            raise ValueError('gathered-linear predecessor SM/PM output parent mismatch')
        # Recover original alias slots through consumed linear rows as well as Q.
        origin = global_; original_slot = slot
        if global_.op == 'FW_linear':
            port = global_.inputs[0]; cell = si.raw[port.endpoint.writer]
            origin_ports = source._ports(si,cell,'outputs')
            original_slot = _one((j for j,p in enumerate(origin_ports) if p == port),'gathered-linear original alias slot')
            origin = _descriptor(si,asdict(projection.post._next(si,_producer(si,cell.inputs[0]))),old['ranks'])
            if (not _same_typed(old['predecessor_source_output_slot'],original_slot)
                    or any(s.op != 'ReduceScatterPrim' or not _same_typed(s.inputs,locals_[0].inputs) for s in locals_)):
                raise ValueError('gathered-linear original previous slot/complete partial cover mismatch')
            partials = [predecessor._linear(pi,_producer(pi,pi.raw[p.endpoint.writer].inputs[0]),(j,len(ps)))
                        for j,p in enumerate(locals_[0].inputs)]
            if not _same_typed([asdict(s) for s in partials],old['partial_steps']):
                raise ValueError('gathered-linear complete previous partial descriptors mismatch')
        if all([op(c) for c in sequence._consumers(si,[p])] == ['FW_linear'] for p in origin.outputs):
            slots,count = groups.setdefault((origin.node,u),([],len(origin.outputs)))
            slots.append(original_slot)
        kinds = [[op(c) for c in sequence._consumers(si,[g])],
                 *[[op(c) for c in sequence._consumers(pi,[p])] for p in ps]]
        if global_.op != 'FW_linear' and (all(k == [] for k in kinds) or all(k == ['FW_add'] for k in kinds)):
            retained.append(old)
        authenticated.append((old,g,ps,kinds))
    if any(not _same_typed(slots,list(range(count))) for slots,count in groups.values()):
        raise ValueError('gathered-linear complete ordered original projection slots required')
    if not _same_typed(retained,closed['retained_units']):
        raise ValueError('gathered-linear predecessor skip classification mismatch')
    return authenticated


def _unit(old,global_,locals_,gathers,parameter,names,spec_count):
    D,T,B,S,I = (old['dimensions'][k] for k in ('D','T','B','S','H'))
    u = old['unit']; O = parameter['pm_shape'][0]
    g = global_.outputs[0]; ps = [s.outputs[0] for s in locals_]
    name = f'frontierGatheredLinearUnitFacts_{g.endpoint.tid}_{u}'
    row = dict(theorem=name,facts_theorem=name,predecessor=old['facts_theorem'],predecessor_facts=old['facts_theorem'],
        unit=u,ranks=old['ranks'],positions=old['positions'],layout='sharded',gather_axis=2,
        global_shape=list(g.endpoint.shape),local_shape=list(ps[0].endpoint.shape),
        dimensions=dict(D=D,T=T,B=B,S=S*T,H=O),
        sm_output_tid=g.endpoint.tid,sm_output_ref=list(g.endpoint.ref),pm_output_tids=[p.endpoint.tid for p in ps],
        pm_output_refs=[list(p.endpoint.ref) for p in ps],source_step=asdict(global_),local_steps=[asdict(s) for s in locals_],
        gather_steps=[asdict(s) for s in gathers],parameters=[parameter],source_output_slot=0,
        predecessor_source_output_slot=old['source_output_slot'])
    middle._contract(row,g,ps)
    gx = global_.inputs[0].endpoint.tid; w = parameter['sm_tid']; out = g.endpoint.tid
    ws = _list(f'q {tid}' for tid in parameter['pm_tids']); ys = _list(f'q {p.endpoint.tid}' for p in ps)
    shared = f'(chunkPrimDimN 0 {D} {u} (t {gx}))'
    i = parameter['spec_index']; rel = 'hrels'+'.2'*i+('.1' if i < spec_count-1 else '')
    proof = [*source._facts_header(name,row),f'  have predecessor := {old["facts_theorem"]} s p t q hs hp hvalues',
        '  have hrels := initialParameterRelations_of_values t q (initialParameterValues_final s p t q hs hp hvalues)',
        f'  have weightRel : RelationCompiler.ShardedRel (t {w}) {ws} 0 {parameter["sm_shape"]} {parameter["pm_shape"]} := {rel}']
    for j,(gather,local) in enumerate(zip(gathers,locals_,strict=True)):
        proof += [f'  have gathered{j} : q {gather.outputs[0].endpoint.tid} = {shared} :=',
            f'    ({names[gather.node]} p q hp).trans predecessor.2.2.symm',
            f'  have local{j} : q {ps[j].endpoint.tid} = fw_linear {shared} (q {parameter["pm_tids"][j]}) := by',
            f'    rw [{names[local.node]} p q hp, gathered{j}]']
    pairs = 'List.Forall₂.nil'
    for j in reversed(range(T)): pairs = f'List.Forall₂.cons local{j} ({pairs})'
    proof += [f'  have localReads : List.Forall₂ (fun w y => y = fw_linear {shared} w) {ws} {ys} :=',f'    {pairs}',
        f'  exact TrainVerify.Denote.source_linear_weight_unit_output_reconstruct {D} {T} {B} {S*T} {I} {O} {u}',
        f'    (t {gx}) {shared} (t {w}) (t {out}) {ws} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        '    predecessor.1 rfl weightRel.shard_shapes rfl weightRel.full_value',
        f'    ({names[global_.node]} s t hs) localReads',f'#print axioms {name}']
    return proof,row


def render(sm,pm,lineages,validation,bound,execution_order):
    """Exactly one fresh predecessor call using the SAME six public objects."""
    try:
        _,closed = predecessor.render(sm,pm,lineages,validation,bound,execution_order)
        return _render(sm,pm,lineages,validation,bound,execution_order,closed)
    except (KeyError,TypeError,AttributeError,IndexError,StopIteration,OverflowError) as exc:
        raise ValueError(f'malformed gathered-linear original source: {exc}') from exc


def _render(sm,pm,lineages,validation,bound,order,closed):
    if not _same_typed(order,dict(sm=build(sm),pm=build(pm))):
        raise ValueError('gathered-linear complete typed execution/inverse order mismatch')
    si,pi = (_Index(v,raw) for v,raw in zip((sm,pm),validation._inputs[:2],strict=True))
    specs = adds._bound(lineages,bound)
    if (not _same_typed([r['lineage'] for r in bound['relations']],[asdict(l) for l in lineages if l.role == Role.PARAMETER])
            or any(not _same_typed([u['unit'] for u in r['units']],[u['unit'] for u in r['lineage']['units']]) for r in bound['relations'])):
        raise ValueError('gathered-linear exact canonical parameter specification order required')
    authenticated = _frontiers(si,pi,closed,validation._inputs[3]['config']['units'])
    proofs,reads,units,result,retained,deferred,consumed = [],[],[],[],[],[],[]; seen = {}; names = {}
    def emit(view,label,step,**metadata):
        if step.node in seen:
            if label != 'sm' or not _same_typed(step,seen[step.node]):
                raise ValueError('gathered-linear duplicate/cross-DP original source operation')
            return
        proof,row = projection._read(view,label,step,order[label])
        name = row['theorem'].replace('projection','frontierGathered')
        proofs.extend(s.replace(row['theorem'],name) for s in proof)
        row.update(theorem=name,**metadata); reads.append(row); names[step.node] = name; seen[step.node] = step
    for i,(old,g,ps,kinds) in enumerate(authenticated):
        cells = sequence._consumers(pi,ps)
        selected = old['gather_axis'] == 1 and kinds[0] == ['FW_linear'] and any('AllGatherPrim' in k for k in kinds[1:])
        if not selected:
            result.append(old)
            if any(_same_typed(old,r) for r in closed['retained_units']): retained.append(old)
            else: deferred.append(dict(old,reason='next FW_view frontier deferred' if all(k == ['FW_view'] for k in kinds)
                                       else 'unsupported complete forward consumer frontier deferred',observed_consumer_ops=kinds))
            continue
        T = len(ps)
        if T <= 1 or len(cells) != T or any(op(c) != 'AllGatherPrim' for c in cells):
            raise ValueError('gathered-linear complete multi-peer AllGather receiver cover required')
        global_ = _linear(si,g); gathers = []; coverage = []
        for j,rank in enumerate(old['ranks']):
            cell = _one((c for c in cells if _same_typed(c.rank,rank)),'gathered-linear original receiver missing/ambiguous')
            sequence._gather_consumer(pi,cell,[tuple(r) for r in cell.inputs])
            if any(cell.node in getattr(pm,k,{}) for k in ('chunk_scopes','wred_scopes')):
                raise ValueError('gathered-linear conflicting gather scope')
            step,meta = projection._gather(pi,cell,tuple(ps),tuple(old['ranks']),j)
            gathers.append(step); coverage.append(dict(meta,producer_metadata='all-peers',input_parent_identity=meta['input_metadata']))
        locals_ = [_linear(pi,s.outputs[0]) for s in gathers]
        for position,field in ((0,'_output_irs'),(1,'_input_irs')):
            parent = getattr(si.raw[global_.node],field)[position].parent.tid
            if any(not _same_typed(getattr(pi.raw[s.node],field)[position].parent.tid,parent) for s in locals_):
                raise ValueError('gathered-linear SM/PM original output/weight parent mismatch')
        parameter = projection._parameter(si,pi,lineages,specs,global_,locals_,old,sharded=True)
        if parameter['kind'] != 'sharded': raise ValueError('gathered-linear typed row-sharded parameter required')
        emit(sm,'sm',global_,frontier_index=i)
        for s,meta in zip(gathers,coverage,strict=True): emit(pm,'pm',s,frontier_index=i,unit=old['unit'],**meta)
        for s in locals_: emit(pm,'pm',s,frontier_index=i,unit=old['unit'])
        proof,row = _unit(old,global_,locals_,gathers,parameter,names,len(specs))
        # Census only: Q can next feed AA(2,1), not necessarily a direct view.
        # These operations are neither read nor consumed in this fragment.
        outgoing = [sequence._consumers(si,global_.outputs),
                    *[sequence._consumers(pi,s.outputs) for s in locals_]]
        row.update(observed_consumer_ops=[[op(c) for c in cs] for cs in outgoing],
                   sm_consumers=[list(c.node) for c in outgoing[0]],
                   pm_consumers=[list(c.node) for c in sequence._consumers(pi,[s.outputs[0] for s in locals_])])
        row['frontier_index'] = i; proofs.extend(proof); units.append(row); result.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, canonical frame, aggregate costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld','noncomputable section','set_option maxHeartbeats 500000',
        *proofs,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return text,dict(status='source-frontier-gathered-linear-values-emitted-uncompiled',reads=reads,units=units,
        frontier_units=result,retained_units=retained,deferred_units=deferred,consumed_frontier_indices=consumed,
        lean_bytes=len(text.encode()),cost_scope='sequence AllGather/output-row linear fragment only; excludes predecessors, frame and imports',
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
