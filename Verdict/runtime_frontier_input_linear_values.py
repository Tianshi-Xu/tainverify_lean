"""Fresh hidden K/V -> input-column linear -> original ReduceScatter facts.

UNCOMPILED candidates only. Q AllGather and skip facts remain unchanged. No
caller receipt, output equation, parameter metadata repair, or new mathematics.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_projection_exchange_values as predecessor
from Verdict import runtime_frontier_alias_exchange_values as source
from Verdict import runtime_frontier_layernorm_values as frontier
from Verdict import runtime_projection_values as projection
from Verdict import runtime_layernorm_values as norm
from Verdict import runtime_add_values as adds
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_output_projection_exchange_values as exchange
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import Role, _Index, _same_typed, op
from Verdict.runtime_schedule import build
from Verdict.runtime_world import _ordinary


def _matrix(ir):
    if (ir is None or type(ir.tid) is not int or type(ir.parent.tid) is not int
            or len(ir.shape) != 2 or len(ir.parent.shape) != 2
            or any(type(n) is not int or n <= 0 for n in (*ir.shape, *ir.parent.shape))
            or len(ir.indmap) != 2
            or any(len(b) != 2 or any(type(n) is not int for n in b) for b in ir.indmap)
            or len(ir.valmap) != 2 or any(type(n) is not int for n in ir.valmap)
            or ir.is_param() is not True or ir.is_grad() is not False):
        raise ValueError('input-linear typed original non-gradient parameter matrix required')


def _linear(index, activation, contribution):
    cells = predecessor.predecessor._consumers(index, [activation])
    cell = _one(cells, 'input-linear complete unique original consumer required')
    node = source.residual._identity(index, cell)
    if (op(cell) != 'FW_linear' or len(cell.inputs) != 2 or len(cell.outputs) != 1
            or len(cell._input_irs) != 2 or len(cell._output_irs) != 1
            or any(node in getattr(index.view, k, {}) for k in ('collective_scopes','chunk_scopes','wred_scopes'))
            or set(cell.kwargs) - {'bias','__consts'} or cell.kwargs.get('bias') is not None
            or not _same_typed(cell.kwargs.get('__consts', []), [])):
        raise ValueError('input-linear original op/arity/ordinary scope/kwargs mismatch')
    params, status = _ordinary(index.view, node, projection.c._get_node_params)
    if status is not None or not _same_typed(params, []):
        raise ValueError('input-linear original empty parameters required')
    source._raw(cell._input_irs[0]); source._raw(cell._output_irs[0]); _matrix(cell._input_irs[1])
    source._edge(index, activation, cell._input_irs[0])
    # Gate EVERY occurrence before norm._binding or Port conversion.
    ref = tuple(cell.inputs[1]); parent = cell._input_irs[1].parent.tid
    for other in index.raw.values():
        if ref not in map(tuple, other.inputs):
            continue
        source.residual._identity(index, other)
        irs = getattr(other, '_input_irs', None)
        if irs is None or len(irs) != len(other.inputs):
            raise ValueError('input-linear complete weight occurrence metadata required')
        for r, ir in zip(other.inputs, irs, strict=True):
            if tuple(r) == ref:
                _matrix(ir)
                if not _same_typed(ir.parent.tid, parent):
                    raise ValueError('input-linear original weight occurrence parent mismatch')
    ins = tuple(projection.post._port(index, r, ir) for r,ir in zip(cell.inputs,cell._input_irs,strict=True))
    outs = source._ports(index, cell, 'outputs')
    x,w = ins; y, = outs
    if (not _same_typed(x, activation) or any(p.endpoint.ref[:2] != tuple(node)[:2] for p in (*ins,*outs))
            or x.value_part != (0,1) or w.value_part != (0,1) or y.value_part != contribution
            or x.parent_shape[-1] != w.parent_shape[1] or x.bounds[-1] != w.bounds[1]
            or w.bounds[0] != (0,w.parent_shape[0])
            or y.parent_shape != (*x.parent_shape[:2],w.parent_shape[0])
            or y.bounds != (*x.bounds[:2],w.bounds[0])
            or x.endpoint.shape[-1] != w.endpoint.shape[1]):
        raise ValueError('input-linear original contraction/column/output shape/value mismatch')
    return routes.Step(tuple(node), 'FW_linear', ins, outs)


def _parameter(si, pi, lineages, specs, global_, locals_, old):
    full = global_.inputs[1]; ports = [s.inputs[1] for s in locals_]
    D,T,u = old['dimensions']['D'],len(ports),old['unit']
    lineage = _one((l for l in lineages if l.role == Role.PARAMETER and _same_typed(l.target,full.endpoint)),
        'input-linear original canonical PARAMETER lineage required')
    i,row,bu = _one(((i,r,b) for i,(r,b) in enumerate(specs) if _same_typed(r['lineage'],asdict(lineage))
        and _same_typed(b['unit'],u)), 'input-linear exact canonical weight/unit required')
    pu = lineage.units[u]; O,IT = full.parent_shape; I = ports[0].endpoint.shape[1]
    if (T <= 1 or IT != I*T or full.bounds != ((0,O),(0,IT))
            or not _same_typed([a.unit for a in lineage.units],list(range(D)))
            or pu.reconstruction != 'tp-axis-gather:1' or pu.positions != ()
            or not _same_typed([p.endpoint for p in pu.pieces],[p.endpoint for p in ports])
            or not _same_typed([p.endpoint.ref[1] for p in ports],old['ranks'])):
        raise ValueError('input-linear canonical ordered input-column weight partition required')
    parent = si.raw[global_.node]._input_irs[1].parent.tid
    for j,(piece,port,step) in enumerate(zip(pu.pieces,ports,locals_,strict=True)):
        if (port.parent_name != full.parent_name or port.parent_shape != full.parent_shape
                or port.bounds != ((0,O),(j*I,(j+1)*I)) or port.endpoint.shape != (O,I)
                or port.value_part != (0,1)
                or not _same_typed((piece.bounds,piece.value_part),(port.bounds,port.value_part))
                or not _same_typed(pi.raw[step.node]._input_irs[1].parent.tid,parent)):
            raise ValueError('input-linear SM/PM weight parent/column/ordered piece mismatch')
    goal = dict(kind='sharded',sm_tid=full.endpoint.tid,pm_tids=[p.endpoint.tid for p in ports],
        dim=1,sm_shape=[O,IT],pm_shape=[O,I])
    if not _same_typed(bu['initial_goal'],goal) or len(bu['bindings']) != T:
        raise ValueError('input-linear exact canonical input-column bound goal required')
    norm._binding(si,row['sm_binding'],full,full.endpoint.ref,'sm')
    for b,p in zip(bu['bindings'],ports,strict=True): norm._binding(pi,b,p,full.endpoint.ref,'pm')
    return dict(goal,role='weight',spec_index=i,sm_ref=list(full.endpoint.ref),pm_refs=[list(p.endpoint.ref) for p in ports])


def _consumers(index, ports):
    refs = {p.endpoint.ref for p in ports}; cells = []
    for node in index.view.nodes():
        actual = {tuple(index.view.source_tensor(t)) for t in index.view.node_inputs(node)}
        if not refs.intersection(actual): continue
        cell = index.raw[tuple(node)]; source.residual._identity(index,cell)
        if not op(cell).startswith('BW_'): cells.append(cell)
    return cells


def _scatter(index, cell, ports, ranks, j):
    node = source.residual._identity(index,cell); T = len(ranks)
    scope = _one((s for s in index.view.collective_scopes.values() if _same_typed(tuple(s.node),tuple(node))),
        'input-linear original ReduceScatter scope required')
    kw = dict(cell.kwargs); rawranks = kw.pop('ranks',None); consts = kw.pop('__consts',[])
    axis = kw.get('dim')
    if (op(cell) != 'ReduceScatterPrim' or type(axis) is not int or axis not in (1,2)
            or not _same_typed(kw,dict(dim=axis)) or not _same_typed(consts,[])
            or type(rawranks) not in (tuple,list) or not _same_typed(tuple(rawranks),tuple(ranks))
            or any(node in getattr(index.view,k,{}) for k in ('chunk_scopes','wred_scopes'))
            or scope.op != 'ReduceScatterPrim' or not _same_typed(scope.params,(axis,))
            or not _same_typed(scope.ranks,tuple(ranks)) or not _same_typed(scope.local_index,j)
            or not _same_typed(node.rank,ranks[j])
            or not _same_typed(scope.input_tids,tuple(p.endpoint.tid for p in ports))
            or not _same_typed(scope.input_shape,ports[j].endpoint.shape)
            or not _same_typed([tuple(r) for r in cell.inputs],[p.endpoint.ref for p in ports])):
        raise ValueError('input-linear original RS ordered contribution/scope/axis/group/local index mismatch')
    writer = _one((w for w in index.view._collective_source['writers'] if _same_typed(
        (w['ref']['world'],w['ref']['runtime_rank'],w['ref']['microbatch'],w['ref']['source_cid'],w['source_irname']),tuple(node))),
        'input-linear original RS writer required')
    if not scope.source_writer or scope.source_writer != writer['export_id']:
        raise ValueError('input-linear original RS source writer mismatch')
    first = ports[0]; parent = source._original(index,first).parent.tid
    for k,p in enumerate(ports):
        original = source._original(index,p)
        if (p.parent_shape != first.parent_shape or p.parent_name != first.parent_name
                or p.bounds != first.bounds or p.endpoint.shape != first.endpoint.shape
                or p.value_part != (k,T) or p.endpoint.ref[:3] != (node[0],ranks[k],node[2])
                or not _same_typed(original.parent.tid,parent)):
            raise ValueError('input-linear original ordered partial producer/parent mismatch')
    width,rem = divmod(first.endpoint.shape[axis],T)
    if rem or width <= 0 or first.bounds[axis] != (0,first.parent_shape[axis]):
        raise ValueError('input-linear RS nondivisible actual axis/shape')
    irs = getattr(cell,'_input_irs',None)
    if irs is None or len(irs) not in (1,T):
        raise ValueError('input-linear RS complete local-only or all-peer metadata required')
    expected = (ports[j],) if len(irs) == 1 else ports
    for p,ir in zip(expected,irs,strict=True): source._edge(index,p,ir)
    outs = source._ports(index,cell,'outputs')
    if len(outs) != 1: raise ValueError('input-linear RS single original output required')
    out, = outs; bounds = list(first.bounds); bounds[axis] = (j*width,(j+1)*width)
    if (out.parent_shape != first.parent_shape or out.parent_name != first.parent_name
            or out.bounds != tuple(bounds) or out.value_part != (0,1)
            or not _same_typed(cell._output_irs[0].parent.tid,parent)
            or not _same_typed(scope.output_tid,out.endpoint.tid)):
        raise ValueError('input-linear RS original output layout/parent/value mismatch')
    kind = 'local-only' if len(irs) == 1 and T > 1 else 'all-peers'
    return routes.Step(tuple(node),'ReduceScatterPrim',tuple(ports),outs,scope.source_writer,
        tuple(ranks),j,split_axis=axis,peers=tuple(zip(ranks,scope.input_tids))), dict(
        input_metadata=kind,output_metadata='present',producer_metadata='all-peers',input_parent_identity=kind)


def _read(view,label,step,order):
    if step.op == 'FW_linear':
        proof,row = projection._read(view,label,step,order)
        name = row['theorem'].replace('projectionLinear','frontierInputLinear')
        return [s.replace(row['theorem'],name) for s in proof],dict(row,theorem=name)
    nodes = view.nodes(); i = next(i for i,n in enumerate(nodes) if tuple(n) == step.node)
    k = order['execution_to_source'].index(i); ins = [p.endpoint.tid for p in step.inputs]
    out = step.outputs[0].endpoint.tid; a = step.split_axis; T = len(step.ranks)
    for source_index in order['execution_to_source'][k:]:
        if set(ins).intersection(t.tid for t in view.node_outputs(nodes[source_index])):
            raise ValueError('input-linear RS original operands written in selected/full BW suffix')
    name = f'frontierInputReduceScatterRead_pm_{out}'; requests = 'pmInputRequests'
    proof = [f'theorem {name} (s t : Store) (h : pmDenoteWithInputs s = some t) :',
        f'    t {out} = chunkPrimDimN {a} {T} {step.local_index} (tensorSum {_list(f"t {x}" for x in ins)}) := by',
        '  apply SourceReduceScatterRead.reduceScatter_value_of_split pmGraph pmScope pmPeers pmGraph.nodes',
        f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) pmNode_{i}',
        f'    {step.node[1]} {list(step.ranks)} {ins} {out} {a} s t rfl ?_ rfl ?_ h',
        '  · calc',f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
        '      _ = _ := rfl',f'  · change ∀ tid ∈ ({ins} : List Tid), ∀ row ∈ {requests}.drop {k}, tid ∉ row.1.outs',
        '    decide',f'#print axioms {name}']
    return proof,dict(theorem=name,world='pm',op=step.op,node=list(step.node),source_index=i,execution_index=k,
        input_tids=ins,output_tid=out,input_refs=[list(p.endpoint.ref) for p in step.inputs],
        output_refs=[list(p.endpoint.ref) for p in step.outputs],params=[a],request='group',
        source_kwargs=dict(view.node_kwargs(nodes[i])),source_step=asdict(step),
        operand_nonwrite_source_indices=order['execution_to_source'][k:])


def _unit(old,global_,locals_,scatters,parameter,names,spec_count):
    D,T,B,S,I = (old['dimensions'][k] for k in ('D','T','B','S','H'))
    u = old['unit']; O = parameter['sm_shape'][0]; a = scatters[0].split_axis
    g = global_.outputs[0]; ps = [s.outputs[0] for s in scatters]
    name = f'frontierInputLinearUnitFacts_{g.endpoint.tid}_{u}'
    row = dict(theorem=name,facts_theorem=name,predecessor=old['facts_theorem'],predecessor_facts=old['facts_theorem'],
        unit=u,ranks=old['ranks'],positions=old['positions'],layout='sharded',gather_axis=a,
        global_shape=list(g.endpoint.shape),local_shape=list(ps[0].endpoint.shape),
        dimensions=dict(D=D,T=T,B=B,S=ps[0].endpoint.shape[1],H=ps[0].endpoint.shape[2]),
        sm_output_tid=g.endpoint.tid,sm_output_ref=list(g.endpoint.ref),pm_output_tids=[p.endpoint.tid for p in ps],
        pm_output_refs=[list(p.endpoint.ref) for p in ps],source_step=asdict(global_),local_steps=[asdict(s) for s in scatters],
        partial_steps=[asdict(s) for s in locals_],parameters=[parameter],source_output_slot=0,
        predecessor_source_output_slot=old['source_output_slot'])
    middle._contract(row,g,ps)
    xs,ws,partials,ys = (_list(f'q {tid}' for tid in ids) for ids in (
        old['pm_output_tids'],parameter['pm_tids'],[s.outputs[0].endpoint.tid for s in locals_],row['pm_output_tids']))
    gx = global_.inputs[0].endpoint.tid; weight = parameter['sm_tid']; out = g.endpoint.tid
    i = parameter['spec_index']; rel = 'hrels'+'.2'*i+('.1' if i < spec_count-1 else '')
    proof = [*source._facts_header(name,row),f'  have predecessor := {old["facts_theorem"]} s p t q hs hp hvalues',
        '  have hrels := initialParameterRelations_of_values t q (initialParameterValues_final s p t q hs hp hvalues)',
        f'  have weightRel : RelationCompiler.ShardedRel (t {weight}) {ws} 1 {[O,I*T]} {[O,I]} := {rel}']
    for j,s in enumerate(locals_): proof += [f'  have local{j} := {names[s.node]} p q hp']
    pairs = 'List.Forall₂.nil'
    for j in reversed(range(T)): pairs = f'List.Forall₂.cons local{j} ({pairs})'
    proof += [f'  have localReads : List.Forall₂ (fun xy y => y = fw_linear xy.1 xy.2) ({xs}.zip {ws}) {partials} :=',
        f'    {pairs}',
        f'  have reduced := TrainVerify.Denote.source_linear_input_unit_output_reduce {D} {T} {B} {S} {I} {O} {u}',
        f'    (t {gx}) (t {weight}) (t {out}) {xs} {ws} {partials}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        '    predecessor.1 rfl rfl predecessor.2.1 weightRel.shard_shapes predecessor.2.2 weightRel.full_value',
        f'    ({names[global_.node]} s t hs) localReads',
        f'  have sumShape : (tensorSum {partials}).shape = {[B,S,O]} := by',
        '    rw [← reduced.2.2]',
        f'    rw [chunkPrimDimN_shape 0 {D} {u} (t {out}) _ reduced.1 (by decide)]', '    rfl']
    for j,step in enumerate(scatters):
        proof += [f'  have scatter{j} := {names[step.node]} p q hp']
    terms = _list(f'chunkPrimDimN {a} {T} {j} (tensorSum {partials})' for j in range(T))
    proof += [f'  have outputs : {ys} = List.ofFn (fun dst : Fin {T} => chunkPrimDimN {a} {T} dst.val (tensorSum {partials})) := by',
        f'    change {ys} = {terms}', '    exact '+_cons_equal([f'scatter{j}' for j in range(T)]),
        '  refine ⟨reduced.1, ?_, ?_⟩', '  · intro y hy',
        '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy',
        '    rcases hy with '+' | '.join('rfl' for _ in range(T))]
    for j in range(T):
        proof += [f'    · rw [scatter{j}, chunkPrimDimN_shape {a} {T} {j} (tensorSum {partials}) _ sumShape (by decide)]', '      rfl']
    proof += ['  · rw [reduced.2.2, outputs]', '    symm',
        f'    exact allGatherPrimDimN_chunks_ofFn {a} {T} (tensorSum {partials})',
        '      (by decide) (by rw [sumShape]; decide) (by rw [sumShape]; decide)',f'#print axioms {name}']
    return proof,row


def _frontiers(si,pi,closed,owners):
    frontier._cover(closed,owners)
    authenticated = []; slot_groups = {}
    # Fresh predecessor classifications must remain a subset of the full frontier.
    for retained in closed['retained_units']:
        if not any(_same_typed(retained,row) for row in closed['frontier_units']):
            raise ValueError('input-linear retained original frontier omitted')
    for old in closed['frontier_units']:
        if 'slot' in old and not _same_typed(old['slot'],old['source_output_slot']):
            raise ValueError('input-linear predecessor alias slot mismatch')
        key = (tuple(old['source_step']['node']),old['unit'])
        slot_groups.setdefault(key,[]).append(old['source_output_slot'])
        g = frontier._output(si,old['source_step'],old['sm_output_ref'])
        ps = [frontier._output(pi,d,r) for d,r in zip(old['local_steps'],old['pm_output_refs'],strict=True)]
        middle._contract(old,g,ps)
        B,S,H = old['local_shape']; u = old['unit']; T = len(ps)
        if (not _same_typed(old['dimensions'],dict(D=len(owners),T=T,B=B,S=S,H=H))
                or not _same_typed(old['positions'],list(range(u*B,(u+1)*B)))
                or type(old['source_output_slot']) is not int
                or not 0 <= old['source_output_slot'] < len(old['source_step']['outputs'])
                or not _same_typed(old['source_step']['outputs'][old['source_output_slot']]['endpoint']['ref'],g.endpoint.ref)
                or not _same_typed(old['sm_output_tid'],g.endpoint.tid)
                or not _same_typed(old['pm_output_tids'],[p.endpoint.tid for p in ps])):
            raise ValueError('input-linear complete strong predecessor dimensions/slot mismatch')
        for index,d in [(si,old['source_step']),*((pi,d) for d in old['local_steps'])]:
            cell = index.raw[tuple(d['node'])]
            if op(cell) == 'AllToAllPrim':
                inputs = []
                for ref in cell.inputs:
                    producer = index.raw[tuple(index.writers[tuple(ref)])]
                    inputs.append(_one((p for p in source._ports(index,producer,'outputs') if p.endpoint.ref == tuple(ref)),
                        'input-linear AA predecessor original input required'))
                step,_ = exchange._boundary(index,cell,inputs,old['ranks'],old['ranks'].index(cell.rank))
            elif op(cell) == 'FW_multiref':
                ins = source._ports(index,cell,'inputs')
                if len(ins) != 1: raise ValueError('input-linear original alias arity')
                source._edge(index,ins[0],cell._input_irs[0])
                step = projection.post._next(index,ins[0])
            else:
                raise ValueError('input-linear unsupported predecessor source descriptor')
            if not _same_typed(asdict(step),d):
                raise ValueError('input-linear complete predecessor descriptor mismatch')
        authenticated.append((old,g,ps))
    for (node,_),slots in slot_groups.items():
        ports = source._ports(si,si.raw[node],'outputs')
        # Projection multiref has a direct SM linear on every original slot;
        # skip multirefs also contain a previously consumed normalization path.
        if all([op(c) for c in _consumers(si,[p])] == ['FW_linear'] for p in ports):
            if not _same_typed(slots,list(range(len(ports)))):
                raise ValueError('input-linear complete ordered original projection slots required')
    return authenticated


def render(sm,pm,lineages,validation,bound,execution_order):
    """Exactly one fresh predecessor call using the SAME six public objects."""
    try:
        _,closed = predecessor.render(sm,pm,lineages,validation,bound,execution_order)
        return _render(sm,pm,lineages,validation,bound,execution_order,closed)
    except (KeyError,TypeError,AttributeError,IndexError,StopIteration,OverflowError) as exc:
        raise ValueError(f'malformed frontier input-linear original source: {exc}') from exc


def _render(sm,pm,lineages,validation,bound,order,closed):
    if not _same_typed(order,dict(sm=build(sm),pm=build(pm))):
        raise ValueError('input-linear complete typed execution/inverse order mismatch')
    si,pi = (_Index(v,raw) for v,raw in zip((sm,pm),validation._inputs[:2],strict=True))
    specs = adds._bound(lineages,bound)
    rows = bound['relations']
    if (not _same_typed([r['lineage'] for r in rows],[asdict(l) for l in lineages if l.role == Role.PARAMETER])
            or any(not _same_typed([u['unit'] for u in r['units']],[u['unit'] for u in r['lineage']['units']]) for r in rows)):
        raise ValueError('input-linear exact canonical parameter specification order required')
    authenticated = _frontiers(si,pi,closed,validation._inputs[3]['config']['units'])
    proofs,reads,units,result,consumed = [],[],[],[],[]; names = {}; seen = {}
    def emit(view,label,step,**metadata):
        if step.node in seen:
            if label != 'sm' or not _same_typed(step,seen[step.node]):
                raise ValueError('input-linear duplicate/cross-DP original source operation')
            return
        proof,row = _read(view,label,step,order[label]); proofs.extend(proof)
        row.update(metadata); reads.append(row); names[step.node] = row['theorem']; seen[step.node] = step
    for i,(old,g,ps) in enumerate(authenticated):
        if old['gather_axis'] != 2 or any(d['op'] != 'AllToAllPrim' for d in old['local_steps']):
            result.append(old); continue
        global_ = _linear(si,g,(0,1)); T = len(ps)
        locals_ = [_linear(pi,p,(j,T)) for j,p in enumerate(ps)]
        parent = si.raw[global_.node]._output_irs[0].parent.tid
        if any(not _same_typed(pi.raw[s.node]._output_irs[0].parent.tid,parent)
               or s.outputs[0].parent_name != global_.outputs[0].parent_name for s in locals_):
            raise ValueError('input-linear SM/PM original output parent/branch identity mismatch')
        parameter = _parameter(si,pi,lineages,specs,global_,locals_,old)
        partials = [s.outputs[0] for s in locals_]; cells = _consumers(pi,partials)
        if len(cells) != T or any(op(c) != 'ReduceScatterPrim' for c in cells):
            raise ValueError('input-linear complete original RS receiver cover required')
        scatters = []; coverage = []
        for j,rank in enumerate(old['ranks']):
            cell = _one((c for c in cells if _same_typed(c.rank,rank)),'input-linear RS original receiver missing/ambiguous')
            step,meta = _scatter(pi,cell,partials,old['ranks'],j); scatters.append(step); coverage.append(meta)
        if len({s.split_axis for s in scatters}) != 1:
            raise ValueError('input-linear RS receiver axes differ')
        emit(sm,'sm',global_,frontier_index=i)
        for s in locals_: emit(pm,'pm',s,frontier_index=i,unit=old['unit'])
        for s,meta in zip(scatters,coverage,strict=True): emit(pm,'pm',s,frontier_index=i,unit=old['unit'],**meta)
        proof,row = _unit(old,global_,locals_,scatters,parameter,names,len(specs))
        row['frontier_index'] = i; proofs.extend(proof); units.append(row); result.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, canonical frame, aggregate costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld','noncomputable section','set_option maxHeartbeats 500000',
        *proofs,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return text,dict(status='source-frontier-input-linear-values-emitted-uncompiled',reads=reads,units=units,
        frontier_units=result,retained_units=closed['retained_units'],deferred_units=closed['deferred_units'],
        consumed_frontier_indices=consumed,lean_bytes=len(text.encode()),
        cost_scope='input-column linear/ReduceScatter fragment only; excludes predecessors, frame and imports',
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
