"""Original-source projection reads and strong DP-unit facts, UNCOMPILED.

The caller emits the same canonical bound/frame and fresh LayerNorm fragment.
No descriptors, output equalities, or shape equalities are caller authority.
Collective raw IR coverage is reported separately from authenticated peer refs.
"""
from dataclasses import asdict

from Verdict import graph_to_lean as c
from Verdict import runtime_add_values as adds
from Verdict import runtime_layernorm_values as norm
from Verdict import runtime_post_add_values as post
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_embedding_position_units import _list
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import Role, _Index, _same_typed, op
from Verdict.runtime_world import _ordinary


def _node(index, cell):
    node = _one((n for n in index.view.nodes() if tuple(n) == tuple(cell.node)),
                'projection original node missing/ambiguous')
    if (not _same_typed(cell.rank, node.rank)
            or not _same_typed(dict(cell.kwargs), dict(index.view.node_kwargs(node)))):
        raise ValueError('projection original owner/kwargs mismatch')
    return node


def _alias(index, descriptor):
    cell = index.raw[tuple(descriptor['node'])]
    producer = norm._next(index, post._port(index, cell.inputs[0], cell._input_irs[0]))
    if not _same_typed(asdict(producer), descriptor):
        raise ValueError('projection fresh LayerNorm descriptor mismatch')
    alias = post._next(index, producer.outputs[0])
    _node(index, index.raw[alias.node])
    if any(p.endpoint.ref[:3] != alias.node[:3] for p in (*alias.inputs, *alias.outputs)):
        raise ValueError('projection alias owner/microbatch mismatch')
    return alias


def _consumer(index, port, allowed):
    return _one((cell for cell in index.raw.values() if op(cell) in allowed
        and cell.rank == port.endpoint.ref[1] and port.endpoint.ref in map(tuple, cell.inputs)),
        'projection branch missing/ambiguous')


def _linear(index, activation):
    cell = _consumer(index, activation, ('FW_linear',))
    node = _node(index, cell)
    params, status = _ordinary(index.view, node, c._get_node_params)
    if status is not None or not _same_typed(params, []) or len(cell.inputs) != 2 or len(cell.outputs) != 1:
        raise ValueError('projection linear original params/arity mismatch')
    ins = tuple(post._port(index, r, ir) for r, ir in zip(cell.inputs, cell._input_irs, strict=True))
    outs = tuple(post._port(index, r, ir) for r, ir in zip(cell.outputs, cell._output_irs, strict=True))
    if not _same_typed(ins[0], activation) or any(p.endpoint.ref[:2] != tuple(node)[:2] for p in (*ins, *outs)):
        raise ValueError('projection linear original ordered input/owner mismatch')
    x, w = ins; y, = outs
    if (len(x.parent_shape) != 3 or len(w.parent_shape) != 2
            or x.parent_shape[-1] != w.parent_shape[-1]
            or x.bounds[-1] != (0, x.parent_shape[-1])
            or w.bounds[-1] != (0, x.parent_shape[-1])
            or any(p.value_part != (0, 1) for p in (*ins, *outs))
            or y.parent_shape != (*x.parent_shape[:2], w.parent_shape[0])
            or y.bounds != (*x.bounds[:2], w.bounds[0])):
        raise ValueError('projection linear full contraction/output parent/bounds/value mismatch')
    return routes.Step(tuple(node), 'FW_linear', ins, outs)


def _gather(index, cell, ports, ranks, j):
    node = _node(index, cell)
    scope = _one((s for s in index.view.collective_scopes.values() if tuple(s.node) == tuple(node)),
                 'projection AllGather scope missing/ambiguous')
    if (scope.op != 'AllGatherPrim' or not scope.source_writer
            or not _same_typed(scope.ranks, ranks) or not _same_typed(scope.local_index, j)
            or not _same_typed(scope.params, (1,))
            or not _same_typed(scope.input_tids, tuple(p.endpoint.tid for p in ports))
            or not _same_typed(scope.input_shape, ports[j].endpoint.shape)):
        raise ValueError('projection AllGather source writer/axis/group/local index/ordered peers mismatch')
    whole = ports[0].parent_shape
    if len(whole) != 3:
        raise ValueError('projection AllGather requires rank-three input')
    end = 0
    for p in ports:
        if (p.parent_shape != whole or p.parent_name != ports[0].parent_name
                or p.value_part != (0, 1) or p.bounds[1][0] != end
                or p.bounds[0] != ports[0].bounds[0] or p.bounds[2] != (0, whole[2])
                or p.endpoint.shape != ports[0].endpoint.shape):
            raise ValueError('projection AllGather ordered complete sequence partition mismatch')
        end = p.bounds[1][1]
    if end != whole[1]:
        raise ValueError('projection AllGather incomplete sequence partition')
    out, = index.view.node_outputs(node)
    ep = index.endpoint(index.view.source_tensor(out))
    bounds = (ports[0].bounds[0], (0, end), ports[0].bounds[2])
    derived = routes.Port(ep, ports[0].parent_name, whole, bounds, (0, 1))
    if ep.shape != tuple(b-a for a, b in bounds) or scope.output_tid != ep.tid:
        raise ValueError('projection AllGather output bounds/shape mismatch')
    for field, expected in [('inputs', ports), ('outputs', (derived,))]:
        if not _same_typed([tuple(r) for r in getattr(cell, field)], [p.endpoint.ref for p in expected]):
            raise ValueError('projection AllGather original ordered fullrefs mismatch')
    coverage = {}
    for field, expected in [('_input_irs', ports), ('_output_irs', (derived,))]:
        irs = getattr(cell, field, None)
        state = 'absent'
        if irs is not None:
            if field == '_input_irs' and len(irs) == 1 and len(ports) > 1:
                selected = (ports[j],); state = 'local-only'
            elif len(irs) == len(expected):
                selected = expected; state = 'all-peers' if field == '_input_irs' else 'present'
            else:
                raise ValueError('projection AllGather partial raw metadata')
            for p, ir in zip(selected, irs, strict=True):
                if not _same_typed(post._port(index, p.endpoint.ref, ir), p):
                    raise ValueError('projection AllGather original raw metadata mismatch')
        coverage['input_metadata' if field == '_input_irs' else 'output_metadata'] = state
    return routes.Step(tuple(node), 'AllGatherPrim', ports, (derived,), scope.source_writer,
        ranks, j, gather_axis=1, peers=tuple(zip(ranks, scope.input_tids))), coverage


def _parameter(si, pi, lineages, specs, global_, locals_, unit, sharded):
    full = global_.inputs[1]; local_ports = [s.inputs[1] for s in locals_]
    D, T, u = unit['dimensions']['D'], len(local_ports), unit['unit']
    parameter = _one((l for l in lineages if l.role == Role.PARAMETER and _same_typed(l.target, full.endpoint)),
                     'projection original weight PARAMETER lineage missing/ambiguous')
    i, row, bu = _one(((i, r, b) for i, (r, b) in enumerate(specs)
        if _same_typed(r['lineage'], asdict(parameter)) and _same_typed(b['unit'], u)),
        'projection same canonical bound weight/unit missing/ambiguous')
    pu = parameter.units[u]
    reconstruction = 'tp-axis-gather:0' if sharded and T > 1 else 'tp-copy-obligation'
    if (not _same_typed([p.unit for p in parameter.units], list(range(D)))
            or pu.reconstruction != reconstruction or pu.positions != ()
            or not _same_typed([p.endpoint for p in pu.pieces], [p.endpoint for p in local_ports])
            or not _same_typed([p.endpoint.ref[1] for p in local_ports], unit['ranks'])):
        raise ValueError('projection weight lineage unit/role/ordered fullrefs mismatch')
    O, I = full.parent_shape
    width = local_ports[0].endpoint.shape[0]
    if full.bounds != ((0, O), (0, I)) or O != width*(T if sharded else 1):
        raise ValueError('projection weight full/partition shape mismatch')
    for j, (piece, port) in enumerate(zip(pu.pieces, local_ports, strict=True)):
        expected = ((j*width, (j+1)*width), (0, I)) if sharded else ((0, O), (0, I))
        if (port.parent_name != full.parent_name or port.parent_shape != full.parent_shape
                or port.bounds != expected or port.endpoint.shape != (width, I)
                or port.value_part != (0, 1)
                or not _same_typed((piece.bounds, piece.value_part), (port.bounds, port.value_part))):
            raise ValueError('projection weight original ordered row pieces mismatch')
    kind = 'sharded' if sharded and T > 1 else 'replicated'
    goal = dict(kind=kind, sm_tid=full.endpoint.tid, pm_tids=[p.endpoint.tid for p in local_ports],
                dim=0 if kind == 'sharded' else None, sm_shape=[O, I], pm_shape=[width, I])
    if not _same_typed(bu['initial_goal'], goal) or len(bu['bindings']) != T:
        raise ValueError('projection bound weight role/goal mismatch')
    norm._binding(si, row['sm_binding'], full, full.endpoint.ref, 'sm')
    for b, p in zip(bu['bindings'], local_ports, strict=True):
        norm._binding(pi, b, p, full.endpoint.ref, 'pm')
    return dict(role='weight', spec_index=i, kind=kind, sm_ref=list(full.endpoint.ref),
        sm_tid=full.endpoint.tid, pm_refs=[list(p.endpoint.ref) for p in local_ports],
        pm_tids=goal['pm_tids'], sm_shape=goal['sm_shape'], pm_shape=goal['pm_shape'])


def _read(view, label, step, order):
    if step.op == 'FW_multiref':
        proof, row = post._read(view, label, step, order)
        name = row['theorem'].replace('postAdd', 'projection')
        proof = [s.replace(row['theorem'], name) for s in proof]
        row['theorem'] = name
        return proof, row
    nodes = view.nodes()
    i, node = _one(((i, n) for i, n in enumerate(nodes) if tuple(n) == step.node),
                   'projection source read writer missing/ambiguous')
    for method, ports in [('node_inputs', step.inputs), ('node_outputs', step.outputs)]:
        if not _same_typed([(tuple(view.source_tensor(t)), t.tid) for t in getattr(view, method)(node)],
                           [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
            raise ValueError('projection source read original ordered ports mismatch')
    k = order['execution_to_source'].index(i)
    ins = [p.endpoint.tid for p in step.inputs]; out = step.outputs[0].endpoint.tid
    for source in order['execution_to_source'][k:]:
        if set(ins) & {t.tid for t in view.node_outputs(nodes[source])}:
            raise ValueError('projection operand is written by selected node or suffix')
    gather = step.op == 'AllGatherPrim'
    name = f'projection{"AllGather" if gather else "Linear"}Read_{label}_{out}'
    requests = f'{label}InputRequests'
    value = (f'allGatherPrimDimN 1 {len(step.ranks)} {step.local_index} {_list(f"t {x}" for x in ins)}'
             if gather else f'fw_linear (t {ins[0]}) (t {ins[1]})')
    law = 'SourceAllGatherRead.allGather_value_of_split' if gather else 'SourceLinearRead.linear_value_of_split'
    args = (f'{node.rank} {list(step.ranks)} {ins} {out} 1 s t rfl ?_ rfl ?_ h' if gather
            else f'{node.rank} {ins[0]} {ins[1]} {out} s t rfl ?_ rfl ?_ ?_ h')
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {out} = {value} := by',
        f'  apply {law} {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{i}',
        f'    {args}', '  · calc',
        f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
        '      _ = _ := rfl']
    if gather:
        proof += [f'  · change ∀ tid ∈ ({ins} : List Tid), ∀ row ∈ {requests}.drop {k}, tid ∉ row.1.outs', '    decide']
    else:
        for tid in ins:
            proof += [f'  · change ∀ row ∈ {requests}.drop {k}, {tid} ∉ row.1.outs', '    decide']
    proof += [f'#print axioms {name}']
    return proof, dict(theorem=name, world=label, op=step.op, node=list(step.node),
        source_index=i, execution_index=k, input_tids=ins, output_tid=out,
        input_refs=[list(p.endpoint.ref) for p in step.inputs], output_refs=[list(p.endpoint.ref) for p in step.outputs],
        params=[1] if gather else [], request='group' if gather else 'global',
        source_kwargs=dict(view.node_kwargs(node)), source_step=asdict(step),
        operand_nonwrite_source_indices=order['execution_to_source'][k:])


def _unit(unit, slot, global_alias, aliases, global_, locals_, gathers, parameter, names, spec_count):
    D, T, B, S, I = (unit['dimensions'][k] for k in ('D', 'T', 'B', 'S', 'H'))
    u = unit['unit']; sharded = bool(gathers)
    if sharded and parameter['kind'] != 'sharded':
        raise ValueError('single-rank gathered projection requires a singleton weight-gather adapter; not emitted')
    O = parameter['pm_shape'][0]
    out = global_.outputs[0].endpoint.tid; weight = parameter['sm_tid']
    gx = global_alias.outputs[slot].endpoint.tid
    ax = [a.outputs[slot].endpoint.tid for a in aliases]
    ys = [s.outputs[0].endpoint.tid for s in locals_]
    xs, outs, ws = (_list(f'q {tid}' for tid in ts) for ts in (ax, ys, parameter['pm_tids']))
    name = f'projectionLinearUnitFacts_{out}_{u}_slot{slot}'
    fullshape = [B*D, S*T, O*T if sharded else O]
    localshape = [B, S*T if sharded else S, O]
    axis = 2 if sharded else 1
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (h : InitialParameterValues s p) :',
        f'    (t {out}).shape = {fullshape} ∧',
        f'    (∀ y ∈ {outs}, y.shape = {localshape}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {out}) = allGatherPrimDimN {axis} {T} 0 {outs} := by',
        f'  have predecessor := {unit["theorem"]} s p t q hs hp h',
        f'  have globalAlias := {names[global_alias.node]} s t hs {gx} {adds._member(slot)}']
    for j, a in enumerate(aliases):
        proof += [f'  have alias{j} := {names[a.node]} p q hp {ax[j]} {adds._member(slot)}']
    proof += [f'  have fullShape : (t {gx}).shape = {[B*D, S*T, I]} :=',
        '    (congrArg Tensor.shape globalAlias).trans predecessor.1',
        f'  have inputShapes : ∀ x ∈ {xs}, x.shape = {[B, S, I]} := by',
        '    intro x hx', '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx',
        '    rcases hx with ' + ' | '.join('rfl' for _ in aliases)]
    for j in range(T):
        proof += [f'    · exact (congrArg Tensor.shape alias{j}).trans',
                  f'        (predecessor.2.1 (q {unit["pm_output_tids"][j]}) {adds._member(j)})']
    proof += [f'  have inputValue : chunkPrimDimN 0 {D} {u} (t {gx}) = allGatherPrimDimN 1 {T} 0 {xs} := by',
        '    rw [globalAlias, ' + ', '.join(f'alias{j}' for j in range(T)) + ']',
        '    exact predecessor.2.2',
        '  have hrels := initialParameterRelations_of_values t q (initialParameterValues_final s p t q hs hp h)']
    i = parameter['spec_index']
    projection = 'hrels' + '.2'*i + ('.1' if i < spec_count-1 else '')
    relation = (f'RelationCompiler.ShardedRel (t {weight}) {ws} 0 {parameter["sm_shape"]} {parameter["pm_shape"]}'
        if parameter['kind'] == 'sharded' else f'RelationCompiler.ReplicatedRel (t {weight}) {ws} {parameter["sm_shape"]}')
    proof += [f'  have weightRel : {relation} := {projection}']
    if sharded:
        shared = f'(chunkPrimDimN 0 {D} {u} (t {gx}))'
        for j, step in enumerate(gathers):
            tid = step.outputs[0].endpoint.tid
            proof += [f'  have gathered{j} : q {tid} = {shared} :=',
                      f'    ({names[step.node]} p q hp).trans inputValue.symm',
                      f'  have local{j} : q {ys[j]} = fw_linear {shared} (q {parameter["pm_tids"][j]}) := by',
                      f'    rw [{names[locals_[j].node]} p q hp, gathered{j}]']
        terms, law = ws, 'source_linear_weight_unit_output_reconstruct'
        relation_type = f'(fun w y => y = fw_linear {shared} w)'
    else:
        for j, step in enumerate(locals_):
            proof += [f'  have local{j} : q {ys[j]} = fw_linear (q {ax[j]}) (t {weight}) :=',
                f'    ({names[step.node]} p q hp).trans (congrArg (fw_linear (q {ax[j]}))',
                f'      (weightRel.replica_values (q {parameter["pm_tids"][j]}) {adds._member(j)}))']
        terms, law = xs, 'source_linear_sequence_unit_output_reconstruct'
        relation_type = f'(fun x y => y = fw_linear x (t {weight}))'
    pairs = 'List.Forall₂.nil'
    for j in reversed(range(T)):
        pairs = f'List.Forall₂.cons local{j} ({pairs})'
    proof += [f'  have localReads : List.Forall₂ {relation_type} {terms} {outs} :=', f'    {pairs}',
        f'  exact TrainVerify.Denote.{law} {D} {T} {B} {S*T if sharded else S} {I} {O} {u}',
        f'    (t {gx}) ' + (shared+' ' if sharded else '') + f'(t {weight}) (t {out}) {terms} {outs}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        '    fullShape rfl ' + ('weightRel.shard_shapes rfl weightRel.full_value' if sharded else
                               'inputShapes weightRel.full_shape inputValue'),
        f'    ({names[global_.node]} s t hs) localReads', f'#print axioms {name}']
    return proof, dict(theorem=name, facts_theorem=name, unit=u, slot=slot, ranks=unit['ranks'],
        positions=unit['positions'], predecessor=unit['theorem'], global_shape=fullshape,
        local_shape=localshape, gather_axis=axis, sm_output_tid=out, pm_output_tids=ys,
        sm_output_ref=list(global_.outputs[0].endpoint.ref), pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_],
        parameters=[parameter], dimensions=dict(D=D, T=T, B=B, S=S, I=I, O=O),
        source_step=asdict(global_), local_steps=[asdict(s) for s in locals_])


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh full-world LayerNorm authentication, then exact source projection closure."""
    _, closed = norm.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed projection source/binding: {exc}') from exc


def _render(sm, pm, lineages, validation, bound, order, closed):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    specs = adds._bound(lineages, bound)
    proofs, reads, units, exchanges, seen, names, used = [], [], [], [], {}, {}, set()
    def emit(view, label, step, **metadata):
        if step.node in seen:
            if label != 'sm' or not _same_typed(seen[step.node], step):
                raise ValueError('projection duplicate/cross-unit/slot consumer')
            return
        proof, row = _read(view, label, step, order[label])
        proofs.extend(proof); row.update(metadata); reads.append(row)
        seen[step.node] = step; names[step.node] = row['theorem']
    for unit in closed['units']:
        global_alias = _alias(si, unit['source_step'])
        aliases = [_alias(pi, d) for d in unit['local_steps']]
        if any(len(a.outputs) != len(global_alias.outputs)
            or [p.parent_name for p in a.outputs] != [p.parent_name for p in global_alias.outputs] for a in aliases):
            raise ValueError('projection alias original slot inventory/order mismatch')
        emit(sm, 'sm', global_alias)
        for a in aliases:
            emit(pm, 'pm', a)
        for slot, activation in enumerate(global_alias.outputs):
            global_ = _linear(si, activation)
            ports = tuple(a.outputs[slot] for a in aliases)
            consumers = [_consumer(pi, p, ('FW_linear', 'AllGatherPrim')) for p in ports]
            kinds = {op(cell) for cell in consumers}
            if len(kinds) != 1:
                raise ValueError('projection mixed branch kinds across ranks')
            gathers = []
            if kinds == {'AllGatherPrim'}:
                for j, cell in enumerate(consumers):
                    step, coverage = _gather(pi, cell, ports, tuple(unit['ranks']), j)
                    emit(pm, 'pm', step, unit=unit['unit'], slot=slot, **coverage)
                    exchanges.append(dict(source_step=asdict(step), unit=unit['unit'], slot=slot, **coverage))
                    gathers.append(step)
            locals_ = [_linear(pi, s.outputs[0]) for s in gathers] if gathers else [_linear(pi, p) for p in ports]
            if any(s.node in used for s in locals_):
                raise ValueError('projection cross-unit/slot linear mix')
            used.update(s.node for s in locals_)
            if any(s.outputs[0].parent_name != global_.outputs[0].parent_name for s in locals_):
                raise ValueError('projection source output slot identity mismatch')
            parameter = _parameter(si, pi, lineages, specs, global_, locals_, unit, bool(gathers))
            emit(sm, 'sm', global_)
            for s in locals_:
                emit(pm, 'pm', s)
            proof, row = _unit(unit, slot, global_alias, aliases, global_, locals_, gathers, parameter, names, len(specs))
            proofs.extend(proof); units.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, fresh predecessors, frame, aggregate cost and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-projection-values-emitted-uncompiled', reads=reads, units=units,
        exchanges=exchanges, lean_bytes=len(text.encode()),
        cost_scope='projection fragment only; excludes LayerNorm/earlier predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
