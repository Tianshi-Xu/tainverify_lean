"""FIRST original-source view checkpoint; emitted Lean is UNCOMPILED.

Fresh projection authentication is mandatory. Raw parent metadata is local to
its original world/DP unit; only predecessor facts supply global DP equality.
No transpose or collective values are proved here.
"""
from dataclasses import asdict
from math import prod

from Verdict import graph_to_lean as c
from Verdict import runtime_projection_values as projection
from Verdict import runtime_post_add_values as post
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_embedding_position_units import _list
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_world import _ordinary


def _output(index, descriptor):
    cell = index.raw[tuple(descriptor['node'])]
    projection._node(index, cell)
    ins = tuple(post._port(index, r, ir) for r, ir in zip(cell.inputs, cell._input_irs, strict=True))
    outs = tuple(post._port(index, r, ir) for r, ir in zip(cell.outputs, cell._output_irs, strict=True))
    step = routes.Step(tuple(cell.node), op(cell), ins, outs)
    if not _same_typed(asdict(step), descriptor) or step.op != 'FW_linear' or len(outs) != 1:
        raise ValueError('view fresh projection source identity mismatch')
    return outs[0]


def _consumer(index, port):
    # This is the forward frontier of an already authenticated training graph.
    # Saved-primal BW reads are not competing forward consumers; they remain in
    # the original schedule and in _read's complete selected/suffix nonwrites.
    # Unknown or multiple forward consumers must still fail closed.
    return _one((cell for cell in index.raw.values()
        if not op(cell).startswith('BW_')
        and _same_typed(cell.rank, port.endpoint.ref[1])
        and port.endpoint.ref in map(tuple, cell.inputs)),
        'view immediate original consumer missing/ambiguous')


def _view(index, cell, producer):
    node = projection._node(index, cell)
    params, status = _ordinary(index.view, node, c._get_node_params)
    if op(cell) != 'FW_view' or status is not None or len(cell.inputs) != 1 or len(cell.outputs) != 1:
        raise ValueError('view original opcode/arity mismatch')
    x, = (post._port(index, r, ir) for r, ir in zip(cell.inputs, cell._input_irs, strict=True))
    y, = (post._port(index, r, ir) for r, ir in zip(cell.outputs, cell._output_irs, strict=True))
    if not _same_typed(x, producer) or any(p.endpoint.ref[:3] != tuple(node)[:3] for p in (x, y)):
        raise ValueError('view original input fullref/identity/owner mismatch')
    if len(x.parent_shape) != 3 or len(y.parent_shape) != 4:
        raise ValueError('view requires original rank-three to rank-four metadata')
    C = y.parent_shape[3]
    start, end = x.bounds[2]
    if (x.parent_shape[2] % C or start % C or end % C
            or y.parent_shape != (*x.parent_shape[:2], x.parent_shape[2]//C, C)
            or y.bounds != (*x.bounds[:2], (start//C, end//C), (0, C))
            or not _same_typed(y.value_part, x.value_part)
            or not _same_typed(params, list(y.endpoint.shape))
            or prod(params) != prod(x.endpoint.shape)):
        raise ValueError('view original full shape/bounds/value partition/product mismatch')
    # _ordinary is the normalized authority; independently check its original
    # size payload because the canonical extractor obtains params from outputs.
    size = dict(cell.kwargs).get('size')
    if (type(size) not in (list, tuple) or len(size) != 4
            or any(type(d) is not int or d == 0 or d < -1 for d in size)
            or list(size).count(-1) > 1):
        raise ValueError('view original size kwargs missing/invalid')
    expected = list(size)
    if -1 in expected:
        divisor = prod(d for d in expected if d != -1)
        if prod(x.endpoint.shape) % divisor:
            raise ValueError('view original inferred size product mismatch')
        expected[expected.index(-1)] = prod(x.endpoint.shape)//divisor
    if not _same_typed(expected, params):
        raise ValueError('view original size kwargs disagree with normalized params')
    return routes.Step(tuple(node), 'FW_view', (x,), (y,))


def _read(view, label, step, order):
    nodes = view.nodes()
    i, node = _one(((i, n) for i, n in enumerate(nodes) if tuple(n) == step.node),
                   'view source writer missing/ambiguous')
    for method, ports in [('node_inputs', step.inputs), ('node_outputs', step.outputs)]:
        if not _same_typed([(tuple(view.source_tensor(t)), t.tid) for t in getattr(view, method)(node)],
                           [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
            raise ValueError('view original ordered fullrefs mismatch')
    k = order['execution_to_source'].index(i)
    inp = step.inputs[0].endpoint.tid
    out = step.outputs[0].endpoint.tid
    for source in order['execution_to_source'][k:]:
        if inp in {t.tid for t in view.node_outputs(nodes[source])}:
            raise ValueError('view operand is written by selected node or suffix')
    params, status = _ordinary(view, node, c._get_node_params)
    if status is not None or len(params) != 4:
        raise ValueError('view read normalized params mismatch')
    name = f'viewRead_{label}_{out}'
    req = f'{label}InputRequests'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {out} = fw_view {params} (t {inp}) := by',
        f'  apply SourceLayoutRead.view_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {req} ({req}.take {k}) ({req}.drop {k+1}) {label}Node_{i}',
        f'    {node.rank} {inp} {out} {params[0]} {params[1:]} s t rfl ?_ rfl ?_ h',
        '  · calc',
        f'      {req} = {req}.take {k} ++ {req}.drop {k} := (List.take_append_drop {k} {req}).symm',
        '      _ = _ := rfl',
        f'  · change ∀ row ∈ {req}.drop {k}, {inp} ∉ row.1.outs',
        '    decide', f'#print axioms {name}']
    return proof, dict(theorem=name, world=label, op='FW_view', node=list(step.node),
        source_index=i, execution_index=k, input_tids=[inp], output_tid=out,
        input_refs=[list(step.inputs[0].endpoint.ref)], output_refs=[list(step.outputs[0].endpoint.ref)],
        params=params, request='global', source_kwargs=dict(view.node_kwargs(node)), source_step=asdict(step),
        operand_nonwrite_source_indices=order['execution_to_source'][k:])


def _unit(prior, global_, locals_, names):
    D, T, B = (prior['dimensions'][k] for k in ('D', 'T', 'B'))
    u, axis = prior['unit'], prior['gather_axis']
    if axis not in (1, 2) or len(locals_) != T:
        raise ValueError('view unsupported predecessor axis/partial unit')
    gx, gy = global_.inputs[0], global_.outputs[0]
    S, H, C = locals_[0].outputs[0].endpoint.shape[1:]
    gshape = [B*D, S*T if axis == 1 else S, H*T if axis == 2 else H, C]
    lshape = [B, S, H, C]
    if (list(gx.endpoint.shape) != prior['global_shape']
            or list(gy.endpoint.shape) != gshape
            or list(gx.endpoint.ref) != prior['sm_output_ref']
            or [list(s.inputs[0].endpoint.ref) for s in locals_] != prior['pm_output_refs']
            or [s.node[1] for s in locals_] != prior['ranks']):
        raise ValueError('view global/ordered local same-branch projection mismatch')
    for j, step in enumerate(locals_):
        x, y = step.inputs[0], step.outputs[0]
        expected_bounds = ((j*S, (j+1)*S), (0, H)) if axis == 1 else ((0, S), (j*H, (j+1)*H))
        if (list(x.endpoint.shape) != prior['local_shape'] or list(y.endpoint.shape) != lshape
                or y.parent_name != gy.parent_name
                or y.parent_shape[1:] != gy.parent_shape[1:]
                or y.bounds[1:3] != expected_bounds
                or y.value_part != gy.value_part):
            raise ValueError('view same-branch head size/ordered partition/bounds mismatch')
    xs = _list(f'q {s.inputs[0].endpoint.tid}' for s in locals_)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in locals_)
    name = f'viewUnitFacts_{gy.endpoint.tid}_{u}_slot{prior["slot"]}'
    pairs = 'List.Forall₂.nil'
    for j in reversed(range(T)):
        pairs = f'List.Forall₂.cons ({names[locals_[j].node]} p q hp) ({pairs})'
    law = 'sequence' if axis == 1 else 'head'
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {gy.endpoint.tid}).shape = {gshape} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {lshape}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {gy.endpoint.tid}) = allGatherPrimDimN {axis} {T} 0 {ys} := by',
        f'  have predecessor := {prior["theorem"]} s p t q hs hp hvalues',
        f'  have localReads : List.Forall₂ (fun x y => y = fw_view {lshape} x) {xs} {ys} :=',
        f'    {pairs}',
        f'  exact TrainVerify.Denote.source_view_{law}_unit_output_reconstruct {D} {T} {B} {S} {H} {C} {u}',
        f'    (t {gx.endpoint.tid}) (t {gy.endpoint.tid}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        f'    predecessor.1 rfl predecessor.2.1 predecessor.2.2 ({names[global_.node]} s t hs) localReads',
        f'#print axioms {name}']
    return proof, dict(theorem=name, facts_theorem=name, predecessor=prior['theorem'],
        unit=u, slot=prior['slot'], ranks=prior['ranks'], positions=prior['positions'], gather_axis=axis,
        global_shape=gshape, local_shape=lshape, dimensions=dict(D=D, T=T, B=B, S=S, H=H, C=C),
        sm_output_tid=gy.endpoint.tid, pm_output_tids=[s.outputs[0].endpoint.tid for s in locals_],
        sm_output_ref=list(gy.endpoint.ref), pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_],
        source_step=asdict(global_), local_steps=[asdict(s) for s in locals_])


def _boundary(index, cell, ports, ranks, j, order):
    node = projection._node(index, cell)
    scope = _one((s for s in index.view.collective_scopes.values() if tuple(s.node) == tuple(node)),
                 'view deferred original AllToAll scope missing/ambiguous')
    if (scope.op != 'AllToAllPrim' or not scope.source_writer
            or not _same_typed(scope.ranks, tuple(ranks))
            or not _same_typed(scope.local_index, j)
            or not _same_typed(scope.input_tids, tuple(p.endpoint.tid for p in ports))
            or not _same_typed(scope.input_shape, ports[j].endpoint.shape)
            or not _same_typed([tuple(r) for r in cell.inputs], [p.endpoint.ref for p in ports])
            or len(cell.outputs) != 1 or len(scope.params) != 2):
        raise ValueError('view deferred AllToAll original peers/group/owner mismatch')
    a, b = scope.params
    if any(type(d) is not int or not 0 <= d < 3 for d in (a, b)) or a == b:
        raise ValueError('view deferred AllToAll unsupported original axes')
    irs = getattr(cell, '_input_irs', None)
    coverage = 'absent'
    if irs is not None:
        if len(irs) == 1 and len(ports) > 1:
            expected = [ports[j]]; coverage = 'local-only'
        elif len(irs) == len(ports):
            expected = ports; coverage = 'all-peers'
        else:
            raise ValueError('view deferred AllToAll partial original metadata')
        for p, ir in zip(expected, irs, strict=True):
            if not _same_typed(post._port(index, p.endpoint.ref, ir), p):
                raise ValueError('view deferred AllToAll original input identity mismatch')
    out = index.endpoint(cell.outputs[0])
    if out.ref[:3] != tuple(node)[:3] or out.tid != scope.output_tid:
        raise ValueError('view deferred AllToAll original output identity mismatch')
    bounds = list(ports[j].bounds)
    end = ports[0].bounds[a][0]
    for p in ports:
        if (p.parent_shape != ports[0].parent_shape or p.parent_name != ports[0].parent_name
                or p.value_part != ports[0].value_part or p.bounds[a][0] != end
                or any(p.bounds[d] != ports[0].bounds[d] for d in range(3) if d != a)):
            raise ValueError('view deferred AllToAll original partition mismatch')
        end = p.bounds[a][1]
    bounds[a] = (ports[0].bounds[a][0], end)
    lo, hi = bounds[b]
    if (hi-lo) % len(ranks):
        raise ValueError('view deferred AllToAll nondivisible split')
    width = (hi-lo)//len(ranks)
    bounds[b] = (lo+j*width, lo+(j+1)*width)
    derived = routes.Port(out, ports[j].parent_name, ports[j].parent_shape, tuple(bounds), ports[j].value_part)
    if out.shape != tuple(hi-lo for lo, hi in bounds):
        raise ValueError('view deferred AllToAll output shape mismatch')
    irs = getattr(cell, '_output_irs', None)
    if irs is not None and (len(irs) != 1 or not _same_typed(post._port(index, out.ref, irs[0]), derived)):
        raise ValueError('view deferred AllToAll original output metadata mismatch')
    i = index.view.nodes().index(node)
    return dict(op='AllToAllPrim', node=list(node), source_index=i,
        execution_index=order['execution_to_source'].index(i), source_writer=scope.source_writer,
        ranks=list(scope.ranks), local_index=j, params=list(scope.params),
        input_refs=[list(p.endpoint.ref) for p in ports], output_ref=list(out.ref),
        input_tids=list(scope.input_tids), output_tid=out.tid, input_metadata=coverage,
        output_metadata='absent' if irs is None else 'present', source_kwargs=dict(cell.kwargs),
        source_inputs=[asdict(p) for p in ports], source_output=asdict(derived))


def render(sm, pm, lineages, validation, bound, execution_order):
    """Authenticate the complete projection predecessor afresh, then the frontier."""
    _, prior = projection.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed view source/binding: {exc}') from exc


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, deferred, seen, names = [], [], [], [], {}, {}
    def emit(view, label, step):
        if step.node in seen:
            if label != 'sm' or not _same_typed(seen[step.node], step):
                raise ValueError('view duplicate/cross-unit consumer')
            return
        proof, row = _read(view, label, step, order[label])
        proofs.extend(proof); reads.append(row)
        seen[step.node] = step; names[step.node] = row['theorem']
    for unit in prior['units']:
        port = _output(si, unit['source_step'])
        global_ = _view(si, _consumer(si, port), port)
        emit(sm, 'sm', global_)
        ports = [_output(pi, d) for d in unit['local_steps']]
        cells = [_consumer(pi, p) for p in ports]
        kinds = {op(cell) for cell in cells}
        if kinds == {'AllToAllPrim'}:
            boundaries = [_boundary(pi, cell, ports, unit['ranks'], j, order['pm'])
                          for j, cell in enumerate(cells)]
            deferred.append(dict(unit=unit['unit'], slot=unit['slot'], ranks=unit['ranks'],
                predecessor=unit['theorem'], global_view=asdict(global_),
                reason='original-authenticated-AllToAll-before-first-local-view', boundaries=boundaries))
            continue
        if kinds != {'FW_view'}:
            raise ValueError('view mixed/unknown immediate original frontier')
        locals_ = [_view(pi, cell, p) for cell, p in zip(cells, ports, strict=True)]
        for step in locals_: emit(pm, 'pm', step)
        proof, row = _unit(unit, global_, locals_, names)
        proofs.extend(proof); units.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, fresh predecessors, frame, aggregate cost and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-first-view-values-emitted-uncompiled', reads=reads, units=units,
        deferred_units=deferred, deferred_stage=('before-first-local-view: original AllToAll boundary; ' if deferred else '')
            + 'after-first-view: transpose/collectives/downstream unproved',
        lean_bytes=len(text.encode()), cost_scope='view fragment only; excludes projection/earlier predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
