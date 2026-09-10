"""First original view/transpose12 source checkpoint; emitted Lean is UNCOMPILED.

The complete fresh exchange and view inventories use the caller's SAME bound
and execution order. No later transpose, attention, public closure, or Torch
refinement is claimed. Original backward nodes remain in every full schedule.
"""
from dataclasses import asdict

from Verdict import graph_to_lean as c
from Verdict import runtime_projection_exchange_values as exchange
from Verdict import runtime_view_values as view
from Verdict import runtime_projection_values as projection
from Verdict import runtime_post_add_values as post
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_embedding_position_units import _list
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_world import _ordinary


def _output(index, descriptor):
    """Read the actual output only: collective raw input IR can be local-only."""
    cell = index.raw[tuple(descriptor['node'])]
    node = projection._node(index, cell)
    outs = tuple(post._port(index, r, ir) for r, ir in
        zip(cell.outputs, cell._output_irs, strict=True))
    if (op(cell) != descriptor['op'] or len(outs) != 1
            or not _same_typed(tuple(asdict(p) for p in outs), descriptor['outputs'])
            or outs[0].endpoint.writer != tuple(node)
            or outs[0].endpoint.ref[:3] != tuple(node)[:3]):
        raise ValueError('transpose fresh original output identity/metadata mismatch')
    return outs[0]


def _transpose(index, cell, producer):
    node = projection._node(index, cell)
    params, status = _ordinary(index.view, node, c._get_node_params)
    kwargs = dict(cell.kwargs)
    consts = kwargs.pop('__consts', [])
    if (op(cell) != 'FW_transpose' or status is not None
            or not _same_typed(params, [1, 2]) or not _same_typed(consts, [])
            or set(kwargs) != {'dim0', 'dim1'}
            or not _same_typed([kwargs['dim0'], kwargs['dim1']], [1, 2])
            or len(cell.inputs) != 1 or len(cell.outputs) != 1):
        raise ValueError('transpose original opcode/axes/kwargs/arity mismatch')
    x, = (post._port(index, r, ir) for r, ir in zip(cell.inputs, cell._input_irs, strict=True))
    y, = (post._port(index, r, ir) for r, ir in zip(cell.outputs, cell._output_irs, strict=True))
    if (not _same_typed(x, producer)
            or any(p.endpoint.ref[:3] != tuple(node)[:3] for p in (x, y))
            or y.endpoint.writer != tuple(node) or len(x.parent_shape) != 4):
        raise ValueError('transpose original input/output fullref/owner/writer mismatch')
    if (y.parent_shape != _swap(x.parent_shape) or y.bounds != _swap(x.bounds)
            or y.endpoint.shape != _swap(x.endpoint.shape)
            or not _same_typed(y.value_part, x.value_part)):
        raise ValueError('transpose original swapped parent/bounds/value partition mismatch')
    return routes.Step(tuple(node), 'FW_transpose', (x,), (y,))


def _swap(xs):
    a, b, c_, d = xs
    return a, c_, b, d


def _contract(prior, global_, ports):
    """Independent full-global and DP-local ordered TP contracts."""
    D, T, B = (prior['dimensions'][k] for k in ('D', 'T', 'B'))
    axis, u = prior['gather_axis'], prior['unit']
    if (any(type(x) is not int or x <= 0 for x in (D, T, B))
            or type(u) is not int or not 0 <= u < D
            or type(axis) is not int or not 0 < axis < len(global_.parent_shape)
            or len(ports) != T or len(set(prior['ranks'])) != T
            or not _same_typed([p.endpoint.ref[1] for p in ports], prior['ranks'])
            or list(global_.endpoint.ref) != prior['sm_output_ref']
            or [list(p.endpoint.ref) for p in ports] != prior['pm_output_refs']):
        raise ValueError('transpose predecessor dimensions/ordered ranks/fullrefs mismatch')
    local = prior['local_shape']
    whole = list(local); whole[0] = B*D; whole[axis] *= T
    if (local[0] != B or prior['global_shape'] != whole
            or global_.endpoint.shape != tuple(whole)
            or global_.parent_shape != tuple(whole)
            or global_.bounds != tuple((0, d) for d in whole)):
        raise ValueError('transpose full global predecessor contract mismatch')
    for j, p in enumerate(ports):
        bounds = [(0, d) for d in local]
        bounds[axis] = (j*local[axis], (j+1)*local[axis])
        if (p.endpoint.shape != tuple(local) or p.parent_shape != (B, *whole[1:])
                or p.bounds != tuple(bounds) or p.parent_name != global_.parent_name
                or p.value_part != global_.value_part):
            raise ValueError('transpose full local predecessor contract mismatch')


def _read(source, label, step, order):
    nodes = source.nodes()
    i, node = _one(((i, n) for i, n in enumerate(nodes) if tuple(n) == step.node),
        'transpose source writer missing/ambiguous')
    for method, ports in [('node_inputs', step.inputs), ('node_outputs', step.outputs)]:
        if not _same_typed([(tuple(source.source_tensor(t)), t.tid) for t in getattr(source, method)(node)],
                [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
            raise ValueError('transpose original ordered fullrefs mismatch')
    k = order['execution_to_source'].index(i)
    inp, out = step.inputs[0].endpoint.tid, step.outputs[0].endpoint.tid
    for source_index in order['execution_to_source'][k:]:
        if inp in {t.tid for t in source.node_outputs(nodes[source_index])}:
            raise ValueError('transpose operand is written by selected node or suffix')
    params, status = _ordinary(source, node, c._get_node_params)
    if status is not None or not _same_typed(params, [1, 2]):
        raise ValueError('transpose read original axes mismatch')
    name, req = f'transposeRead_{label}_{out}', f'{label}InputRequests'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {out} = transposeAxes 1 2 (t {inp}) := by',
        f'  apply SourceLayoutRead.transposeAxes_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {req} ({req}.take {k}) ({req}.drop {k+1}) {label}Node_{i}',
        f'    {node.rank} {inp} {out} 1 2 s t rfl ?_ rfl ?_ h',
        '  · calc',
        f'      {req} = {req}.take {k} ++ {req}.drop {k} := (List.take_append_drop {k} {req}).symm',
        '      _ = _ := rfl',
        f'  · change ∀ row ∈ {req}.drop {k}, {inp} ∉ row.1.outs',
        '    decide', f'#print axioms {name}']
    return proof, dict(theorem=name, world=label, op=step.op, node=list(step.node),
        source_index=i, execution_index=k, input_tids=[inp], output_tid=out,
        input_refs=[list(step.inputs[0].endpoint.ref)], output_refs=[list(step.outputs[0].endpoint.ref)],
        params=params, axes=params, request='global', source_kwargs=dict(source.node_kwargs(node)),
        source_step=asdict(step), operand_nonwrite_source_indices=order['execution_to_source'][k:])


def _unit(prior, global_, locals_, names):
    gx, gy = global_.inputs[0], global_.outputs[0]
    _contract(prior, gx, [s.inputs[0] for s in locals_])
    D, T, B = (prior['dimensions'][k] for k in ('D', 'T', 'B'))
    u, axis = prior['unit'], prior['gather_axis']
    if axis not in (1, 3):
        raise ValueError('transpose unsupported TP axis')
    _, S, H, C = prior['local_shape']
    gshape, lshape = list(_swap(prior['global_shape'])), list(_swap(prior['local_shape']))
    out_axis = 3 if axis == 3 else 2
    name = f'transposeUnitFacts_{gy.endpoint.tid}_{u}_slot{prior["slot"]}'
    row = dict(theorem=name, facts_theorem=name, predecessor=prior['facts_theorem'],
        unit=u, slot=prior['slot'], ranks=prior['ranks'], positions=prior['positions'],
        dimensions=dict(D=D, T=T, B=B, S=S, H=H, C=C),
        input_gather_axis=axis, gather_axis=out_axis, axes=[1, 2],
        global_shape=gshape, local_shape=lshape, input_shape=prior['local_shape'],
        sm_output_tid=gy.endpoint.tid, sm_output_ref=list(gy.endpoint.ref),
        pm_output_tids=[s.outputs[0].endpoint.tid for s in locals_],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_],
        input_refs=[list(s.inputs[0].endpoint.ref) for s in locals_],
        source_step=asdict(global_), local_steps=[asdict(s) for s in locals_],
        deferred_stage='after-first-transpose12: later transpose/attention/downstream unproved')
    _contract(row, gy, [s.outputs[0] for s in locals_])
    xs = _list(f'q {s.inputs[0].endpoint.tid}' for s in locals_)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in locals_)
    pairs = 'List.Forall₂.nil'
    for step in reversed(locals_):
        pairs = f'List.Forall₂.cons ({names[step.node]} p q hp) ({pairs})'
    law = 'inner' if axis == 3 else 'sequence'
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {gy.endpoint.tid}).shape = {gshape} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {lshape}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {gy.endpoint.tid}) = allGatherPrimDimN {out_axis} {T} 0 {ys} := by',
        f'  have predecessor := {prior["facts_theorem"]} s p t q hs hp hvalues',
        f'  have localReads : List.Forall₂ (fun x y => y = transposeAxes 1 2 x) {xs} {ys} :=',
        f'    {pairs}',
        f'  exact TrainVerify.Denote.source_transpose12_{law}_unit_output_reconstruct {D} {T} {B} {S} {H} {C} {u}',
        f'    (t {gx.endpoint.tid}) (t {gy.endpoint.tid}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        f'    predecessor.1 rfl predecessor.2.1 predecessor.2.2 ({names[global_.node]} s t hs) localReads',
        f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Reauthenticate predecessors rather than accepting caller DTO authority."""
    _, prior = exchange.render(sm, pm, lineages, validation, bound, execution_order)
    _, views = view.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, validation, execution_order, prior, views)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed transpose original source: {exc}') from exc


def _render(sm, pm, validation, order, prior, views):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, view_units, units, seen, names = [], [], [], [], {}, {}

    def emit(source, label, step):
        if step.node in seen:
            if label != 'sm' or not _same_typed(seen[step.node], step):
                raise ValueError('transpose duplicate/cross-unit full source identity')
            return
        proof, row = (view._read if step.op == 'FW_view' else _read)(source, label, step, order[label])
        row.update(input_rank=len(step.inputs[0].endpoint.shape),
            output_rank=len(step.outputs[0].endpoint.shape),
            input_shape=list(step.inputs[0].endpoint.shape),
            output_shape=list(step.outputs[0].endpoint.shape))
        proofs.extend(proof); reads.append(row); seen[step.node] = step; names[step.node] = row['theorem']

    for original in prior['units']:
        unit = original
        g = _output(si, unit['source_step'])
        ports = [_output(pi, d) for d in unit['local_steps']]
        _contract(unit, g, ports)
        if len(g.parent_shape) == 3:
            if unit['gather_axis'] != 1:
                raise ValueError('transpose unsupported rank-three predecessor')
            global_view = view._view(si, view._consumer(si, g), g)
            old = _one((r for r in views['reads'] if r['world'] == 'sm'
                and _same_typed(r['source_step'], asdict(global_view))),
                'transpose existing global view full source identity missing/ambiguous')
            names[global_view.node] = old['theorem']
            locals_ = [view._view(pi, view._consumer(pi, p), p) for p in ports]
            for step in locals_: emit(pm, 'pm', step)
            proof, unit = view._unit(unit, global_view, locals_, names)
            old_name = unit['theorem']
            new_name = 'transposePreViewUnitFacts_'+old_name.removeprefix('viewUnitFacts_')
            proof = [line.replace(old_name, new_name) for line in proof]
            unit.update(theorem=new_name, facts_theorem=new_name,
                input_gather_axis=1, deferred_stage='after-first-local-view: first transpose12 pending')
            g, ports = global_view.outputs[0], [s.outputs[0] for s in locals_]
            _contract(unit, g, ports)
            proofs.extend(proof); view_units.append(unit)
        elif len(g.parent_shape) != 4:
            raise ValueError('transpose unsupported predecessor rank')
        global_ = _transpose(si, view._consumer(si, g), g)
        locals_ = [_transpose(pi, view._consumer(pi, p), p) for p in ports]
        emit(sm, 'sm', global_)
        for step in locals_: emit(pm, 'pm', step)
        proof, row = _unit(unit, global_, locals_, names)
        proofs.extend(proof); units.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, full cost and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-first-transpose-values-emitted-uncompiled',
        reads=reads, view_units=view_units, units=units, lean_bytes=len(text.encode()),
        deferred_stage='after-first-transpose12: later transpose/attention/downstream unproved',
        cost_scope='first transpose and needed local view fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
