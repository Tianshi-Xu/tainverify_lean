"""First actual contiguous source values, UNCOMPILED.

Only the fresh SAME six-argument query-transpose frontier supplies authority.
Parent owns contiguous_values receipt wiring, imports and kernel closure.
No AllToAll, view or later-step advancement is performed here.
Denote tensor identity only: no physical storage, stride or aliasing claim.
"""
from dataclasses import asdict

from Verdict import runtime_query_transpose_values as predecessor
from Verdict import runtime_middle_exchange_values as middle
from Verdict import graph_to_lean as c
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_world import _ordinary
from Verdict import runtime_view_values as view
from Verdict import runtime_projection_values as projection
from Verdict import runtime_post_add_values as post
from Verdict.runtime_embedding_position_units import _list
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op


def render(sm, pm, lineages, validation, bound, execution_order):
    """Caller receipts and output facts are never accepted as authority."""
    try:
        _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed contiguous original source: {exc}') from exc


def _consumer(index, port):
    cell = view._consumer(index, port)
    return cell, _authenticate_cell(index, cell)


def _authenticate_cell(index, cell):
    _kwargs(cell.kwargs)
    node = projection._node(index, cell)
    if (op(cell) != 'FW_contiguous'
            or str(index.view.node_opname(node)).split('.')[-1] != op(cell)
            or node in getattr(index.view, 'collective_scopes', {})):
        raise ValueError('contiguous requires immediate original global opcode')
    auth = dict(source_writer=None, writer_ref=None)
    snapshot = getattr(index.view, '_collective_source', None)
    if snapshot is not None:
        from trainverify.runtime_source_authority import writer_export_id
        writer = _one((w for w in snapshot['writers'] if _same_typed(
            (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
             w['ref']['source_cid'], w['source_irname']), tuple(node))),
            'contiguous source writer missing/ambiguous')
        ref = writer['ref']
        if (ref['op'] != op(cell) or type(ref['call_instance']) is not int
                or ref['call_instance'] < 0 or writer['export_id'] != writer_export_id(ref)):
            raise ValueError('contiguous original writer/export/call mismatch')
        fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
        for key in ('inputs', 'outputs'):
            if not _same_typed(writer[key], [dict(zip(fields, r)) for r in getattr(cell, key)]):
                raise ValueError('contiguous writer ordered fullrefs mismatch')
        auth.update(source_writer=writer['export_id'], writer_ref=dict(ref))
    if not _same_typed(tuple(cell.node), tuple(node)):
        raise ValueError('contiguous original typed node identity mismatch')
    for method, refs in [('node_inputs', cell.inputs), ('node_outputs', cell.outputs)]:
        actual = [tuple(index.view.source_tensor(t)) for t in getattr(index.view, method)(node)]
        if not _same_typed(actual, [tuple(r) for r in refs]):
            raise ValueError('contiguous original ordered fullrefs mismatch')
    if len(cell.inputs) != 1 or len(cell.outputs) != 1:
        raise ValueError('contiguous original unary arity mismatch')
    return auth


def _unary(index, cell, producer):
    _authenticate_cell(index, cell)
    # Require the original producer, not only its serialized Port descriptor.
    raw_producer = index.raw[producer.endpoint.writer]
    originals = getattr(raw_producer, '_output_irs', None)
    inputs = getattr(cell, '_input_irs', None)
    outputs = getattr(cell, '_output_irs', None)
    if (originals is None or len(originals) != len(raw_producer.outputs)
            or any(ir is None for ir in originals)
            or inputs is None or len(inputs) != 1 or inputs[0] is None
            or outputs is None or len(outputs) != 1 or outputs[0] is None):
        raise ValueError('contiguous complete original producer/input/output metadata required')
    original = originals[list(map(tuple, raw_producer.outputs)).index(producer.endpoint.ref)]
    if (not _same_typed(post._port(index, producer.endpoint.ref, original), producer)
            or not _same_typed(post._port(index, producer.endpoint.ref, inputs[0]), producer)):
        raise ValueError('contiguous original producer/consumer metadata mismatch')
    if (type(original.parent.tid) is not int or type(inputs[0].parent.tid) is not int
            or not _same_typed(original.parent.tid, inputs[0].parent.tid)):
        raise ValueError('contiguous original producer/consumer parent identity mismatch')
    node = projection._node(index, cell)
    _parameters(index.view, node)
    x = post._port(index, cell.inputs[0], inputs[0])
    y = post._port(index, cell.outputs[0], outputs[0])
    if (not _same_typed(x, producer)
            or any(not _same_typed(p.endpoint.ref[:3], tuple(node)[:3]) for p in (x, y))
            or not _same_typed(y.endpoint.writer, tuple(node))):
        raise ValueError('contiguous original input/output fullref/owner/writer mismatch')
    if not _same_typed((y.parent_shape, y.bounds, y.endpoint.shape, y.value_part),
                       (x.parent_shape, x.bounds, x.endpoint.shape, x.value_part)):
        raise ValueError('contiguous original inherited geometry/value partition mismatch')
    return routes.Step(tuple(node), 'FW_contiguous', (x,), (y,))


def _kwargs(kw):
    if (type(kw) is not dict or set(kw) - {'__consts'}
            or ('__consts' in kw and not _same_typed(kw['__consts'], []))):
        raise ValueError('contiguous strict original kwargs mismatch')


def _parameters(source, node):
    # Inspect extractor output BEFORE _ordinary's ``params or []`` coercion.
    if (str(source.node_opname(node)).split('.')[-1] != 'FW_contiguous'
            or node in getattr(source, 'collective_scopes', {})
            or len(source.node_inputs(node)) != 1 or len(source.node_outputs(node)) != 1):
        raise ValueError('contiguous original opcode/global request/arity mismatch')
    _kwargs(source.node_kwargs(node))
    raw = c._get_node_params(source, node, num_parts=0)
    if raw is not None and not _same_typed(raw, []):
        raise ValueError('contiguous original empty params required')
    params, status = _ordinary(source, node, lambda *a, **k: raw)
    if status is not None or not _same_typed(params, []):
        raise ValueError('contiguous original normalized params mismatch')
    return params


def _read(source, label, step, order):
    nodes = source.nodes()
    i, node = _one(((i, n) for i, n in enumerate(nodes) if _same_typed(tuple(n), step.node)),
        'contiguous source writer missing/ambiguous')
    if step.op != 'FW_contiguous':
        raise ValueError('contiguous read step opcode mismatch')
    for method, ports in [('node_inputs', step.inputs), ('node_outputs', step.outputs)]:
        if not _same_typed([(tuple(source.source_tensor(t)), t.tid) for t in getattr(source, method)(node)],
                [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
            raise ValueError('contiguous original ordered fullrefs mismatch')
    schedule = order['execution_to_source']
    if (any(type(n) is not int for n in schedule) or sorted(schedule) != list(range(len(nodes)))):
        raise ValueError('contiguous incomplete original execution order')
    k = schedule.index(i)
    inp, out = step.inputs[0].endpoint.tid, step.outputs[0].endpoint.tid
    for source_index in schedule[k:]:
        if inp in {t.tid for t in source.node_outputs(nodes[source_index])}:
            raise ValueError('contiguous operand is written by selected node or suffix')
    params = _parameters(source, node)
    name, req = f'contiguousRead_{label}_{out}', f'{label}InputRequests'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {out} = t {inp} := by',
        f'  apply SourceContiguousRead.contiguous_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {req} ({req}.take {k}) ({req}.drop {k+1}) {label}Node_{i}',
        f'    {node.rank} {inp} {out} s t rfl ?_ rfl ?_ h',
        '  · calc',
        f'      {req} = {req}.take {k} ++ {req}.drop {k} := (List.take_append_drop {k} {req}).symm',
        '      _ = _ := rfl',
        f'  · change ∀ row ∈ {req}.drop {k}, {inp} ∉ row.1.outs',
        '    decide', f'#print axioms {name}']
    return proof, dict(theorem=name, world=label, op=step.op, node=list(step.node),
        source_index=i, execution_index=k, input_tids=[inp], output_tid=out,
        input_refs=[list(step.inputs[0].endpoint.ref)], output_refs=[list(step.outputs[0].endpoint.ref)],
        params=params, request='global', source_kwargs=dict(source.node_kwargs(node)),
        source_step=asdict(step), operand_nonwrite_source_indices=schedule[k:])


def _unit(prior, global_, locals_, names):
    if prior['layout'] != 'sharded':
        raise ValueError('contiguous unsupported predecessor layout')
    gx, gy = global_.inputs[0], global_.outputs[0]
    middle._contract(prior, gx, [s.inputs[0] for s in locals_])
    D, T = (prior['dimensions'][k] for k in ('D', 'T'))
    u, axis = prior['unit'], prior['gather_axis']
    name = f'contiguousUnitFacts_{gy.endpoint.tid}_{u}'
    row = dict(theorem=name, facts_theorem=name, family='FW_contiguous',
        predecessor=prior['facts_theorem'], unit=u, ranks=prior['ranks'], positions=prior['positions'],
        dimensions=dict(prior['dimensions']), layout=prior['layout'],
        input_gather_axis=axis, gather_axis=axis,
        global_shape=list(prior['global_shape']), local_shape=list(prior['local_shape']),
        sm_output_tid=gy.endpoint.tid, sm_output_ref=list(gy.endpoint.ref),
        pm_output_tids=[s.outputs[0].endpoint.tid for s in locals_],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_],
        source_step=asdict(global_), local_steps=[asdict(s) for s in locals_])
    middle._contract(row, gy, [s.outputs[0] for s in locals_])
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in locals_)
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {gy.endpoint.tid}).shape = {row["global_shape"]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {gy.endpoint.tid}) = allGatherPrimDimN {axis} {T} 0 {ys} := by',
        f'  have predecessor := {prior["facts_theorem"]} s p t q hs hp hvalues',
        '  rw [' + ', '.join([f'{names[global_.node]} s t hs',
            *[f'{names[s.node]} p q hp' for s in locals_]]) + ']',
        '  exact predecessor', f'#print axioms {name}']
    return proof, row


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, names, seen, identities = [], [], [], {}, {}, set()
    old = prior['frontier_units']
    for i, unit in enumerate(old):
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], unit['unit'])), 'contiguous DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (unit['ranks'], unit['positions'])):
            raise ValueError('contiguous source DP ownership/ordered ranks mismatch')
        g = middle._output(si, unit['source_step'])
        ps = [middle._output(pi, d) for d in unit['local_steps']]
        middle._contract(unit, g, ps)
        key = (g.endpoint.ref, unit['unit'], tuple(unit['ranks']))
        if key in identities:
            raise ValueError('contiguous duplicate original frontier identity')
        identities.add(key)
        gc, ga = _consumer(si, g)
        pcs = [_consumer(pi, p) for p in ps]
        global_ = _unary(si, gc, g)
        locals_ = [_unary(pi, c, p) for (c, _), p in zip(pcs, ps, strict=True)]
        for source, label, step, auth in [(sm, 'sm', global_, ga),
                *[(pm, 'pm', s, a) for s, (_, a) in zip(locals_, pcs, strict=True)]]:
            if step.node in seen:
                if label != 'sm' or not _same_typed(seen[step.node], step):
                    raise ValueError('contiguous duplicate/cross-unit source operation')
                continue
            proof, row = _read(source, label, step, order[label])
            row.update(**auth, unit=unit['unit'], frontier_index=i,
                input_metadata='present', output_metadata='present', input_parent_identity='both-present')
            proofs.extend(proof); reads.append(row)
            names[step.node] = row['theorem']; seen[step.node] = step
        proof, row = _unit(unit, global_, locals_, names)
        proofs.extend(proof); units.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent owns capture, receipt wiring, imports, assembly and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-contiguous-values-emitted-uncompiled',
        reads=reads, units=units, frontier_units=units, deferred_units=[],
        consumed_frontier_indices=list(range(len(old))), lean_bytes=len(text.encode()),
        deferred_stage='after-first-contiguous: AllToAll/view/downstream unproved',
        cost_scope='new contiguous fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
