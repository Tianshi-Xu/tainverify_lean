"""First post-attention query transpose12 source values, UNCOMPILED.

Only the fresh SAME six-argument query-matmul frontier supplies authority.
Parent owns query_transpose_values receipt wiring, imports and kernel closure.
No view, linear or later-step advancement is performed here.
"""
from dataclasses import asdict

from Verdict import runtime_query_matmul_values as predecessor
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_transpose_values as transpose
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
        raise ValueError(f'malformed query transpose original source: {exc}') from exc


def _consumer(index, port):
    cell = view._consumer(index, port)
    node = projection._node(index, cell)
    if (op(cell) != 'FW_transpose'
            or str(index.view.node_opname(node)).split('.')[-1] != op(cell)
            or node in getattr(index.view, 'collective_scopes', {})):
        raise ValueError('query transpose requires immediate original global transpose')
    auth = dict(source_writer=None, writer_ref=None)
    snapshot = getattr(index.view, '_collective_source', None)
    if snapshot is not None:
        from trainverify.runtime_source_authority import writer_export_id
        writer = _one((w for w in snapshot['writers'] if _same_typed(
            (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
             w['ref']['source_cid'], w['source_irname']), tuple(node))),
            'query transpose source writer missing/ambiguous')
        ref = writer['ref']
        if (ref['op'] != op(cell) or type(ref['call_instance']) is not int
                or ref['call_instance'] < 0 or writer['export_id'] != writer_export_id(ref)):
            raise ValueError('query transpose original writer/export/call mismatch')
        fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
        for key in ('inputs', 'outputs'):
            if not _same_typed(writer[key], [dict(zip(fields, r)) for r in getattr(cell, key)]):
                raise ValueError('query transpose writer ordered fullrefs mismatch')
        auth.update(source_writer=writer['export_id'], writer_ref=dict(ref))
    return cell, auth


def _transpose(index, cell, producer):
    # Require the original producer, not only its serialized Port descriptor.
    raw_producer = index.raw[producer.endpoint.writer]
    originals = getattr(raw_producer, '_output_irs', None)
    inputs = getattr(cell, '_input_irs', None)
    outputs = getattr(cell, '_output_irs', None)
    if (originals is None or len(originals) != len(raw_producer.outputs)
            or any(ir is None for ir in originals)
            or inputs is None or len(inputs) != 1 or inputs[0] is None
            or outputs is None or len(outputs) != 1 or outputs[0] is None):
        raise ValueError('query transpose complete original producer/input/output metadata required')
    original = originals[list(map(tuple, raw_producer.outputs)).index(producer.endpoint.ref)]
    if (not _same_typed(post._port(index, producer.endpoint.ref, original), producer)
            or not _same_typed(post._port(index, producer.endpoint.ref, inputs[0]), producer)):
        raise ValueError('query transpose original producer/consumer metadata mismatch')
    if (type(original.parent.tid) is not int or type(inputs[0].parent.tid) is not int
            or not _same_typed(original.parent.tid, inputs[0].parent.tid)):
        raise ValueError('query transpose original producer/consumer parent identity mismatch')
    return transpose._transpose(index, cell, producer)


def _read(source, label, step, order):
    proof, row = transpose._read(source, label, step, order)
    name = f'queryTransposeRead_{label}_{step.outputs[0].endpoint.tid}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row['theorem'] = name
    return proof, row


def _unit(prior, global_, locals_, names):
    if prior['layout'] != 'sharded' or not _same_typed(prior['gather_axis'], 2):
        raise ValueError('query transpose unsupported predecessor layout/axis')
    gx, gy = global_.inputs[0], global_.outputs[0]
    middle._contract(prior, gx, [s.inputs[0] for s in locals_])
    D, T, B = (prior['dimensions'][k] for k in ('D', 'T', 'B'))
    _, S, H, C = locals_[0].inputs[0].endpoint.shape
    u = prior['unit']
    if any(type(n) is not int or n <= 0 for n in (D, T, B, S, H, C)):
        raise ValueError('query transpose positive integer geometry required')
    name = f'queryTransposeUnitFacts_{gy.endpoint.tid}_{u}'
    row = dict(theorem=name, facts_theorem=name, family='FW_transpose',
        predecessor=prior['facts_theorem'], unit=u, ranks=prior['ranks'], positions=prior['positions'],
        dimensions=dict(D=D, T=T, B=B, S=S, H=H, C=C), layout='sharded',
        input_gather_axis=2, gather_axis=1, axes=[1, 2],
        global_shape=list(transpose._swap(prior['global_shape'])),
        local_shape=list(transpose._swap(prior['local_shape'])), input_shape=prior['local_shape'],
        sm_output_tid=gy.endpoint.tid, sm_output_ref=list(gy.endpoint.ref),
        pm_output_tids=[s.outputs[0].endpoint.tid for s in locals_],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_],
        source_step=asdict(global_), local_steps=[asdict(s) for s in locals_])
    middle._contract(row, gy, [s.outputs[0] for s in locals_])
    xs = _list(f'q {s.inputs[0].endpoint.tid}' for s in locals_)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in locals_)
    pairs = 'List.Forall₂.nil'
    for step in reversed(locals_):
        pairs = f'List.Forall₂.cons ({names[step.node]} p q hp) ({pairs})'
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {gy.endpoint.tid}).shape = {row["global_shape"]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {gy.endpoint.tid}) = allGatherPrimDimN 1 {T} 0 {ys} := by',
        f'  have predecessor := {prior["facts_theorem"]} s p t q hs hp hvalues',
        f'  have localReads : List.Forall₂ (fun x y => y = transposeAxes 1 2 x) {xs} {ys} :=',
        f'    {pairs}',
        f'  exact TrainVerify.Denote.source_transpose12_query_unit_output_reconstruct {D} {T} {B} {S} {H} {C} {u}',
        f'    (t {gx.endpoint.tid}) (t {gy.endpoint.tid}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        f'    predecessor.1 rfl predecessor.2.1 predecessor.2.2 ({names[global_.node]} s t hs) localReads',
        f'#print axioms {name}']
    return proof, row


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, names, seen, identities = [], [], [], {}, {}, set()
    old = prior['frontier_units']
    for i, unit in enumerate(old):
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], unit['unit'])), 'query transpose DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (unit['ranks'], unit['positions'])):
            raise ValueError('query transpose source DP ownership/ordered ranks mismatch')
        g = middle._output(si, unit['source_step'])
        ps = [middle._output(pi, d) for d in unit['local_steps']]
        middle._contract(unit, g, ps)
        key = (g.endpoint.ref, unit['unit'], tuple(unit['ranks']))
        if key in identities:
            raise ValueError('query transpose duplicate original frontier identity')
        identities.add(key)
        gc, ga = _consumer(si, g)
        pcs = [_consumer(pi, p) for p in ps]
        global_ = _transpose(si, gc, g)
        locals_ = [_transpose(pi, c, p) for (c, _), p in zip(pcs, ps, strict=True)]
        for source, label, step, auth in [(sm, 'sm', global_, ga),
                *[(pm, 'pm', s, a) for s, (_, a) in zip(locals_, pcs, strict=True)]]:
            if step.node in seen:
                if label != 'sm' or not _same_typed(seen[step.node], step):
                    raise ValueError('query transpose duplicate/cross-unit source operation')
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
    return text, dict(status='source-query-transpose-values-emitted-uncompiled',
        reads=reads, units=units, frontier_units=units, deferred_units=[],
        consumed_frontier_indices=list(range(len(old))), lean_bytes=len(text.encode()),
        deferred_stage='after-first-query-transpose12: view/linear/downstream unproved',
        cost_scope='new query transpose fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
