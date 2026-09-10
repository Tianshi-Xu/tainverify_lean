"""First original FW_div values under fresh six-argument source authority.

Generated Lean is UNCOMPILED. The Denote algebra is total at zero; original
source admission still requires positive integral divisors. No Torch claim.
"""
from copy import deepcopy
from dataclasses import asdict
from math import isfinite

from Verdict import graph_to_lean as compiler
from Verdict import runtime_matmul_exchange_values as predecessor
from Verdict import runtime_matmul_values as matmul
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_projection_values as projection
from Verdict import runtime_post_add_values as post
from Verdict import runtime_view_values as view
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_world import _ordinary


def _lossless_nat(kwargs):
    """Prove representability before conversion, independently of the getter.

    A Python int is exact; a finite integral float has an exact integer ratio.
    Zero is representable but remains rejected by the unchanged _ordinary.
    """
    consts = kwargs.get('__consts')
    if (type(consts) not in (list, tuple) or len(consts) != 1
            or type(consts[0]) not in (int, float)):
        raise ValueError('div unsupported lossless raw scalar Nat representation')
    raw = consts[0]
    if type(raw) is float:
        if not isfinite(raw):
            raise ValueError('div unsupported lossless nonfinite raw scalar')
        numerator, denominator = raw.as_integer_ratio()
        if denominator != 1:
            raise ValueError('div unsupported lossless fractional raw scalar')
    else:
        numerator = raw
    if numerator < 0:
        raise ValueError('div unsupported lossless negative raw scalar')
    return numerator


def _scalar(source, node):
    raw_nat = _lossless_nat(dict(source.node_kwargs(node)))
    params, status = _ordinary(source, node, compiler._get_node_params)
    if status is not None or not _same_typed(params, [raw_nat]):
        raise ValueError('div lossless raw scalar to normalized Nat binding mismatch')
    return params[0]


def _div(index, cell, producer):
    _lossless_nat(dict(cell.kwargs))
    node = projection._node(index, cell)
    c = _scalar(index.view, node)
    if (op(cell) != 'FW_div' or str(index.view.node_opname(node)).split('.')[-1] != 'FW_div'
            or len(cell.inputs) != 1 or len(cell.outputs) != 1
            or node in getattr(index.view, 'collective_scopes', {})):
        raise ValueError('div original opcode/arity/global request mismatch')
    for method, refs in [('node_inputs', cell.inputs), ('node_outputs', cell.outputs)]:
        if not _same_typed([tuple(index.view.source_tensor(t)) for t in getattr(index.view, method)(node)],
                [tuple(r) for r in refs]):
            raise ValueError('div original ordered fullrefs mismatch')
    ins, outs = getattr(cell, '_input_irs', None), getattr(cell, '_output_irs', None)
    if ins is None or outs is None or len(ins) != 1 or len(outs) != 1:
        raise ValueError('div requires complete paired original metadata')
    x = post._port(index, cell.inputs[0], ins[0]); y = post._port(index, cell.outputs[0], outs[0])
    if (not _same_typed(x, producer) or any(p.endpoint.ref[:3] != tuple(node)[:3] for p in (x, y))
            or y.endpoint.writer != tuple(node)):
        raise ValueError('div producer consumer paired metadata/owner/writer mismatch')
    if (len(x.endpoint.shape) != 4 or y.endpoint.shape != x.endpoint.shape
            or not _same_typed((y.parent_shape, y.bounds, y.value_part),
                (x.parent_shape, x.bounds, x.value_part))):
        raise ValueError('div input-derived output parent/bounds/value mismatch')
    auth = dict(source_writer=None, writer_ref=None, scalar_nat=c,
        source_kwargs=deepcopy(dict(cell.kwargs)), input_metadata='present', output_metadata='present')
    snapshot = getattr(index.view, '_collective_source', None)
    if snapshot is not None:
        from trainverify.runtime_source_authority import writer_export_id
        writer = _one((w for w in snapshot['writers'] if _same_typed(
            (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
             w['ref']['source_cid'], w['source_irname']), tuple(node))), 'div source writer missing/ambiguous')
        ref = writer['ref']
        if (ref['op'] != 'FW_div' or type(ref['call_instance']) is not int or ref['call_instance'] < 0
                or writer['export_id'] != writer_export_id(ref)):
            raise ValueError('div original writer/export/call mismatch')
        fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
        for key in ('inputs', 'outputs'):
            if not _same_typed(writer[key], [dict(zip(fields, r)) for r in getattr(cell, key)]):
                raise ValueError('div source writer ordered fullrefs mismatch')
        auth.update(source_writer=writer['export_id'], writer_ref=deepcopy(ref))
    return routes.Step(tuple(node), 'FW_div', (x,), (y,)), auth


def _read(source, label, step, order):
    nodes = source.nodes()
    i, node = _one(((i, n) for i, n in enumerate(nodes) if tuple(n) == step.node),
        'div source writer missing/ambiguous')
    for method, ports in [('node_inputs', step.inputs), ('node_outputs', step.outputs)]:
        if not _same_typed([(tuple(source.source_tensor(t)), t.tid) for t in getattr(source, method)(node)],
                [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
            raise ValueError('div read original ordered fullrefs mismatch')
    if (step.op != 'FW_div' or str(source.node_opname(node)).split('.')[-1] != 'FW_div'
            or len(step.inputs) != 1 or len(step.outputs) != 1
            or node in getattr(source, 'collective_scopes', {})):
        raise ValueError('div read opcode/arity/global request mismatch')
    c = _scalar(source, node); k = order['execution_to_source'].index(i)
    inp = step.inputs[0].endpoint.tid; out = step.outputs[0].endpoint.tid
    for j in order['execution_to_source'][k:]:
        if inp in {t.tid for t in source.node_outputs(nodes[j])}:
            raise ValueError('div operand is written by selected node or suffix')
    name = f'divRead_{label}_{out}'; req = f'{label}InputRequests'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {out} = fw_div ({c} : Scalar) (t {inp}) := by',
        f'  apply SourceDivRead.div_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {req} ({req}.take {k}) ({req}.drop {k+1}) {label}Node_{i}',
        f'    {node.rank} {c} {inp} {out} s t rfl ?_ rfl ?_ h',
        '  · calc',
        f'      {req} = {req}.take {k} ++ {req}.drop {k} := (List.take_append_drop {k} {req}).symm',
        '      _ = _ := rfl',
        f'  · change ∀ row ∈ {req}.drop {k}, {inp} ∉ row.1.outs',
        '    decide', f'#print axioms {name}']
    return proof, dict(theorem=name, world=label, op='FW_div', node=list(step.node),
        source_index=i, execution_index=k, input_tids=[inp], output_tid=out,
        input_refs=[list(step.inputs[0].endpoint.ref)], output_refs=[list(step.outputs[0].endpoint.ref)],
        params=[c], scalar_nat=c, request='global', source_kwargs=deepcopy(dict(source.node_kwargs(node))),
        source_step=asdict(step), operand_nonwrite_source_indices=order['execution_to_source'][k:])


def _unit(old, global_, locals_, names, c):
    D, T, B = (old['dimensions'][k] for k in ('D', 'T', 'B'))
    _, H, Q, C = old['local_shape']; u = old['unit']; out = global_.outputs[0].endpoint
    if old['global_shape'] != [B*D, H, Q, C*T] or len(locals_) != T:
        raise ValueError('div full axis3 shape contract mismatch')
    name = f'divUnitFacts_{out.tid}_{u}'
    row = dict(theorem=name, facts_theorem=name, predecessor=old['facts_theorem'], family='FW_div',
        unit=u, ranks=old['ranks'], positions=old['positions'], layout='sharded', gather_axis=3,
        input_gather_axis=3, output_gather_axis=3, scalar_nat=c,
        dimensions=dict(D=D, T=T, B=B, H=H, Q=Q, C=C),
        global_shape=[B*D, H, Q, C*T], local_shape=[B, H, Q, C],
        sm_output_ref=list(out.ref), sm_output_tid=out.tid,
        input_refs=[list(s.inputs[0].endpoint.ref) for s in locals_],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_],
        pm_output_tids=[s.outputs[0].endpoint.tid for s in locals_],
        source_step=asdict(global_), local_steps=[asdict(s) for s in locals_])
    middle._contract(row, global_.outputs[0], [s.outputs[0] for s in locals_])
    xs = _list(f'q {s.inputs[0].endpoint.tid}' for s in locals_)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in locals_)
    terms = _list(f'fw_div ({c} : Scalar) (q {s.inputs[0].endpoint.tid})' for s in locals_)
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {out.tid}).shape = {row["global_shape"]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {out.tid}) = allGatherPrimDimN 3 {T} 0 {ys} := by',
        f'  have predecessor := {old["facts_theorem"]} s p t q hs hp hvalues',
        f'  have outputs : {ys} = List.map (fw_div ({c} : Scalar)) {xs} := by',
        f'    change {ys} = {terms}',
        '    exact '+_cons_equal([f'{names[s.node]} p q hp' for s in locals_]),
        f'  exact TrainVerify.Denote.source_div_unit_output_reconstruct ({c} : Scalar) {D} {T} {B} {H} {Q} {C} {u}',
        f'    (t {global_.inputs[0].endpoint.tid}) (t {out.tid}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        '    predecessor.1 rfl predecessor.2.1 predecessor.2.2',
        f'    ({names[global_.node]} s t hs) outputs', f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh SAME six arguments; predecessor receipts are not a public input."""
    _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed div original source: {exc}') from exc


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, deferred, frontier = [], [], [], [], []
    identities, names, emitted = set(), {}, {}
    for i, old in enumerate(prior['frontier_units']):
        g = middle._output(si, old['source_step'])
        ports = [middle._output(pi, d) for d in old['local_steps']]
        middle._contract(old, g, ports)
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], old['unit'])), 'div source DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (old['ranks'], old['positions'])):
            raise ValueError('div source DP ownership/ordered ranks mismatch')
        identity = (g.endpoint.ref, tuple(p.endpoint.ref for p in ports))
        if identity in identities: raise ValueError('div duplicate original frontier identity')
        identities.add(identity)
        gc = view._consumer(si, g); cells = [view._consumer(pi, p) for p in ports]
        kinds = {op(c) for c in (gc, *cells)}
        if kinds == {'FW_matmul'}:
            _, gr = matmul._consumer(si, g, order['sm'])
            consumers = [matmul._consumer(pi, p, order['pm'])[1] for p in ports]
            if any(not _same_typed(r['port_positions'], gr['port_positions']) for r in consumers):
                raise ValueError('div deferred original ordered port mismatch')
            deferred.append(dict(unit=old['unit'], frontier_index=i, predecessor=old['facts_theorem'],
                source_boundary=old, global_first_consumer=gr, first_consumers=consumers,
                reason='first-original-FW_matmul-value-boundary-unproved', value_proved=False))
            frontier.append(old); continue
        if kinds != {'FW_div'}: raise ValueError('div unknown/mixed first forward frontier')
        if old['layout'] != 'sharded' or not _same_typed(old['gather_axis'], 3):
            raise ValueError('div requires sharded axis3 predecessor')
        global_, ga = _div(si, gc, g)
        pairs = [_div(pi, c, p) for c, p in zip(cells, ports, strict=True)]
        if any(a['scalar_nat'] != ga['scalar_nat'] for _, a in pairs):
            raise ValueError('div independently authenticated SM/PM scalar mismatch')
        locals_ = [s for s, _ in pairs]
        for source, label, step, auth in [(sm, 'sm', global_, ga), *[(pm, 'pm', s, a) for s, a in pairs]]:
            if step.node in names:
                if label != 'sm' or not _same_typed(emitted[step.node], (asdict(step), auth)):
                    raise ValueError('div duplicate/cross-unit source operation')
                continue
            proof, row = _read(source, label, step, order[label])
            row.update(**auth, unit=old['unit'], frontier_index=i)
            names[step.node] = row['theorem']; emitted[step.node] = (asdict(step), auth)
            proofs.extend(proof); reads.append(row)
        proof, unit = _unit(old, global_, locals_, names, ga['scalar_nat'])
        unit['frontier_index'] = i
        proofs.extend(proof); units.append(unit); frontier.append(unit)
    text = '\n'.join(['-- UNCOMPILED: parent owns actual capture, caps, assembly and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-div-values-emitted-uncompiled', reads=reads, units=units,
        deferred_units=deferred, frontier_units=frontier, lean_bytes=len(text.encode()),
        deferred_stage='after-first-source-div: attention/softmax/downstream unproved',
        cost_scope='new division fragment only; excludes predecessors, frame and imports',
        scalar_scope='positive integral source admission; total Denote algebra at zero; not Torch refinement',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
