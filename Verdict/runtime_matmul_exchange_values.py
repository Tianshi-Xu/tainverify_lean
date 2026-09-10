"""Post-matmul faithful AA(1,3) source checkpoint; Lean is UNCOMPILED.

The global score remains the predecessor matmul, not a later SM division.
Replicated missing-operand matmul boundaries retain their exact old facts.
"""
from dataclasses import asdict

from Verdict import runtime_matmul_values as predecessor
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_projection_exchange_values as exchange
from Verdict import runtime_projection_values as projection
from Verdict import runtime_view_values as view
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op


def _boundary(index, cell, ports, ranks, j):
    """Re-use the input-derived AA geometry, adding exact writer fullrefs."""
    step, coverage = exchange._boundary(index, cell, ports, ranks, j)
    if (step.gather_axis, step.split_axis) != (1, 3) or len(ports[0].parent_shape) != 4:
        raise ValueError('matmul-exchange requires rank4 AA(1,3)')
    writer = _one((w for w in index.view._collective_source['writers']
        if w['export_id'] == step.source_writer), 'matmul-exchange source writer missing/ambiguous')
    call = writer['ref']['call_instance']
    if type(call) is not int or call < 0:
        raise ValueError('matmul-exchange original call identity mismatch')
    fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
    for key in ('inputs', 'outputs'):
        if not _same_typed(writer[key], [dict(zip(fields, r)) for r in getattr(cell, key)]):
            raise ValueError('matmul-exchange source writer ordered fullrefs mismatch')
    coverage['writer_ref'] = dict(writer['ref'])
    return step, coverage


def _read(pm, step, order):
    proof, row = exchange._read(pm, step, order)
    name = f'matmulExchangeRead_pm_{step.outputs[0].endpoint.tid}'
    proof = [s.replace(row['theorem'], name) for s in proof]
    row.update(theorem=name, input_shapes=[list(p.endpoint.shape) for p in step.inputs],
        output_shape=list(step.outputs[0].endpoint.shape), output_gather_axis=3)
    return proof, row


def _unit(prior, global_, ports, steps, names):
    middle._contract(prior, global_, ports)
    if prior['layout'] != 'sharded' or not _same_typed(prior['gather_axis'], 1):
        raise ValueError('matmul-exchange requires sharded axis1 predecessor')
    D, T, B = (prior['dimensions'][k] for k in ('D', 'T', 'B'))
    _, S, H, CT = ports[0].endpoint.shape
    C, remainder = divmod(CT, T)
    if remainder or C <= 0:
        raise ValueError('matmul-exchange nondivisible positive actual split')
    if len(steps) != T or any((s.gather_axis, s.split_axis) != (1, 3) for s in steps):
        raise ValueError('matmul-exchange incomplete/mixed actual outputs')
    u = prior['unit']; g = global_.endpoint.tid
    name = f'matmulExchangeUnitFacts_{g}_{u}'
    row = dict(theorem=name, facts_theorem=name, predecessor=prior['facts_theorem'],
        family='AllToAllPrim', unit=u, ranks=prior['ranks'], positions=prior['positions'],
        layout='sharded', input_gather_axis=1, gather_axis=3, output_gather_axis=3, split_axis=3,
        dimensions=dict(D=D, T=T, B=B, S=S, H=H, C=C),
        global_shape=[B*D, S*T, H, C*T], input_shape=[B, S, H, C*T], local_shape=[B, S*T, H, C],
        sm_output_tid=g, sm_output_ref=list(global_.endpoint.ref), source_step=prior['source_step'],
        input_refs=[list(p.endpoint.ref) for p in ports],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in steps],
        pm_output_tids=[s.outputs[0].endpoint.tid for s in steps], local_steps=[asdict(s) for s in steps])
    middle._contract(row, global_, [s.outputs[0] for s in steps])
    xs = _list(f'q {p.endpoint.tid}' for p in ports)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in steps)
    terms = _list(f'AllToAllSourceFaithful.tensor {T} {j} 1 3 {xs}' for j in range(T))
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {g}).shape = {row["global_shape"]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {g}) = allGatherPrimDimN 3 {T} 0 {ys} := by',
        f'  have predecessor := {prior["facts_theorem"]} s p t q hs hp hvalues',
        f'  have outputs : {ys} = List.ofFn (fun dst : Fin {T} => AllToAllSourceFaithful.tensor {T} dst.val 1 3 {xs}) := by',
        f'    change {ys} = {terms}',
        '    exact '+_cons_equal([f'{names[s.node]} p q hp' for s in steps]),
        f'  exact SourceRank4Exchange.axis1_output_facts {D} {u} {T} {B} {S} {H} {C} (t {g}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) rfl predecessor.2.1 predecessor.1 predecessor.2.2 outputs',
        f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Always obtain fresh matmul facts under the SAME six-argument authority."""
    _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed matmul-exchange original source: {exc}') from exc


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, deferred, frontier = [], [], [], [], []
    identities, seen, names = set(), set(), {}
    for i, old in enumerate(prior['frontier_units']):
        global_ = middle._output(si, old['source_step'])
        ports = [middle._output(pi, d) for d in old['local_steps']]
        middle._contract(old, global_, ports)
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], old['unit'])), 'matmul-exchange DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (old['ranks'], old['positions'])):
            raise ValueError('matmul-exchange DP ownership/ordered ranks mismatch')
        identity = (global_.endpoint.ref, tuple(p.endpoint.ref for p in ports))
        if identity in identities:
            raise ValueError('matmul-exchange duplicate original frontier identity')
        identities.add(identity)
        cells = [view._consumer(pi, p) for p in ports]
        kinds = {op(c) for c in cells}
        if kinds == {'FW_matmul'}:
            # Deferral proves no new value and preserves any authenticated old
            # layout verbatim (in particular replicated V / gather_axis=None).
            _, gr = predecessor._consumer(si, global_, order['sm'])
            consumers = [predecessor._consumer(pi, p, order['pm'])[1] for p in ports]
            if any(not _same_typed(r['port_positions'], gr['port_positions']) for r in consumers):
                raise ValueError('matmul-exchange deferred original ordered port mismatch')
            deferred.append(dict(unit=old['unit'], frontier_index=i, predecessor=old['facts_theorem'],
                source_boundary=old, global_first_consumer=gr, first_consumers=consumers,
                reason='first-original-FW_matmul-value-boundary-unproved', value_proved=False))
            frontier.append(old)
            continue
        if kinds != {'AllToAllPrim'}:
            raise ValueError('matmul-exchange unknown/mixed first forward frontier')
        if old['layout'] != 'sharded' or not _same_typed(old['gather_axis'], 1):
            raise ValueError('matmul-exchange requires sharded axis1 predecessor')
        steps = []; start = len(reads)
        for j, cell in enumerate(cells):
            step, coverage = _boundary(pi, cell, ports, old['ranks'], j)
            if step.node in seen:
                raise ValueError('matmul-exchange duplicate/cross-unit consumer')
            seen.add(step.node)
            proof, read = _read(pm, step, order['pm'])
            read.update(unit=old['unit'], frontier_index=i, **coverage)
            proofs.extend(proof); reads.append(read); steps.append(step); names[step.node] = read['theorem']
        proof, unit = _unit(old, global_, ports, steps, names)
        unit['frontier_index'] = i
        for read in reads[start:]:
            read.update(dimensions=unit['dimensions'], layout=unit['layout'])
        proofs.extend(proof); units.append(unit); frontier.append(unit)
    text = '\n'.join(['-- UNCOMPILED: parent owns actual capture, caps, assembly and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-matmul-exchange-values-emitted-uncompiled', reads=reads, units=units,
        deferred_units=deferred, frontier_units=frontier, lean_bytes=len(text.encode()),
        deferred_stage='after-post-matmul-exchange: SM division/attention/downstream unproved',
        cost_scope='new matmul exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
