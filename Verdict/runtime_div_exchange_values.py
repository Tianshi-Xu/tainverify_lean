"""Faithful post-division PM AA(3,1); generated Lean remains UNCOMPILED.

No SM softmax step is advanced. Fresh six-argument division authority owns the
complete ordered frontier and complete SM/PM/BW schedules.
"""
from dataclasses import asdict

from Verdict import runtime_div_values as predecessor
from Verdict import runtime_post_transpose_values as reverse
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_matmul_values as matmul
from Verdict import runtime_view_values as view
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op


def _boundary(index, cell, ports, ranks, j):
    if op(cell) != 'AllToAllPrim':
        raise ValueError('div-exchange requires original AllToAllPrim')
    return reverse._boundary(index, cell, ports, ranks, j)


def _read(source, step, order):
    proof, row = reverse._read(source, 'pm', step, order)
    name = f'divExchangeRead_pm_{step.outputs[0].endpoint.tid}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row.update(theorem=name, input_gather_axis=3, output_gather_axis=1)
    return proof, row


def _unit(old, global_, ports, steps, names):
    D, T, B = (old['dimensions'][k] for k in ('D', 'T', 'B'))
    _, heads, H, C = ports[0].endpoint.shape
    S, rem = divmod(heads, T)
    if rem or any(type(n) is not int or n <= 0 for n in (S, H, C)):
        raise ValueError('div-exchange nondivisible or nonpositive input geometry')
    u = old['unit']; g = global_.endpoint.tid
    name = f'divExchangeUnitFacts_{g}_{u}'
    row = dict(theorem=name, facts_theorem=name, predecessor=old['facts_theorem'],
        family='AllToAllPrim', unit=u, ranks=old['ranks'], positions=old['positions'],
        dimensions=dict(D=D, T=T, B=B, S=S, H=H, C=C), layout='sharded',
        input_gather_axis=3, gather_axis=1, output_gather_axis=1,
        global_shape=[B*D, S*T, H, C*T], local_shape=[B, S, H, C*T],
        input_shape=list(ports[0].endpoint.shape),
        sm_output_tid=g, sm_output_ref=list(global_.endpoint.ref),
        pm_output_tids=[s.outputs[0].endpoint.tid for s in steps],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in steps],
        input_refs=[list(p.endpoint.ref) for p in ports],
        source_step=old['source_step'], local_steps=[asdict(s) for s in steps])
    middle._contract(row, global_, [s.outputs[0] for s in steps])
    xs = _list(f'q {p.endpoint.tid}' for p in ports)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in steps)
    terms = _list(f'AllToAllSourceFaithful.tensor {T} {j} 3 1 {xs}' for j in range(T))
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {g}).shape = {row["global_shape"]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {g}) = allGatherPrimDimN 1 {T} 0 {ys} := by',
        f'  have predecessor := {old["facts_theorem"]} s p t q hs hp hvalues',
        f'  have outputs : {ys} = List.ofFn (fun dst : Fin {T} => AllToAllSourceFaithful.tensor {T} dst.val 3 1 {xs}) := by',
        f'    change {ys} = {terms}',
        '    exact '+_cons_equal([f'{names[s.node]} p q hp' for s in steps]),
        f'  exact SourceRank4ReverseExchange.axis3_output_facts {D} {u} {T} {B} {S} {H} {C} (t {g}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) rfl predecessor.2.1 predecessor.1 predecessor.2.2 outputs',
        f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Only original source arguments, never caller-provided predecessor facts."""
    _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed div-exchange original source: {exc}') from exc


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, deferred, frontier = [], [], [], [], []
    identities, names = set(), {}
    for i, old in enumerate(prior['frontier_units']):
        g = middle._output(si, old['source_step'])
        ports = [middle._output(pi, d) for d in old['local_steps']]
        middle._contract(old, g, ports)
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], old['unit'])), 'div-exchange DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (old['ranks'], old['positions'])):
            raise ValueError('div-exchange source DP ownership/ordered ranks mismatch')
        identity = (g.endpoint.ref, tuple(p.endpoint.ref for p in ports))
        if identity in identities:
            raise ValueError('div-exchange duplicate original frontier identity')
        identities.add(identity)
        cells = [view._consumer(pi, p) for p in ports]
        kinds = {op(c) for c in cells}
        if kinds == {'FW_matmul'}:
            if old['layout'] != 'replicated_within_dp' or old['gather_axis'] is not None:
                raise ValueError('div-exchange deferred boundary requires replicated None')
            _, gr = matmul._consumer(si, g, order['sm'])
            consumers = [matmul._consumer(pi, p, order['pm'])[1] for p in ports]
            if any(not _same_typed(r['port_positions'], gr['port_positions']) for r in consumers):
                raise ValueError('div-exchange deferred original ordered port mismatch')
            deferred.append(dict(unit=old['unit'], frontier_index=i, predecessor=old['facts_theorem'],
                source_boundary=old, global_first_consumer=gr, first_consumers=consumers,
                reason='first-original-FW_matmul-value-boundary-unproved', value_proved=False))
            frontier.append(old)
            continue
        if kinds != {'AllToAllPrim'}:
            raise ValueError('div-exchange unknown/mixed first forward frontier')
        if old['layout'] != 'sharded' or not _same_typed(old['gather_axis'], 3):
            raise ValueError('div-exchange requires sharded axis3 predecessor')
        steps = []
        for j, cell in enumerate(cells):
            step, coverage = _boundary(pi, cell, ports, old['ranks'], j)
            if step.node in names:
                raise ValueError('div-exchange duplicate/cross-unit original operation')
            proof, read = _read(pm, step, order['pm'])
            read.update(unit=old['unit'], frontier_index=i, **coverage)
            names[step.node] = read['theorem']
            proofs.extend(proof); reads.append(read); steps.append(step)
        proof, unit = _unit(old, g, ports, steps, names)
        unit['frontier_index'] = i
        for read in reads[-len(steps):]:
            read.update(dimensions=unit['dimensions'], layout=unit['layout'])
        proofs.extend(proof); units.append(unit); frontier.append(unit)
    text = '\n'.join(['-- UNCOMPILED: parent owns actual capture, caps, assembly and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-div-exchange-values-emitted-uncompiled', reads=reads, units=units,
        deferred_units=deferred, frontier_units=frontier, lean_bytes=len(text.encode()),
        deferred_stage='after-post-div-exchange: SM softmax/attention/downstream unproved',
        cost_scope='new division exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
