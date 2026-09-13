"""Original rank-four head exchanges on every projection frontier, UNCOMPILED.

Only AA reads/facts are new. Global views and residual carries remain intact;
ordinary transpose successors are inventoried, not consumed. Parent owns actual
capture, assembly, aggregate costs, original helper objects and kernel closure.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_projection_view_values as predecessor
from Verdict import runtime_softmax_exchange_values as inner
from Verdict import runtime_projection_exchange_values as channel
from Verdict import runtime_middle_exchange_values as middle
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build


_BACKENDS = {(4, 1, 2): inner, (4, 1, 3): channel, (4, 2, 1): middle}


def render(sm, pm, lineages, validation, bound, execution_order):
    """Exactly one fresh predecessor call with precisely the SAME six inputs."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError, ZeroDivisionError) as exc:
        raise ValueError(f'malformed head-exchange original source: {exc}') from exc


def _census(si, pi, g, ps):
    outgoing = [predecessor._outgoing(si, [g]), *[predecessor._outgoing(pi, [p]) for p in ps]]
    peers = predecessor._outgoing(pi, ps)  # deduplicated in original source order
    return dict(observed_consumer_ops=[[op(c) for c in cs] for cs in outgoing],
        sm_consumers=[list(c.node) for c in outgoing[0]], pm_consumers=[list(c.node) for c in peers],
        downstream_consumers=[dict(node=list(c.node), op=op(c), source_kwargs=dict(c.kwargs),
            source_inputs=[list(r) for r in c.inputs], source_outputs=[list(r) for r in c.outputs])
            for c in [*outgoing[0], *peers]])


def _frontiers(si, pi, lineages, bound, order, closed, owners):
    """Reauthenticate rank-three ancestry, then cross-bind the actual FW views.

    input_frontier is only a candidate record. The original predecessor gate
    rebuilds its producers and independently expands its carry/fork inventory.
    Its rank-three input contract is never applied to rank-four output records.
    No second render or caller-supplied proof hypothesis is used.
    """
    predecessor.frontier._cover(closed, owners)
    rows = closed['frontier_units']
    inputs = []; selected = []
    for i, old in enumerate(rows):
        cell = si.raw[tuple(old['source_step']['node'])]
        if op(cell) == 'FW_view':
            inputs.append(old['input_frontier']); selected.append(i)
        elif op(cell) == 'FW_multiref':
            inputs.append(old)
        else:
            raise ValueError('head-exchange original view/retained fork required')
    if (not _same_typed(closed['consumed_frontier_indices'], selected)
            or not _same_typed(closed['units'], [rows[i] for i in selected])
            or not _same_typed(closed['retained_units'], [r for i,r in enumerate(rows) if i not in selected])
            or not _same_typed(closed['deferred_units'], [])
            or any(not _same_typed(rows[i]['frontier_index'], i) for i in selected)):
        raise ValueError('head-exchange complete ordered view classification required')
    # These classifications come from original operations, not receipt labels.
    exchanged = [i for i,r in enumerate(inputs)
        if all(op(pi.raw[tuple(s['node'])]) == 'AllToAllPrim' for s in r['local_steps'])]
    ancestry = dict(frontier_units=inputs, units=[inputs[i] for i in exchanged],
        consumed_frontier_indices=exchanged,
        retained_units=[r for r in inputs if op(si.raw[tuple(r['source_step']['node'])]) == 'FW_multiref'],
        deferred_units=[r for r in inputs if all(op(pi.raw[tuple(s['node'])]) == 'ReduceScatterPrim' for s in r['local_steps'])])
    authenticated = predecessor._frontiers(si, pi, lineages, bound, order, ancestry, owners)
    result = []
    for i, (prior, g, ps, kinds, history) in enumerate(authenticated):
        old = rows[i]
        if i not in selected:
            result.append((old, g, ps)); continue
        if any(k != ['FW_view'] for k in kinds):
            raise ValueError('head-exchange complete original view cover required')
        global_ = predecessor._view(si, predecessor.view._consumer(si, g), g)
        locals_ = [predecessor._view(pi, predecessor.view._consumer(pi, p), p) for p in ps]
        parent = si.raw[global_.node]._output_irs[0].parent.tid
        if any(not _same_typed(pi.raw[s.node]._output_irs[0].parent.tid, parent) for s in locals_):
            raise ValueError('head-exchange SM/PM original view output parent mismatch')
        names = {}
        for index, label, step in [(si, 'sm', global_), *((pi, 'pm', s) for s in locals_)]:
            _, read = predecessor.view._read(index.view, label, step, order[label])
            names[step.node] = read['theorem'].replace('viewRead_', 'frontierProjectionViewRead_')
        _, fresh = predecessor.view._unit(dict(prior, slot=prior['source_output_slot'], theorem=prior['facts_theorem']),
            global_, locals_, names)
        name = fresh['theorem'].replace('viewUnitFacts_', 'frontierProjectionViewUnitFacts_')
        expected = dict(prior); expected.update(fresh)
        expected.update(theorem=name, facts_theorem=name, source_output_slot=0, slot=0,
            predecessor_facts=prior['facts_theorem'], input_frontier=prior, producer_history=history,
            frontier_index=i, layout='sharded', deferred_stage='after-projection-view: downstream original consumers unproved')
        expected.update(_census(si, pi, global_.outputs[0], [s.outputs[0] for s in locals_]))
        if not _same_typed(old, expected):
            raise ValueError('head-exchange complete original view/history/frontier descriptor mismatch')
        g, ps = global_.outputs[0], [s.outputs[0] for s in locals_]
        middle._contract(old, g, ps)
        result.append((old, g, ps))
    return result


def _original(index, port):
    cell = index.raw[port.endpoint.writer]
    predecessor.source.residual._identity(index, cell)
    if cell._output_irs is None or len(cell._output_irs) != len(cell.outputs):
        raise ValueError('head-exchange complete original producer metadata required')
    j = _one((j for j,r in enumerate(cell.outputs) if _same_typed(tuple(r), port.endpoint.ref)),
        'head-exchange original producer slot missing/ambiguous')
    ir = cell._output_irs[j]
    predecessor._edge(index, port, ir)
    return ir


def _boundary(index, cell, ports, ranks, j):
    """Strict present/raw/parent gate before a legacy rank-four constructor."""
    node = predecessor.source.residual._identity(index, cell)
    # Maintained nnScaler wrapper -> AllToAllAllToAllSingle.forward ->
    # all_to_all_single(itensor, idim, odim, ranks); backward swaps the axes.
    signature = getattr(getattr(cell, 'ir', None), 'signature', None)
    if type(signature) is not str or signature != 'nnscaler.runtime.adapter.nn.alltoall_alltoall':
        raise ValueError('head-exchange original AllToAll callable mismatch')
    if any(node in getattr(index.view, k, {}) for k in ('chunk_scopes', 'wred_scopes')):
        raise ValueError('head-exchange conflicting original collective scope')
    irs, outs = cell._input_irs, cell._output_irs
    if irs is None or len(irs) not in (1, len(ports)) or outs is None or len(outs) != 1:
        raise ValueError('head-exchange complete present original metadata required')
    originals = [_original(index, p) for p in ports]
    parents = [ir.parent.tid for ir in originals]
    if any(not _same_typed(parent, parents[0]) for parent in parents):
        raise ValueError('head-exchange original peer parent identity mismatch')
    for p in ports:
        if len(p.endpoint.shape) != 4 or p.value_part != (0, 1):
            raise ValueError('head-exchange rank-four full-value peers required')
    expected = (ports[j],) if len(irs) == 1 else ports
    for p, ir in zip(expected, irs, strict=True): predecessor._edge(index, p, ir)
    predecessor._raw(outs[0], 4)
    if not _same_typed(outs[0].parent.tid, parents[j]):
        raise ValueError('head-exchange original receiver output parent mismatch')
    scope = index.view.collective_scopes[node]
    if len(scope.params) != 2 or any(type(a) is not int for a in scope.params):
        raise ValueError('head-exchange typed original axes required')
    key = (len(ports[0].endpoint.shape), *scope.params)
    if key not in _BACKENDS:
        raise ValueError('head-exchange unsupported original rank/axes')
    backend = _BACKENDS[key]
    step, meta = backend._boundary(index, cell, ports, ranks, j)
    return step, backend, dict(meta, producer_metadata='all-peers', input_parent_identity=meta['input_metadata'])


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order, dict(sm=build(sm), pm=build(pm))):
        raise ValueError('head-exchange complete typed execution/inverse order mismatch')
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    authenticated = _frontiers(si, pi, lineages, bound, order, closed, validation._inputs[3]['config']['units'])
    proofs, reads, units, result, retained, consumed = [], [], [], [], [], []
    names = {}; seen = set()
    for i, (old, g, ps) in enumerate(authenticated):
        if old['source_step']['op'] == 'FW_multiref':
            result.append(old); retained.append(old); continue
        cells = predecessor._outgoing(pi, ps)
        if len(ps) <= 1 or len(cells) != len(ps) or any(op(c) != 'AllToAllPrim' for c in cells):
            raise ValueError('head-exchange complete original AllToAll receiver cover required')
        steps = []; backends = []
        for j, rank in enumerate(old['ranks']):
            cell = _one((c for c in cells if _same_typed(c.rank, rank)), 'head-exchange receiver missing/ambiguous')
            step, backend, meta = _boundary(pi, cell, ps, old['ranks'], j)
            if step.node in seen: raise ValueError('head-exchange duplicate/cross-DP receiver')
            seen.add(step.node)
            proof, read = channel._read(pm, step, order['pm'])
            name = read['theorem'].replace('projectionExchange', 'frontierHeadExchange')
            proofs.extend(s.replace(read['theorem'], name) for s in proof)
            read.update(theorem=name, unit=old['unit'], frontier_index=i, **meta)
            reads.append(read); names[step.node] = name; steps.append(step); backends.append(backend)
        if any(b is not backends[0] for b in backends) or any(s.gather_axis != old['gather_axis'] for s in steps):
            raise ValueError('head-exchange mixed original axis families/input layout')
        proof, fresh = backends[0]._unit(old, g, ps, steps, names)
        name = f'frontierHeadExchangeUnitFacts_{g.endpoint.tid}_{old["unit"]}_slot{old["source_output_slot"]}'
        proofs.extend(s.replace(fresh['theorem'], name) for s in proof)
        row = dict(old); row.update(fresh)
        shape = list(steps[0].outputs[0].endpoint.shape)
        row.update(theorem=name, facts_theorem=name, source_output_slot=old['source_output_slot'],
            pm_output_slots=[0 for _ in steps], slot=old['source_output_slot'], layout='sharded',
            dimensions=dict(D=old['dimensions']['D'], T=len(ps), **dict(zip(('B','S','H','C'), shape))),
            local_shape=shape, input_frontier=old, predecessor_facts=old['facts_theorem'], frontier_index=i,
            input_gather_axis=steps[0].gather_axis, output_gather_axis=steps[0].split_axis,
            deferred_stage='after-head-exchange: original transpose/downstream consumers unproved')
        outputs = [s.outputs[0] for s in steps]
        middle._contract(row, g, outputs)
        row.update(_census(si, pi, g, outputs))
        units.append(row); result.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, aggregate costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section', 'set_option maxHeartbeats 500000',
        *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-frontier-head-exchange-values-emitted-uncompiled', reads=reads, units=units,
        frontier_units=result, retained_units=retained, deferred_units=[], consumed_frontier_indices=consumed,
        lean_bytes=len(text.encode()), cost_scope='head exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
