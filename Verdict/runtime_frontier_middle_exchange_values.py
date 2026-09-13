"""Original K AA(2,1) frontier fragment, UNCOMPILED.

Retains the SM endpoint and the complete mixed frontier. No matmul values,
canonical assembly, kernel completion or Torch refinement are claimed.
"""
from Verdict import runtime_frontier_post_transpose_values as predecessor
from Verdict import runtime_middle_exchange_values as backend
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build
from Verdict.runtime_embedding_units import _one


_view = predecessor._view
_head = predecessor._head


def render(sm, pm, lineages, validation, bound, execution_order):
    """Exactly one public predecessor call with the SAME six caller objects."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError, ZeroDivisionError) as exc:
        raise ValueError(f'malformed frontier middle-exchange original source: {exc}') from exc


def _frontiers(sm, pm, si, pi, lineages, validation, bound, order, closed):
    """Reconstruct the earlier-stage contracts from original source + history.

    Stage outputs (especially replicated V) are not sharded transpose inputs.
    Peel candidate history to the view boundary, then use the source-bound
    constructors in order. Their branch/DP/carry inventory is independent of the
    candidate classifications. The accepted retained alias constructor also
    binds complete proof names and provenance, not just endpoint shapes.
    """
    views = []
    for row in closed['frontier_units']:
        current = row; seen = set()
        while op(si.raw[tuple(current['source_step']['node'])]) != 'FW_multiref':
            if id(current) in seen:
                raise ValueError('middle-exchange cyclic candidate history')
            seen.add(id(current))
            if (op(si.raw[tuple(current['source_step']['node'])]) == 'FW_view'
                    and all(op(pi.raw[tuple(s['node'])]) == 'FW_view' for s in current['local_steps'])):
                break
            current = current['input_frontier']
        views.append(current)
    selected = [i for i,r in enumerate(views) if op(si.raw[tuple(r['source_step']['node'])]) == 'FW_view']
    candidate = dict(frontier_units=views, units=[views[i] for i in selected],
        consumed_frontier_indices=selected, retained_units=[r for i,r in enumerate(views) if i not in selected],
        deferred_units=[])
    _, head = _head._render(sm, pm, lineages, validation, bound, order, candidate)
    _, first = predecessor.predecessor._render(sm, pm, lineages, validation, bound, order, head)
    _, expected = predecessor._render(sm, pm, lineages, validation, bound, order, first)
    if not _same_typed(closed, expected):
        raise ValueError('middle-exchange complete original post-transpose/history/frontier mismatch')
    return closed['frontier_units']


def _boundary(index, cell, ports, ranks, j):
    originals = [predecessor.predecessor._producer(index, ref) for ref in cell.inputs]
    if not _same_typed(tuple(ports), tuple(originals)):
        raise ValueError('middle-exchange complete original ordered peer descriptors mismatch')
    actual, selected, coverage = _head._boundary(index, cell, ports, ranks, j)
    if selected is not backend:
        raise ValueError('middle-exchange only original AA(2,1) is consumable')
    return actual, coverage


def _read(index, label, step, order):
    actual, coverage = _boundary(index, index.raw[step.node], step.inputs, step.ranks, step.local_index)
    if label != 'pm' or not _same_typed(actual, step) or not _same_typed(order, build(index.view)):
        raise ValueError('middle-exchange original step/full schedule mismatch')
    proof, row = backend._read(index.view, actual, order)
    row.update(coverage, source_signature=index.raw[step.node].ir.signature)
    return proof, row


def _unconsumed(old, globals_, cells):
    """Classify only after source authentication; unknown is never a skip."""
    replica = (old['layout'] == 'replicated_within_dp' and old['gather_axis'] is None
        and len(cells) == len(old['ranks']) and len(globals_) == 1
        and all(s['op'] == 'AllGatherPrim' for s in old['local_steps'])
        and all(op(c) == 'FW_matmul' for c in [*globals_, *cells]))
    return 'retained' if replica else 'deferred'


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order, dict(sm=build(sm), pm=build(pm))):
        raise ValueError('middle-exchange complete typed execution/inverse order mismatch')
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, result, retained, deferred, consumed = [], [], [], [], [], [], []
    names = {}; seen = set()
    authenticated = _frontiers(sm, pm, si, pi, lineages, validation, bound, order, closed)
    for i, old in enumerate(authenticated):
        g = predecessor.predecessor._producer(si, old['sm_output_ref'])
        ps = [predecessor.predecessor._producer(pi, ref) for ref in old['pm_output_refs']]
        if op(si.raw[tuple(old['source_step']['node'])]) == 'FW_multiref':
            result.append(old); retained.append(old); continue
        backend._contract(old, g, ps)  # includes replicated-within-DP, never sharded-only for V
        cells = _view.column._consumers(pi, ps)
        if not cells or any(op(c) != 'AllToAllPrim' for c in cells):
            result.append(old)
            classification = _unconsumed(old, _view.column._consumers(si, [g]), cells)
            (retained if classification == 'retained' else deferred).append(old)
            continue
        if len(ps) <= 1 or len(cells) != len(ps):
            raise ValueError('middle-exchange complete original receiver cover required')
        steps = []
        for j, rank in enumerate(old['ranks']):
            cell = _one((c for c in cells if _same_typed(c.rank, rank)), 'middle-exchange receiver missing/ambiguous')
            step, _ = _boundary(pi, cell, ps, old['ranks'], j)
            if step.node in seen:
                raise ValueError('middle-exchange duplicate/cross-unit original receiver')
            seen.add(step.node)
            proof, read = _read(pi, 'pm', step, order['pm'])
            name = read['theorem'].replace('middleExchangeRead_', 'frontierMiddleExchangeRead_')
            proofs.extend(s.replace(read['theorem'], name) for s in proof)
            read.update(theorem=name, frontier_index=i, unit=old['unit'])
            reads.append(read); names[step.node] = name; steps.append(step)
        proof, row = backend._unit(old, g, ps, steps, names)
        name = f'frontierMiddleExchangeUnitFacts_{g.endpoint.tid}_{old["unit"]}_slot{old["source_output_slot"]}'
        proofs.extend(s.replace(row['theorem'], name) for s in proof)
        shape = list(steps[0].outputs[0].endpoint.shape)
        row.update(theorem=name, facts_theorem=name, source_output_slot=old['source_output_slot'],
            slot=old['source_output_slot'], pm_output_slots=[0 for _ in steps], input_frontier=old,
            predecessor_facts=old['facts_theorem'], frontier_index=i,
            dimensions=dict(D=old['dimensions']['D'], T=len(ps), **dict(zip(('B','S','H','C'), shape))),
            axes=[2,1], output_gather_axis=1,
            deferred_stage='after-middle-exchange: original matmul/downstream values unproved')
        row.update(predecessor._census(si, pi, g, [s.outputs[0] for s in steps]))
        units.append(row); result.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, aggregate costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld','noncomputable section','set_option maxHeartbeats 500000',
        *proofs,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return text, dict(status='source-frontier-middle-exchange-values-emitted-uncompiled', reads=reads, units=units,
        frontier_units=result, retained_units=retained, deferred_units=deferred, consumed_frontier_indices=consumed,
        lean_bytes=len(text.encode()), cost_scope='middle exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
