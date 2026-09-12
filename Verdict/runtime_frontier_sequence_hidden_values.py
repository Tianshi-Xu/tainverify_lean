"""Selective sequence -> hidden AA(1,2) candidates, UNCOMPILED.

The complete fresh next-linear frontier is authority. Only PM advances; SM and
all retained facts keep their original source identities. No new mathematics.
"""
from Verdict import runtime_frontier_next_linear_values as predecessor
from Verdict import runtime_frontier_layernorm_values as frontier
from Verdict import runtime_frontier_alias_exchange_values as source
from Verdict import runtime_output_projection_exchange_values as exchange
from Verdict import runtime_middle_exchange_values as middle
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build


def render(sm, pm, lineages, validation, bound, execution_order):
    """Refresh exactly once with the SAME six objects, never a caller receipt."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, validation, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed frontier-sequence-hidden original source: {exc}') from exc


def _render(sm, pm, validation, order, closed):
    if not _same_typed(order, {'sm': build(sm), 'pm': build(pm)}):
        raise ValueError('frontier-sequence-hidden complete typed execution order mismatch')
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    owners = validation._inputs[3]['config']['units']; D = len(owners)
    frontier._cover(closed, owners)
    authenticated = []
    # Authenticate EVERY original row before selection or emitting anything.
    for old in closed['frontier_units']:
        g = frontier._output(si, old['source_step'], old['sm_output_ref'])
        ps = [frontier._output(pi, step, ref) for step, ref in
              zip(old['local_steps'], old['pm_output_refs'], strict=True)]
        middle._contract(old, g, ps)
        B, S, H = old['local_shape']; T = len(ps); u = old['unit']
        if (not _same_typed(old['dimensions'], dict(D=D,T=T,B=B,S=S,H=H))
                or not _same_typed(old['positions'], list(range(u*B,(u+1)*B)))
                or type(old['source_output_slot']) is not int
                or not 0 <= old['source_output_slot'] < len(old['source_step']['outputs'])
                or not _same_typed(old['source_step']['outputs'][old['source_output_slot']]['endpoint']['ref'], g.endpoint.ref)
                or not _same_typed(old['sm_output_tid'], g.endpoint.tid)
                or not _same_typed(old['pm_output_tids'], [p.endpoint.tid for p in ps])):
            raise ValueError('frontier-sequence-hidden complete strong frontier dimensions/slot mismatch')
        authenticated.append((old, g, ps))
    proofs, reads, units, result, retained, deferred, consumed = [], [], [], [], [], [], []
    names = {}
    for i, (old, g, ps) in enumerate(authenticated):
        consumers = [source._consumers(si, [g]), *[source._consumers(pi, [p]) for p in ps]]
        kinds = [[op(c) for c in cs] for cs in consumers]
        if old['gather_axis'] == 2:
            if all(ks == [] for ks in kinds) or all(ks == ['FW_add'] for ks in kinds):
                retained.append(old)
            else:
                deferred.append(dict(old, reason='unsupported hidden-frontier forward consumer', observed_consumer_ops=kinds))
            result.append(old)
            continue
        if not any('AllToAllPrim' in ks for ks in kinds[1:]):
            deferred.append(dict(old, reason='sequence frontier has no PM exchange consumer', observed_consumer_ops=kinds))
            result.append(old)
            continue
        # Lowered AA inputs contain all peers: each sender must observe the SAME
        # complete receiver set, not merely one arbitrarily chosen local reader.
        cells = consumers[1]; ranks = old['ranks']; T = len(ps)
        if (len(cells) != T or any(op(c) != 'AllToAllPrim' for c in cells)
                or sorted(c.rank for c in cells) != sorted(ranks)
                or any({tuple(c.node) for c in cs} != {tuple(c.node) for c in cells}
                       or len(cs) != T for cs in consumers[2:])
                or len(consumers[0]) > 1):
            raise ValueError('frontier-sequence-hidden partial or fan-out exchange cover unsupported')
        if kinds[0] not in ([], ['FW_add']):
            deferred.append(dict(old, reason='unsupported SM forward consumer; SM never exchanges', observed_consumer_ops=kinds))
            result.append(old)
            continue
        steps = []
        for j, rank in enumerate(ranks):
            cell, = [c for c in cells if _same_typed(c.rank, rank)]
            if (not getattr(cell, '_input_irs', None)
                    or any(cell.node in getattr(pi.view, key, {}) for key in ('wred_scopes', 'chunk_scopes'))):
                raise ValueError('frontier-sequence-hidden original input metadata/collective-only scope required')
            step, coverage = exchange._boundary(pi, cell, ps, ranks, j)
            if not _same_typed(cell._output_irs[0].parent.tid, source._original(pi, ps[j]).parent.tid):
                raise ValueError('frontier-sequence-hidden original output parent identity mismatch')
            if step.node in names:
                raise ValueError('frontier-sequence-hidden duplicate/cross-DP operation')
            proof, row = exchange._read(pm, step, order['pm'])
            name = row['theorem'].replace('outputProjectionExchangeRead_', 'frontierSequenceHiddenRead_')
            proofs.extend(line.replace(row['theorem'], name) for line in proof)
            row.update(theorem=name, unit=old['unit'], frontier_index=i, **coverage)
            reads.append(row); steps.append(step); names[step.node] = name
        proof, row = exchange._unit(old, g, ps, steps, names)
        name = 'frontierSequenceHiddenUnitFacts_' + '_'.join(map(str, [g.endpoint.tid, old['unit'], *row['pm_output_tids']]))
        proofs.extend(line.replace(row['theorem'], name) for line in proof)
        # Existing helper's S is the INPUT sequence width. Frontier S is always
        # the actual OUTPUT local width, as required by downstream consumers.
        row.update(theorem=name, facts_theorem=name, predecessor_facts=old['facts_theorem'],
                   dimensions=dict(D=D,T=T,B=row['local_shape'][0],S=row['local_shape'][1],H=row['local_shape'][2]),
                   source_output_slot=old['source_output_slot'], frontier_index=i)
        row['sm_consumers'] = [list(c.node) for c in consumers[0]]
        row['pm_consumers'] = [list(c.node) for c in source._consumers(pi, [s.outputs[0] for s in steps])]
        for read in reads[-T:]:
            read.update(dimensions=row['dimensions'], layout=row['layout'])
        units.append(row); result.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-frontier-sequence-hidden-values-emitted-uncompiled',
        reads=reads, units=units, frontier_units=result, retained_units=retained, deferred_units=deferred,
        consumed_frontier_indices=consumed, lean_bytes=len(text.encode()),
        cost_scope='selective sequence-hidden fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
