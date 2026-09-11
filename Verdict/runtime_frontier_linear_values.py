"""Sequence frontier -> direct copied-weight linear source candidates.

No aliases are invented. SAME-six fresh predecessor and canonical parameter
frame supply the facts; parent owns assembly, cost and kernel verification.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_layernorm_values as predecessor
from Verdict import runtime_frontier_alias_exchange_values as frontier_source
from Verdict import runtime_output_projection_values as direct
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_add_values as adds
from Verdict.runtime_lineage import Role, _Index, _same_typed, op
from Verdict.runtime_schedule import build


def _rename(text):
    """Finite renaming of existing helper identifiers, not a proof grammar."""
    return text.replace('outputProjectionRead_', 'frontierLinearRead_').replace(
        'outputProjectionUnitFacts_', 'frontierLinearUnitFacts_')


def _matrix(ir):
    """Gate raw rank-two weight types before the legacy Port conversion."""
    if (ir is None or type(ir.tid) is not int or type(ir.parent.tid) is not int
            or len(ir.shape) != 2 or len(ir.parent.shape) != 2
            or any(type(n) is not int or n <= 0 for n in (*ir.shape, *ir.parent.shape))
            or len(ir.indmap) != 2
            or any(len(b) != 2 or any(type(n) is not int for n in b) for b in ir.indmap)
            or len(ir.valmap) != 2 or any(type(n) is not int for n in ir.valmap)
            or ir.is_param() is not True or ir.is_grad() is not False):
        raise ValueError('frontier-linear typed original parameter matrix required')


def _linear(index, activation):
    cell, = frontier_source._consumers(index, [activation])
    if (len(cell.inputs) != 2 or len(cell.outputs) != 1
            or len(getattr(cell, '_input_irs', [])) != 2
            or len(getattr(cell, '_output_irs', [])) != 1):
        raise ValueError('frontier-linear complete original linear metadata required')
    frontier_source._raw(cell._input_irs[0])
    frontier_source._raw(cell._output_irs[0])
    _matrix(cell._input_irs[1])
    frontier_source._edge(index, activation, cell._input_irs[0])
    return direct._linear(index, activation)


def render(sm, pm, lineages, validation, bound, execution_order):
    """Rebuild the predecessor exactly once from the same six objects."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed frontier-linear original source: {exc}') from exc


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order, {'sm': build(sm), 'pm': build(pm)}):
        raise ValueError('frontier-linear complete typed execution order mismatch')
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    specs = adds._bound(lineages, bound)
    parameters = [l for l in lineages if l.role == Role.PARAMETER]
    if not _same_typed([r['lineage'] for r in bound['relations']], [asdict(l) for l in parameters]):
        raise ValueError('frontier-linear canonical bound spec order mismatch')
    for row, parameter in zip(bound['relations'], parameters, strict=True):
        if not _same_typed([u['unit'] for u in row['units']], [u.unit for u in parameter.units]):
            raise ValueError('frontier-linear canonical bound unit spec order mismatch')
    owners = validation._inputs[3]['config']['units']; D = len(owners)
    predecessor._cover(closed, owners)
    proofs, reads, units, frontier, retained, deferred, consumed = [], [], [], [], [], [], []
    seen, names = {}, {}
    for i, old in enumerate(closed['frontier_units']):
        g = predecessor._output(si, old['source_step'], old['sm_output_ref'])
        ps = [predecessor._output(pi, s, ref) for s,ref in zip(old['local_steps'], old['pm_output_refs'], strict=True)]
        middle._contract(old, g, ps)
        B, S, H = old['local_shape']; T = len(ps); u = old['unit']
        if (not _same_typed(old['dimensions'], dict(D=D,T=T,B=B,S=S,H=H))
                or not _same_typed(old['positions'], list(range(u*B,(u+1)*B)))
                or type(old['source_output_slot']) is not int
                or not 0 <= old['source_output_slot'] < len(old['source_step']['outputs'])
                or not _same_typed(old['source_step']['outputs'][old['source_output_slot']]['endpoint']['ref'], g.endpoint.ref)
                or not _same_typed(old['sm_output_tid'], g.endpoint.tid)
                or not _same_typed(old['pm_output_tids'], [p.endpoint.tid for p in ps])):
            raise ValueError('frontier-linear complete strong frontier dimensions/slot mismatch')
        consumers = [frontier_source._consumers(si, [g]),
                     *[frontier_source._consumers(pi, [p]) for p in ps]]
        kinds = [[op(c) for c in cs] for cs in consumers]
        if old['gather_axis'] != 1:
            if all(ks == [] for ks in kinds) or all(ks == ['FW_add'] for ks in kinds):
                retained.append(old)
            else:
                deferred.append(dict(old, reason='unsupported hidden-frontier forward consumer', observed_consumer_ops=kinds))
            frontier.append(old)
            continue
        if not any('FW_linear' in ks for ks in kinds):
            deferred.append(dict(old, reason='sequence frontier has no direct linear consumer', observed_consumer_ops=kinds))
            frontier.append(old)
            continue
        if any(ks != ['FW_linear'] for ks in kinds):
            raise ValueError('frontier-linear partial or fan-out linear consumer cover unsupported')
        global_ = _linear(si, g); locals_ = [_linear(pi, p) for p in ps]
        for field, slot in (('_input_irs', 1), ('_output_irs', 0)):
            parent = getattr(si.raw[global_.node], field)[slot].parent.tid
            if any(not _same_typed(getattr(pi.raw[s.node], field)[slot].parent.tid, parent) for s in locals_):
                raise ValueError('frontier-linear original SM/PM parameter/output parent identity mismatch')
        for index, steps in ((si, [global_]), (pi, locals_)):
            refs = {s.inputs[1].endpoint.ref for s in steps}
            for cell in index.raw.values():
                if not refs.intersection(map(tuple, cell.inputs)):
                    continue
                irs = getattr(cell, '_input_irs', None)
                if irs is None or len(irs) != len(cell.inputs):
                    raise ValueError('frontier-linear complete original parameter occurrence metadata required')
                for ref, ir in zip(cell.inputs, irs, strict=True):
                    if tuple(ref) in refs:
                        _matrix(ir)
        parameter = direct._parameter(si, pi, lineages, specs, global_, locals_, old)
        for view, label, step in [(sm, 'sm', global_), *((pm, 'pm', s) for s in locals_)]:
            if step.node in seen:
                if label != 'sm' or not _same_typed(seen[step.node], step):
                    raise ValueError('frontier-linear duplicate/cross-unit consumer')
                continue
            proof, row = direct._read(view, label, step, order[label])
            proofs.extend(map(_rename, proof)); row['theorem'] = _rename(row['theorem'])
            row.update(unit=old['unit'], frontier_index=i)
            reads.append(row); seen[step.node] = step; names[step.node] = row['theorem']
        proof, row = direct._unit(old, global_, locals_, parameter, names, len(specs))
        proofs.extend(map(_rename, proof))
        dims = row['dimensions']
        row.update(theorem=_rename(row['theorem']), facts_theorem=_rename(row['facts_theorem']),
            dimensions=dict(D=D,T=dims['T'],B=dims['B'],S=dims['S'],H=dims['O']),
            input_shape=list(global_.inputs[0].endpoint.shape), input_width=dims['I'],
            local_input_shape=list(locals_[0].inputs[0].endpoint.shape),
            source_output_slot=0, frontier_index=i, predecessor_facts=old['facts_theorem'])
        row['sm_consumers'] = [list(c.node) for c in frontier_source._consumers(si, global_.outputs)]
        row['pm_consumers'] = [list(c.node) for c in frontier_source._consumers(pi, [s.outputs[0] for s in locals_])]
        units.append(row); frontier.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-frontier-linear-values-emitted-uncompiled', reads=reads, units=units,
        frontier_units=frontier, consumed_frontier_indices=consumed, retained_units=retained, deferred_units=deferred,
        lean_bytes=len(text.encode()), cost_scope='frontier direct linear fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
