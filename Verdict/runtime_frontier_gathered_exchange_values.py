"""Fresh row-linear hidden output -> original AA(2,1), UNCOMPILED.

Only this exchange fragment is emitted. Full source linear, K/V and skip facts
remain intact; parent owns canonical assembly, aggregate cost and kernel gate.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_gathered_linear_values as predecessor
from Verdict import runtime_projection_exchange_values as exchange
from Verdict import runtime_frontier_alias_exchange_values as source
from Verdict import runtime_frontier_layernorm_values as frontier
from Verdict import runtime_frontier_sequence_alias_values as sequence
from Verdict import runtime_middle_exchange_values as middle
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import Role, _Index, _same_typed, op
from Verdict import runtime_projection_values as projection
from Verdict import runtime_frontier_input_linear_values as column
from Verdict import runtime_add_values as adds
from Verdict.runtime_schedule import build


def render(sm, pm, lineages, validation, bound, execution_order):
    """Exactly one fresh predecessor call on the SAME six public objects."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed gathered-exchange original source: {exc}') from exc


def _boundary(index, cell, ports, ranks, j):
    """Strict present IR gate around the generic logical-peer AA adapter."""
    node = source.residual._identity(index, cell)
    if any(node in getattr(index.view, k, {}) for k in ('chunk_scopes', 'wred_scopes')):
        raise ValueError('gathered-exchange conflicting original receiver scope')
    irs = getattr(cell, '_input_irs', None)
    outs = getattr(cell, '_output_irs', None)
    if irs is None or len(irs) not in (1, len(ports)) or outs is None or len(outs) != 1:
        raise ValueError('gathered-exchange complete present original metadata required')
    parents = [source._original(index, p).parent.tid for p in ports]
    if any(not _same_typed(p, parents[0]) for p in parents):
        raise ValueError('gathered-exchange original peer parent identity mismatch')
    expected = (ports[j],) if len(irs) == 1 else ports
    for p, ir in zip(expected, irs, strict=True): source._edge(index, p, ir)
    source._raw(outs[0])
    if not _same_typed(outs[0].parent.tid, parents[j]):
        raise ValueError('gathered-exchange original receiver output parent mismatch')
    step, meta = exchange._boundary(index, cell, ports, ranks, j)
    if (step.gather_axis, step.split_axis) != (2, 1):
        raise ValueError('gathered-exchange original AA(2,1) required')
    return step, dict(meta, producer_metadata='all-peers', input_parent_identity=meta['input_metadata'])


def _frontiers(si, pi, lineages, bound, order, closed, owners):
    """Authenticate the outgoing mixed state, NOT gathered-linear's input state.

    A row-linear ends at its local linear; input-column linear ends at RS and
    carries partial descriptors. Both recover the real SM alias slot upstream.
    Read adapters are exercised for full-suffix validation, not emitted again.
    """
    frontier._cover(closed, owners)
    specs = adds._bound(lineages, bound)
    if (not _same_typed([r['lineage'] for r in bound['relations']], [asdict(l) for l in lineages if l.role == Role.PARAMETER])
            or any(not _same_typed([u['unit'] for u in r['units']], [u['unit'] for u in r['lineage']['units']]) for r in bound['relations'])):
        raise ValueError('gathered-exchange exact canonical parameter specification order required')
    rows = closed['frontier_units']; units = closed['units']
    indices = closed['consumed_frontier_indices']
    if (not _same_typed([r['frontier_index'] for r in units], indices)
            or any(type(i) is not int or not 0 <= i < len(rows) for i in indices)
            or len(set(indices)) != len(indices)
            or any(not _same_typed(rows[r['frontier_index']], r) for r in units)
            or [r['unit'] for r in rows] != sorted(r['unit'] for r in rows)):
        raise ValueError('gathered-exchange complete ordered incoming row-linear frontier required')
    groups = {}; retained = []; deferred = []; advanced = []; authenticated = []
    for i, old in enumerate(rows):
        g = frontier._output(si, old['source_step'], old['sm_output_ref'])
        ps = [frontier._output(pi, s, r) for s, r in zip(old['local_steps'], old['pm_output_refs'], strict=True)]
        global_ = predecessor._descriptor(si, old['source_step'], old['ranks'])
        locals_ = [predecessor._descriptor(pi, s, old['ranks']) for s in old['local_steps']]
        middle._contract(old, g, ps)
        B, S, H = old['local_shape']; slot = old['source_output_slot']; u = old['unit']
        if (not _same_typed(old['dimensions'], dict(D=len(owners), T=len(ps), B=B, S=S, H=H))
                or not _same_typed(old['positions'], list(range(u*B, (u+1)*B)))
                or type(slot) is not int or not 0 <= slot < len(global_.outputs)
                or not _same_typed(global_.outputs[slot], g)
                or ('slot' in old and not _same_typed(old['slot'], slot))
                or not _same_typed(old['sm_output_tid'], g.endpoint.tid)
                or not _same_typed(old['pm_output_tids'], [p.endpoint.tid for p in ps])
                or g.value_part != (0, 1)):
            raise ValueError('gathered-exchange strong original dimensions/slot/output mismatch')
        parent = source._original(si, g).parent.tid
        if any(not _same_typed(source._original(pi, p).parent.tid, parent) for p in ps):
            raise ValueError('gathered-exchange SM/PM original output parent mismatch')
        origin = global_; original_slot = slot
        if global_.op == 'FW_linear':
            port = global_.inputs[0]; cell = si.raw[port.endpoint.writer]
            origin_ports = source._ports(si, cell, 'outputs')
            original_slot = _one((j for j, p in enumerate(origin_ports) if _same_typed(p, port)),
                                 'gathered-exchange original alias output slot missing/ambiguous')
            origin = predecessor._descriptor(si, asdict(projection.post._next(si, predecessor._producer(si, cell.inputs[0]))), old['ranks'])
            if not _same_typed(old['predecessor_source_output_slot'], original_slot):
                raise ValueError('gathered-exchange original predecessor alias slot mismatch')
            projection._read(si.view, 'sm', global_, order['sm'])
            if all(s.op == 'ReduceScatterPrim' for s in locals_):
                if any(not _same_typed(s.inputs, locals_[0].inputs) for s in locals_):
                    raise ValueError('gathered-exchange complete original partial peer cover required')
                partials = [column._linear(pi, predecessor._producer(pi, pi.raw[p.endpoint.writer].inputs[0]), (j, len(ps)))
                            for j, p in enumerate(locals_[0].inputs)]
                if not _same_typed([asdict(s) for s in partials], old['partial_steps']):
                    raise ValueError('gathered-exchange complete original partial descriptors mismatch')
                parameter = column._parameter(si, pi, lineages, specs, global_, partials, old)
                for s in (*partials, *locals_): column._read(pi.view, 'pm', s, order['pm'])
            elif all(s.op == 'FW_linear' for s in locals_):
                advanced.append(i)
                gathers = []
                for j, local in enumerate(locals_):
                    cell = pi.raw[local.inputs[0].endpoint.writer]
                    ports = tuple(predecessor._producer(pi, r) for r in cell.inputs)
                    sequence._gather_consumer(pi, cell, [p.endpoint.ref for p in ports])
                    step, _ = projection._gather(pi, cell, ports, tuple(old['ranks']), j)
                    if not _same_typed(local.inputs[0], step.outputs[0]):
                        raise ValueError('gathered-exchange original gather/linear edge mismatch')
                    gathers.append(step)
                    projection._read(pi.view, 'pm', step, order['pm'])
                    projection._read(pi.view, 'pm', local, order['pm'])
                if not _same_typed([asdict(s) for s in gathers], old['gather_steps']):
                    raise ValueError('gathered-exchange complete original gather descriptors mismatch')
                parameter = projection._parameter(si, pi, lineages, specs, global_, locals_, old, sharded=True)
                parent = si.raw[global_.node]._input_irs[1].parent.tid
                if any(not _same_typed(pi.raw[s.node]._input_irs[1].parent.tid, parent) for s in locals_):
                    raise ValueError('gathered-exchange original row-weight parent mismatch')
            else:
                raise ValueError('gathered-exchange mixed original linear boundary family')
            if not _same_typed([parameter], old['parameters']):
                raise ValueError('gathered-exchange canonical original parameter descriptor mismatch')
        if all([op(c) for c in sequence._consumers(si, [p])] == ['FW_linear'] for p in origin.outputs):
            slots, count = groups.setdefault((origin.node, u), ([], len(origin.outputs)))
            slots.append(original_slot)
        kinds = [[op(c) for c in sequence._consumers(si, [g])],
                 *[[op(c) for c in sequence._consumers(pi, [p])] for p in ps]]
        if global_.op != 'FW_linear' and (all(k == [] for k in kinds) or all(k == ['FW_add'] for k in kinds)):
            retained.append(old)
        elif i not in advanced:
            deferred.append(old)
        authenticated.append((old, g, ps, kinds))
    if (any(not _same_typed(slots, list(range(count))) for slots, count in groups.values())
            or not _same_typed(advanced, indices) or not _same_typed(retained, closed['retained_units'])
            or len(deferred) != len(closed['deferred_units'])
            or any(any(k not in d or not _same_typed(d[k], v) for k, v in r.items())
                   for r, d in zip(deferred, closed['deferred_units'], strict=True))):
        raise ValueError('gathered-exchange complete original ordered slots/classification cover mismatch')
    return authenticated


def _deferred_reason(kinds):
    return ('next FW_view frontier deferred' if kinds and all(k == ['FW_view'] for k in kinds)
            else 'unsupported complete forward consumer frontier deferred')


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order, dict(sm=build(sm), pm=build(pm))):
        raise ValueError('gathered-exchange complete typed execution/inverse order mismatch')
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    authenticated = _frontiers(si, pi, lineages, bound, order, closed, validation._inputs[3]['config']['units'])
    proofs, reads, units, result, retained, deferred, consumed = [], [], [], [], [], [], []
    names = {}; seen = set()
    for i, (old, g, ps, kinds) in enumerate(authenticated):
        cells = sequence._consumers(pi, ps)
        selected = old['source_step']['op'] == 'FW_linear' and old['gather_axis'] == 2 and any('AllToAllPrim' in k for k in kinds[1:])
        if not selected:
            result.append(old)
            if any(_same_typed(old, r) for r in closed['retained_units']): retained.append(old)
            else: deferred.append(dict(old, reason=_deferred_reason(kinds), observed_consumer_ops=kinds))
            continue
        if len(ps) <= 1 or len(cells) != len(ps) or any(op(c) != 'AllToAllPrim' for c in cells):
            raise ValueError('gathered-exchange complete original receiver cover required')
        steps = []
        for j, rank in enumerate(old['ranks']):
            cell = _one((c for c in cells if _same_typed(c.rank, rank)), 'gathered-exchange original receiver missing/ambiguous')
            step, meta = _boundary(pi, cell, ps, old['ranks'], j)
            if step.node in seen: raise ValueError('gathered-exchange duplicate/cross-DP receiver')
            seen.add(step.node)
            proof, row = exchange._read(pm, step, order['pm'])
            name = row['theorem'].replace('projectionExchange', 'frontierGatheredExchange')
            proofs.extend(s.replace(row['theorem'], name) for s in proof)
            row.update(theorem=name, frontier_index=i, unit=old['unit'], **meta)
            reads.append(row); names[step.node] = name; steps.append(step)
        proof, row = exchange._unit(dict(old, slot=old['source_output_slot']), g, ps, steps, names)
        name = row['theorem'].replace('projectionExchange', 'frontierGatheredExchange')
        proofs.extend(s.replace(row['theorem'], name) for s in proof)
        B, S, H = row['local_shape']
        row.update(theorem=name, facts_theorem=name, layout='sharded',
                   dimensions=dict(D=old['dimensions']['D'], T=len(ps), B=B, S=S, H=H),
                   source_output_slot=old['source_output_slot'], predecessor_facts=old['facts_theorem'], frontier_index=i,
                   deferred_stage='after-gathered-output-exchange: original downstream consumers deferred')
        middle._contract(row, g, [s.outputs[0] for s in steps])
        outgoing = [sequence._consumers(si, [g]), *[sequence._consumers(pi, s.outputs) for s in steps]]
        row.update(observed_consumer_ops=[[op(c) for c in cs] for cs in outgoing],
                   sm_consumers=[list(c.node) for c in outgoing[0]],
                   pm_consumers=[list(c.node) for c in sequence._consumers(pi, [s.outputs[0] for s in steps])])
        units.append(row); result.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, aggregate costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section', 'set_option maxHeartbeats 500000',
        *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-frontier-gathered-exchange-values-emitted-uncompiled', reads=reads, units=units,
        frontier_units=result, retained_units=retained, deferred_units=deferred, consumed_frontier_indices=consumed,
        lean_bytes=len(text.encode()), cost_scope='gathered output exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
