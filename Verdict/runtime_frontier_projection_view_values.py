"""Fresh mixed Q/K/V frontier -> original rank-changing views, UNCOMPILED.

Only the view fragment is emitted. Every old row remains as input_frontier;
reconstructed producer history is source-derived, never receipt authority.
The parent owns assembly, aggregate costs, original runs and kernel validation.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_gathered_exchange_values as predecessor
from Verdict import runtime_frontier_gathered_linear_values as gathered
from Verdict import runtime_frontier_input_linear_values as column
from Verdict import runtime_frontier_alias_exchange_values as source
from Verdict import runtime_frontier_layernorm_values as frontier
from Verdict import runtime_frontier_sequence_alias_values as sequence
from Verdict import runtime_projection_values as projection
from Verdict import runtime_view_values as view
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_add_values as adds
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import Role, _Index, _same_typed, op
from Verdict.runtime_schedule import build


def render(sm, pm, lineages, validation, bound, execution_order):
    """Exactly one fresh predecessor, with precisely the SAME six inputs."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError, ZeroDivisionError) as exc:
        raise ValueError(f'malformed projection-view original source: {exc}') from exc


def _alias_producer(index, port, ranks):
    cell = index.raw[port.endpoint.writer]
    if op(cell) != 'FW_multiref':
        raise ValueError('projection-view original ancestry requires a multiref fork')
    step = projection.post._next(index, gathered._producer(index, cell.inputs[0]))
    step = gathered._descriptor(index, asdict(step), ranks)
    slot = _one((j for j, p in enumerate(step.outputs) if _same_typed(p, port)),
                'projection-view original ancestry fork output missing/ambiguous')
    return step, slot


def _carry_fork(index, origin, ranks):
    """Follow projection alias <- LN <- [PM exchange <-] residual fork."""
    cell = index.raw[origin.inputs[0].endpoint.writer]
    if op(cell) != 'FW_layernorm':
        raise ValueError('projection-view original projection ancestry requires LayerNorm')
    activation = gathered._producer(index, cell.inputs[0])
    norm = frontier._next(index, activation)
    if not _same_typed(norm.outputs, origin.inputs):
        raise ValueError('projection-view original normalization/alias edge mismatch')
    cell = index.raw[activation.endpoint.writer]
    if op(cell) == 'AllToAllPrim':
        ports = [gathered._producer(index, ref) for ref in cell.inputs]
        forks = [_alias_producer(index, p, ranks) for p in ports]
        slot = forks[0][1]
        if any(j != slot for _, j in forks):
            raise ValueError('projection-view original ancestry exchange slot mismatch')
        steps, _ = source._exchange(index, [f for f, _ in forks], slot, ranks)
        j = ranks.index(cell.rank)
        if not _same_typed(steps[j].outputs, (activation,)):
            raise ValueError('projection-view original ancestry exchange output mismatch')
        return forks[j]
    return _alias_producer(index, activation, ranks)


def _frontiers(si, pi, lineages, bound, order, closed, owners):
    """Authenticate the outgoing AA/RS/skip state, not the AA INPUT state."""
    frontier._cover(closed, owners)
    specs = adds._bound(lineages, bound)
    if (not _same_typed([r['lineage'] for r in bound['relations']], [asdict(l) for l in lineages if l.role == Role.PARAMETER])
            or any(not _same_typed([u['unit'] for u in r['units']], [u['unit'] for u in r['lineage']['units']]) for r in bound['relations'])):
        raise ValueError('projection-view canonical parameter order mismatch')
    rows = closed['frontier_units']; indices = closed['consumed_frontier_indices']
    if (any(type(i) is not int or not 0 <= i < len(rows) for i in indices)
            or len(set(indices)) != len(indices)
            or not _same_typed([r['frontier_index'] for r in closed['units']], indices)
            or any(not _same_typed(rows[r['frontier_index']], r) for r in closed['units'])
            or [r['unit'] for r in rows] != sorted(r['unit'] for r in rows)):
        raise ValueError('projection-view complete ordered incoming frontier required')
    groups = {}; retained = []; deferred = []; exchanged = []; authenticated = []; origins = {}
    for i, old in enumerate(rows):
        ranks = old['ranks']; u = old['unit']
        g = frontier._output(si, old['source_step'], old['sm_output_ref'])
        ps = [frontier._output(pi, s, r) for s, r in zip(old['local_steps'], old['pm_output_refs'], strict=True)]
        global_ = gathered._descriptor(si, old['source_step'], ranks)
        locals_ = []
        for descriptor in old['local_steps']:
            cell = pi.raw[tuple(descriptor['node'])]
            if op(cell) == 'AllToAllPrim':
                ports = [gathered._producer(pi, r) for r in cell.inputs]
                step, _ = predecessor._boundary(pi, cell, ports, ranks, ranks.index(cell.rank))
                if not _same_typed(asdict(step), descriptor):
                    raise ValueError('projection-view complete original AA descriptor mismatch')
            else:
                step = gathered._descriptor(pi, descriptor, ranks)
            locals_.append(step)
        middle._contract(old, g, ps)
        B, S, H = old['local_shape']; slot = old['source_output_slot']
        if (not _same_typed(old['dimensions'], dict(D=len(owners), T=len(ps), B=B, S=S, H=H))
                or not _same_typed(old['positions'], list(range(u*B, (u+1)*B)))
                or type(slot) is not int or not 0 <= slot < len(global_.outputs)
                or not _same_typed(global_.outputs[slot], g)
                or ('slot' in old and not _same_typed(old['slot'], slot))
                or not _same_typed(old['sm_output_tid'], g.endpoint.tid)
                or not _same_typed(old['pm_output_tids'], [p.endpoint.tid for p in ps])
                or g.value_part != (0, 1)):
            raise ValueError('projection-view original dimensions/slot/output mismatch')
        parent = source._original(si, g).parent.tid
        if any(not _same_typed(source._original(pi, p).parent.tid, parent) for p in ps):
            raise ValueError('projection-view original SM/PM producer parent mismatch')
        history = dict(source_step=asdict(global_), local_steps=[asdict(s) for s in locals_])
        origin = global_; original_slot = slot
        if global_.op == 'FW_linear':
            port = global_.inputs[0]; cell = si.raw[port.endpoint.writer]
            origin = gathered._descriptor(si, asdict(projection.post._next(si, gathered._producer(si, cell.inputs[0]))), ranks)
            original_slot = _one((j for j, p in enumerate(origin.outputs) if _same_typed(p, port)),
                                 'projection-view original alias slot missing/ambiguous')
            if slot != 0:
                raise ValueError('projection-view linear source output slot must be zero')
            projection._read(si.view, 'sm', global_, order['sm'])
            if all(s.op == 'ReduceScatterPrim' for s in locals_):
                if (not _same_typed(old['predecessor_source_output_slot'], original_slot)
                        or any(not _same_typed(s.inputs, locals_[0].inputs) or s.split_axis != old['gather_axis'] for s in locals_)):
                    raise ValueError('projection-view original partial cover/axis/alias slot mismatch')
                partials = [column._linear(pi, gathered._producer(pi, pi.raw[p.endpoint.writer].inputs[0]), (j, len(ps)))
                            for j, p in enumerate(locals_[0].inputs)]
                if not _same_typed([asdict(s) for s in partials], old['partial_steps']):
                    raise ValueError('projection-view complete original partial descriptors mismatch')
                local_linears = partials
                parameter = column._parameter(si, pi, lineages, specs, global_, partials, old)
                for s in (*partials, *locals_): column._read(pi.view, 'pm', s, order['pm'])
                history['partial_steps'] = [asdict(s) for s in partials]
                facts = f'frontierInputLinearUnitFacts_{g.endpoint.tid}_{u}'
                deferred.append(old)
            elif all(s.op == 'AllToAllPrim' for s in locals_):
                exchanged.append(i)
                ports = locals_[0].inputs
                if any(not _same_typed(s.inputs, ports) for s in locals_):
                    raise ValueError('projection-view original Q ordered producer cover mismatch')
                linears = [gathered._descriptor(pi, asdict(gathered._linear(pi,
                    gathered._producer(pi, pi.raw[p.endpoint.writer].inputs[0]))), ranks) for p in ports]
                gathers = []
                for j, local in enumerate(linears):
                    if not _same_typed(local.outputs[0], ports[j]):
                        raise ValueError('projection-view Q producer output mismatch')
                    cell = pi.raw[local.inputs[0].endpoint.writer]
                    inputs = tuple(gathered._producer(pi, r) for r in cell.inputs)
                    sequence._gather_consumer(pi, cell, [p.endpoint.ref for p in inputs])
                    gather, _ = projection._gather(pi, cell, inputs, tuple(ranks), j)
                    if not _same_typed(gather.outputs[0], local.inputs[0]):
                        raise ValueError('projection-view original gather/linear edge mismatch')
                    gathers.append(gather)
                    step, _ = predecessor._boundary(pi, pi.raw[locals_[j].node], ports, ranks, j)
                    if not _same_typed(step, locals_[j]) or old['gather_axis'] != step.split_axis:
                        raise ValueError('projection-view original Q exchange descriptor/axis mismatch')
                    predecessor.exchange._read(pi.view, step, order['pm'])
                    for s in (gather, local): projection._read(pi.view, 'pm', s, order['pm'])
                local_linears = linears
                parameter = projection._parameter(si, pi, lineages, specs, global_, linears, old, sharded=True)
                parent = si.raw[global_.node]._input_irs[1].parent.tid
                if any(not _same_typed(pi.raw[s.node]._input_irs[1].parent.tid, parent) for s in linears):
                    raise ValueError('projection-view Q weight parent mismatch')
                history.update(linear_steps=[asdict(s) for s in linears], gather_steps=[asdict(s) for s in gathers])
                facts = f'frontierGatheredExchangeUnitFacts_{g.endpoint.tid}_{u}_slot{slot}'
            else:
                raise ValueError('projection-view unsupported mixed producer family')
            local_origins = []
            for j, linear in enumerate(local_linears):
                adapter = pi.raw[linear.inputs[0].endpoint.writer]
                alias, alias_slot = _alias_producer(pi, gathered._producer(pi, adapter.inputs[j]), ranks)
                if alias_slot != original_slot:
                    raise ValueError('projection-view original SM/PM projection slot mismatch')
                local_origins.append(alias)
            ancestry = (origin, local_origins)
            if u in origins and not _same_typed(origins[u], ancestry):
                raise ValueError('projection-view original projection ancestry mismatch')
            origins[u] = ancestry
            history.update(parameters=[parameter], original_alias_step=asdict(origin), original_alias_slot=original_slot)
            for key in ('parameters', 'partial_steps', 'gather_steps', 'linear_steps'):
                if key in old and (key not in history or not _same_typed(old[key], history[key])):
                    raise ValueError('projection-view carried original producer history mismatch')
            if old['facts_theorem'] != facts:
                raise ValueError('projection-view original complete facts theorem mismatch')
        else:
            # A skip remains a complete multiref, not a fabricated singleton.
            if global_.op != 'FW_multiref' or any(s.op != 'FW_multiref' for s in locals_):
                raise ValueError('projection-view unsupported original skip producer')
            for index, label, step in [(si, 'sm', global_), *((pi, 'pm', s) for s in locals_)]:
                projection.post._read(index.view, label, step, order[label])
            retained.append(old)
        if all([op(c) for c in sequence._consumers(si, [p])] == ['FW_linear'] for p in origin.outputs):
            slots, count = groups.setdefault((origin.node, u), ([], len(origin.outputs)))
            slots.append(original_slot)
        kinds = [[op(c) for c in sequence._consumers(si, [g])],
                 *[[op(c) for c in sequence._consumers(pi, [p])] for p in ps]]
        if global_.op != 'FW_linear' and not (all(k == [] for k in kinds) or all(k == ['FW_add'] for k in kinds)):
            raise ValueError('projection-view original skip consumer mismatch')
        authenticated.append((old, g, ps, kinds, history))
    if (any(not _same_typed(slots, list(range(count))) for slots, count in groups.values())
            or not _same_typed(exchanged, indices) or not _same_typed(retained, closed['retained_units'])
            or len(deferred) != len(closed['deferred_units'])
            or any(any(k not in d or not _same_typed(d[k], v) for k, v in r.items())
                   for r, d in zip(deferred, closed['deferred_units'], strict=True))):
        raise ValueError('projection-view original ordered slots/classification cover mismatch')
    # Receipt classifications are not an inventory: independently expand the
    # selected residual-fork output into ALL original projection outputs, and
    # retain every nonselected sibling in the original fork's output order.
    if set(origins) != {owner['unit'] for owner in owners}:
        raise ValueError('projection-view original projection ancestry DP cover missing')
    expected = []; expected_carries = []
    for owner in sorted(owners, key=lambda owner: owner['unit']):
        u, ranks = owner['unit'], owner['ranks']
        origin, local_origins = origins[u]
        fork, selected_slot = _carry_fork(si, origin, ranks)
        local_forks = [_carry_fork(pi, alias, ranks) for alias in local_origins]
        if any(slot != selected_slot or len(local.outputs) != len(fork.outputs)
               for local, slot in local_forks):
            raise ValueError('projection-view original carry fork SM/PM inventory mismatch')
        for slot, g in enumerate(fork.outputs):
            if slot == selected_slot:
                expected.extend((u, gathered._linear(si, p).outputs[0]) for p in origin.outputs)
            else:
                ps = [local.outputs[slot] for local, _ in local_forks]
                expected.append((u, g))
                expected_carries.append((u, g, ps, asdict(fork), [asdict(local) for local, _ in local_forks]))
    actual = [(old['unit'], g) for old, g, _, _, _ in authenticated]
    carries = [(old['unit'], g, ps, history['source_step'], history['local_steps'])
               for old, g, ps, _, history in authenticated if old['source_step']['op'] == 'FW_multiref']
    if not _same_typed(actual, expected) or not _same_typed(carries, expected_carries):
        raise ValueError('projection-view original ancestry carry/output inventory mismatch')
    return authenticated


def _raw(ir, rank):
    """Original types are checked BEFORE Port metadata performs lossy casts."""
    if (ir is None or type(ir.tid) is not int or type(ir.parent.tid) is not int
            or len(ir.shape) != rank or len(ir.parent.shape) != rank
            or any(type(d) is not int or d <= 0 for d in (*ir.shape, *ir.parent.shape))
            or len(ir.indmap) != rank
            or any(len(b) != 2 or any(type(n) is not int for n in b)
                   or not 0 <= b[0] < b[1] <= d for b, d in zip(ir.indmap, ir.parent.shape))
            or tuple(ir.shape) != tuple(hi-lo for lo, hi in ir.indmap)
            or len(ir.valmap) != 2 or any(type(n) is not int for n in ir.valmap)
            or not 0 <= ir.valmap[0] < ir.valmap[1]
            or ir.is_param() is not False or ir.is_grad() is not False):
        raise ValueError('projection-view typed original shape/parent/bounds/value/flags required')


def _edge(index, producer, ir):
    cell = index.raw[producer.endpoint.writer]
    source.residual._identity(index, cell)
    slot = _one((j for j, ref in enumerate(cell.outputs) if _same_typed(tuple(ref), producer.endpoint.ref)),
                'projection-view original producer output slot missing/ambiguous')
    original = cell._output_irs[slot]
    for raw in (original, ir): _raw(raw, len(producer.endpoint.shape))
    if (not _same_typed(original.tid, ir.tid)
            or not _same_typed(original.parent.tid, ir.parent.tid)
            or not _same_typed(projection.post._port(index, producer.endpoint.ref, original), producer)
            or not _same_typed(projection.post._port(index, producer.endpoint.ref, ir), producer)):
        raise ValueError('projection-view original producer/consumer object/parent/fullref mismatch')


def _view(index, cell, producer):
    node = source.residual._identity(index, cell)
    signature = getattr(getattr(cell, 'ir', None), 'signature', None)
    if type(signature) is not str or signature != 'torch.Tensor.view':
        raise ValueError('projection-view original function must be torch.Tensor.view')
    if (op(cell) != 'FW_view' or len(cell.inputs) != 1 or len(cell.outputs) != 1
            or len(cell._input_irs) != 1 or len(cell._output_irs) != 1
            or any(node in getattr(index.view, k, {}) for k in ('collective_scopes','chunk_scopes','wred_scopes'))
            or set(cell.kwargs)-{'size','__consts'} or not _same_typed(cell.kwargs.get('__consts', []), [])):
        raise ValueError('projection-view original arity/scope/size kwargs mismatch')
    _raw(cell._input_irs[0], 3); _raw(cell._output_irs[0], 4)
    _edge(index, producer, cell._input_irs[0])
    return view._view(index, cell, producer)


def _outgoing(index, ports):
    """Authenticate rank-four successor edges without proving their operations."""
    cells = column._consumers(index, ports)
    for cell in cells:
        inputs = []
        for ref in cell.inputs:
            writer = index.raw[tuple(index.writers[tuple(ref)])]
            source.residual._identity(index, writer)
            slot = _one((j for j, r in enumerate(writer.outputs) if _same_typed(tuple(r), tuple(ref))),
                        'projection-view successor original input writer missing/ambiguous')
            ir = writer._output_irs[slot]; _raw(ir, 4)
            inputs.append(projection.post._port(index, ref, ir))
        irs = cell._input_irs
        expected = inputs
        if op(cell) == 'AllToAllPrim':
            scope = index.view.collective_scopes[cell.node]
            ranks = tuple(p.endpoint.ref[1] for p in inputs)
            j = ranks.index(cell.rank)
            a, b = scope.params
            if (scope.op != op(cell) or not scope.source_writer
                    or any(type(d) is not int or not 0 <= d < 4 for d in (a, b)) or a == b
                    or not _same_typed(scope.ranks, ranks) or not _same_typed(scope.local_index, j)
                    or not _same_typed(scope.input_tids, tuple(p.endpoint.tid for p in inputs))
                    or not _same_typed(scope.input_shape, inputs[j].endpoint.shape)
                    or not _same_typed(tuple(cell.kwargs['ranks']), ranks)
                    or not _same_typed((cell.kwargs['idim'], cell.kwargs['odim']), (a, b))):
                raise ValueError('projection-view successor original collective scope mismatch')
            if irs is not None and len(irs) == 1: expected = [inputs[j]]
        if irs is None or len(irs) != len(expected):
            raise ValueError('projection-view successor complete original input metadata required')
        for p, ir in zip(expected, irs, strict=True): _edge(index, p, ir)
        if cell._output_irs is None or len(cell._output_irs) != len(cell.outputs):
            raise ValueError('projection-view successor complete original output metadata required')
        for ref, ir in zip(cell.outputs, cell._output_irs, strict=True):
            _raw(ir, 4)
            port = projection.post._port(index, ref, ir)
            if port.endpoint.writer != tuple(cell.node) or port.endpoint.ref[:3] != tuple(cell.node)[:3]:
                raise ValueError('projection-view successor original output owner mismatch')
    return cells


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order, dict(sm=build(sm), pm=build(pm))):
        raise ValueError('projection-view complete typed execution/inverse order mismatch')
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    authenticated = _frontiers(si, pi, lineages, bound, order, closed, validation._inputs[3]['config']['units'])
    proofs, reads, units, result, retained, deferred, consumed = [], [], [], [], [], [], []
    names = {}; seen = {}
    for i, (old, g, ps, kinds, history) in enumerate(authenticated):
        if old['source_step']['op'] == 'FW_multiref':
            result.append(old); retained.append(old); continue
        if any(k != ['FW_view'] for k in kinds):
            raise ValueError('projection-view complete unique original view cover required')
        global_ = _view(si, view._consumer(si, g), g)
        locals_ = [_view(pi, view._consumer(pi, p), p) for p in ps]
        parent = si.raw[global_.node]._output_irs[0].parent.tid
        if any(not _same_typed(pi.raw[s.node]._output_irs[0].parent.tid, parent) for s in locals_):
            raise ValueError('projection-view original SM/PM view output parent mismatch')
        for index, label, step in [(si, 'sm', global_), *((pi, 'pm', s) for s in locals_)]:
            key = (label, step.node)
            if key in seen:
                if label != 'sm' or not _same_typed(seen[key], step):
                    raise ValueError('projection-view duplicate/cross-unit consumer')
                continue
            proof, row = view._read(index.view, label, step, order[label])
            name = row['theorem'].replace('viewRead_', 'frontierProjectionViewRead_')
            proofs.extend(s.replace(row['theorem'], name) for s in proof)
            row.update(theorem=name, frontier_index=i, unit=old['unit'])
            reads.append(row); seen[key] = step; names[step.node] = name
        prior = dict(old, slot=old['source_output_slot'], theorem=old['facts_theorem'])
        proof, fresh = view._unit(prior, global_, locals_, names)
        name = fresh['theorem'].replace('viewUnitFacts_', 'frontierProjectionViewUnitFacts_')
        proofs.extend(s.replace(fresh['theorem'], name) for s in proof)
        row = dict(old)
        row.update(fresh)
        row.update(theorem=name, facts_theorem=name, source_output_slot=0, slot=0,
                   predecessor_facts=old['facts_theorem'], input_frontier=old, producer_history=history,
                   frontier_index=i, layout='sharded', deferred_stage='after-projection-view: downstream original consumers unproved')
        middle._contract(row, global_.outputs[0], [s.outputs[0] for s in locals_])
        outgoing = [_outgoing(si, global_.outputs), *[_outgoing(pi, s.outputs) for s in locals_]]
        pm_consumers = _outgoing(pi, [s.outputs[0] for s in locals_])
        row.update(observed_consumer_ops=[[op(c) for c in cs] for cs in outgoing],
                   sm_consumers=[list(c.node) for c in outgoing[0]],
                   pm_consumers=[list(c.node) for c in pm_consumers],
                   downstream_consumers=[dict(node=list(c.node), op=op(c), source_kwargs=dict(c.kwargs),
                       source_inputs=[list(r) for r in c.inputs], source_outputs=[list(r) for r in c.outputs])
                       for c in [*outgoing[0], *pm_consumers]])
        units.append(row); result.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, aggregate costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section', 'set_option maxHeartbeats 500000',
        *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-frontier-projection-view-values-emitted-uncompiled', reads=reads, units=units,
        frontier_units=result, retained_units=retained, deferred_units=deferred, consumed_frontier_indices=consumed,
        lean_bytes=len(text.encode()), cost_scope='projection view fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
