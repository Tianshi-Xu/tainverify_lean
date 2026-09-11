"""Fresh residual -> all aliases -> faithful hidden/sequence frontier candidates.

No caller receipt or output premise is authority. This fragment does not advance
LayerNorm or consume the retained skip. Parent owns assembly/cost/kernel gates.
"""
from dataclasses import asdict, replace

from Verdict import runtime_attention_residual_values as residual
from Verdict import runtime_post_add_values as post
from Verdict import runtime_embedding_route_values as primitive
from Verdict import runtime_add_values as adds
from Verdict import runtime_middle_exchange_values as middle
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build


def _raw(ir):
    """Reject bool/float observations before any Port conversion."""
    if (ir is None or type(ir.tid) is not int or type(ir.parent.tid) is not int
            or len(ir.shape) != 3 or len(ir.parent.shape) != 3
            or any(type(n) is not int or n <= 0 for n in (*ir.shape, *ir.parent.shape))
            or len(ir.indmap) != 3
            or any(len(b) != 2 or any(type(n) is not int for n in b) for b in ir.indmap)
            or len(ir.valmap) != 2 or any(type(n) is not int for n in ir.valmap)):
        raise ValueError('frontier typed original rank-three shape/parent/bounds/value required')


def _ports(index, cell, field):
    irs = getattr(cell, '_'+field[:-1]+'_irs', None)
    if irs is None or len(irs) != len(getattr(cell, field)):
        raise ValueError('frontier complete original metadata required')
    for ir in irs:
        _raw(ir)
    return residual._ports(index, cell, field)


def _output(index, descriptor):
    cell = index.raw[tuple(descriptor['node'])]
    residual._identity(index, cell)
    _ports(index, cell, 'outputs')
    return residual._output(index, descriptor)


def _original(index, port):
    cell = index.raw[port.endpoint.writer]
    residual._identity(index, cell)
    ports = _ports(index, cell, 'outputs')
    j = _one((j for j, p in enumerate(ports) if p.endpoint.ref == port.endpoint.ref),
             'frontier original producer output missing/ambiguous')
    if not _same_typed(ports[j], port):
        raise ValueError('frontier original producer metadata mismatch')
    return cell._output_irs[j]


def _edge(index, port, ir):
    original = _original(index, port)
    _raw(ir)
    observed = residual._port(index, port.endpoint.ref, ir)
    if not _same_typed(original.parent.tid, ir.parent.tid):
        raise ValueError('frontier producer/consumer parent identity mismatch')
    if not _same_typed(observed, port):
        raise ValueError('frontier original edge metadata mismatch')


def _alias(index, descriptor):
    producer = _output(index, descriptor)
    cell = _one((c for c in index.raw.values() if op(c) == 'FW_multiref'
                 and producer.endpoint.ref in map(tuple, c.inputs)),
                'frontier original multiref missing/ambiguous')
    residual._identity(index, cell)
    _ports(index, cell, 'inputs')
    _ports(index, cell, 'outputs')
    if (any(cell.node in getattr(index.view, key, {}) for key in ('collective_scopes', 'chunk_scopes', 'wred_scopes'))
            or set(cell.kwargs) - {'times', '__consts'}
            or not _same_typed(cell.kwargs.get('__consts', []), [])):
        raise ValueError('frontier multiref ordinary scope/kwargs mismatch')
    _edge(index, producer, cell._input_irs[0])
    return post._next(index, producer)


def _facts_header(name, row):
    lines = residual._facts_header(name, row)
    lines[-1] = lines[-1].replace('allGatherPrimDimN 2 ', f'allGatherPrimDimN {row["gather_axis"]} ')
    return lines


def _alias_unit(old, global_, locals_, slot, names):
    g = global_.outputs[slot]; ps = [a.outputs[slot] for a in locals_]
    name = f'frontierAliasFacts_{g.endpoint.tid}_{old["unit"]}'
    row = residual._row(old, g, ps, global_, locals_, name)
    row.update(slot=slot, source_output_slot=slot, predecessor_facts=old['facts_theorem'])
    equations = [f'{names[global_.node]} s t hs {g.endpoint.tid} {adds._member(slot)}']
    equations += [f'{names[a.node]} p q hp {p.endpoint.tid} {adds._member(slot)}'
                  for a, p in zip(locals_, ps, strict=True)]
    proof = [*_facts_header(name, row), '  rw ['+', '.join(equations)+']',
             f'  exact {old["facts_theorem"]} s p t q hs hp hvalues', f'#print axioms {name}']
    return proof, row


def _exchange(index, aliases, slot, ranks):
    ports = tuple(a.outputs[slot] for a in aliases)
    for j, port in enumerate(ports):
        cell = _one((c for c in index.raw.values() if op(c) == 'AllToAllPrim'
                     and c.rank == ranks[j] and port.endpoint.ref in map(tuple, c.inputs)),
                    'frontier original AllToAll missing/ambiguous')
        node = residual._identity(index, cell)
        scope = _one((s for s in index.view.collective_scopes.values() if _same_typed(tuple(s.node), tuple(node))),
                     'frontier original exchange scope missing/ambiguous')
        writer = _one((w for w in index.view._collective_source['writers'] if _same_typed(
            (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
             w['ref']['source_cid'], w['source_irname']), tuple(node))),
            'frontier original exchange writer missing/ambiguous')
        if (scope.op != 'AllToAllPrim' or not _same_typed(scope.params, (2, 1))
                or not _same_typed(scope.ranks, tuple(ranks))
                or not _same_typed(scope.local_index, j)
                or not _same_typed(scope.input_tids, tuple(p.endpoint.tid for p in ports))
                or not _same_typed(scope.input_shape, port.endpoint.shape)
                or scope.source_writer != writer['export_id']
                or len(cell.outputs) != 1
                or not _same_typed(scope.output_tid, index.endpoint(cell.outputs[0]).tid)):
            raise ValueError('frontier original exchange scope/peers/writer mismatch')
        kw = dict(cell.kwargs); rawranks = kw.pop('ranks', None); consts = kw.pop('__consts', [])
        if (type(rawranks) not in (list, tuple) or not _same_typed(tuple(rawranks), tuple(ranks))
                or not _same_typed(kw, dict(idim=2, odim=1)) or not _same_typed(consts, [])):
            raise ValueError('frontier original exchange kwargs mismatch')
        irs = getattr(cell, '_input_irs', None)
        if irs is not None:
            expected = (ports[j],) if len(irs) == 1 else ports
            if len(irs) != len(expected):
                raise ValueError('frontier incomplete exchange input metadata')
            for p, ir in zip(expected, irs, strict=True):
                _edge(index, p, ir)
        irs = getattr(cell, '_output_irs', None)
        if irs is not None:
            if len(irs) != 1 or len(cell.outputs) != 1:
                raise ValueError('frontier incomplete exchange output metadata')
            _raw(irs[0])
            if not _same_typed(irs[0].parent.tid, _original(index, port).parent.tid):
                raise ValueError('frontier exchange output branch parent identity mismatch')
            residual._port(index, cell.outputs[0], irs[0])
    # Narrow only the selection search, never the source read's output list.
    selected = [replace(a, outputs=(a.outputs[slot],)) for a in aliases]
    _, steps, metadata = post._exchange(index, selected, tuple(ranks))
    return steps, metadata


def _consumers(index, ports):
    """Lowered fullrefs prevent corrupted raw targets masquerading as deferrals."""
    by_ref = {p.endpoint.ref: p for p in ports}
    cells = []
    for node in index.view.nodes():
        refs = [tuple(index.view.source_tensor(t)) for t in index.view.node_inputs(node)]
        if not by_ref.keys() & set(refs):
            continue
        cell = index.raw[tuple(node)]
        residual._identity(index, cell)
        if op(cell).startswith('BW_'):
            continue
        if op(cell) != 'AllToAllPrim':
            irs = getattr(cell, '_input_irs', None)
            if irs is None or len(irs) != len(refs):
                raise ValueError('frontier consumer complete original metadata required')
            for ref, ir in zip(refs, irs, strict=True):
                if ref in by_ref:
                    _edge(index, by_ref[ref], ir)
        cells.append(cell)
    return cells


def _exchange_unit(alias, steps, names):
    D, T, B, ST, H = (alias['dimensions'][k] for k in ('D', 'T', 'B', 'S', 'H'))
    S = ST // T; u = alias['unit']; g = alias['sm_output_tid']
    name = f'frontierExchangeFacts_{g}_{u}'
    row = dict(alias, theorem=name, facts_theorem=name, predecessor_facts=alias['facts_theorem'],
        dimensions=dict(D=D, T=T, B=B, S=S, H=H*T), gather_axis=1,
        local_shape=[B, S, H*T], input_shape=alias['local_shape'], input_gather_axis=2,
        pm_output_tids=[s.outputs[0].endpoint.tid for s in steps],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in steps],
        local_steps=[asdict(s) for s in steps])
    xs = _list(f'q {tid}' for tid in alias['pm_output_tids'])
    ys = _list(f'q {tid}' for tid in row['pm_output_tids'])
    terms = _list(f'AllToAllSourceFaithful.tensor {T} {j} 2 1 {xs}' for j in range(T))
    proof = [*_facts_header(name, row),
        f'  have predecessor := {alias["facts_theorem"]} s p t q hs hp hvalues',
        f'  have outputs : {ys} = List.ofFn (fun dst : Fin {T} => AllToAllSourceFaithful.tensor {T} dst.val 2 1 {xs}) := by',
        f'    change {ys} = {terms}',
        '    exact '+_cons_equal([f'{names[s.node]} p q hp' for s in steps]),
        f'  exact SourceHiddenSequenceExchange.output_facts {D} {u} {T} {B} {S} {H} (t {g}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide)',
        '    rfl predecessor.2.1 predecessor.1 predecessor.2.2 outputs', f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """The SAME six inputs freshly reconstruct the residual predecessor."""
    try:
        _, closed = residual.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, validation, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed frontier alias/exchange original source: {exc}') from exc


def _render(sm, pm, validation, order, closed):
    if not _same_typed(order, {'sm': build(sm), 'pm': build(pm)}):
        raise ValueError('frontier complete typed execution order differs from original schedule')
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    owners = validation._inputs[3]['config']['units']
    groups = {}
    for old in closed['frontier_units']:
        if (type(old['unit']) is not int or not _same_typed(old['dimensions']['D'], len(owners))
                or old['layout'] != 'sharded' or not _same_typed(old['gather_axis'], 2)):
            raise ValueError('frontier exact DP dimensions/hidden layout required')
        owner = _one((u for u in owners if _same_typed(u['unit'], old['unit'])),
                     'frontier DP owner missing/ambiguous')
        if not _same_typed((old['ranks'], old['positions']), (owner['ranks'], owner['positions'])):
            raise ValueError('frontier exact DP ranks/positions mismatch')
        groups.setdefault(tuple(old['sm_output_ref']), []).append(old['unit'])
    if not groups or any(len(us) != len(owners) or len(set(us)) != len(us)
                         or set(us) != {u['unit'] for u in owners} for us in groups.values()):
        raise ValueError('frontier complete original DP unit cover required')
    proofs, reads, aliases, exchanges, frontier, retained = [], [], [], [], [], []
    names, seen, local_seen = {}, {}, set()
    for i, old in enumerate(closed['frontier_units']):
        g = _output(si, old['source_step'])
        ps = [_output(pi, d) for d in old['local_steps']]
        middle._contract(old, g, ps)
        global_ = _alias(si, old['source_step'])
        locals_ = [_alias(pi, d) for d in old['local_steps']]
        parents = [_original(si, p).parent.tid for p in global_.outputs]
        for a in locals_:
            if a.node in local_seen:
                raise ValueError('frontier duplicate/cross-DP local alias')
            local_seen.add(a.node)
            if not _same_typed([_original(pi, p).parent.tid for p in a.outputs], parents):
                raise ValueError('frontier ordered SM/PM alias parent identity mismatch')
        for source, label, alias in [(sm, 'sm', global_), *((pm, 'pm', a) for a in locals_)]:
            if alias.node not in names:
                proof, row = post._read(source, label, alias, order[label])
                name = f'frontierMultirefRead_{label}_{alias.outputs[0].endpoint.tid}'
                proofs.extend(line.replace(row['theorem'], name) for line in proof)
                row.update(theorem=name, frontier_index=i)
                names[alias.node] = name; reads.append(row); seen[alias.node] = alias
            elif not _same_typed(seen[alias.node], alias):
                raise ValueError('frontier shared SM alias identity mismatch')
        for slot in range(len(global_.outputs)):
            proof, alias = _alias_unit(old, global_, locals_, slot, names)
            alias['frontier_index'] = i
            proofs.extend(proof); aliases.append(alias)
            sm_consumers = _consumers(si, [global_.outputs[slot]])
            pm_consumers = _consumers(pi, [a.outputs[slot] for a in locals_])
            alias['sm_consumers'] = [list(c.node) for c in sm_consumers]
            alias['pm_consumers'] = [list(c.node) for c in pm_consumers]
            targets = [c for c in pm_consumers if op(c) == 'AllToAllPrim']
            if not targets:
                frontier.append(alias); retained.append(alias)
                continue
            steps, coverage = _exchange(pi, locals_, slot, old['ranks'])
            for step, meta in zip(steps, coverage, strict=True):
                if step.node in local_seen:
                    raise ValueError('frontier duplicate/cross-DP exchange')
                local_seen.add(step.node)
                proof, row = primitive._read(pm, 'pm', step, order['pm'])
                name = f'frontierAllToAllRead_pm_{step.outputs[0].endpoint.tid}'
                proofs.extend(line.replace(row['theorem'], name) for line in proof)
                row.update(theorem=name, unit=old['unit'], slot=slot, **meta,
                    request='group', params=[step.gather_axis, step.split_axis],
                    source_kwargs=dict(pm.node_kwargs(pi.raw[step.node].node)),
                    operand_nonwrite_source_indices=order['pm']['execution_to_source'][row['execution_index']:])
                names[step.node] = name; reads.append(row)
            proof, row = _exchange_unit(alias, steps, names)
            row['input_pm_consumers'] = row.pop('pm_consumers')
            row['pm_consumers'] = [list(c.node) for c in _consumers(pi, [s.outputs[0] for s in steps])]
            proofs.extend(proof); exchanges.append(row); frontier.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, integration, cost and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-frontier-alias-exchange-values-emitted-uncompiled', reads=reads,
        alias_units=aliases, exchange_units=exchanges, units=frontier, frontier_units=frontier,
        consumed_frontier_indices=list(range(len(closed['frontier_units']))), retained_units=retained, deferred_units=[],
        lean_bytes=len(text.encode()), cost_scope='frontier fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
