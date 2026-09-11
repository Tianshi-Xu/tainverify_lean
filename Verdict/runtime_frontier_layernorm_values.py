"""Fresh residual frontier -> sequence-sharded LayerNorm source candidates.

SAME six public inputs; no caller receipt or output premise. The parent owns
canonical assembly, parameter frame, imports, aggregate cost and kernel gates.
Retained skip rows keep every predecessor fact and their original order.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_alias_exchange_values as predecessor
from Verdict import runtime_layernorm_values as layernorm
from Verdict import runtime_attention_residual_values as residual
from Verdict import runtime_post_add_values as post
from Verdict import runtime_add_values as adds
from Verdict import runtime_middle_exchange_values as middle
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import Role, _Index, _same_typed, op
from Verdict.runtime_schedule import build


def _output(index, descriptor, ref):
    """Select the complete source output by fullref, not a shared SM/PM slot."""
    cell = index.raw[tuple(descriptor['node'])]
    residual._identity(index, cell)
    ports = predecessor._ports(index, cell, 'outputs')
    if (not _same_typed([asdict(p) for p in ports], list(descriptor['outputs']))
            or op(cell) != descriptor['op']):
        raise ValueError('frontier-layernorm predecessor source output mismatch')
    return _one((p for p in ports if _same_typed(p.endpoint.ref, tuple(ref))),
                'frontier-layernorm predecessor fullref missing/ambiguous')


def _vector(ir):
    """Rank-one parameters need their own gate BEFORE Port's int coercions."""
    if (ir is None or type(ir.tid) is not int or type(ir.parent.tid) is not int
            or len(ir.shape) != 1 or len(ir.parent.shape) != 1
            or any(type(n) is not int or n <= 0 for n in (*ir.shape, *ir.parent.shape))
            or len(ir.indmap) != 1
            or any(len(b) != 2 or any(type(n) is not int for n in b) for b in ir.indmap)
            or len(ir.valmap) != 2 or any(type(n) is not int for n in ir.valmap)
            or not ir.is_param() or ir.is_grad()):
        raise ValueError('frontier-layernorm typed original parameter vector required')


def _next(index, activation):
    # Use lowered fullrefs for discovery: corrupted raw op/refs cannot disappear.
    consumers = predecessor._consumers(index, [activation])
    cell = _one((c for c in consumers if op(c) == 'FW_layernorm'),
                'frontier-layernorm original LN consumer missing/ambiguous')
    node = residual._identity(index, cell)
    if (len(cell.inputs) != 3 or len(cell.outputs) != 1
            or len(getattr(cell, '_input_irs', [])) != 3
            or len(getattr(cell, '_output_irs', [])) != 1):
        raise ValueError('frontier-layernorm complete original LN metadata required')
    predecessor._raw(cell._input_irs[0]); predecessor._raw(cell._output_irs[0])
    for ir in cell._input_irs[1:]:
        _vector(ir)
    H = activation.endpoint.shape[-1]
    kw = cell.kwargs; normalized = kw.get('normalized_shape')
    if (any(node in getattr(index.view, key, {}) for key in ('collective_scopes','chunk_scopes','wred_scopes'))
            or set(kw) - {'normalized_shape','eps','__consts'}
            or type(normalized) not in (list, tuple)
            or not _same_typed(tuple(normalized), (H,))
            or not _same_typed(kw.get('eps', 1e-5), 1e-5)
            or not _same_typed(kw.get('__consts', []), [])):
        raise ValueError('frontier-layernorm original LN scope/normalized_shape/eps/consts mismatch')
    predecessor._edge(index, activation, cell._input_irs[0])
    step = layernorm._next(index, activation)
    if (step.outputs[0].endpoint.writer != tuple(node)
            or step.outputs[0].endpoint.ref[:3] != tuple(node)[:3]):
        raise ValueError('frontier-layernorm original output writer/owner mismatch')
    # _binding reads EVERY original occurrence. Gate their raw vector types too.
    refs = {p.endpoint.ref for p in step.inputs[1:]}
    for other in index.raw.values():
        if not refs.intersection(map(tuple, other.inputs)):
            continue
        irs = getattr(other, '_input_irs', None)
        if irs is None or len(irs) != len(other.inputs):
            raise ValueError('frontier-layernorm complete parameter occurrence metadata required')
        for ref, ir in zip(other.inputs, irs, strict=True):
            if tuple(ref) in refs:
                _vector(ir)
    return step


def _cover(closed, owners):
    groups = {}
    for row in closed['frontier_units']:
        owner = _one((u for u in owners if _same_typed(u['unit'], row['unit'])),
                     'frontier-layernorm exact DP owner missing/ambiguous')
        if (type(row['unit']) is not int or not _same_typed(row['dimensions']['D'], len(owners))
                or not _same_typed((row['ranks'],row['positions']), (owner['ranks'],owner['positions']))
                or row['layout'] != 'sharded' or type(row['gather_axis']) is not int
                or row['gather_axis'] not in (1,2)):
            raise ValueError('frontier-layernorm exact DP layout/ranks/positions mismatch')
        groups.setdefault(tuple(row['sm_output_ref']), []).append(row['unit'])
    if not groups or any(len(us) != len(owners) or len(set(us)) != len(us)
                         or set(us) != {u['unit'] for u in owners} for us in groups.values()):
        raise ValueError('frontier-layernorm complete DP frontier cover required')


def _rename(line):
    return line.replace('layernormRead_', 'frontierLayernormRead_').replace(
        'layernormUnitFacts_', 'frontierLayernormUnitFacts_')


def render(sm, pm, lineages, validation, bound, execution_order):
    """Always rebuild the predecessor from these identical six inputs."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed frontier-layernorm original source: {exc}') from exc


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order, {'sm': build(sm), 'pm': build(pm)}):
        raise ValueError('frontier-layernorm complete typed execution order mismatch')
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    specs = adds._bound(lineages, bound)
    parameters = [l for l in lineages if l.role == Role.PARAMETER]
    if not _same_typed([r['lineage'] for r in bound['relations']], [asdict(l) for l in parameters]):
        raise ValueError('frontier-layernorm canonical bound spec order mismatch')
    for row, parameter in zip(bound['relations'], parameters, strict=True):
        if not _same_typed([u['unit'] for u in row['units']], [u.unit for u in parameter.units]):
            raise ValueError('frontier-layernorm canonical bound unit spec order mismatch')
    owners = validation._inputs[3]['config']['units']; D = len(owners)
    _cover(closed, owners)
    proofs, reads, units, frontier, retained, deferred, consumed = [], [], [], [], [], [], []
    seen, used = {}, set()
    for i, old in enumerate(closed['frontier_units']):
        g = _output(si, old['source_step'], old['sm_output_ref'])
        ps = [_output(pi, s, ref) for s, ref in zip(old['local_steps'], old['pm_output_refs'], strict=True)]
        middle._contract(old, g, ps)
        B, S, H = old['local_shape']; T = len(ps); u = old['unit']
        if (not _same_typed(old['dimensions'], dict(D=D,T=T,B=B,S=S,H=H))
                or not _same_typed(old['positions'], list(range(u*B,(u+1)*B)))
                or type(old['source_output_slot']) is not int
                or not 0 <= old['source_output_slot'] < len(old['source_step']['outputs'])
                or not _same_typed(old['source_step']['outputs'][old['source_output_slot']]['endpoint']['ref'], g.endpoint.ref)
                or not _same_typed(old['sm_output_tid'], g.endpoint.tid)
                or not _same_typed(old['pm_output_tids'], [p.endpoint.tid for p in ps])):
            raise ValueError('frontier-layernorm complete strong frontier dimensions/slot mismatch')
        sm_consumers = predecessor._consumers(si, [g])
        local_consumers = [predecessor._consumers(pi, [p]) for p in ps]
        consumers = [sm_consumers, *local_consumers]
        if old['gather_axis'] != 1:
            # Proven boundary facts survive, but layout alone is NOT skip identity.
            # A terminal boundary or a single matching later residual add is retained;
            # all other real consumers are explicitly deferred (not newly proved).
            kinds = [[op(c) for c in cs] for cs in consumers]
            skip = all(ks == [] for ks in kinds) or all(ks == ['FW_add'] for ks in kinds)
            if skip:
                retained.append(old)
            else:
                deferred.append(dict(old, reason='unsupported hidden-frontier forward consumer',
                    observed_consumer_ops=kinds))
            frontier.append(old)
            continue
        if not any(op(c) == 'FW_layernorm' for cs in consumers for c in cs):
            deferred.append(dict(old, reason='sequence frontier has no LayerNorm consumer',
                observed_consumer_ops=[[op(c) for c in cs] for cs in consumers]))
            frontier.append(old)
            continue
        if any(len(cs) != 1 or op(cs[0]) != 'FW_layernorm' for cs in consumers):
            raise ValueError('frontier-layernorm partial or fan-out LN consumer cover unsupported')
        global_ = _next(si, g)
        locals_ = [_next(pi, p) for p in ps]
        parent = si.raw[global_.node]._output_irs[0].parent.tid
        if any(not _same_typed(pi.raw[s.node]._output_irs[0].parent.tid, parent) for s in locals_):
            raise ValueError('frontier-layernorm SM/PM output parent identity mismatch')
        for role in (1, 2):
            parent = si.raw[global_.node]._input_irs[role].parent.tid
            if any(not _same_typed(pi.raw[s.node]._input_irs[role].parent.tid, parent) for s in locals_):
                raise ValueError('frontier-layernorm original parameter SM/PM parent identity mismatch')
        if any(s.node in used for s in locals_):
            raise ValueError('frontier-layernorm duplicate/cross-unit local consumer')
        used.update(s.node for s in locals_)
        params = [layernorm._parameter(si, pi, lineages, specs, role, global_, locals_, old, D) for role in (1, 2)]
        for view, label, step in [(sm, 'sm', global_), *((pm, 'pm', s) for s in locals_)]:
            key = (label, step.node)
            if key in seen:
                if not _same_typed(seen[key], step):
                    raise ValueError('frontier-layernorm shared source consumer ambiguity')
                continue
            proof, row = layernorm._read(view, label, step, order[label])
            proofs.extend(map(_rename, proof)); row['theorem'] = _rename(row['theorem'])
            reads.append(row); seen[key] = step
        proof, row = layernorm._unit(old, global_, locals_, params, D, len(specs))
        proofs.extend(map(_rename, proof))
        row.update(theorem=_rename(row['theorem']), facts_theorem=_rename(row['facts_theorem']),
            layout='sharded', sm_output_ref=list(global_.outputs[0].endpoint.ref),
            pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_], frontier_index=i,
            source_output_slot=0, predecessor_facts=old['facts_theorem'])
        row['sm_consumers'] = [list(c.node) for c in predecessor._consumers(si, global_.outputs)]
        row['pm_consumers'] = [list(c.node) for c in predecessor._consumers(pi, [s.outputs[0] for s in locals_])]
        units.append(row); frontier.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-frontier-layernorm-values-emitted-uncompiled', reads=reads, units=units,
        frontier_units=frontier, consumed_frontier_indices=consumed, retained_units=retained, deferred_units=deferred,
        lean_bytes=len(text.encode()), cost_scope='frontier LayerNorm fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
