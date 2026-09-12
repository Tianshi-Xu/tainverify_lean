"""Pair complete hidden-sharded frontier facts at original ordered ADDs.

UNCOMPILED candidates only. No alias recovery, new mathematics, caller receipt,
output premise or completion claim. Unconsumed rows retain their original order.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_sequence_hidden_values as predecessor
from Verdict import runtime_frontier_layernorm_values as frontier
from Verdict import runtime_frontier_alias_exchange_values as source
from Verdict import runtime_attention_residual_values as residual
from Verdict import runtime_middle_exchange_values as middle
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build


def render(sm, pm, lineages, validation, bound, execution_order):
    """Refresh the SAME six objects exactly once; private seams are not authority."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, validation, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed frontier-add original source: {exc}') from exc


def _output(index, descriptor, ref):
    port = frontier._output(index, descriptor, ref)
    cell = index.raw[tuple(descriptor['node'])]
    if not _same_typed([asdict(index.endpoint(r)) for r in cell.inputs],
                       [p['endpoint'] for p in descriptor['inputs']]):
        raise ValueError('frontier-add producer original ordered input endpoints mismatch')
    return port


def _render(sm, pm, validation, order, closed):
    if not _same_typed(order, {'sm': build(sm), 'pm': build(pm)}):
        raise ValueError('frontier-add complete typed execution order mismatch')
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    owners = validation._inputs[3]['config']['units']; D = len(owners)
    frontier._cover(closed, owners)
    authenticated = []
    # Authenticate the ENTIRE frontier before selecting any operation.
    for old in closed['frontier_units']:
        g = _output(si, old['source_step'], old['sm_output_ref'])
        ps = [_output(pi, step, ref) for step, ref in
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
            raise ValueError('frontier-add complete strong frontier dimensions/slot mismatch')
        authenticated.append((old, g, ps))
    consumers = [[source._consumers(si, [g]), *[source._consumers(pi, [p]) for p in ps]]
                 for old, g, ps in authenticated]
    proofs, reads, units, retained, deferred = [], [], [], [], []
    names, replacements, consumed, used, groups = {}, {}, set(), set(), {}
    for i, (old, g, ps) in enumerate(authenticated):
        if i in consumed:
            continue
        cs = consumers[i]
        if old['gather_axis'] != 2 or not all(len(xs) == 1 and op(xs[0]) == 'FW_add' for xs in cs):
            continue
        cell = cs[0][0]
        # Source operand order is the proof record order, never a semantic label.
        indices = []
        for ref in cell.inputs:
            matches = [j for j,(r,p,_) in enumerate(authenticated)
                       if _same_typed(r['unit'],old['unit']) and _same_typed(p.endpoint.ref,tuple(ref))]
            if len(matches) != 1:
                break
            indices.append(matches[0])
        if len(indices) != 2:
            continue
        if len(set(indices)) != 2 or consumed.intersection(indices):
            raise ValueError('frontier-add duplicate operand consumption unsupported')
        records = [authenticated[j][0] for j in indices]
        keys = ('unit','ranks','positions','dimensions','layout','gather_axis','global_shape','local_shape')
        if not _same_typed([records[0][k] for k in keys], [records[1][k] for k in keys]):
            raise ValueError('frontier-add operand DP shape/layout mismatch')
        for j in indices:
            if (not all(len(xs) == 1 and op(xs[0]) == 'FW_add' for xs in consumers[j])
                    or not _same_typed([tuple(xs[0].node) for xs in consumers[j]], [tuple(xs[0].node) for xs in cs])):
                raise ValueError('frontier-add partial/fan-out or mismatched original ADD pairing')
        global_ = residual._boundary(si, cell, tuple(authenticated[j][1] for j in indices))
        locals_ = []
        for k, rank in enumerate(old['ranks']):
            pc = cs[k+1][0]
            if not _same_typed(pc.rank, rank) or tuple(pc.node) in used:
                raise ValueError('frontier-add duplicate/cross-DP local ADD')
            local = residual._boundary(pi, pc, tuple(authenticated[j][2][k] for j in indices))
            if not _same_typed(pc._output_irs[0].parent.tid, cell._output_irs[0].parent.tid):
                raise ValueError('frontier-add SM/PM original output parent identity mismatch')
            locals_.append(local); used.add(local.node)
        for label, view, step in [('sm',sm,global_), *(('pm',pm,s) for s in locals_)]:
            if step.node not in names:
                proof, row = residual._read(view,label,step,order[label])
                name = f'frontierAddRead_{label}_{step.outputs[0].endpoint.tid}'
                proofs.extend(line.replace(row['theorem'],name) for line in proof)
                row.update(theorem=name,unit=old['unit'],input_frontier_indices=indices)
                reads.append(row); names[step.node] = name
        proof, row = residual._unit(records[0],global_,locals_,records,names)
        name = f'frontierAddUnitFacts_{row["sm_output_tid"]}_{old["unit"]}'
        proofs.extend(line.replace(row['theorem'],name) for line in proof)
        row.update(theorem=name,facts_theorem=name,source_output_slot=0,input_frontier_indices=indices)
        units.append(row); replacements[min(indices)] = row; consumed.update(indices)
        groups.setdefault(global_.node,[]).append(old['unit'])
    if any(not _same_typed(sorted(us), sorted(o['unit'] for o in owners)) for us in groups.values()):
        raise ValueError('frontier-add incomplete original ADD DP cover')
    result = []
    for i,(old,_,_) in enumerate(authenticated):
        if i in replacements:
            result.append(replacements[i])
        if i in consumed:
            continue
        result.append(old)
        kinds = [[op(c) for c in xs] for xs in consumers[i]]
        if all(not ks for ks in kinds):
            retained.append(old)
        else:
            deferred.append(dict(old,reason='no complete exclusive hidden ADD operand pair',observed_consumer_ops=kinds))
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-frontier-add-values-emitted-uncompiled',reads=reads,units=units,
        frontier_units=result,retained_units=retained,deferred_units=deferred,
        consumed_frontier_indices=sorted(consumed),lean_bytes=len(text.encode()),
        cost_scope='paired frontier ADD fragment only; excludes predecessors, frame and imports',
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
