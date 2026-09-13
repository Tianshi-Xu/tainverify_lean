"""Fresh complete next-LN -> every sequence-layout multiref output.

Only aliases are consumed. Hidden skips and explicit deferrals retain their
complete facts in predecessor order; downstream collectives/linear are not
consumed. Parent owns aggregate budget, imports, assembly and kernel checking.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_next_layernorm_values as predecessor
from Verdict import runtime_frontier_layernorm_values as layernorm
from Verdict import runtime_frontier_alias_exchange_values as alias
from Verdict import runtime_post_add_values as post
from Verdict import runtime_add_values as adds
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_projection_values as projection
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh SAME-six predecessor exactly once; never a caller receipt."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed sequence alias original source: {exc}') from exc


def _gather_consumer(index, cell, refs):
    """Authenticate a discovery boundary, not an AllGather value fact.

    The public predecessor revalidates live adapter/export authority. Retained
    collective IR may be local-only, but every logical peer must independently
    resolve to its own original producer output; never clone local metadata.
    """
    ranks = cell.kwargs.get('ranks')
    if (type(ranks) not in (tuple, list) or not ranks
            or any(type(r) is not int or r < 0 for r in ranks)
            or len(set(ranks)) != len(ranks) or cell.rank not in ranks
            or len(refs) != len(ranks)
            or not _same_typed([r[:3] for r in refs],
                [(cell.node[0], rank, cell.node[2]) for rank in ranks])):
        raise ValueError('sequence alias AllGather complete ordered rank peers required')
    ranks = tuple(ranks); j = ranks.index(cell.rank)
    kw = dict(cell.kwargs); kw.pop('ranks')
    consts = kw.pop('__consts', [])
    if not _same_typed(kw, dict(dim=1)) or not _same_typed(consts, []):
        raise ValueError('sequence alias AllGather original kwargs mismatch')
    ports, originals = [], []
    for ref in refs:
        writer = index.writers.get(ref)
        if writer is None:
            raise ValueError('sequence alias AllGather peer original producer required')
        producer = index.raw[tuple(writer)]
        alias.residual._identity(index, producer)
        port = _one((p for p in alias._ports(index, producer, 'outputs') if p.endpoint.ref == ref),
                    'sequence alias AllGather peer output missing/ambiguous')
        ports.append(port); originals.append(alias._original(index, port))
    if any(not _same_typed(ir.parent.tid, originals[0].parent.tid) for ir in originals):
        raise ValueError('sequence alias AllGather peer parent identity mismatch')
    irs = getattr(cell, '_input_irs', None)
    outs = getattr(cell, '_output_irs', None)
    if irs is None or len(irs) not in (1, len(ports)) or outs is None or len(outs) != 1:
        raise ValueError('sequence alias AllGather complete original metadata required')
    selected = (ports[j],) if len(irs) == 1 else ports
    for port, ir in zip(selected, irs, strict=True):
        alias._edge(index, port, ir)
    alias._raw(outs[0])
    if not _same_typed(outs[0].parent.tid, originals[j].parent.tid):
        raise ValueError('sequence alias AllGather output parent identity mismatch')
    scope = _one((s for s in index.view.collective_scopes.values()
                  if _same_typed(tuple(s.node), tuple(cell.node))),
                 'sequence alias AllGather scope missing/ambiguous')
    writer = _one((w for w in index.view._collective_source['writers'] if _same_typed(
        (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
         w['ref']['source_cid'], w['source_irname']), tuple(cell.node))),
        'sequence alias AllGather writer missing/ambiguous')
    if (scope.source_writer != writer['export_id'] or len(cell.outputs) != 1
            or not _same_typed(scope.output_tid, index.endpoint(cell.outputs[0]).tid)):
        raise ValueError('sequence alias AllGather scope writer/output mismatch')
    # Reuse source adapter for complete sequence partition, local-index binding,
    # output shape/bounds, ordered fullrefs and local-only/all-peer metadata.
    # Its permissive absent-metadata mode is intentionally excluded above.
    projection._gather(index, cell, tuple(ports), ranks, j)


def _consumers(index, ports):
    """Full lowered discovery with ordinary edges and strict collective IR."""
    by_ref = {p.endpoint.ref: p for p in ports}
    cells = []
    for node in index.view.nodes():
        refs = [tuple(index.view.source_tensor(t)) for t in index.view.node_inputs(node)]
        if not by_ref.keys() & set(refs):
            continue
        cell = index.raw[tuple(node)]
        alias.residual._identity(index, cell)
        if op(cell).startswith('BW_'):
            continue
        if op(cell) == 'AllGatherPrim':
            # Bind requested descriptors as well as otherwise-unrequested peers.
            for ref in refs:
                if ref in by_ref:
                    alias._original(index, by_ref[ref])
            _gather_consumer(index, cell, refs)
        elif op(cell) != 'AllToAllPrim':
            irs = getattr(cell, '_input_irs', None)
            if irs is None or len(irs) != len(refs):
                raise ValueError('frontier consumer complete original metadata required')
            for ref, ir in zip(refs, irs, strict=True):
                if ref in by_ref:
                    alias._edge(index, by_ref[ref], ir)
        cells.append(cell)
    return cells


def _unit(old, global_, locals_, slot, names, frontier_index):
    g = global_.outputs[slot]; ps = [step.outputs[slot] for step in locals_]
    name = f'frontierSequenceAliasFacts_{g.endpoint.tid}_{old["unit"]}'
    row = dict(theorem=name, facts_theorem=name, unit=old['unit'],
        ranks=old['ranks'], positions=old['positions'], dimensions=old['dimensions'],
        layout=old['layout'], gather_axis=old['gather_axis'],
        global_shape=old['global_shape'], local_shape=old['local_shape'],
        sm_output_tid=g.endpoint.tid, sm_output_ref=list(g.endpoint.ref),
        pm_output_tids=[p.endpoint.tid for p in ps], pm_output_refs=[list(p.endpoint.ref) for p in ps],
        source_step=asdict(global_), local_steps=[asdict(step) for step in locals_],
        slot=slot, source_output_slot=slot, frontier_index=frontier_index,
        predecessor_facts=old['facts_theorem'])
    middle._contract(row, g, ps)
    equations = [f'{names[global_.node]} s t hs {g.endpoint.tid} {adds._member(slot)}']
    equations += [f'{names[step.node]} p q hp {p.endpoint.tid} {adds._member(slot)}'
                  for step,p in zip(locals_,ps,strict=True)]
    return [*alias._facts_header(name,row), '  rw ['+', '.join(equations)+']',
        f'  exact {old["facts_theorem"]} s p t q hs hp hvalues', f'#print axioms {name}'], row


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order, {'sm': build(sm), 'pm': build(pm)}):
        raise ValueError('sequence alias complete typed execution order mismatch')
    si, pi = (_Index(v,raw) for v,raw in zip((sm,pm),validation._inputs[:2],strict=True))
    owners = validation._inputs[3]['config']['units']
    layernorm._cover(closed,owners)
    proofs, reads, units, frontier, retained, deferred, consumed = [], [], [], [], [], [], []
    names, seen, local_seen = {}, {}, set()
    for i,old in enumerate(closed['frontier_units']):
        g = layernorm._output(si,old['source_step'],old['sm_output_ref'])
        ps = [layernorm._output(pi,s,ref) for s,ref in zip(old['local_steps'],old['pm_output_refs'],strict=True)]
        # Validate every old row, including multi-output hidden skips, before
        # selecting a consumer. Never let Python bool/float equality certify shape.
        B,S,H = old['local_shape']; u = old['unit']
        if (any(type(n) is not int or n <= 0 for n in
                (*old['local_shape'], *old['global_shape'], *old['dimensions'].values()))
                or not _same_typed(old['dimensions'],dict(D=len(owners),T=len(ps),B=B,S=S,H=H))
                or not _same_typed(old['positions'],list(range(u*B,(u+1)*B)))
                or type(old['source_output_slot']) is not int
                or not 0 <= old['source_output_slot'] < len(old['source_step']['outputs'])
                or not _same_typed(old['source_step']['outputs'][old['source_output_slot']]['endpoint']['ref'],g.endpoint.ref)
                or not _same_typed(old['sm_output_tid'],g.endpoint.tid)
                or not _same_typed(old['pm_output_tids'],[p.endpoint.tid for p in ps])):
            raise ValueError('sequence alias complete typed predecessor dimensions/shape/slot mismatch')
        middle._contract(old,g,ps)
        consumers = [_consumers(si,[g]), *[_consumers(pi,[p]) for p in ps]]
        kinds = [[op(c) for c in cs] for cs in consumers]
        if old['gather_axis'] != 1:
            if all(ks == [] for ks in kinds) or all(ks == ['FW_add'] for ks in kinds):
                retained.append(old)
            else:
                deferred.append(dict(old,reason='unsupported hidden-frontier forward consumer',observed_consumer_ops=kinds))
            frontier.append(old)
            continue
        if not any('FW_multiref' in ks for ks in kinds):
            deferred.append(dict(old,reason='sequence frontier has no multiref consumer',observed_consumer_ops=kinds))
            frontier.append(old)
            continue
        if any(ks != ['FW_multiref'] for ks in kinds):
            raise ValueError('sequence alias partial or mixed/fan-out consumer cover unsupported')
        global_ = alias._alias(si,old['source_step'])
        locals_ = [alias._alias(pi,s) for s in old['local_steps']]
        parents = [alias._original(si,p).parent.tid for p in global_.outputs]
        for step in locals_:
            if step.node in local_seen:
                raise ValueError('sequence alias duplicate/cross-DP local alias')
            local_seen.add(step.node)
            if not _same_typed([alias._original(pi,p).parent.tid for p in step.outputs],parents):
                raise ValueError('sequence alias ordered SM/PM output parent mismatch')
        for view,label,step in [(sm,'sm',global_), *((pm,'pm',s) for s in locals_)]:
            if step.node in names:
                if not _same_typed(seen[step.node],step):
                    raise ValueError('sequence alias shared global descriptor mismatch')
                continue
            proof,row = post._read(view,label,step,order[label])
            name = f'frontierSequenceMultirefRead_{label}_{step.outputs[0].endpoint.tid}'
            proofs.extend(line.replace(row['theorem'],name) for line in proof)
            row.update(theorem=name,frontier_index=i)
            reads.append(row); names[step.node] = name; seen[step.node] = step
        for slot in range(len(global_.outputs)):
            proof,row = _unit(old,global_,locals_,slot,names,i)
            row['sm_consumers'] = [list(c.node) for c in _consumers(si,[global_.outputs[slot]])]
            row['pm_consumers'] = [list(c.node) for c in _consumers(pi,[s.outputs[slot] for s in locals_])]
            proofs.extend(proof); units.append(row); frontier.append(row)
        consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text,dict(status='source-frontier-sequence-alias-values-emitted-uncompiled',reads=reads,
        units=units,alias_units=units,frontier_units=frontier,retained_units=retained,deferred_units=deferred,
        consumed_frontier_indices=consumed,lean_bytes=len(text.encode()),
        cost_scope='sequence alias fragment only; excludes predecessors, frame and imports',
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
