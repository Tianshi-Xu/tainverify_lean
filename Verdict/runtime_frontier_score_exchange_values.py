"""Original score AA(1,3) frontier, UNCOMPILED.

The SM endpoint remains the ordered Q/K score, NOT its following division.
Only PM exchange reads and complete conditional facts are new. Both SM and PM
scalar successors are inventoried without consuming or proving their values.
"""
from Verdict import runtime_frontier_score_matmul_values as predecessor
from Verdict import runtime_matmul_exchange_values as backend
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_schedule import build
from Verdict.runtime_embedding_units import _one

_view = predecessor._view
_head = predecessor.predecessor._head
_transpose = predecessor._transpose


def render(sm, pm, lineages, validation, bound, execution_order):
    """One public predecessor call with the identical six authority objects."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError, ZeroDivisionError) as exc:
        raise ValueError(f'malformed frontier score-exchange original source: {exc}') from exc


def _frontiers(sm, pm, si, pi, lineages, validation, bound, order, closed):
    """Expand the binary join before reauthenticating the original inventory.

    Histories are candidates only. Rebuild every stage from the source-bound
    view/fork boundary, including both Q/K operands, then compare the COMPLETE
    score detail (names, joins, descriptors, histories and classifications).
    Never pass merged score outputs to a pre-matmul sharded frontier gate.
    """
    views = []
    def peel(row, active):
        if id(row) in active:
            raise ValueError('score-exchange cyclic candidate history')
        active = active | {id(row)}
        kind = op(si.raw[tuple(row['source_step']['node'])])
        if kind == 'FW_matmul':
            if len(row['input_frontiers']) != 2:
                raise ValueError('score-exchange complete binary history required')
            for operand in row['input_frontiers']: peel(operand, active)
        elif kind == 'FW_multiref' or (kind == 'FW_view' and
                all(op(pi.raw[tuple(s['node'])]) == 'FW_view' for s in row['local_steps'])):
            views.append(row)
        else:
            peel(row['input_frontier'], active)
    for row in closed['frontier_units']: peel(row, set())
    selected = [i for i,r in enumerate(views) if op(si.raw[tuple(r['source_step']['node'])]) == 'FW_view']
    candidate = dict(frontier_units=views, units=[views[i] for i in selected],
        consumed_frontier_indices=selected, retained_units=[r for i,r in enumerate(views) if i not in selected],
        deferred_units=[])
    _, head = _head._render(sm,pm,lineages,validation,bound,order,candidate)
    _, first = _transpose._render(sm,pm,lineages,validation,bound,order,head)
    _, post = predecessor._post._render(sm,pm,lineages,validation,bound,order,first)
    _, middle = predecessor.predecessor._render(sm,pm,lineages,validation,bound,order,post)
    _, expected = predecessor._render(sm,pm,lineages,validation,bound,order,middle)
    if not _same_typed(closed, expected):
        raise ValueError('score-exchange complete original binary/history/frontier mismatch')
    return closed['frontier_units']


def _boundary(index, cell, ports, ranks, j):
    originals = [_transpose._producer(index, ref) for ref in cell.inputs]
    if not _same_typed(tuple(ports), tuple(originals)):
        raise ValueError('score-exchange complete original ordered peer descriptors mismatch')
    strict, selected, coverage = _head._boundary(index,cell,ports,ranks,j)
    actual, writer = backend._boundary(index,cell,ports,ranks,j)
    if selected is not backend.exchange or not _same_typed(strict,actual):
        raise ValueError('score-exchange only original rank4 AA(1,3) is consumable')
    return actual, dict(coverage, **writer)


def _read(index, step, order):
    actual, coverage = _boundary(index,index.raw[step.node],step.inputs,step.ranks,step.local_index)
    if step.node[0] != 'p' or not _same_typed(actual,step) or not _same_typed(order,build(index.view)):
        raise ValueError('score-exchange original fresh step/full schedule mismatch')
    proof, row = backend._read(index.view,actual,order)
    row.update(coverage,source_signature=index.raw[step.node].ir.signature)
    return proof, row


def _classification(source_kind, cells):
    """Only independently authenticated original residuals are retained skips."""
    if source_kind == 'FW_multiref': return 'retained'
    if source_kind == 'FW_matmul' and cells and all(op(c) == 'AllToAllPrim' for c in cells):
        return 'ready'
    return 'deferred'


def _unit(index, prior, global_, ports, steps, names):
    """Fresh ordered receiver/remote-peer cover before the actual five-arg law.

    The complete prior fact is source-authenticated by _frontiers, not inferred
    from matching shapes or invented names here.
    """
    if (not _same_typed([s.node[1] for s in steps],prior['ranks'])
            or len({s.node for s in steps}) != len(steps)
            or not _same_typed([list(p.endpoint.ref) for p in ports],prior['pm_output_refs'])
            or not _same_typed(list(global_.endpoint.ref),prior['sm_output_ref'])):
        raise ValueError('score-exchange original ordered receiver/DP/input cover mismatch')
    cells = _view.column._consumers(index,ports)
    if len(cells) != len(steps) or {tuple(c.node) for c in cells} != {s.node for s in steps}:
        raise ValueError('score-exchange complete original first receiver cover mismatch')
    for j,step in enumerate(steps):
        actual,_ = _boundary(index,index.raw[step.node],ports,prior['ranks'],j)
        if not _same_typed(actual,step):
            raise ValueError('score-exchange complete original receiver/remote-peer step mismatch')
    return backend._unit(prior,global_,ports,steps,names)


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order,dict(sm=build(sm),pm=build(pm))):
        raise ValueError('score-exchange complete typed execution/inverse order mismatch')
    si,pi = (_Index(v,raw) for v,raw in zip((sm,pm),validation._inputs[:2],strict=True))
    old = _frontiers(sm,pm,si,pi,lineages,validation,bound,order,closed)
    proofs,reads,units,result,retained,deferred,consumed = [],[],[],[],[],[],[]
    seen=set(); names={}
    for i,row in enumerate(old):
        g = _transpose._producer(si,row['sm_output_ref'])
        ps = [_transpose._producer(pi,ref) for ref in row['pm_output_refs']]
        cells = _view.column._consumers(pi,ps)
        classification = _classification(op(si.raw[tuple(row['source_step']['node'])]),cells)
        if classification == 'retained':
            result.append(row); retained.append(row); continue
        backend.middle._contract(row,g,ps)
        if classification == 'deferred':
            result.append(row)
            deferred.append(dict(frontier_index=i,unit=row['unit'],source_boundary=row,
                reason='unavailable-or-unsupported-original-consumer',value_proved=False))
            continue
        if len(ps) <= 1 or len(cells) != len(ps):
            raise ValueError('score-exchange complete original receiver cover required')
        steps=[]
        for j,rank in enumerate(row['ranks']):
            cell = _one((c for c in cells if _same_typed(c.rank,rank)), 'score-exchange receiver missing/ambiguous')
            step,_ = _boundary(pi,cell,ps,row['ranks'],j)
            if step.node in seen: raise ValueError('score-exchange duplicate/cross-DP original receiver')
            seen.add(step.node)
            proof,read = _read(pi,step,order['pm'])
            name = read['theorem'].replace('matmulExchangeRead_','frontierScoreExchangeRead_')
            proofs.extend(s.replace(read['theorem'],name) for s in proof)
            read.update(theorem=name,unit=row['unit'],frontier_index=i)
            reads.append(read); names[step.node]=name; steps.append(step)
        proof,fresh = _unit(pi,row,g,ps,steps,names)
        name = fresh['theorem'].replace('matmulExchangeUnitFacts_','frontierScoreExchangeUnitFacts_')
        proofs.extend(s.replace(fresh['theorem'],name) for s in proof)
        shape = list(steps[0].outputs[0].endpoint.shape)
        fresh.update(theorem=name,facts_theorem=name,input_frontier=row,predecessor_facts=row['facts_theorem'],
            source_output_slot=row['source_output_slot'],slot=row['source_output_slot'],pm_output_slots=[0 for _ in steps],
            frontier_index=i,dimensions=dict(D=row['dimensions']['D'],T=len(ps),**dict(zip(('B','S','H','C'),shape))),
            axes=[1,3],deferred_stage='after-score-exchange: original SM and PM division values unproved')
        fresh.update(predecessor._census(si,pi,g,[s.outputs[0] for s in steps]))
        units.append(fresh); result.append(fresh); consumed.append(i)
    text='\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, aggregate costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld','noncomputable section','set_option maxHeartbeats 500000',
        *proofs,'end','end TrainVerify.Denote.RuntimeWorld',''])
    return text,dict(status='source-frontier-score-exchange-values-emitted-uncompiled',reads=reads,units=units,
        frontier_units=result,retained_units=retained,deferred_units=deferred,consumed_frontier_indices=consumed,
        lean_bytes=len(text.encode()),cost_scope='score exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
