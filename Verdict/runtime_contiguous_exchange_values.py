"""First original contiguous -> faithful AA(1,2), UNCOMPILED.

Fresh SAME six-argument contiguous rendering is the sole predecessor authority.
SM stays at contiguous. No view, matmul, or other frontier is skipped/advanced.
The parent owns capture, assembly, imports, compilation and acceptance.
"""
from Verdict import runtime_contiguous_values as predecessor
from Verdict import runtime_softmax_exchange_values as exchange
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_projection_values as projection
from Verdict import runtime_post_add_values as post
from Verdict import runtime_view_values as view
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op


def _boundary(index, cell, ports, ranks, j):
    """Tighten original-source authentication, reuse faithful geometry machinery."""
    if (not ranks or any(type(r) is not int or r < 0 for r in ranks)
            or type(j) is not int or not 0 <= j < len(ranks)
            or len(ports) != len(ranks) or len(set(ranks)) != len(ranks)
            or len({p.endpoint.ref for p in ports}) != len(ports)):
        raise ValueError('contiguous-exchange complete ordered integer sender cover required')
    node = projection._node(index, cell)
    if (not _same_typed(tuple(node), tuple(cell.node)) or type(node.rank) is not int
            or not _same_typed(cell.rank, node.rank) or op(cell) != 'AllToAllPrim'
            or str(index.view.node_opname(node)).split('.')[-1] != 'AllToAllPrim'):
        raise ValueError('contiguous-exchange original node/op identity mismatch')
    for method, refs in [('node_inputs', cell.inputs), ('node_outputs', cell.outputs)]:
        if not _same_typed([tuple(index.view.source_tensor(t)) for t in getattr(index.view, method)(node)],
                           [tuple(r) for r in refs]):
            raise ValueError('contiguous-exchange original ordered fullrefs mismatch')
    if type(cell.kwargs) is not dict:
        raise ValueError('contiguous-exchange original kwargs container mismatch')
    writer = _one((w for w in index.view._collective_source['writers'] if _same_typed(
        (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
         w['ref']['source_cid'], w['source_irname']), tuple(node))),
        'contiguous-exchange original writer missing/ambiguous')
    if type(writer['ref']['call_instance']) is not int or writer['ref']['call_instance'] < 0:
        raise ValueError('contiguous-exchange original call identity mismatch')
    for p in ports:
        if (len(p.parent_shape) != 4 or len(p.endpoint.shape) != 4 or len(p.bounds) != 4
                or any(type(n) is not int or n <= 0 for n in (*p.parent_shape, *p.endpoint.shape))
                or any(len(b) != 2 or any(type(n) is not int for n in b)
                       or not 0 <= b[0] < b[1] <= d or b[1]-b[0] != s
                       for b, d, s in zip(p.bounds, p.parent_shape, p.endpoint.shape, strict=True))):
            raise ValueError('contiguous-exchange exact integer shape/bounds required')
        producer = index.raw[p.endpoint.writer]
        irs = getattr(producer, '_output_irs', None)
        if irs is None or len(irs) != len(producer.outputs) or any(ir is None for ir in irs):
            raise ValueError('contiguous-exchange complete original producer cover required')
        original = irs[list(map(tuple, producer.outputs)).index(p.endpoint.ref)]
        if (type(original.parent.tid) is not int
                or not _same_typed(post._port(index, p.endpoint.ref, original), p)):
            raise ValueError('contiguous-exchange original producer metadata mismatch')
    outputs = getattr(cell, '_output_irs', None)
    if outputs is None or len(outputs) != 1 or outputs[0] is None:
        raise ValueError('contiguous-exchange original output metadata required')
    step, coverage = exchange._boundary(index, cell, ports, ranks, j)
    coverage['producer_metadata'] = 'all-peers'
    return step, coverage


def _read(source, step, order):
    schedule = order['execution_to_source']
    if (any(type(n) is not int for n in schedule)
            or sorted(schedule) != list(range(len(source.nodes())))):
        raise ValueError('contiguous-exchange incomplete original execution order')
    proof, row = exchange._read(source, step, order)
    name = f'contiguousExchangeRead_pm_{step.outputs[0].endpoint.tid}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row['theorem'] = name
    return proof, row


def _unit(old, global_, ports, steps, names):
    # D/T/B come from prior facts; S/heads/C and exact heads/T from actual inputs.
    proof, row = exchange._unit(old, global_, ports, steps, names)
    name = f'contiguousExchangeUnitFacts_{global_.endpoint.tid}_{old["unit"]}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row.update(theorem=name, facts_theorem=name)
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Never accept caller-provided predecessor/output facts."""
    try:
        _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed contiguous-exchange original source: {exc}') from exc


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, names, identities = [], [], [], {}, set()
    for i, old in enumerate(prior['frontier_units']):
        if old['layout'] != 'sharded' or not _same_typed(old['gather_axis'], 1):
            raise ValueError('contiguous-exchange requires sharded axis1 predecessor')
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], old['unit'])), 'contiguous-exchange DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (old['ranks'], old['positions'])):
            raise ValueError('contiguous-exchange original DP ownership/order mismatch')
        g = middle._output(si, old['source_step'])
        ports = [middle._output(pi, d) for d in old['local_steps']]
        middle._contract(old, g, ports)
        identity = (g.endpoint.ref, tuple(p.endpoint.ref for p in ports))
        if identity in identities:
            raise ValueError('contiguous-exchange duplicate frontier identity')
        identities.add(identity)
        steps = []
        for j, port in enumerate(ports):
            cell = view._consumer(pi, port)
            step, coverage = _boundary(pi, cell, ports, old['ranks'], j)
            if step.node in names:
                raise ValueError('contiguous-exchange duplicate/cross-DP original operation')
            proof, row = _read(pm, step, order['pm'])
            row.update(unit=old['unit'], frontier_index=i, **coverage)
            names[step.node] = row['theorem']
            proofs.extend(proof); reads.append(row); steps.append(step)
        proof, row = _unit(old, g, ports, steps, names)
        row['frontier_index'] = i
        for read in reads[-len(steps):]:
            read.update(dimensions=row['dimensions'], layout=row['layout'])
        proofs.extend(proof); units.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent owns actual capture, assembly and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-contiguous-exchange-values-emitted-uncompiled',
        reads=reads, units=units, frontier_units=units, deferred_units=[],
        consumed_frontier_indices=list(range(len(units))), lean_bytes=len(text.encode()),
        deferred_stage='after-contiguous-exchange: view/downstream unproved',
        cost_scope='new contiguous exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
