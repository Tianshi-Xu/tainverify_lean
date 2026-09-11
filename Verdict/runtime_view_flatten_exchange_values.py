"""Original rank-three flatten-view -> faithful AA(2,1), UNCOMPILED.

Fresh SAME-six flatten facts are the sole authority. SM remains at its view;
only immediate PM sequence-split then hidden-gather operations are advanced.
The parent owns capture, wiring, imports, assembly and kernel acceptance.
"""
from dataclasses import asdict

from Verdict import runtime_view_flatten_values as predecessor
from Verdict import runtime_projection_exchange_values as exchange
from Verdict import runtime_embedding_route_values as primitive
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_view_values as view
from Verdict import runtime_projection_values as projection
from Verdict import runtime_post_add_values as post
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed


def _boundary(index, cell, ports, ranks, j):
    """Authenticate original sources before deriving a receiver's geometry."""
    if (not ranks or any(type(r) is not int or r < 0 for r in ranks)
            or type(j) is not int or not 0 <= j < len(ranks)
            or len(ports) != len(ranks) or len(set(ranks)) != len(ranks)
            or len({p.endpoint.ref for p in ports}) != len(ports)):
        raise ValueError('view-flatten-exchange complete ordered integer sender cover required')
    node = projection._node(index, cell)
    if (not _same_typed(tuple(node), tuple(cell.node)) or type(node.rank) is not int
            or not _same_typed(cell.rank, node.rank)
            or str(index.view.node_opname(node)).split('.')[-1] != 'AllToAllPrim'):
        raise ValueError('view-flatten-exchange original node/op identity mismatch')
    for method, refs in [('node_inputs', cell.inputs), ('node_outputs', cell.outputs)]:
        if not _same_typed([tuple(index.view.source_tensor(t)) for t in getattr(index.view, method)(node)],
                           [tuple(r) for r in refs]):
            raise ValueError('view-flatten-exchange original ordered fullrefs mismatch')
    if type(cell.kwargs) is not dict or not _same_typed(cell.kwargs, index.view.node_kwargs(node)):
        raise ValueError('view-flatten-exchange original raw kwargs mismatch')
    scope = _one((s for s in index.view.collective_scopes.values() if tuple(s.node) == tuple(node)),
        'view-flatten-exchange original scope missing/ambiguous')
    if not _same_typed(scope.params, (2, 1)):
        raise ValueError('view-flatten-exchange exact integer params required')
    writer = _one((w for w in index.view._collective_source['writers'] if _same_typed(
        (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
         w['ref']['source_cid'], w['source_irname']), tuple(node))),
        'view-flatten-exchange original writer missing/ambiguous')
    if type(writer['ref']['call_instance']) is not int or writer['ref']['call_instance'] < 0:
        raise ValueError('view-flatten-exchange original call identity mismatch')
    fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
    for key, refs in [('inputs', cell.inputs), ('outputs', cell.outputs)]:
        if not _same_typed(writer[key], [dict(zip(fields, ref, strict=True)) for ref in refs]):
            raise ValueError('view-flatten-exchange source writer ordered fullrefs mismatch')
    for p in ports:
        if (len(p.parent_shape) != 3 or len(p.endpoint.shape) != 3 or len(p.bounds) != 3
                or any(type(n) is not int or n <= 0 for n in (*p.parent_shape, *p.endpoint.shape))
                or any(len(b) != 2 or any(type(n) is not int for n in b)
                       or not 0 <= b[0] < b[1] <= d or b[1]-b[0] != s
                       for b, d, s in zip(p.bounds, p.parent_shape, p.endpoint.shape, strict=True))):
            raise ValueError('view-flatten-exchange exact integer rank-three shape/bounds required')
        producer = index.raw[p.endpoint.writer]
        irs = getattr(producer, '_output_irs', None)
        if irs is None or len(irs) != len(producer.outputs) or any(ir is None for ir in irs):
            raise ValueError('view-flatten-exchange complete original producer cover required')
        original = irs[list(map(tuple, producer.outputs)).index(p.endpoint.ref)]
        if (type(original.parent.tid) is not int
                or not _same_typed(post._port(index, p.endpoint.ref, original), p)):
            raise ValueError('view-flatten-exchange original producer metadata mismatch')
    outputs = getattr(cell, '_output_irs', None)
    if (outputs is None or len(outputs) != 1 or outputs[0] is None
            or type(outputs[0].parent.tid) is not int):
        raise ValueError('view-flatten-exchange complete typed original output metadata required')
    step, coverage = exchange._boundary(index, cell, ports, ranks, j)
    coverage['producer_metadata'] = 'all-peers'
    inputs = getattr(cell, '_input_irs', None)
    coverage['input_parent_identity'] = 'not-observed'
    if inputs is not None:
        expected = [ports[j]] if len(inputs) == 1 and len(ports) > 1 else ports
        for p, ir in zip(expected, inputs, strict=True):
            producer = index.raw[p.endpoint.writer]
            original = producer._output_irs[list(map(tuple, producer.outputs)).index(p.endpoint.ref)]
            if (type(ir.parent.tid) is not int or type(original.parent.tid) is not int
                    or not _same_typed(ir.parent.tid, original.parent.tid)):
                raise ValueError('view-flatten-exchange original producer/consumer parent identity mismatch')
        coverage['input_parent_identity'] = coverage['input_metadata']
    return step, coverage


def _read(source, step, order):
    proof, row = primitive._read(source, 'pm', step, order)
    name = f'viewFlattenExchangeRead_pm_{step.outputs[0].endpoint.tid}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row.update(theorem=name, request='group', params=[2, 1],
        source_kwargs=dict(source.node_kwargs(next(n for n in source.nodes() if tuple(n) == step.node))),
        operand_nonwrite_source_indices=order['execution_to_source'][row['execution_index']:])
    return proof, row


def _unit(old, global_, ports, steps, names):
    D, T, B = (old['dimensions'][k] for k in ('D', 'T', 'B'))
    middle._contract(old, global_, ports)
    _, ST, H = ports[0].endpoint.shape
    S, rem = divmod(ST, T)
    if rem or S <= 0:
        raise ValueError('view-flatten-exchange nondivisible actual sequence')
    u = old['unit']; g = global_.endpoint.tid
    name = f'viewFlattenExchangeUnitFacts_{g}_{u}'
    row = dict(theorem=name, facts_theorem=name, predecessor=old['facts_theorem'],
        family='AllToAllPrim', unit=u, ranks=old['ranks'], positions=old['positions'],
        dimensions=dict(D=D, T=T, B=B, S=S, H=H), layout='sharded',
        input_gather_axis=2, gather_axis=1, output_gather_axis=1, split_axis=1,
        global_shape=[B*D, ST, H*T], input_shape=[B, ST, H], local_shape=[B, S, H*T],
        sm_output_tid=g, sm_output_ref=list(global_.endpoint.ref),
        pm_output_tids=[s.outputs[0].endpoint.tid for s in steps],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in steps],
        input_refs=[list(p.endpoint.ref) for p in ports],
        source_step=old['source_step'], local_steps=[asdict(s) for s in steps])
    middle._contract(row, global_, [s.outputs[0] for s in steps])
    xs = _list(f'q {p.endpoint.tid}' for p in ports)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in steps)
    terms = _list(f'AllToAllSourceFaithful.tensor {T} {j} 2 1 {xs}' for j in range(T))
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {g}).shape = {row["global_shape"]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {g}) = allGatherPrimDimN 1 {T} 0 {ys} := by',
        f'  have predecessor := {old["facts_theorem"]} s p t q hs hp hvalues',
        f'  have outputs : {ys} = List.ofFn (fun dst : Fin {T} => AllToAllSourceFaithful.tensor {T} dst.val 2 1 {xs}) := by',
        f'    change {ys} = {terms}',
        '    exact '+_cons_equal([f'{names[s.node]} p q hp' for s in steps]),
        f'  exact SourceHiddenSequenceExchange.output_facts {D} {u} {T} {B} {S} {H} (t {g}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) rfl predecessor.2.1 predecessor.1 predecessor.2.2 outputs',
        f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Never accept caller-supplied receipts, output facts, or repaired order."""
    try:
        _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed view-flatten-exchange original source: {exc}') from exc


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, names, identities = [], [], [], {}, set()
    for i, old in enumerate(prior['frontier_units']):
        if old['layout'] != 'sharded' or not _same_typed(old['gather_axis'], 2):
            raise ValueError('view-flatten-exchange requires axis2 sharded predecessor')
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], old['unit'])), 'view-flatten-exchange DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (old['ranks'], old['positions'])):
            raise ValueError('view-flatten-exchange original DP ownership/order mismatch')
        g = middle._output(si, old['source_step'])
        ports = [middle._output(pi, d) for d in old['local_steps']]
        middle._contract(old, g, ports)
        identity = (g.endpoint.ref, tuple(p.endpoint.ref for p in ports))
        if identity in identities:
            raise ValueError('view-flatten-exchange duplicate frontier identity')
        identities.add(identity)
        steps = []
        for j, port in enumerate(ports):
            cell = view._consumer(pi, port)
            step, coverage = _boundary(pi, cell, ports, old['ranks'], j)
            if step.node in names:
                raise ValueError('view-flatten-exchange duplicate/cross-DP original operation')
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
    return text, dict(status='source-view-flatten-exchange-values-emitted-uncompiled',
        reads=reads, units=units, frontier_units=units, deferred_units=[],
        consumed_frontier_indices=list(range(len(units))), lean_bytes=len(text.encode()),
        deferred_stage='after-flatten-exchange: downstream unproved',
        cost_scope='new flatten exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
