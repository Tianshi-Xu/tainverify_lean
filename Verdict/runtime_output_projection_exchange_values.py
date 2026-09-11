"""Original output linear -> faithful rank-three AA(1,2), UNCOMPILED.

Fresh SAME-six output-projection facts are the sole authority. SM remains at
its linear; PM hidden splits precede ordered sequence gathering. No residual
add, capture, assembly, import, public or Torch refinement is claimed here.
"""
from dataclasses import asdict

from Verdict import runtime_output_projection_values as predecessor
from Verdict import runtime_embedding_routes as routes
from Verdict import runtime_embedding_route_values as primitive
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_view_values as view
from Verdict import runtime_projection_values as projection
from Verdict import runtime_post_add_values as post
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op


def _boundary(index, cell, ports, ranks, j):
    """Authenticate original sources before deriving a receiver's geometry."""
    if (not ranks or any(type(r) is not int or r < 0 for r in ranks)
            or type(j) is not int or not 0 <= j < len(ranks)
            or len(ports) != len(ranks) or len(set(ranks)) != len(ranks)
            or len({p.endpoint.ref for p in ports}) != len(ports)):
        raise ValueError('output-projection-exchange complete ordered integer sender cover required')
    node = projection._node(index, cell)
    if (not _same_typed(tuple(node), tuple(cell.node)) or type(node.rank) is not int
            or not _same_typed(cell.rank, node.rank)
            or str(index.view.node_opname(node)).split('.')[-1] != 'AllToAllPrim'):
        raise ValueError('output-projection-exchange original node/op identity mismatch')
    for method, refs in [('node_inputs', cell.inputs), ('node_outputs', cell.outputs)]:
        if not _same_typed([tuple(index.view.source_tensor(t)) for t in getattr(index.view, method)(node)],
                           [tuple(r) for r in refs]):
            raise ValueError('output-projection-exchange original ordered fullrefs mismatch')
    if type(cell.kwargs) is not dict or not _same_typed(cell.kwargs, index.view.node_kwargs(node)):
        raise ValueError('output-projection-exchange original raw kwargs mismatch')
    scope = _one((s for s in index.view.collective_scopes.values() if tuple(s.node) == tuple(node)),
        'output-projection-exchange original scope missing/ambiguous')
    if not _same_typed(scope.params, (1, 2)):
        raise ValueError('output-projection-exchange exact integer params required')
    writer = _one((w for w in index.view._collective_source['writers'] if _same_typed(
        (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
         w['ref']['source_cid'], w['source_irname']), tuple(node))),
        'output-projection-exchange original writer missing/ambiguous')
    if type(writer['ref']['call_instance']) is not int or writer['ref']['call_instance'] < 0:
        raise ValueError('output-projection-exchange original call identity mismatch')
    fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
    for key, refs in [('inputs', cell.inputs), ('outputs', cell.outputs)]:
        if not _same_typed(writer[key], [dict(zip(fields, ref, strict=True)) for ref in refs]):
            raise ValueError('output-projection-exchange source writer ordered fullrefs mismatch')
    for p in ports:
        if (len(p.parent_shape) != 3 or len(p.endpoint.shape) != 3 or len(p.bounds) != 3
                or any(type(n) is not int or n <= 0 for n in (*p.parent_shape, *p.endpoint.shape))
                or any(len(b) != 2 or any(type(n) is not int for n in b)
                       or not 0 <= b[0] < b[1] <= d or b[1]-b[0] != s
                       for b, d, s in zip(p.bounds, p.parent_shape, p.endpoint.shape, strict=True))):
            raise ValueError('output-projection-exchange exact integer rank-three shape/bounds required')
        producer = index.raw[p.endpoint.writer]
        irs = getattr(producer, '_output_irs', None)
        if irs is None or len(irs) != len(producer.outputs) or any(ir is None for ir in irs):
            raise ValueError('output-projection-exchange complete original producer cover required')
        original = irs[list(map(tuple, producer.outputs)).index(p.endpoint.ref)]
        if (any(type(n) is not int or n <= 0 for n in original.shape)
                or not _same_typed(tuple(original.shape), p.endpoint.shape)):
            raise ValueError('output-projection-exchange original producer shape must be exact positive integers')
        if (type(original.parent.tid) is not int
                or not _same_typed(post._port(index, p.endpoint.ref, original), p)):
            raise ValueError('output-projection-exchange original producer metadata mismatch')
    outputs = getattr(cell, '_output_irs', None)
    if (outputs is None or len(outputs) != 1 or outputs[0] is None
            or type(outputs[0].parent.tid) is not int):
        raise ValueError('output-projection-exchange complete typed original output metadata required')
    from trainverify.runtime_source_authority import writer_export_id
    writer = _one((w for w in index.view._collective_source['writers']
        if _same_typed((w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
                       w['ref']['source_cid'], w['source_irname']), tuple(node))
        and w['ref']['op'] == 'AllToAllPrim'),
        'output-projection-exchange original source writer missing/ambiguous')
    if (scope.source_writer != writer_export_id(writer['ref'])
            or scope.source_writer != writer['export_id']):
        raise ValueError('output-projection-exchange original source writer identity mismatch')
    if (op(cell) != 'AllToAllPrim' or scope.op != 'AllToAllPrim' or not scope.source_writer
            or not _same_typed(scope.ranks, tuple(ranks))
            or not _same_typed(scope.local_index, j)
            or not _same_typed(node.rank, ranks[j])
            or not _same_typed(scope.input_tids, tuple(p.endpoint.tid for p in ports))
            or not _same_typed(scope.input_shape, ports[j].endpoint.shape)
            or not _same_typed([tuple(r) for r in cell.inputs], [p.endpoint.ref for p in ports])
            or len(cell.outputs) != 1 or len(scope.params) != 2):
        raise ValueError('output-projection-exchange original ordered peers/owner/scope mismatch')
    a, b = scope.params
    rank = len(ports[0].parent_shape)
    if (any(type(d) is not int for d in (a, b))
            or (rank, a, b) != (3, 1, 2)):
        raise ValueError('output-projection-exchange unsupported original axis family')
    kwargs = dict(cell.kwargs)
    consts = kwargs.pop('__consts', [])
    if (not _same_typed(consts, []) or set(kwargs) != {'ranks', 'idim', 'odim'}
            or not _same_typed(kwargs['idim'], a) or not _same_typed(kwargs['odim'], b)
            or type(kwargs['ranks']) not in (list, tuple)
            or not _same_typed(tuple(kwargs['ranks']), tuple(ranks))):
        raise ValueError('output-projection-exchange original kwargs disagree with scope')
    if (len(ports) != len(ranks) or len(set(ranks)) != len(ranks)
            or [p.endpoint.ref[1] for p in ports] != list(ranks)):
        raise ValueError('output-projection-exchange original peer identity mismatch')
    first = ports[0]
    end = 0
    for p in ports:
        if (p.parent_name != first.parent_name or p.parent_shape != first.parent_shape
                or p.value_part != first.value_part or p.bounds[a][0] != end
                or p.bounds[b] != (0, first.parent_shape[b])
                or any(p.bounds[d] != first.bounds[d] for d in range(rank) if d != a)):
            raise ValueError('output-projection-exchange original gather partition/split interval mismatch')
        end = p.bounds[a][1]
    if end != first.parent_shape[a]:
        raise ValueError('output-projection-exchange incomplete original gather cover')
    width, remainder = divmod(first.parent_shape[b], len(ranks))
    if remainder or width <= 0:
        raise ValueError('output-projection-exchange nondivisible original split')
    bounds = list(first.bounds)
    bounds[a] = (0, end)
    bounds[b] = (j*width, (j+1)*width)
    out = index.endpoint(cell.outputs[0])
    if (out.ref[:3] != tuple(node)[:3] or out.writer != tuple(node)
            or out.tid != scope.output_tid or out.shape != tuple(hi-lo for lo, hi in bounds)):
        raise ValueError('output-projection-exchange original output identity/shape mismatch')
    derived = routes.Port(out, first.parent_name, first.parent_shape, tuple(bounds), first.value_part)
    coverage = dict(producer_metadata='all-peers', input_parent_identity='not-observed')
    for field, expected in [('_input_irs', ports), ('_output_irs', (derived,))]:
        irs = getattr(cell, field, None)
        kind = 'input_metadata' if field == '_input_irs' else 'output_metadata'
        coverage[kind] = 'absent'
        if irs is None:
            continue
        if field == '_input_irs' and len(irs) == 1 and len(ports) > 1:
            expected = (ports[j],)
            coverage[kind] = 'local-only'
        else:
            coverage[kind] = 'all-peers' if field == '_input_irs' else 'present'
        if len(irs) != len(expected):
            raise ValueError('output-projection-exchange partial original metadata')
        for p, ir in zip(expected, irs, strict=True):
            if ir is None or type(ir.parent.tid) is not int:
                raise ValueError('output-projection-exchange complete typed metadata/parent identity required')
            if (any(type(n) is not int or n <= 0 for n in ir.shape)
                    or not _same_typed(tuple(ir.shape), p.endpoint.shape)):
                raise ValueError('output-projection-exchange original IR shape must be exact positive integers')
            if field == '_input_irs':
                producer = index.raw[p.endpoint.writer]
                original = producer._output_irs[list(map(tuple, producer.outputs)).index(p.endpoint.ref)]
                if not _same_typed(ir.parent.tid, original.parent.tid):
                    raise ValueError('output-projection-exchange original parent identity mismatch')
                coverage['input_parent_identity'] = coverage[kind]
            if not _same_typed(post._port(index, p.endpoint.ref, ir), p):
                raise ValueError('output-projection-exchange paired original metadata mismatch')
    return routes.Step(tuple(node), 'AllToAllPrim', tuple(ports), (derived,), scope.source_writer,
        tuple(ranks), j, gather_axis=a, split_axis=b,
        peers=tuple(zip(ranks, scope.input_tids))), coverage


def _read(source, step, order):
    schedule = order['execution_to_source']
    if (any(type(n) is not int for n in schedule) or len(schedule) != len(source.nodes())
            or set(schedule) != set(range(len(source.nodes())))):
        raise ValueError('output-projection-exchange complete execution order required')
    proof, row = primitive._read(source, 'pm', step, order)
    name = f'outputProjectionExchangeRead_pm_{step.outputs[0].endpoint.tid}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row.update(theorem=name, request='group', params=[1, 2],
        source_kwargs=dict(source.node_kwargs(next(n for n in source.nodes() if tuple(n) == step.node))),
        operand_nonwrite_source_indices=order['execution_to_source'][row['execution_index']:])
    return proof, row


def _unit(old, global_, ports, steps, names):
    D, T, B = (old['dimensions'][k] for k in ('D', 'T', 'B'))
    middle._contract(old, global_, ports)
    _, S, HT = ports[0].endpoint.shape
    H, rem = divmod(HT, T)
    if rem or H <= 0:
        raise ValueError('output-projection-exchange nondivisible actual hidden')
    u = old['unit']; g = global_.endpoint.tid
    name = f'outputProjectionExchangeUnitFacts_{g}_{u}'
    row = dict(theorem=name, facts_theorem=name, predecessor=old['facts_theorem'],
        family='AllToAllPrim', unit=u, ranks=old['ranks'], positions=old['positions'],
        dimensions=dict(D=D, T=T, B=B, S=S, H=H), layout='sharded',
        input_gather_axis=1, gather_axis=2, output_gather_axis=2, split_axis=2,
        global_shape=[B*D, S*T, HT], input_shape=[B, S, HT], local_shape=[B, S*T, H],
        sm_output_tid=g, sm_output_ref=list(global_.endpoint.ref),
        pm_output_tids=[s.outputs[0].endpoint.tid for s in steps],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in steps],
        input_refs=[list(p.endpoint.ref) for p in ports],
        source_step=old['source_step'], local_steps=[asdict(s) for s in steps])
    middle._contract(row, global_, [s.outputs[0] for s in steps])
    xs = _list(f'q {p.endpoint.tid}' for p in ports)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in steps)
    terms = _list(f'AllToAllSourceFaithful.tensor {T} {j} 1 2 {xs}' for j in range(T))
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {g}).shape = {row["global_shape"]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {g}) = allGatherPrimDimN 2 {T} 0 {ys} := by',
        f'  have predecessor := {old["facts_theorem"]} s p t q hs hp hvalues',
        f'  have outputs : {ys} = List.ofFn (fun dst : Fin {T} => AllToAllSourceFaithful.tensor {T} dst.val 1 2 {xs}) := by',
        f'    change {ys} = {terms}',
        '    exact '+_cons_equal([f'{names[s.node]} p q hp' for s in steps]),
        f'  exact SourceSequenceHiddenExchange.output_facts {D} {u} {T} {B} {S} {H} (t {g}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) rfl predecessor.2.1 predecessor.1 predecessor.2.2 outputs',
        f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Never accept caller-supplied receipts, output facts, or repaired order."""
    try:
        _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed output-projection-exchange original source: {exc}') from exc


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, names, identities = [], [], [], {}, set()
    for i, old in enumerate(prior['frontier_units']):
        if old['layout'] != 'sharded' or not _same_typed(old['gather_axis'], 1):
            raise ValueError('output-projection-exchange requires axis1 sharded predecessor')
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], old['unit'])), 'output-projection-exchange DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (old['ranks'], old['positions'])):
            raise ValueError('output-projection-exchange original DP ownership/order mismatch')
        g = middle._output(si, old['source_step'])
        ports = [middle._output(pi, d) for d in old['local_steps']]
        middle._contract(old, g, ports)
        identity = (g.endpoint.ref, tuple(p.endpoint.ref for p in ports))
        if identity in identities:
            raise ValueError('output-projection-exchange duplicate frontier identity')
        identities.add(identity)
        steps = []
        for j, port in enumerate(ports):
            cell = view._consumer(pi, port)
            step, coverage = _boundary(pi, cell, ports, old['ranks'], j)
            if step.node in names:
                raise ValueError('output-projection-exchange duplicate/cross-DP original operation')
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
    return text, dict(status='source-output-projection-exchange-values-emitted-uncompiled',
        reads=reads, units=units, frontier_units=units, deferred_units=[],
        consumed_frontier_indices=list(range(len(units))), lean_bytes=len(text.encode()),
        deferred_stage='after-output-projection-exchange: downstream unproved',
        cost_scope='new output projection exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
