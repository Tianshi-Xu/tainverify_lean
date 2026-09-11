"""Faithful post-softmax PM AA(1,2); generated Lean remains UNCOMPILED.

No SM output or FW_matmul step is advanced. Fresh six-argument softmax authority owns the
complete ordered frontier and complete SM/PM/BW schedules.
"""
from dataclasses import asdict

from Verdict import runtime_softmax_values as predecessor
from Verdict import runtime_projection_values as projection
from Verdict import runtime_post_add_values as post
from Verdict import runtime_embedding_routes as routes
from Verdict import runtime_embedding_route_values as primitive
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_matmul_values as matmul
from Verdict import runtime_view_values as view
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op


def _boundary(index, cell, ports, ranks, j):
    """Derive output from the independently authenticated ordered input cover."""
    node = projection._node(index, cell)
    kind = op(cell)
    if kind != 'AllToAllPrim':
        raise ValueError('softmax-exchange unsupported collective')
    a, b = 1, 2
    scope = _one((s for s in index.view.collective_scopes.values() if tuple(s.node) == tuple(node)),
        'softmax-exchange source scope missing/ambiguous')
    from trainverify.runtime_source_authority import writer_export_id
    writer = _one((w for w in index.view._collective_source['writers']
        if _same_typed((w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
                       w['ref']['source_cid'], w['source_irname']), tuple(node))
        and w['ref']['op'] == kind), 'softmax-exchange source writer missing/ambiguous')
    if (scope.source_writer != writer_export_id(writer['ref'])
            or scope.source_writer != writer['export_id']):
        raise ValueError('softmax-exchange source writer/export/call identity mismatch')
    fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
    for key, refs in [('inputs', cell.inputs), ('outputs', cell.outputs)]:
        if not _same_typed(writer[key], [dict(zip(fields, ref)) for ref in refs]):
            raise ValueError('softmax-exchange source writer ordered fullrefs mismatch')
    if (scope.op != kind or not _same_typed(scope.params, (a, b) if b else (a,))
            or not _same_typed(scope.ranks, tuple(ranks))
            or not _same_typed(scope.local_index, j)
            or not _same_typed(node.rank, ranks[j])
            or not _same_typed(scope.input_tids, tuple(p.endpoint.tid for p in ports))
            or not _same_typed(scope.input_shape, ports[j].endpoint.shape)
            or not _same_typed([tuple(r) for r in cell.inputs], [p.endpoint.ref for p in ports])
            or len(cell.outputs) != 1):
        raise ValueError('softmax-exchange ordered source peers/owner/scope mismatch')
    kwargs = dict(cell.kwargs); consts = kwargs.pop('__consts', [])
    expected = dict(idim=a, odim=b) if b else dict(dim=a)
    rawranks = kwargs.pop('ranks', None)
    if (type(rawranks) not in (list, tuple) or not _same_typed(tuple(rawranks), tuple(ranks))
            or not _same_typed(kwargs, expected) or not _same_typed(consts, [])):
        raise ValueError('softmax-exchange raw kwargs mismatch')
    if (len(ports) != len(ranks) or len(set(ranks)) != len(ranks)
            or not _same_typed([p.endpoint.ref[1] for p in ports], list(ranks))):
        raise ValueError('softmax-exchange peer rank identity mismatch')
    first = ports[0]
    if len(first.parent_shape) != 4:
        raise ValueError('softmax-exchange rank-four input required')
    end = 0
    for p in ports:
        if (p.parent_shape != first.parent_shape or p.parent_name != first.parent_name
                or p.value_part != first.value_part or p.bounds[a][0] != end
                or p.endpoint.shape != first.endpoint.shape
                or any(p.bounds[d] != (0, first.parent_shape[d]) for d in range(4) if d != a)):
            raise ValueError('softmax-exchange input contiguous gather/full split partition mismatch')
        end = p.bounds[a][1]
    if end != first.parent_shape[a]:
        raise ValueError('softmax-exchange input gather incomplete cover')
    bounds = [(0, d) for d in first.parent_shape]
    if b is not None:
        width, rem = divmod(first.parent_shape[b], len(ranks))
        if rem or width <= 0:
            raise ValueError('softmax-exchange nondivisible actual split axis')
        bounds[b] = (j*width, (j+1)*width)
    out = index.endpoint(cell.outputs[0])
    if (out.ref[:3] != tuple(node)[:3] or out.writer != tuple(node)
            or not _same_typed(out.tid, scope.output_tid)
            or out.shape != tuple(hi-lo for lo, hi in bounds)):
        raise ValueError('softmax-exchange output original identity/shape mismatch')
    derived = routes.Port(out, first.parent_name, first.parent_shape, tuple(bounds), first.value_part)
    coverage = dict(input_parent_identity='not-observed')
    for field, expected_ports in [('_input_irs', ports), ('_output_irs', (derived,))]:
        irs = getattr(cell, field, None)
        key = 'input_metadata' if field == '_input_irs' else 'output_metadata'
        coverage[key] = 'absent'
        if irs is None:
            continue
        if field == '_input_irs' and len(irs) == 1 and len(ports) > 1:
            expected_ports = (ports[j],); coverage[key] = 'local-only'
        else:
            coverage[key] = 'all-peers' if field == '_input_irs' else 'present'
        if len(irs) != len(expected_ports):
            raise ValueError('softmax-exchange partial original metadata')
        for p, ir in zip(expected_ports, irs, strict=True):
            if not _same_typed(post._port(index, p.endpoint.ref, ir), p):
                raise ValueError('softmax-exchange original paired metadata mismatch')
            if field == '_input_irs':
                producer = index.raw[p.endpoint.writer]
                producer_irs = getattr(producer, '_output_irs', None)
                if producer_irs is None or len(producer_irs) != len(producer.outputs):
                    raise ValueError('softmax-exchange complete original producer output metadata required')
                original = producer_irs[list(map(tuple, producer.outputs)).index(p.endpoint.ref)]
                if (original is None or type(ir.parent.tid) is not int
                        or not _same_typed(ir.parent.tid, original.parent.tid)):
                    raise ValueError('softmax-exchange original producer/consumer parent identity mismatch')
                coverage['input_parent_identity'] = coverage['input_metadata']
    return routes.Step(tuple(node), kind, tuple(ports), (derived,), scope.source_writer,
        tuple(ranks), j, gather_axis=a, split_axis=b,
        peers=tuple(zip(ranks, scope.input_tids))), coverage


def _read(source, step, order):
    proof, row = primitive._read(source, 'pm', step, order)
    name = f'softmaxExchangeRead_pm_{step.outputs[0].endpoint.tid}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row.update(theorem=name, input_gather_axis=1, output_gather_axis=2,
        params=[1, 2], source_kwargs=dict(source.node_kwargs(next(n for n in source.nodes() if tuple(n) == step.node))),
        operand_nonwrite_source_indices=order['execution_to_source'][row['execution_index']:])
    return proof, row


def _unit(old, global_, ports, steps, names):
    D, T, B = (old['dimensions'][k] for k in ('D', 'T', 'B'))
    if any(type(n) is not int or n <= 0 for n in (D, T, B)):
        raise ValueError('softmax-exchange positive integer DP dimensions required')
    _, S, heads, C = ports[0].endpoint.shape
    if any(type(n) is not int or n <= 0 for n in (S, heads, C)):
        raise ValueError('softmax-exchange positive integer input geometry required')
    H, rem = divmod(heads, T)
    if rem or any(type(n) is not int or n <= 0 for n in (S, H, C)):
        raise ValueError('softmax-exchange nondivisible or nonpositive input geometry')
    u = old['unit']; g = global_.endpoint.tid
    name = f'softmaxExchangeUnitFacts_{g}_{u}'
    row = dict(theorem=name, facts_theorem=name, predecessor=old['facts_theorem'],
        family='AllToAllPrim', unit=u, ranks=old['ranks'], positions=old['positions'],
        dimensions=dict(D=D, T=T, B=B, S=S, H=H, C=C), layout='sharded',
        input_gather_axis=1, gather_axis=2, output_gather_axis=2,
        global_shape=[B*D, S*T, H*T, C], local_shape=[B, S*T, H, C],
        input_shape=list(ports[0].endpoint.shape),
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
        f'  exact SourceRank4InnerExchange.axis1_output_facts {D} {u} {T} {B} {S} {H} {C} (t {g}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) rfl predecessor.2.1 predecessor.1 predecessor.2.2 outputs',
        f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Only original source arguments, never caller-provided predecessor facts."""
    try:
        _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed softmax-exchange original source: {exc}') from exc


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, deferred, frontier = [], [], [], [], []
    identities, names = set(), {}
    for i, old in enumerate(prior['frontier_units']):
        g = middle._output(si, old['source_step'])
        ports = [middle._output(pi, d) for d in old['local_steps']]
        middle._contract(old, g, ports)
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], old['unit'])), 'softmax-exchange DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (old['ranks'], old['positions'])):
            raise ValueError('softmax-exchange source DP ownership/ordered ranks mismatch')
        identity = (g.endpoint.ref, tuple(p.endpoint.ref for p in ports))
        if identity in identities:
            raise ValueError('softmax-exchange duplicate original frontier identity')
        identities.add(identity)
        cells = [view._consumer(pi, p) for p in ports]
        kinds = {op(c) for c in cells}
        if kinds == {'FW_matmul'}:
            if old['layout'] != 'replicated_within_dp' or old['gather_axis'] is not None:
                raise ValueError('softmax-exchange deferred boundary requires replicated None')
            _, gr = matmul._consumer(si, g, order['sm'])
            consumers = [matmul._consumer(pi, p, order['pm'])[1] for p in ports]
            if any(not _same_typed(r['port_positions'], gr['port_positions']) for r in consumers):
                raise ValueError('softmax-exchange deferred original ordered port mismatch')
            deferred.append(dict(unit=old['unit'], frontier_index=i, predecessor=old['facts_theorem'],
                source_boundary=old, global_first_consumer=gr, first_consumers=consumers,
                reason='first-original-FW_matmul-value-boundary-unproved', value_proved=False))
            frontier.append(old)
            continue
        if kinds != {'AllToAllPrim'}:
            raise ValueError('softmax-exchange unknown/mixed first forward frontier')
        if old['layout'] != 'sharded' or not _same_typed(old['gather_axis'], 1):
            raise ValueError('softmax-exchange requires sharded axis1 predecessor')
        steps = []
        for j, cell in enumerate(cells):
            step, coverage = _boundary(pi, cell, ports, old['ranks'], j)
            if step.node in names:
                raise ValueError('softmax-exchange duplicate/cross-unit original operation')
            proof, read = _read(pm, step, order['pm'])
            read.update(unit=old['unit'], frontier_index=i, **coverage)
            names[step.node] = read['theorem']
            proofs.extend(proof); reads.append(read); steps.append(step)
        proof, unit = _unit(old, g, ports, steps, names)
        unit['frontier_index'] = i
        for read in reads[-len(steps):]:
            read.update(dimensions=unit['dimensions'], layout=unit['layout'])
        proofs.extend(proof); units.append(unit); frontier.append(unit)
    text = '\n'.join(['-- UNCOMPILED: parent owns actual capture, caps, assembly and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-softmax-exchange-values-emitted-uncompiled', reads=reads, units=units,
        deferred_units=deferred, frontier_units=frontier, lean_bytes=len(text.encode()),
        deferred_stage='after-softmax-exchange: attention matmul/downstream unproved',
        cost_scope='new softmax exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
