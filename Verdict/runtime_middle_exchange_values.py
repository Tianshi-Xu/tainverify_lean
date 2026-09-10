"""Original K middle exchange source checkpoint. Emitted Lean is UNCOMPILED.

Only faithful AA(2,1) reads and output facts are new. Other authenticated
first FW_matmul consumers are explicit deferred boundaries, not value proofs.
"""
from dataclasses import asdict

from Verdict import runtime_post_transpose_values as predecessor
from Verdict import runtime_transpose_values as transpose
from Verdict import runtime_projection_values as projection
from Verdict import runtime_view_values as view
from Verdict import runtime_post_add_values as post
from Verdict import runtime_embedding_routes as routes
from Verdict import runtime_embedding_route_values as primitive
from Verdict import graph_to_lean as c
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op
from Verdict.runtime_world import _ordinary


def _output(index, descriptor):
    """Fresh endpoint/optional metadata, including replicated predecessors."""
    cell = index.raw[tuple(descriptor['node'])]
    node = projection._node(index, cell)
    if (op(cell) != descriptor['op'] or op(cell) != str(index.view.node_opname(node)).split('.')[-1]
            or len(cell.outputs) != 1 or len(descriptor['outputs']) != 1):
        raise ValueError('middle-exchange predecessor original opcode/arity mismatch')
    for method, refs in [('node_inputs', cell.inputs), ('node_outputs', cell.outputs)]:
        if not _same_typed([tuple(index.view.source_tensor(t)) for t in getattr(index.view, method)(node)],
                [tuple(r) for r in refs]):
            raise ValueError('middle-exchange predecessor original ordered fullrefs mismatch')
    d = descriptor['outputs'][0]; endpoint = index.endpoint(cell.outputs[0])
    if (not _same_typed(asdict(endpoint), d['endpoint']) or endpoint.writer != tuple(node)
            or endpoint.ref[:3] != tuple(node)[:3]):
        raise ValueError('middle-exchange predecessor original endpoint mismatch')
    port = routes.Port(endpoint, d['parent_name'], d['parent_shape'], d['bounds'], d['value_part'])
    irs = getattr(cell, '_output_irs', None)
    if irs is not None and (len(irs) != 1 or not _same_typed(post._port(index, cell.outputs[0], irs[0]), port)):
        raise ValueError('middle-exchange predecessor original metadata mismatch')
    return port


def _contract(prior, global_, ports):
    if prior['layout'] == 'sharded':
        return transpose._contract(prior, global_, ports)
    D, T, B = (prior['dimensions'][k] for k in ('D', 'T', 'B'))
    u = prior['unit']; whole = prior['global_shape']; local = prior['local_shape']
    if (prior['layout'] != 'replicated_within_dp' or prior['gather_axis'] is not None
            or any(type(n) is not int or n <= 0 for n in (D, T, B))
            or type(u) is not int or not 0 <= u < D or len(whole) != 4
            or len(ports) != T or len(set(prior['ranks'])) != T
            or not _same_typed([p.endpoint.ref[1] for p in ports], prior['ranks'])
            or not _same_typed(list(global_.endpoint.ref), prior['sm_output_ref'])
            or not _same_typed([list(p.endpoint.ref) for p in ports], prior['pm_output_refs'])
            or local != [B, *whole[1:]] or whole[0] != B*D
            or global_.endpoint.shape != tuple(whole) or global_.parent_shape != tuple(whole)
            or global_.bounds != tuple((0, d) for d in whole)):
        raise ValueError('middle-exchange replicated predecessor full DP contract mismatch')
    for p in ports:
        if (p.endpoint.shape != tuple(local) or p.parent_shape != tuple(local)
                or p.bounds != tuple((0, d) for d in local)
                or p.parent_name != global_.parent_name or p.value_part != global_.value_part):
            raise ValueError('middle-exchange replicated predecessor local shape/value mismatch')


def _boundary(index, cell, ports, ranks, j):
    """Derive output from the independently authenticated ordered input cover."""
    node = projection._node(index, cell)
    kind = op(cell)
    if kind != 'AllToAllPrim':
        raise ValueError('middle-exchange unsupported collective')
    a, b = 2, 1
    scope = _one((s for s in index.view.collective_scopes.values() if tuple(s.node) == tuple(node)),
        'middle-exchange source scope missing/ambiguous')
    from trainverify.runtime_source_authority import writer_export_id
    writer = _one((w for w in index.view._collective_source['writers']
        if _same_typed((w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
                       w['ref']['source_cid'], w['source_irname']), tuple(node))
        and w['ref']['op'] == kind), 'middle-exchange source writer missing/ambiguous')
    if (scope.source_writer != writer_export_id(writer['ref'])
            or scope.source_writer != writer['export_id']):
        raise ValueError('middle-exchange source writer/export/call identity mismatch')
    fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
    for key, refs in [('inputs', cell.inputs), ('outputs', cell.outputs)]:
        if not _same_typed(writer[key], [dict(zip(fields, ref)) for ref in refs]):
            raise ValueError('middle-exchange source writer ordered fullrefs mismatch')
    if (scope.op != kind or not _same_typed(scope.params, (a, b) if b else (a,))
            or not _same_typed(scope.ranks, tuple(ranks))
            or not _same_typed(scope.local_index, j)
            or not _same_typed(node.rank, ranks[j])
            or not _same_typed(scope.input_tids, tuple(p.endpoint.tid for p in ports))
            or not _same_typed(scope.input_shape, ports[j].endpoint.shape)
            or not _same_typed([tuple(r) for r in cell.inputs], [p.endpoint.ref for p in ports])
            or len(cell.outputs) != 1):
        raise ValueError('middle-exchange ordered source peers/owner/scope mismatch')
    kwargs = dict(cell.kwargs); consts = kwargs.pop('__consts', [])
    expected = dict(idim=a, odim=b) if b else dict(dim=a)
    rawranks = kwargs.pop('ranks', None)
    if (type(rawranks) not in (list, tuple) or not _same_typed(tuple(rawranks), tuple(ranks))
            or not _same_typed(kwargs, expected) or not _same_typed(consts, [])):
        raise ValueError('middle-exchange raw kwargs mismatch')
    if (len(ports) != len(ranks) or len(set(ranks)) != len(ranks)
            or not _same_typed([p.endpoint.ref[1] for p in ports], list(ranks))):
        raise ValueError('middle-exchange peer rank identity mismatch')
    first = ports[0]
    if len(first.parent_shape) != 4:
        raise ValueError('middle-exchange rank-four input required')
    end = 0
    for p in ports:
        if (p.parent_shape != first.parent_shape or p.parent_name != first.parent_name
                or p.value_part != first.value_part or p.bounds[a][0] != end
                or p.endpoint.shape != first.endpoint.shape
                or any(p.bounds[d] != (0, first.parent_shape[d]) for d in range(4) if d != a)):
            raise ValueError('middle-exchange input contiguous gather/full split partition mismatch')
        end = p.bounds[a][1]
    if end != first.parent_shape[a]:
        raise ValueError('middle-exchange input gather incomplete cover')
    bounds = [(0, d) for d in first.parent_shape]
    if b is not None:
        width, rem = divmod(first.parent_shape[b], len(ranks))
        if rem or width <= 0:
            raise ValueError('middle-exchange nondivisible actual split axis')
        bounds[b] = (j*width, (j+1)*width)
    out = index.endpoint(cell.outputs[0])
    if (out.ref[:3] != tuple(node)[:3] or out.writer != tuple(node)
            or not _same_typed(out.tid, scope.output_tid)
            or out.shape != tuple(hi-lo for lo, hi in bounds)):
        raise ValueError('middle-exchange output original identity/shape mismatch')
    derived = routes.Port(out, first.parent_name, first.parent_shape, tuple(bounds), first.value_part)
    coverage = {}
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
            raise ValueError('middle-exchange partial original metadata')
        for p, ir in zip(expected_ports, irs, strict=True):
            if not _same_typed(post._port(index, p.endpoint.ref, ir), p):
                raise ValueError('middle-exchange original paired metadata mismatch')
    return routes.Step(tuple(node), kind, tuple(ports), (derived,), scope.source_writer,
        tuple(ranks), j, gather_axis=a, split_axis=b,
        peers=tuple(zip(ranks, scope.input_tids))), coverage


def _deferred(index, port, cell, order):
    """Authenticate the original first consumer; do not infer matmul values."""
    node = projection._node(index, cell)
    params, status = _ordinary(index.view, node, c._get_node_params)
    kwargs = dict(cell.kwargs); consts = kwargs.pop('__consts', [])
    if (op(cell) != 'FW_matmul' or str(index.view.node_opname(node)).split('.')[-1] != 'FW_matmul'
            or status is not None or not _same_typed(params, [])
            or kwargs or not _same_typed(consts, []) or len(cell.inputs) != 2 or len(cell.outputs) != 1):
        raise ValueError('middle-exchange deferred original FW_matmul opcode/kwargs/arity mismatch')
    for method, refs in [('node_inputs', cell.inputs), ('node_outputs', cell.outputs)]:
        if not _same_typed([tuple(index.view.source_tensor(t)) for t in getattr(index.view, method)(node)],
                [tuple(r) for r in refs]):
            raise ValueError('middle-exchange deferred original ordered fullrefs mismatch')
        for ref in refs:
            endpoint = index.endpoint(ref)
            if endpoint.ref[:3] != tuple(node)[:3] or (method == 'node_outputs' and endpoint.writer != tuple(node)):
                raise ValueError('middle-exchange deferred original owner/writer mismatch')
    positions = [i for i, ref in enumerate(cell.inputs) if _same_typed(tuple(ref), port.endpoint.ref)]
    if not positions:
        raise ValueError('middle-exchange deferred first consumer port missing')
    coverage = {}
    for field, refs in [('_input_irs', cell.inputs), ('_output_irs', cell.outputs)]:
        irs = getattr(cell, field, None); coverage[field] = 'absent' if irs is None else 'present'
        if irs is None: continue
        if len(irs) != len(refs): raise ValueError('middle-exchange deferred partial metadata')
        for i, (ref, ir) in enumerate(zip(refs, irs, strict=True)):
            actual = post._port(index, ref, ir)
            if field == '_input_irs' and i in positions and not _same_typed(actual, port):
                raise ValueError('middle-exchange deferred predecessor paired metadata mismatch')
    source_index = index.view.nodes().index(node)
    return dict(op='FW_matmul', node=list(node), source_index=source_index,
        execution_index=order['execution_to_source'].index(source_index),
        first_consumer=True, producer_ref=list(port.endpoint.ref), port_positions=positions,
        input_refs=[list(r) for r in cell.inputs], output_refs=[list(r) for r in cell.outputs],
        source_kwargs=dict(cell.kwargs), metadata=coverage, value_proved=False)


def _read(source, step, order):
    proof, row = primitive._read(source, 'pm', step, order)
    name = f'middleExchangeRead_pm_{step.outputs[0].endpoint.tid}'
    proof = [s.replace(row['theorem'], name) for s in proof]
    row.update(theorem=name, output_refs=[list(p.endpoint.ref) for p in step.outputs],
        params=[2, 1], request='group', source_kwargs=dict(source.node_kwargs(next(n for n in source.nodes() if tuple(n) == step.node))),
        input_shapes=[list(p.endpoint.shape) for p in step.inputs],
        output_shape=list(step.outputs[0].endpoint.shape),
        operand_nonwrite_source_indices=order['execution_to_source'][row['execution_index']:])
    return proof, row


def _unit(prior, global_, ports, steps, names):
    if prior['layout'] != 'sharded' or not _same_typed(prior['gather_axis'], 2):
        raise ValueError('middle-exchange requires sharded axis2 predecessor')
    transpose._contract(prior, global_, ports)
    D, T, B = (prior['dimensions'][k] for k in ('D', 'T', 'B'))
    _, sequence, H, C = ports[0].endpoint.shape
    S, rem = divmod(sequence, T)
    if rem or S <= 0: raise ValueError('middle-exchange nondivisible actual split axis')
    u = prior['unit']; g = global_.endpoint.tid
    name = f'middleExchangeUnitFacts_{g}_{u}'
    row = dict(prior, theorem=name, facts_theorem=name, predecessor=prior['facts_theorem'],
        family='AllToAllPrim', layout='sharded', input_gather_axis=2, gather_axis=1,
        dimensions=dict(D=D, T=T, B=B, S=S, H=H, C=C),
        input_shape=list(ports[0].endpoint.shape), local_shape=list(steps[0].outputs[0].endpoint.shape),
        input_refs=[list(p.endpoint.ref) for p in ports],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in steps],
        pm_output_tids=[s.outputs[0].endpoint.tid for s in steps],
        local_steps=[asdict(s) for s in steps])
    transpose._contract(row, global_, [s.outputs[0] for s in steps])
    xs = _list(f'q {p.endpoint.tid}' for p in ports)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in steps)
    terms = _list(f'AllToAllSourceFaithful.tensor {T} {j} 2 1 {xs}' for j in range(T))
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {g}).shape = {row["global_shape"]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {g}) = allGatherPrimDimN 1 {T} 0 {ys} := by',
        f'  have predecessor := {prior["facts_theorem"]} s p t q hs hp hvalues',
        f'  have outputs : {ys} = List.ofFn (fun dst : Fin {T} => AllToAllSourceFaithful.tensor {T} dst.val 2 1 {xs}) := by',
        f'    change {ys} = {terms}',
        '    exact '+_cons_equal([f'{names[s.node]} p q hp' for s in steps]),
        f'  exact SourceRank4MiddleExchange.axis2_output_facts {D} {u} {T} {B} {S} {H} {C} (t {g}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) rfl predecessor.2.1 predecessor.1 predecessor.2.2 outputs',
        f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh predecessor under the SAME caller authority, bound and full schedule."""
    _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed middle-exchange original source: {exc}') from exc


def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, deferred, frontier = [], [], [], [], []
    seen, names, identities = set(), {}, set()
    for original in prior['units']:
        global_ = _output(si, original['source_step'])
        ports = [_output(pi, d) for d in original['local_steps']]
        _contract(original, global_, ports)
        identity = (global_.endpoint.ref, tuple(p.endpoint.ref for p in ports))
        if identity in identities: raise ValueError('middle-exchange duplicate original unit fullrefs')
        identities.add(identity)
        cells = [view._consumer(pi, p) for p in ports]
        kinds = {op(cell) for cell in cells}
        if len(kinds) != 1 or not kinds <= {'AllToAllPrim', 'FW_matmul'}:
            raise ValueError('middle-exchange unknown/mixed first forward frontier')
        if kinds == {'FW_matmul'}:
            consumers = [_deferred(pi, p, cell, order['pm']) for p, cell in zip(ports, cells, strict=True)]
            global_consumer = _deferred(si, global_, view._consumer(si, global_), order['sm'])
            deferred.append(dict(unit=original['unit'], slot=original['slot'],
                predecessor=original['facts_theorem'], source_boundary=original,
                reason='first-original-FW_matmul-value-boundary-unproved',
                first_consumers=consumers, global_first_consumer=global_consumer))
            frontier.append(original)
            continue
        if original['layout'] != 'sharded' or not _same_typed(original['gather_axis'], 2):
            raise ValueError('middle-exchange requires sharded axis2 predecessor')
        steps = []; start = len(reads)
        for j, cell in enumerate(cells):
            step, coverage = _boundary(pi, cell, ports, original['ranks'], j)
            if step.node in seen: raise ValueError('middle-exchange duplicate/cross-unit source identity')
            seen.add(step.node)
            proof, read = _read(pm, step, order['pm'])
            read.update(unit=original['unit'], slot=original['slot'], **coverage)
            proofs.extend(proof); reads.append(read); steps.append(step); names[step.node] = read['theorem']
        proof, unit = _unit(original, global_, ports, steps, names)
        for read in reads[start:]:
            read.update(dimensions=unit['dimensions'], layout=unit['layout'], output_gather_axis=unit['gather_axis'])
        proofs.extend(proof); units.append(unit); frontier.append(unit)
    if len(frontier) != len(prior['units']) or len(units)+len(deferred) != len(frontier):
        raise ValueError('middle-exchange incomplete original frontier coverage')
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, assembly, actual capture/caps and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-middle-exchange-values-emitted-uncompiled', reads=reads, units=units,
        deferred_units=deferred, frontier_units=frontier, lean_bytes=len(text.encode()),
        deferred_stage='after-middle-exchange: matmul/attention/downstream unproved',
        cost_scope='new middle-exchange fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
