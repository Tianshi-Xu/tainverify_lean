"""First original projection exchanges; emitted source facts are UNCOMPILED.

Only fresh view/projection authentication supplies input facts. Rank-four
exchanges retain the global view; rank-three exchanges retain the global linear.
No downstream local view, transpose, public closure or Torch refinement is proved.
"""
from dataclasses import asdict

from Verdict import runtime_view_values as view
from Verdict import runtime_projection_values as projection
from Verdict import runtime_post_add_values as post
from Verdict import runtime_embedding_route_values as primitive
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op


def _output(index, descriptor):
    """Re-read original producer metadata, never manufacture a port from a DTO."""
    cell = index.raw[tuple(descriptor['node'])]
    node = projection._node(index, cell)
    ins = tuple(post._port(index, r, ir) for r, ir in zip(cell.inputs, cell._input_irs, strict=True))
    outs = tuple(post._port(index, r, ir) for r, ir in zip(cell.outputs, cell._output_irs, strict=True))
    step = routes.Step(tuple(node), op(cell), ins, outs)
    if (op(cell) not in ('FW_view', 'FW_linear') or len(outs) != 1
            or not _same_typed(asdict(step), descriptor)
            or outs[0].endpoint.writer != step.node):
        raise ValueError('projection-exchange fresh original producer mismatch')
    return outs[0]


def _boundary(index, cell, ports, ranks, j):
    """Authenticate one original receiver, deriving its layout from input ports."""
    node = projection._node(index, cell)
    scope = _one((s for s in index.view.collective_scopes.values() if tuple(s.node) == tuple(node)),
                 'projection-exchange original scope missing/ambiguous')
    from trainverify.runtime_source_authority import writer_export_id
    writer = _one((w for w in index.view._collective_source['writers']
        if _same_typed((w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
                       w['ref']['source_cid'], w['source_irname']), tuple(node))
        and w['ref']['op'] == 'AllToAllPrim'),
        'projection-exchange original source writer missing/ambiguous')
    if (scope.source_writer != writer_export_id(writer['ref'])
            or scope.source_writer != writer['export_id']):
        raise ValueError('projection-exchange original source writer identity mismatch')
    if (op(cell) != 'AllToAllPrim' or scope.op != 'AllToAllPrim' or not scope.source_writer
            or not _same_typed(scope.ranks, tuple(ranks))
            or not _same_typed(scope.local_index, j)
            or not _same_typed(node.rank, ranks[j])
            or not _same_typed(scope.input_tids, tuple(p.endpoint.tid for p in ports))
            or not _same_typed(scope.input_shape, ports[j].endpoint.shape)
            or not _same_typed([tuple(r) for r in cell.inputs], [p.endpoint.ref for p in ports])
            or len(cell.outputs) != 1 or len(scope.params) != 2):
        raise ValueError('projection-exchange original ordered peers/owner/scope mismatch')
    a, b = scope.params
    rank = len(ports[0].parent_shape)
    if (any(type(d) is not int for d in (a, b))
            or (rank, a, b) not in ((4, 1, 3), (4, 2, 3), (3, 2, 1))):
        raise ValueError('projection-exchange unsupported original axis family')
    kwargs = dict(cell.kwargs)
    consts = kwargs.pop('__consts', [])
    if (not _same_typed(consts, []) or set(kwargs) != {'ranks', 'idim', 'odim'}
            or not _same_typed(kwargs['idim'], a) or not _same_typed(kwargs['odim'], b)
            or type(kwargs['ranks']) not in (list, tuple)
            or not _same_typed(tuple(kwargs['ranks']), tuple(ranks))):
        raise ValueError('projection-exchange original kwargs disagree with scope')
    if (len(ports) != len(ranks) or len(set(ranks)) != len(ranks)
            or [p.endpoint.ref[1] for p in ports] != list(ranks)):
        raise ValueError('projection-exchange original peer identity mismatch')
    first = ports[0]
    end = 0
    for p in ports:
        if (p.parent_name != first.parent_name or p.parent_shape != first.parent_shape
                or p.value_part != first.value_part or p.bounds[a][0] != end
                or p.bounds[b] != (0, first.parent_shape[b])
                or any(p.bounds[d] != first.bounds[d] for d in range(rank) if d != a)):
            raise ValueError('projection-exchange original gather partition/split interval mismatch')
        end = p.bounds[a][1]
    if end != first.parent_shape[a]:
        raise ValueError('projection-exchange incomplete original gather cover')
    width, remainder = divmod(first.parent_shape[b], len(ranks))
    if remainder or width <= 0:
        raise ValueError('projection-exchange nondivisible original split')
    bounds = list(first.bounds)
    bounds[a] = (0, end)
    bounds[b] = (j*width, (j+1)*width)
    out = index.endpoint(cell.outputs[0])
    if (out.ref[:3] != tuple(node)[:3] or out.writer != tuple(node)
            or out.tid != scope.output_tid or out.shape != tuple(hi-lo for lo, hi in bounds)):
        raise ValueError('projection-exchange original output identity/shape mismatch')
    derived = routes.Port(out, first.parent_name, first.parent_shape, tuple(bounds), first.value_part)
    coverage = {}
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
            raise ValueError('projection-exchange partial original metadata')
        for p, ir in zip(expected, irs, strict=True):
            if not _same_typed(post._port(index, p.endpoint.ref, ir), p):
                raise ValueError('projection-exchange paired original metadata mismatch')
    return routes.Step(tuple(node), 'AllToAllPrim', tuple(ports), (derived,), scope.source_writer,
        tuple(ranks), j, gather_axis=a, split_axis=b,
        peers=tuple(zip(ranks, scope.input_tids))), coverage


def _read(pm, step, order):
    proof, row = primitive._read(pm, 'pm', step, order)
    name = f'projectionExchangeRead_pm_{step.outputs[0].endpoint.tid}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row.update(theorem=name, output_refs=[list(step.outputs[0].endpoint.ref)],
        params=[step.gather_axis, step.split_axis], request='group',
        source_kwargs=dict(pm.node_kwargs(next(n for n in pm.nodes() if tuple(n) == step.node))),
        operand_nonwrite_source_indices=order['execution_to_source'][row['execution_index']:])
    return proof, row


def _unit(prior, global_, ports, steps, names):
    D, T, B = (prior['dimensions'][k] for k in ('D', 'T', 'B'))
    u = prior['unit']
    if any(type(x) is not int or x <= 0 for x in (D, T, B)) or not 0 <= u < D:
        raise ValueError('projection-exchange invalid unit dimensions')
    a, b = steps[0].gather_axis, steps[0].split_axis
    if (len(ports) != T or len(steps) != T or prior['gather_axis'] != a
            or list(global_.endpoint.ref) != prior['sm_output_ref']
            or [list(p.endpoint.ref) for p in ports] != prior['pm_output_refs']
            or any((s.gather_axis, s.split_axis) != (a, b) for s in steps)):
        raise ValueError('projection-exchange mixed family or predecessor ports')
    shape = ports[0].endpoint.shape
    if b == 3:
        _, S, H, CT = shape
        C, rem = divmod(CT, T)
        if rem or C <= 0: raise ValueError('projection-exchange nondivisible actual channels')
        local_input = [B, S, H, C*T]
        global_shape = [B*D, S*T if a == 1 else S, H*T if a == 2 else H, C*T]
        local_shape = [B, global_shape[1], global_shape[2], C]
        dimensions = dict(D=D, T=T, B=B, S=S, H=H, C=C)
        law = f'SourceRank4Exchange.axis{a}_output_facts'
        dims = f'{D} {u} {T} {B} {S} {H} {C}'
        positive = 5
    else:
        _, ST, H = shape
        S, rem = divmod(ST, T)
        if rem or S <= 0: raise ValueError('projection-exchange nondivisible actual sequence')
        local_input, global_shape, local_shape = [B, S*T, H], [B*D, S*T, H*T], [B, S, H*T]
        dimensions = dict(D=D, T=T, B=B, S=S, H=H)
        law, dims, positive = 'SourceHiddenSequenceExchange.output_facts', f'{D} {u} {T} {B} {S} {H}', 4
    if (list(global_.endpoint.shape) != global_shape or global_.parent_shape != tuple(global_shape)
            or global_.bounds != tuple((0, d) for d in global_shape)
            or prior['global_shape'] != global_shape or prior['local_shape'] != local_input):
        raise ValueError('projection-exchange full global contract mismatch')
    for j, (p, step) in enumerate(zip(ports, steps, strict=True)):
        if (list(p.endpoint.shape) != local_input or list(step.outputs[0].endpoint.shape) != local_shape
                or p.parent_name != global_.parent_name
                or p.parent_shape != (B, *global_shape[1:]) or p.bounds[0] != (0, B)
                or p.value_part != global_.value_part or step.node[1] != prior['ranks'][j]):
            raise ValueError('projection-exchange full local contract mismatch')
    xs = _list(f'q {p.endpoint.tid}' for p in ports)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in steps)
    g = global_.endpoint.tid
    name = f'projectionExchangeUnitFacts_{g}_{u}_slot{prior["slot"]}'
    terms = _list(f'AllToAllSourceFaithful.tensor {T} {j} {a} {b} {xs}' for j in range(T))
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {g}).shape = {global_shape} ∧',
        f'    (∀ x ∈ {ys}, x.shape = {local_shape}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {g}) = allGatherPrimDimN {b} {T} 0 {ys} := by',
        f'  have predecessor := {prior["facts_theorem"]} s p t q hs hp hvalues',
        f'  have outputs : {ys} = List.ofFn (fun dst : Fin {T} => AllToAllSourceFaithful.tensor {T} dst.val {a} {b} {xs}) := by',
        f'    change {ys} = {terms}',
        '    exact ' + _cons_equal([f'{names[s.node]} p q hp' for s in steps]),
        f'  exact {law} {dims} (t {g}) {xs} {ys}',
        '    ' + ' '.join(['(by decide)']*positive) + ' rfl predecessor.2.1 predecessor.1 predecessor.2.2 outputs',
        f'#print axioms {name}']
    return proof, dict(theorem=name, facts_theorem=name, predecessor=prior['facts_theorem'],
        unit=u, slot=prior['slot'], ranks=prior['ranks'], positions=prior['positions'], dimensions=dimensions,
        global_shape=global_shape, input_shape=local_input, local_shape=local_shape,
        input_gather_axis=a, gather_axis=b, split_axis=b,
        sm_output_tid=g, sm_output_ref=list(global_.endpoint.ref),
        pm_output_tids=[s.outputs[0].endpoint.tid for s in steps],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in steps],
        input_refs=[list(p.endpoint.ref) for p in ports], source_step=prior['source_step'],
        local_steps=[asdict(s) for s in steps],
        deferred_stage='after-first-exchange: local view/transpose/downstream pending')


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh complete source predecessors under exactly the same bound/schedule."""
    _, views = view.render(sm, pm, lineages, validation, bound, execution_order)
    _, projections = projection.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, validation, execution_order, views, projections)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed projection-exchange source: {exc}') from exc


def _render(sm, pm, validation, order, views, projections):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    # Preserve the fresh original projection inventory order (including deferred
    # routes). Matching uses both global and ordered local producer fullrefs;
    # theorem names and display slots are not discovery/order authority.
    candidates = [(u, None, list(u['source_step']['inputs'][0]['endpoint']['ref']),
        [list(s['inputs'][0]['endpoint']['ref']) for s in u['local_steps']]) for u in views['units']]
    candidates += [(d, d, list(d['global_view']['inputs'][0]['endpoint']['ref']),
        d['boundaries'][0]['input_refs']) for d in views['deferred_units']]
    work, consumed = [], set()
    for original in projections['units']:
        i, candidate = _one(((i, c) for i, c in enumerate(candidates)
            if _same_typed(c[0]['unit'], original['unit'])
            and _same_typed(c[0]['ranks'], original['ranks'])
            and _same_typed(c[2], original['sm_output_ref'])
            and _same_typed(c[3], original['pm_output_refs'])),
            'projection-exchange fresh projection route missing/ambiguous')
        route, deferred, _, _ = candidate
        if i in consumed or route['predecessor'] != original['facts_theorem']:
            raise ValueError('projection-exchange duplicate route/predecessor identity mismatch')
        consumed.add(i)
        work.append((original if deferred is not None else route, deferred))
    if len(consumed) != len(candidates):
        raise ValueError('projection-exchange incomplete fresh route coverage')
    proofs, reads, units, seen, names = [], [], [], set(), {}
    for prior, deferred in work:
        global_ = _output(si, prior['source_step'])
        ports = tuple(_output(pi, d) for d in prior['local_steps'])
        cells = [view._consumer(pi, p) for p in ports]
        if {op(c) for c in cells} != {'AllToAllPrim'}:
            raise ValueError('projection-exchange mixed/unknown first forward frontier')
        if deferred is not None:
            boundaries = [view._boundary(pi, cell, ports, prior['ranks'], j, order['pm'])
                          for j, cell in enumerate(cells)]
            if not _same_typed(boundaries, deferred['boundaries']):
                raise ValueError('projection-exchange fresh deferred boundary mismatch')
        steps = []
        for j, cell in enumerate(cells):
            step, coverage = _boundary(pi, cell, ports, prior['ranks'], j)
            if step.node in seen:
                raise ValueError('projection-exchange duplicate/cross-unit consumer')
            seen.add(step.node)
            proof, row = _read(pm, step, order['pm'])
            row.update(unit=prior['unit'], slot=prior['slot'], **coverage)
            proofs.extend(proof); reads.append(row); names[step.node] = row['theorem']; steps.append(step)
        proof, row = _unit(prior, global_, ports, steps, names)
        proofs.extend(proof); units.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessor/frame, full cost and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-first-projection-exchange-values-emitted-uncompiled',
        reads=reads, units=units, lean_bytes=len(text.encode()),
        deferred_stage='after-first-exchange: local view/transpose/downstream pending',
        cost_scope='projection exchange fragment only; excludes all predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
