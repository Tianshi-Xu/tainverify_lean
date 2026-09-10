"""Closed embedding-predecessor FW_add values on original final Stores.

render(sm, pm, lineages, validation, bound, execution_order) returns an
UNCOMPILED candidate. The parent owns imports, the identical bound/spec order,
predecessor theorem emission, aggregate cost caps and kernel verification.
No new lineage, alternate source authority or caller output premises are added.
"""
from dataclasses import asdict

from Verdict import graph_to_lean as c
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_embedding_position_units import _binding, _cons_equal, _list
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import Role, _Index, _same_typed, op
from Verdict.runtime_schedule import build
from Verdict.runtime_world import _ordinary


def _member(position):
    term = 'List.mem_cons_self'
    for _ in range(position):
        term = f'(List.mem_cons_of_mem _ {term})'
    return term


def _bound(lineages, bound):
    if bound.get('status') != 'initial-parameter-relations-bound':
        raise ValueError('add requires canonical initial parameter binding')
    parameters = [l for l in lineages if l.role == Role.PARAMETER]
    rows = bound['relations']
    if len(rows) != len(parameters):
        raise ValueError('add bound specification inventory mismatch')
    for parameter in parameters:
        row = _one((r for r in rows if _same_typed(r['lineage'], asdict(parameter))),
                   'add bound parameter lineage missing/ambiguous')
        if len(row['units']) != len(parameter.units):
            raise ValueError('add bound unit inventory mismatch')
        for unit in parameter.units:
            bu = _one((u for u in row['units'] if _same_typed(u['unit'], unit.unit)),
                      'add bound unit missing/ambiguous')
            copied = unit.reconstruction == 'tp-copy-obligation'
            expected = dict(kind='replicated' if copied else 'sharded', sm_tid=parameter.target.tid,
                pm_tids=[p.endpoint.tid for p in unit.pieces],
                dim=None if copied else int(unit.reconstruction.split(':')[1]),
                sm_shape=list(parameter.target.shape), pm_shape=list(unit.pieces[0].endpoint.shape))
            if not _same_typed(bu['initial_goal'], expected):
                raise ValueError('add bound specification differs from original lineage')
    return [(row, unit) for row in rows for unit in row['units']]


def _ordinary_step(view, index, cell):
    node = _one((n for n in view.nodes() if tuple(n) == tuple(cell.node)),
                'add original node missing/ambiguous')
    params, status = _ordinary(view, node, c._get_node_params)
    if op(cell) != 'FW_add' or params != [] or status is not None:
        raise ValueError('unsupported ordinary add source schema')
    # _Index.meta deliberately inventories only existing lineage operators.
    # Read add ports directly from their authenticated original IR; do not
    # extend that authority or infer an output layout from equal input shapes.
    def port(ref, ir):
        from Verdict.runtime_lineage import _metadata
        name, shape, bounds, value, _, _ = _metadata(ir)
        endpoint = index.endpoint(ref)
        if (type(ir.tid) is not int or ir.tid != ref[3]
                or type(name) is not str or not name or len(shape) != len(bounds)
                or any(type(d) is not int or d <= 0 for d in shape)
                or any(len(b) != 2 or any(type(x) is not int for x in b)
                       or not 0 <= b[0] < b[1] <= d for b, d in zip(bounds, shape))
                or any(type(x) is not int for x in value)
                or endpoint.shape != tuple(b-a for a, b in bounds)):
            raise ValueError('add original raw port identity/layout mismatch')
        return routes.Port(endpoint, name, shape, bounds, value)
    return routes.Step(tuple(cell.node), op(cell),
        tuple(port(ref, ir) for ref, ir in zip(cell.inputs, cell._input_irs, strict=True)),
        tuple(port(ref, ir) for ref, ir in zip(cell.outputs, cell._output_irs, strict=True)))


def _pointwise_layout(step, left, right):
    # Bind consumer metadata to the original producer ports, then require the
    # pointwise output to inherit their placement. Logical output names differ.
    if not _same_typed(step.inputs, (left, right)):
        raise ValueError('add consumer metadata differs from original predecessors')
    layout = lambda p: (p.parent_shape, p.bounds, p.value_part)
    if (not _same_typed(layout(left), layout(right))
            or not _same_typed(layout(step.outputs[0]), layout(left))):
        raise ValueError('add output layout differs from pointwise predecessors')


def _read(view, label, step, order):
    nodes = view.nodes()
    i = _one((i for i, n in enumerate(nodes) if tuple(n) == step.node),
             'add original writer missing/ambiguous')
    n = nodes[i]
    for method, ports in [('node_inputs', step.inputs), ('node_outputs', step.outputs)]:
        if not _same_typed([(tuple(view.source_tensor(t)), t.tid) for t in getattr(view, method)(n)],
                           [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
            raise ValueError('add original ordered ports mismatch')
    k = order['execution_to_source'].index(i)
    ins = [p.endpoint.tid for p in step.inputs]
    out = step.outputs[0].endpoint.tid
    for source in order['execution_to_source'][k:]:
        if set(ins) & {t.tid for t in view.node_outputs(nodes[source])}:
            raise ValueError('add operand is written by selected node or suffix')
    left, right = ins
    name = f'addRead_{label}_{out}'
    requests = f'{label}InputRequests'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {out} = elemwiseAdd (t {left}) (t {right}) := by',
        f'  apply SourceAddRead.add_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{i}',
        f'    {n.rank} {left} {right} {out} s t rfl ?_ rfl ?_ ?_ h',
        '  · calc',
        f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
        '      _ = _ := rfl']
    for tid in ins:
        proof += [f'  · change ∀ row ∈ {requests}.drop {k}, {tid} ∉ row.1.outs', '    decide']
    proof += [f'#print axioms {name}']
    return proof, dict(theorem=name, world=label, op=step.op, node=list(step.node),
        ref=list(step.outputs[0].endpoint.ref), source_index=i, execution_index=k,
        input_tids=ins, input_refs=[list(p.endpoint.ref) for p in step.inputs], output_tid=out,
        params=[], request='global', source_kwargs=dict(view.node_kwargs(n)),
        operand_nonwrite_source_indices=order['execution_to_source'][k:],
        source_step=asdict(step))


def _shapes(prefix, route, record, lineages, specs):
    """Derive full/local predecessor shapes solely from existing input contracts."""
    ids = _one((l for l in lineages if l.target.ref == route.batch_key), 'add input lineage missing')
    row, bu = specs[record['spec_index']]
    goal = bu['initial_goal']
    ws = _list(f'q {tid}' for tid in record['pm_weight_tids'])
    relation = (f'RelationCompiler.ReplicatedRel (t {record["sm_weight_tid"]}) {ws} {goal["sm_shape"]}'
        if goal['kind'] == 'replicated' else
        f'RelationCompiler.ShardedRel (t {record["sm_weight_tid"]}) {ws} 1 {goal["sm_shape"]} {goal["pm_shape"]}')
    projection = 'hrels' + '.2' * record['spec_index'] + ('.1' if record['spec_index'] < len(specs)-1 else '')
    u, T = route.unit, len(route.ranks)
    full = route.global_embedding.outputs[0].endpoint
    sm_ids, sm_weight = record['sm_input_tid'], record['sm_weight_tid']
    direct = route.ranks[0].chunk is None
    global_read = f'embeddingRead_{full.tid}' if direct else f'embeddingRouteRead_sm_{full.tid}'
    proof = [f'  have {prefix}Weights : {relation} := {projection}',
        f'  have {prefix}FullIds : (t {sm_ids}).shape = {list(ids.target.shape)} :=',
        f'    (inputStoreRelation_{sm_ids}_{record["input_lanes"][0]} s p t q hs hp).full_shape',
        f'  have {prefix}FullShape : (t {full.tid}).shape = {list(full.shape)} := by',
        f'    have hshape := congrArg Tensor.shape ({global_read} s t hs)',
        f'    rw [fw_embedding_shape, {prefix}FullIds, {prefix}Weights.full_shape] at hshape',
        '    exact hshape']
    for j, rank in enumerate(route.ranks):
        loader = rank.loader.endpoint
        lane = record['input_lanes'][j]
        lane_tids = _list(f'q {unit.pieces[lane].endpoint.tid}' for unit in ids.units)
        weight = rank.embedding.inputs[1].endpoint
        emb = rank.embedding.outputs[0].endpoint
        proof += [f'  have {prefix}Ids{j} : (q {loader.tid}).shape = {list(loader.shape)} :=',
            f'    (inputStoreRelation_{sm_ids}_{lane} s p t q hs hp).shard_shapes (q {loader.tid})',
            f'      (by change q {loader.tid} ∈ {lane_tids}; exact {_member(u)})',
            f'  have {prefix}Weight{j} : (q {weight.tid}).shape = {list(weight.shape)} :=',
            f'    {prefix}Weights.{"shard_shapes" if direct else "replica_shapes"} (q {weight.tid}) {_member(j)}']
        input_tid = loader.tid
        ids_shape = f'{prefix}Ids{j}'
        if not direct:
            chunk = rank.chunk.outputs[0].endpoint
            proof += [f'  have {prefix}Chunk{j} : (q {chunk.tid}).shape = {list(chunk.shape)} := by',
                f'    rw [embeddingRouteRead_pm_{chunk.tid} p q hp]',
                f'    exact chunkPrimDimN_shape 1 {T} {j} (q {loader.tid}) {list(loader.shape)} {prefix}Ids{j} (by decide)']
            input_tid, ids_shape = chunk.tid, f'{prefix}Chunk{j}'
        read = f'embeddingRead_{emb.tid}' if direct else f'embeddingRouteRead_pm_{emb.tid}'
        proof += [f'  have {prefix}Embedding{j} : (q {emb.tid}).shape = {list(emb.shape)} := by',
            f'    have hshape := congrArg Tensor.shape ({read} p q hp)',
            f'    rw [fw_embedding_shape, {ids_shape}, {prefix}Weight{j}] at hshape',
            '    exact hshape']
    for j, rank in enumerate(route.ranks):
        output = rank.output.endpoint
        proof += [f'  have {prefix}Local{j} : (q {output.tid}).shape = {list(output.shape)} := by']
        if direct:
            proof += [f'    exact {prefix}Embedding{j}']
        else:
            senders = [r.embedding.outputs[0].endpoint.tid for r in route.ranks]
            proof += [f'    have hshape := AllToAllSourceFaithful.tensor_shape {T} {j} 1 2',
                f'      (q {senders[0]}) {_list(f"q {tid}" for tid in senders[1:])} (by decide)',
                f'    rw [{prefix}Embedding0] at hshape',
                f'    exact (congrArg Tensor.shape (embeddingRouteRead_pm_{output.tid} p q hp)).trans hshape']
    terms = _list(f'q {r.output.endpoint.tid}' for r in route.ranks)
    shape = list(route.ranks[0].output.endpoint.shape)
    proof += [f'  have {prefix}Shapes : ∀ x ∈ {terms}, x.shape = {shape} := by',
        '    intro x hx', '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx',
        '    rcases hx with ' + ' | '.join('rfl' for _ in route.ranks)]
    proof += [f'    · exact {prefix}Local{j}' for j in range(T)]
    proof += [f'  have {prefix}Indexed : ∀ r (hr : r < ({terms}).length),',
        f'      (({terms}).get ⟨r, hr⟩).shape = {shape} := by',
        '    intro r hr', f'    exact {prefix}Shapes _ (List.get_mem _ _)']
    return proof


def _unit(step, locals_, pair, records, lineages, specs):
    left, right = pair
    D = len(_one((l for l in lineages if l.target.ref == left.batch_key), 'add input missing').units)
    T, u = len(left.ranks), left.unit
    B, S, H = left.ranks[0].output.endpoint.shape
    fulls = [r.global_embedding.outputs[0].endpoint.tid for r in pair]
    local_lists = [_list(f'q {r.output.endpoint.tid}' for r in route.ranks) for route in pair]
    out = step.outputs[0].endpoint.tid
    outs = [s.outputs[0].endpoint.tid for s in locals_]
    terms = _list(f'q {tid}' for tid in outs)
    name = f'addUnit_{out}_{u}'
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (h : InitialParameterValues s p) :',
        f'    chunkPrimDimN 0 {D} {u} (t {out}) =',
        f'    allGatherPrimDimN 2 {T} 0 {terms} := by',
        '  have hrels := initialParameterRelations_of_values t q (initialParameterValues_final s p t q hs hp h)']
    for prefix, route, record in zip(('a', 'b'), pair, records, strict=True):
        proof += _shapes(prefix, route, record, lineages, specs)
    add_terms = _list(f'elemwiseAdd (q {a.output.endpoint.tid}) (q {b.output.endpoint.tid})'
                      for a, b in zip(left.ranks, right.ranks, strict=True))
    proof += [f'  have localAdds : {terms} = List.zipWith elemwiseAdd {local_lists[0]} {local_lists[1]} := by',
        f'    change {terms} = {add_terms}',
        '    exact ' + _cons_equal([f'addRead_pm_{tid} p q hp' for tid in outs]),
        f'  exact TrainVerify.Denote.source_add_unit_output_reconstruct {D} {T} {B} {S} {H} {u}',
        f'    (t {fulls[0]}) (t {fulls[1]}) (t {out}) {local_lists[0]} {local_lists[1]} {terms}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        '    aFullShape bFullShape rfl rfl aIndexed bIndexed',
        f'    ({records[0]["theorem"]} s p t q hs hp h) ({records[1]["theorem"]} s p t q hs hp h)',
        f'    (addRead_sm_{out} s t hs) localAdds', f'#print axioms {name}']
    return proof, dict(theorem=name, unit=u, positions=list(left.positions),
        ranks=[r.rank for r in left.ranks], dimensions=dict(D=D, T=T, B=B, S=S, H=H),
        sm_output_ref=list(step.outputs[0].endpoint.ref), sm_output_tid=out,
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_], pm_output_tids=outs,
        predecessors=[dict(theorem=r['theorem'], spec_index=r['spec_index'], route=asdict(route))
                      for route, r in zip(pair, records, strict=True)],
        source_step=asdict(step), local_steps=[asdict(s) for s in locals_])


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh source census, exact ordered matches, internal shapes, no output premise."""
    fresh = routes.census(sm, pm, lineages, validation)
    canonical_order = {'sm': build(sm), 'pm': build(pm)}
    if not _same_typed(execution_order, canonical_order):
        raise ValueError('add execution order differs from original source schedule')
    try:
        return _render(sm, pm, lineages, validation, bound, execution_order, fresh)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed add source/binding: {exc}') from exc


def _render(sm, pm, lineages, validation, bound, order, fresh):
    from Verdict import runtime_embedding_units, runtime_embedding_position_units
    from Verdict import runtime_embedding_values, runtime_embedding_route_values
    specs = _bound(lineages, bound)
    # These are the established producer domains, not a shape-based substitute.
    _, direct = runtime_embedding_units.render(sm, pm, lineages, bound)
    _, complex_ = runtime_embedding_position_units.render(sm, pm, lineages, validation, bound)
    # Recheck the final-Store read footprints of the predecessor proof chain.
    runtime_embedding_values.render(sm, pm, lineages, order)
    runtime_embedding_route_values.render(sm, pm, lineages, validation, order)
    records = direct['units'] + complex_['units']
    supported = {}
    raw_sm, raw_pm = validation._inputs[:2]
    si, pi = _Index(sm, raw_sm), _Index(pm, raw_pm)
    for route in fresh.routes:
        ref = route.global_embedding.outputs[0].endpoint.ref
        record = _one((r for r in records if _same_typed(r['sm_output_ref'], list(ref)) and r['unit'] == route.unit),
                      'add predecessor is not a closed supported embedding unit')
        if (not _same_typed(record['pm_output_refs'], [list(r.output.endpoint.ref) for r in route.ranks])
                or (ref, route.unit) in supported):
            raise ValueError('add predecessor output/unit ambiguity')
        # Direct renderer validates goals; bind also the complete original raw
        # parameter identity, as the complex renderer already does.
        row, bu = specs[record['spec_index']]
        _binding(row['sm_binding'], route.global_embedding.inputs[1], route.parameter_key, 'sm', raw_sm)
        if len(bu['bindings']) != len(route.ranks):
            raise ValueError('add predecessor binding count mismatch')
        for binding, rank in zip(bu['bindings'], route.ranks, strict=True):
            _binding(binding, rank.embedding.inputs[1], route.parameter_key, 'pm', raw_pm)
        supported[(ref, route.unit)] = (route, record)
    global_refs = {ref for ref, _ in supported}
    proofs, units, reads, seen, source_pairs, used_local = [], [], [], {}, set(), set()
    for cell in raw_sm:
        if op(cell) != 'FW_add' or not cell.inputs or not all(tuple(ref) in global_refs for ref in cell.inputs):
            continue
        step = _ordinary_step(sm, si, cell)
        inputs = tuple(tuple(ref) for ref in cell.inputs)
        if inputs in source_pairs:
            raise ValueError('ambiguous duplicate original global add pair')
        source_pairs.add(inputs)
        unit_ids = [unit['unit'] for unit in validation._inputs[3]['config']['units']]
        for u in unit_ids:
            pair_records = [_one((value for (ref, unit), value in supported.items() if ref == operand and unit == u),
                                 'add predecessor unit missing/ambiguous') for operand in inputs]
            pair, recs = tuple(zip(*pair_records))
            left, right = pair
            _pointwise_layout(step, left.global_embedding.outputs[0], right.global_embedding.outputs[0])
            ranks = tuple(r.rank for r in left.ranks)
            if (left.unit != right.unit or left.positions != right.positions
                    or ranks != tuple(r.rank for r in right.ranks)
                    or len(left.global_embedding.outputs[0].endpoint.shape) != 3
                    or left.global_embedding.outputs[0].endpoint.shape != right.global_embedding.outputs[0].endpoint.shape
                    or step.outputs[0].endpoint.shape != left.global_embedding.outputs[0].endpoint.shape):
                raise ValueError('add predecessor unit/ranks/positions/full shape mismatch')
            locals_ = []
            for j, (a, b) in enumerate(zip(left.ranks, right.ranks, strict=True)):
                expected = (a.output.endpoint.ref, b.output.endpoint.ref)
                matches = [pc for pc in raw_pm if op(pc) == 'FW_add' and pc.rank == ranks[j]
                           and tuple(tuple(ref) for ref in pc.inputs) == expected]
                pc = _one(matches, 'add original ordered local pair missing/ambiguous')
                local = _ordinary_step(pm, pi, pc)
                _pointwise_layout(local, a.output, b.output)
                if (tuple(pc.node) in used_local or len(a.output.endpoint.shape) != 3
                        or a.output.endpoint.shape != b.output.endpoint.shape
                        or a.output.bounds != b.output.bounds
                        or local.outputs[0].endpoint.shape != a.output.endpoint.shape):
                    raise ValueError('add duplicate local candidate or shard shape/placement mismatch')
                used_local.add(tuple(pc.node))
                locals_.append(local)
            for label, view, selected in [('sm', sm, step), *(('pm', pm, local) for local in locals_)]:
                ref = selected.outputs[0].endpoint.ref
                if ref in seen:
                    if not _same_typed(seen[ref], selected):
                        raise ValueError('add output identity ambiguity')
                    continue
                proof, read = _read(view, label, selected, order[label])
                proofs += proof; reads.append(read); seen[ref] = selected
            proof, unit = _unit(step, locals_, pair, recs, lineages, specs)
            proofs += proof; units.append(unit)
    text = '\n'.join(['-- UNCOMPILED: parent-owned imports, integration, cost cap and kernel check required.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-add-unit-values-emitted-uncompiled', reads=reads, units=units,
        lean_bytes=len(text.encode('utf-8')), cost_scope='only this emitted add-read/unit fragment; excludes predecessors and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
