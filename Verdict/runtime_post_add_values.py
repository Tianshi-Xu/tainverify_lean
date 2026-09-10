"""Source-authenticated post-add alias and exchange reads, UNCOMPILED.

Original alias and faithful exchange values consume reusable predecessor
shape/value facts. Parent owns imports, complete costs and kernel verification.
Binding checks consume original IDs/layout/spec order, not ancillary runtime_name
or extra annotations. Collective metadata coverage remains absent/local-only/all-peers.
"""
from dataclasses import asdict

from Verdict import graph_to_lean as c
from Verdict import runtime_add_values as adds
from Verdict import runtime_embedding_route_values as primitive_reads
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_embedding_position_units import _list
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _metadata, _same_typed, op
from Verdict.runtime_world import _ordinary


def _port(index, ref, ir):
    name, shape, bounds, value, _, _ = _metadata(ir)
    endpoint = index.endpoint(ref)
    if (type(ir.tid) is not int or ir.tid != ref[3]
            or type(name) is not str or not name or len(shape) != len(bounds)
            or any(type(d) is not int or d <= 0 for d in shape)
            or any(len(b) != 2 or any(type(x) is not int for x in b)
                   or not 0 <= b[0] < b[1] <= d for b, d in zip(bounds, shape))
            or len(value) != 2 or any(type(x) is not int for x in value)
            or not 0 <= value[0] < value[1]
            or tuple(ir.shape) != endpoint.shape
            or endpoint.shape != tuple(b-a for a, b in bounds)):
        raise ValueError('post-add raw port identity/layout mismatch')
    return routes.Port(endpoint, name, shape, bounds, value)


def _layout(port):
    return port.parent_shape, port.bounds, port.value_part


def _next(index, producer):
    ref = producer.endpoint.ref
    cell = _one((cell for cell in index.raw.values()
                 if op(cell) == 'FW_multiref' and ref in map(tuple, cell.inputs)),
                'post-add multiref consumer missing/ambiguous')
    node = _one((n for n in index.view.nodes() if tuple(n) == tuple(cell.node)),
                'post-add original multiref node missing/ambiguous')
    params, status = _ordinary(index.view, node, c._get_node_params)
    if (status is not None or len(cell.inputs) != 1 or not cell.outputs
            or type(cell.kwargs.get('times')) is not int
            or not _same_typed(params, [len(cell.outputs)])
            or cell.rank != ref[1]):
        raise ValueError('post-add multiref source params/arity/owner mismatch')
    inputs = tuple(_port(index, r, ir) for r, ir in zip(cell.inputs, cell._input_irs, strict=True))
    outputs = tuple(_port(index, r, ir) for r, ir in zip(cell.outputs, cell._output_irs, strict=True))
    if not _same_typed(inputs, (producer,)):
        raise ValueError('post-add multiref consumer metadata mismatch')
    if any(not _same_typed(_layout(p), _layout(producer)) for p in outputs):
        raise ValueError('post-add multiref output layout/value partition mismatch')
    if len({p.endpoint.ref for p in outputs}) != len(outputs):
        raise ValueError('post-add duplicate multiref output')
    return routes.Step(tuple(node), 'FW_multiref', inputs, outputs)


def _read(view, label, step, order):
    nodes = view.nodes()
    i, node = _one(((i, n) for i, n in enumerate(nodes) if tuple(n) == step.node),
                   'post-add original multiref writer missing/ambiguous')
    for method, ports in [('node_inputs', step.inputs), ('node_outputs', step.outputs)]:
        if not _same_typed([(tuple(view.source_tensor(t)), t.tid) for t in getattr(view, method)(node)],
                           [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
            raise ValueError('post-add original ordered ports mismatch')
    k = order['execution_to_source'].index(i)
    inp = step.inputs[0].endpoint.tid
    outs = [p.endpoint.tid for p in step.outputs]
    for source in order['execution_to_source'][k:]:
        if inp in {t.tid for t in view.node_outputs(nodes[source])}:
            raise ValueError('post-add operand is written by selected node or suffix')
    name = f'postAddMultirefRead_{label}_{outs[0]}'
    requests = f'{label}InputRequests'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    ∀ output ∈ ({outs} : List Tid), t output = t {inp} := by',
        '  intro output houtput',
        f'  apply SourceMultirefRead.multiref_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{i}',
        f'    {node.rank} {inp} {outs} output s t rfl ?_ rfl ?_ houtput h',
        '  · calc',
        f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
        '      _ = _ := rfl',
        f'  · change ∀ row ∈ {requests}.drop {k}, {inp} ∉ row.1.outs',
        '    decide', f'#print axioms {name}']
    return proof, dict(theorem=name, world=label, op=step.op, node=list(step.node),
        source_index=i, execution_index=k, input_tids=[inp],
        input_refs=[list(p.endpoint.ref) for p in step.inputs], output_tids=outs,
        output_refs=[list(p.endpoint.ref) for p in step.outputs], params=[len(outs)],
        source_kwargs=dict(view.node_kwargs(node)), request='global', source_step=asdict(step),
        operand_nonwrite_source_indices=order['execution_to_source'][k:])


def _exchange(index, aliases, ranks):
    """Select the same original output slot, not merely equal tensor shapes."""
    slots = []
    for j, alias in enumerate(aliases):
        tids = {p.endpoint.tid for p in alias.outputs}
        scope = _one((s for s in index.view.collective_scopes.values()
                      if s.op == 'AllToAllPrim' and s.node.rank == ranks[j]
                      and tids.intersection(s.input_tids)),
                     'post-add AllToAll consumer missing/ambiguous')
        if scope.ranks != ranks or scope.local_index != j:
            raise ValueError('post-add AllToAll cross-unit/order mismatch')
        slot = _one((slot for slot, p in enumerate(alias.outputs)
                     if scope.input_tids[j] == p.endpoint.tid),
                    'post-add AllToAll local multiref slot missing/ambiguous')
        slots.append((slot, scope))
    if len({slot for slot, _ in slots}) != 1:
        raise ValueError('post-add AllToAll mixed multiref slots')
    slot = slots[0][0]
    ports = tuple(a.outputs[slot] for a in aliases)
    expected = tuple(p.endpoint.tid for p in ports)
    whole = ports[0].parent_shape
    steps, metadata = [], []
    for j, (_, scope) in enumerate(slots):
        if scope.input_tids != expected:
            raise ValueError('post-add AllToAll ordered peer/slot mismatch')
        gather, split = scope.params
        if (len(whole) != 3 or gather != 2 or split != 1
                or whole[split] % len(ranks)):
            raise ValueError('post-add unsupported hidden-to-sequence AllToAll axes/divisibility')
        end = 0
        for p in ports:
            if (p.parent_name != ports[0].parent_name or p.parent_shape != whole
                    or p.value_part != ports[0].value_part or p.bounds[gather][0] != end
                    or any(b != (0, whole[d]) for d, b in enumerate(p.bounds) if d != gather)):
                raise ValueError('post-add ordered hidden partition metadata mismatch')
            end = p.bounds[gather][1]
        if end != whole[gather]:
            raise ValueError('post-add incomplete source hidden partition')
        bounds = list(ports[0].bounds)
        bounds[gather] = (0, end)
        width = whole[split] // len(ranks)
        bounds[split] = (j*width, (j+1)*width)
        out, = index.view.node_outputs(scope.node)
        ep = index.endpoint(index.view.source_tensor(out))
        derived = routes.Port(ep, ports[0].parent_name, whole, tuple(bounds), ports[0].value_part)
        if ep.shape != tuple(b-a for a, b in bounds):
            raise ValueError('post-add AllToAll transported bounds/shape mismatch')
        cell = index.raw[tuple(scope.node)]
        for field, expected_ports in [('inputs', ports), ('outputs', (derived,))]:
            if not _same_typed([tuple(r) for r in getattr(cell, field)],
                               [p.endpoint.ref for p in expected_ports]):
                raise ValueError('post-add AllToAll raw ordered ports mismatch')
        # Adapted cells enumerate all peer refs but may retain only the LOCAL
        # original IR. Bind that IR by exact ref+rank, never zip it to peer zero.
        irs = getattr(cell, '_input_irs', None)
        input_coverage = 'absent'
        if irs is not None:
            if len(irs) == len(ports):
                selected = ports; input_coverage = 'all-peers'
            elif len(irs) == 1:
                selected = (ports[j],); input_coverage = 'local-only'
            else:
                raise ValueError('post-add incomplete AllToAll raw input metadata')
            for ir, p in zip(irs, selected, strict=True):
                if not _same_typed(_port(index, p.endpoint.ref, ir), p):
                    raise ValueError('post-add AllToAll raw input metadata mismatch')
        irs = getattr(cell, '_output_irs', None)
        if irs is not None:
            if len(irs) != 1 or not _same_typed(_port(index, ep.ref, irs[0]), derived):
                raise ValueError('post-add AllToAll raw output metadata mismatch')
        steps.append(routes.Step(tuple(scope.node), 'AllToAllPrim', ports, (derived,),
            scope.source_writer, ranks, j, gather_axis=gather, split_axis=split,
            peers=tuple(zip(ranks, scope.input_tids))))
        metadata.append(dict(input_metadata=input_coverage, output_metadata='present' if irs is not None else 'absent'))
    return slot, steps, metadata


def _unit(unit, global_alias, local_aliases, reads, slot):
    D, T, u = unit['dimensions']['D'], unit['dimensions']['T'], unit['unit']
    out = global_alias.outputs[slot].endpoint.tid
    outs = [a.outputs[slot].endpoint.tid for a in local_aliases]
    name = f'postAddAliasUnit_{out}_{u}_slot{slot}'
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (h : InitialParameterValues s p) :',
        f'    chunkPrimDimN 0 {D} {u} (t {out}) =',
        f'    allGatherPrimDimN 2 {T} 0 {_list(f"q {tid}" for tid in outs)} := by']
    rewrites = [f'{reads[global_alias.node]} s t hs {out} {adds._member(slot)}']
    rewrites += [f'{reads[a.node]} p q hp {tid} {adds._member(slot)}'
                 for a, tid in zip(local_aliases, outs, strict=True)]
    proof += ['  rw [' + ', '.join(rewrites) + ']',
              f'  exact {unit["theorem"]} s p t q hs hp h', f'#print axioms {name}']
    return proof, dict(theorem=name, unit=u, slot=slot, ranks=unit['ranks'], positions=unit['positions'],
        dimensions=unit['dimensions'], predecessor=unit['theorem'], sm_output_tid=out,
        pm_output_tids=outs, sm_output_ref=list(global_alias.outputs[slot].endpoint.ref),
        pm_output_refs=[list(a.outputs[slot].endpoint.ref) for a in local_aliases])


def _exchange_unit(unit, global_alias, local_aliases, names, slot, steps, read_names):
    from Verdict.runtime_embedding_position_units import _cons_equal
    d = unit['dimensions']
    D, T, B, ST, H, u = d['D'], d['T'], d['B'], d['S'], d['H'], unit['unit']
    S = ST // T
    global_out = global_alias.outputs[slot].endpoint.tid
    inputs = [a.outputs[slot].endpoint.tid for a in local_aliases]
    outputs = [s.outputs[0].endpoint.tid for s in steps]
    xs, ys = _list(f'q {tid}' for tid in inputs), _list(f'q {tid}' for tid in outputs)
    name = f'postAddExchangeFacts_{global_out}_{u}'
    alias_unit = f'postAddAliasUnit_{global_out}_{u}_slot{slot}'
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (h : InitialParameterValues s p) :',
        f'    (t {global_out}).shape = {[B * D, ST, H * T]} ∧',
        f'    (∀ x ∈ {ys}, x.shape = {[B, S, H * T]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {global_out}) = allGatherPrimDimN 1 {T} 0 {ys} := by',
        f'  have af := {unit["facts_theorem"]} s p t q hs hp h',
        f'  have hx : ∀ x ∈ {xs}, x.shape = {[B, ST, H]} := by',
        '    intro x hx',
        '    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx',
        '    rcases hx with ' + ' | '.join('rfl' for _ in inputs)]
    for j, (a, tid) in enumerate(zip(local_aliases, inputs, strict=True)):
        proof += [f'    · exact (congrArg Tensor.shape ({names[a.node]} p q hp {tid} {adds._member(slot)})).trans',
            f'        (af.2.1 (q {unit["pm_output_tids"][j]}) {adds._member(j)})']
    aa_terms = _list(f'AllToAllSourceFaithful.tensor {T} {j} 2 1 {xs}' for j in range(T))
    proof += [f'  have hy : {ys} = List.ofFn (fun dst : Fin {T} => AllToAllSourceFaithful.tensor {T} dst.val 2 1 {xs}) := by',
        f'    change {ys} = {aa_terms}',
        '    exact ' + _cons_equal([f'{read_names[step.node]} p q hp' for step in steps]),
        f'  exact SourceHiddenSequenceExchange.output_facts {D} {u} {T} {B} {S} {H} (t {global_out}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) rfl hx',
        f'    ((congrArg Tensor.shape ({names[global_alias.node]} s t hs {global_out} {adds._member(slot)})).trans af.1)',
        f'    ({alias_unit} s p t q hs hp h) hy', f'#print axioms {name}']
    return proof, dict(theorem=name, unit=u, slot=slot, ranks=unit['ranks'], positions=unit['positions'],
        sm_output_tid=global_out, pm_output_tids=outputs, input_tids=inputs,
        global_shape=[B * D, ST, H * T], local_shape=[B, S, H * T], gather_axis=1,
        predecessor_facts=unit['facts_theorem'], predecessor_value=alias_unit)


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh add closure + original raw identity; no serialized authority input."""
    # Includes fresh census, full-world authentication, fresh strict schedule,
    # parameter binding and all predecessor final-Store operand nonwrites.
    _, closed = adds.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, validation, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed post-add source: {exc}') from exc


def _render(sm, pm, validation, order, closed):
    si, pi = (_Index(view, raw) for view, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    proofs, reads, units, exchanges, names, seen = [], [], [], [], {}, {}
    exchange_units, exchange_names = [], {}
    for unit in closed['units']:
        # Reconstitute producer steps from original raw nodes and compare the
        # fresh add descriptors. DTOs are never rehydrated into authority.
        producers = []
        for index, descriptor in [(si, unit['source_step']), *((pi, d) for d in unit['local_steps'])]:
            cell = index.raw[tuple(descriptor['node'])]
            step = adds._ordinary_step(index.view, index, cell)
            if not _same_typed(asdict(step), descriptor):
                raise ValueError('post-add fresh add descriptor mismatch')
            producers.append(_next(index, step.outputs[0]))
        global_alias, *local_aliases = producers
        for alias in local_aliases:
            if len(alias.outputs) != len(global_alias.outputs):
                raise ValueError('post-add multiref ordered output arity mismatch')
            if [p.parent_name for p in alias.outputs] != [p.parent_name for p in global_alias.outputs]:
                raise ValueError('post-add multiref ordered output metadata mismatch')
        for view, label, alias in [(sm, 'sm', global_alias), *((pm, 'pm', a) for a in local_aliases)]:
            if alias.node not in seen:
                proof, row = _read(view, label, alias, order[label])
                proofs += proof; reads.append(row); seen[alias.node] = alias; names[alias.node] = row['theorem']
            elif not _same_typed(seen[alias.node], alias):
                raise ValueError('post-add shared multiref identity ambiguity')
        slot, steps, metadata = _exchange(pi, local_aliases, tuple(unit['ranks']))
        for step, coverage in zip(steps, metadata, strict=True):
            if step.node in seen:
                raise ValueError('post-add duplicate/cross-unit AllToAll')
            proof, row = primitive_reads._read(pm, 'pm', step, order['pm'])
            # Reuse exact source read machinery, with a distinct stable name.
            name = f'postAddAllToAllRead_pm_{step.outputs[0].endpoint.tid}'
            proof = [line.replace(row['theorem'], name) for line in proof]
            row.update(theorem=name, slot=slot, unit=unit['unit'], **coverage,
                operand_nonwrite_source_indices=order['pm']['execution_to_source'][row['execution_index']:])
            proofs += proof; reads.append(row); seen[step.node] = step
            exchange_names[step.node] = name
            exchanges.append(dict(theorem=name, slot=slot, unit=unit['unit'], source_step=asdict(step), **coverage))
        for output_slot in range(len(global_alias.outputs)):
            proof, row = _unit(unit, global_alias, local_aliases, names, output_slot)
            proofs += proof; units.append(row)
        proof, row = _exchange_unit(unit, global_alias, local_aliases, names, slot, steps, exchange_names)
        proofs += proof; exchange_units.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent imports/integration/cost/kernel verification required.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-post-add-values-emitted-uncompiled', reads=reads, units=units,
        exchanges=exchanges, exchange_units=exchange_units, lean_bytes=len(text.encode()),
        cost_scope='post-add fragment only; excludes add and earlier predecessors/imports',
        alltoall_activation_emitted=bool(exchange_units), alltoall_activation_reconstruction=False,
        proof_admissible=False, kernel_value_proved=False,
        public_complete=False, torch_refinement=False)
