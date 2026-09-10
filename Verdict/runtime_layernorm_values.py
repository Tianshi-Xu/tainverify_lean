"""Original-source LayerNorm reads and DP-unit facts, explicitly UNCOMPILED.

The caller must emit the SAME canonical bound specs, parameter frame and fresh
post-add predecessors, and import denote.SourceLayernormRead/SourceLayernormUnit.
This fragment excludes those dependencies from its cost. No output hypotheses,
new lineages, tensor-value observations, or serialized descriptors are authority.
Only consumed binding fields are authenticated (not runtime_name/extra labels).
"""
from dataclasses import asdict

from Verdict import graph_to_lean as c
from Verdict import runtime_add_values as adds
from Verdict import runtime_post_add_values as post
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_embedding_position_units import _list
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import Role, _Index, _same_typed, op
from Verdict.runtime_world import _ordinary


def _next(index, activation):
    cell = _one((cell for cell in index.raw.values() if op(cell) == 'FW_layernorm'
                 and activation.endpoint.ref in map(tuple, cell.inputs)),
                'layernorm consumer missing/ambiguous')
    node = _one((n for n in index.view.nodes() if tuple(n) == tuple(cell.node)),
                'layernorm original writer missing/ambiguous')
    params, status = _ordinary(index.view, node, c._get_node_params)
    if (status is not None or not _same_typed(params, [])
            or not _same_typed(dict(cell.kwargs), dict(index.view.node_kwargs(node)))
            or len(cell.inputs) != 3 or len(cell.outputs) != 1
            or not _same_typed(cell.rank, node.rank)):
        raise ValueError('layernorm source params/arity/owner mismatch')
    ins = tuple(post._port(index, r, ir) for r, ir in zip(cell.inputs, cell._input_irs, strict=True))
    outs = tuple(post._port(index, r, ir) for r, ir in zip(cell.outputs, cell._output_irs, strict=True))
    if (not _same_typed(ins[0], activation)
            or not _same_typed(post._layout(outs[0]), post._layout(activation))
            or any(p.endpoint.ref[:2] != tuple(node)[:2] for p in (*ins, *outs))):
        raise ValueError('layernorm ordered activation/output layout/owner mismatch')
    return routes.Step(tuple(node), 'FW_layernorm', ins, outs)


def _read(view, label, step, order):
    nodes = view.nodes()
    i, node = _one(((i, n) for i, n in enumerate(nodes) if tuple(n) == step.node),
                   'layernorm source writer missing/ambiguous')
    for method, ports in [('node_inputs', step.inputs), ('node_outputs', step.outputs)]:
        if not _same_typed([(tuple(view.source_tensor(t)), t.tid) for t in getattr(view, method)(node)],
                           [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
            raise ValueError('layernorm original ordered ports mismatch')
    k = order['execution_to_source'].index(i)
    ins = [p.endpoint.tid for p in step.inputs]
    out = step.outputs[0].endpoint.tid
    for source in order['execution_to_source'][k:]:
        if set(ins) & {t.tid for t in view.node_outputs(nodes[source])}:
            raise ValueError('layernorm operand is written by selected node or suffix')
    x, gamma, beta = ins
    name = f'layernormRead_{label}_{out}'
    requests = f'{label}InputRequests'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {out} = fw_layernorm (t {x}) (t {gamma}) (t {beta}) := by',
        f'  apply SourceLayernormRead.layernorm_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {requests} ({requests}.take {k}) ({requests}.drop {k+1}) {label}Node_{i}',
        f'    {node.rank} {x} {gamma} {beta} {out} s t rfl ?_ rfl ?_ ?_ ?_ h',
        '  · calc',
        f'      {requests} = {requests}.take {k} ++ {requests}.drop {k} := (List.take_append_drop {k} {requests}).symm',
        '      _ = _ := rfl']
    for tid in ins:
        proof += [f'  · change ∀ row ∈ {requests}.drop {k}, {tid} ∉ row.1.outs', '    decide']
    proof += [f'#print axioms {name}']
    return proof, dict(theorem=name, world=label, op=step.op, node=list(step.node),
        source_index=i, execution_index=k, input_tids=ins, output_tid=out,
        input_refs=[list(p.endpoint.ref) for p in step.inputs],
        output_refs=[list(p.endpoint.ref) for p in step.outputs], params=[], request='global',
        source_kwargs=dict(view.node_kwargs(node)), source_step=asdict(step),
        operand_nonwrite_source_indices=order['execution_to_source'][k:])


def _alias(index, ref, closed):
    """Rebuild from original add and alias cells, then compare fresh descriptors."""
    cell = index.raw[index.endpoint(ref).writer]
    producer = index.raw[index.endpoint(cell.inputs[0]).writer]
    alias = post._next(index, adds._ordinary_step(index.view, index, producer).outputs[0])
    row = _one((r for r in closed['reads'] if tuple(r['node']) == alias.node),
               'layernorm fresh alias descriptor missing/ambiguous')
    if not _same_typed(asdict(alias), row['source_step']):
        raise ValueError('layernorm original alias descriptor mismatch')
    return alias


def _binding(index, binding, port, sm_ref, world):
    """Every original parameter occurrence must carry complete consistent metadata."""
    parents = []
    for cell in index.raw.values():
        for ref, ir in zip(cell.inputs, getattr(cell, '_input_irs', [])):
            if not _same_typed(tuple(ref), port.endpoint.ref):
                continue
            if (not ir.is_param() or ir.is_grad() or type(ir.parent.tid) is not int
                    or not _same_typed(post._port(index, ref, ir), port)):
                raise ValueError('layernorm original parameter role/metadata mismatch')
            parents.append(ir.parent.tid)
    parent = _one(set(parents), 'layernorm original parameter parent missing/ambiguous')
    if (port.endpoint.phase != 'initial' or port.endpoint.writer is not None
            or port.endpoint.ref[0] != world[0] or port.endpoint.ref[2] != -1
            or port.endpoint.ref[4] != 0):
        raise ValueError('layernorm requires original initial parameter input')
    expected = dict(world=world, rank=port.endpoint.ref[1], ref=list(port.endpoint.ref),
        tid=port.endpoint.tid, sm_ref=list(sm_ref), logical_name=port.parent_name,
        parent_tid=parent, full_shape=list(port.parent_shape),
        bounds=[list(b) for b in port.bounds], value_part=list(port.value_part),
        shape=list(port.endpoint.shape))
    if not _same_typed({k: binding.get(k) for k in expected}, expected):
        raise ValueError('layernorm original parameter binding mismatch')


def _parameter(si, pi, lineages, specs, role, global_, locals_, unit, D):
    full = global_.inputs[role]
    local_ports = [s.inputs[role] for s in locals_]
    H = global_.inputs[0].endpoint.shape[-1]
    parameter = _one((l for l in lineages if l.role == Role.PARAMETER
                      and _same_typed(l.target, full.endpoint)),
                     'layernorm original PARAMETER lineage missing/ambiguous')
    spec_index, row, bu = _one(((i, r, b) for i, (r, b) in enumerate(specs)
        if _same_typed(r['lineage'], asdict(parameter)) and _same_typed(b['unit'], unit['unit'])),
        'layernorm bound parameter/unit missing/ambiguous')
    if not _same_typed([u.unit for u in parameter.units], list(range(D))):
        raise ValueError('layernorm parameter unit inventory/order mismatch')
    pu = parameter.units[unit['unit']]
    if (pu.reconstruction != 'tp-copy-obligation' or pu.positions != ()
            or not _same_typed([p.endpoint for p in pu.pieces], [p.endpoint for p in local_ports])
            or not _same_typed([p.endpoint.ref[1] for p in local_ports], unit['ranks'])):
        raise ValueError('layernorm parameter role/unit/rank order mismatch')
    for p in [full, *local_ports]:
        if (p.parent_name != full.parent_name or p.parent_shape != (H,)
                or p.endpoint.shape != (H,) or p.bounds != ((0, H),) or p.value_part != (0, 1)):
            raise ValueError('layernorm parameters must be replicated full hidden vectors')
    for piece, port in zip(pu.pieces, local_ports, strict=True):
        if not _same_typed((piece.bounds, piece.value_part), (port.bounds, port.value_part)):
            raise ValueError('layernorm parameter piece metadata mismatch')
    expected = dict(kind='replicated', sm_tid=full.endpoint.tid,
        pm_tids=[p.endpoint.tid for p in local_ports], dim=None, sm_shape=[H], pm_shape=[H])
    if not _same_typed(bu['initial_goal'], expected) or len(bu['bindings']) != len(local_ports):
        raise ValueError('layernorm bound ordered replicated parameter goal mismatch')
    _binding(si, row['sm_binding'], full, full.endpoint.ref, 'sm')
    for b, p in zip(bu['bindings'], local_ports, strict=True):
        _binding(pi, b, p, full.endpoint.ref, 'pm')
    return dict(role='gamma' if role == 1 else 'beta', spec_index=spec_index,
        sm_ref=list(full.endpoint.ref), sm_tid=full.endpoint.tid,
        pm_refs=[list(p.endpoint.ref) for p in local_ports], pm_tids=expected['pm_tids'])


def _unit(unit, global_, locals_, parameters, D, spec_count):
    u, T = unit['unit'], len(locals_)
    B, S, H = unit['local_shape']
    x = global_.inputs[0].endpoint.tid
    out = global_.outputs[0].endpoint.tid
    ins = [s.inputs[0].endpoint.tid for s in locals_]
    outs = [s.outputs[0].endpoint.tid for s in locals_]
    xs, ys = (_list(f'q {tid}' for tid in ts) for ts in (ins, outs))
    gamma, beta = [p['sm_tid'] for p in parameters]
    name = f'layernormUnitFacts_{out}_{u}'
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (h : InitialParameterValues s p) :',
        f'    (t {out}).shape = {[B*D, S*T, H]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {[B, S, H]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {out}) = allGatherPrimDimN 1 {T} 0 {ys} := by',
        f'  have predecessor := {unit["theorem"]} s p t q hs hp h',
        '  have hrels := initialParameterRelations_of_values t q (initialParameterValues_final s p t q hs hp h)']
    for p in parameters:
        i, role = p['spec_index'], p['role']
        projection = 'hrels' + '.2'*i + ('.1' if i < spec_count-1 else '')
        replicas = _list(f'q {tid}' for tid in p['pm_tids'])
        proof += [f'  have {role}Rel : RelationCompiler.ReplicatedRel (t {p["sm_tid"]}) {replicas} [{H}] := {projection}']
    for j, tid in enumerate(outs):
        proof += [f'  have local{j} : q {tid} = fw_layernorm (q {ins[j]}) (t {gamma}) (t {beta}) :=',
                  f'    (layernormRead_pm_{tid} p q hp).trans',
                  f'      (congrArg₂ (fun g b => fw_layernorm (q {ins[j]}) g b)']
        for p in parameters:
            proof += [f'        ({p["role"]}Rel.replica_values (q {p["pm_tids"][j]}) {adds._member(j)})']
        proof[-1] += ')'
    pairs = 'List.Forall₂.nil'
    for j in reversed(range(T)):
        pairs = f'List.Forall₂.cons local{j} ({pairs})'
    proof += [f'  have localReads : List.Forall₂ (fun x y => y = fw_layernorm x (t {gamma}) (t {beta})) {xs} {ys} :=',
        f'    {pairs}',
        f'  exact TrainVerify.Denote.source_layernorm_unit_output_reconstruct {D} {T} {B} {S} {H} {u}',
        f'    (t {x}) (t {gamma}) (t {beta}) (t {out}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        '    predecessor.1 rfl predecessor.2.1 gammaRel.full_shape betaRel.full_shape predecessor.2.2',
        f'    (layernormRead_sm_{out} s t hs) localReads', f'#print axioms {name}']
    return proof, dict(theorem=name, facts_theorem=name, unit=u, ranks=unit['ranks'], positions=unit['positions'],
        dimensions=dict(D=D, T=T, B=B, S=S, H=H), predecessor=unit['theorem'],
        global_shape=[B*D, S*T, H], local_shape=[B, S, H], gather_axis=1,
        sm_output_tid=out, pm_output_tids=outs, parameters=parameters,
        source_step=asdict(global_), local_steps=[asdict(s) for s in locals_])


def render(sm, pm, lineages, validation, bound, execution_order):
    """Fresh post-add closure, original raw ports and one canonical spec order."""
    _, closed = post.render(sm, pm, lineages, validation, bound, execution_order)
    try:
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration) as exc:
        raise ValueError(f'malformed layernorm source/binding: {exc}') from exc


def _render(sm, pm, lineages, validation, bound, order, closed):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    specs = adds._bound(lineages, bound)
    parameters = [l for l in lineages if l.role == Role.PARAMETER]
    if not _same_typed([r['lineage'] for r in bound['relations']], [asdict(l) for l in parameters]):
        raise ValueError('layernorm canonical bound spec order mismatch')
    for row, parameter in zip(bound['relations'], parameters, strict=True):
        if not _same_typed([u['unit'] for u in row['units']], [u.unit for u in parameter.units]):
            raise ValueError('layernorm canonical bound unit spec order mismatch')
    config = validation._inputs[3]['config']['units']
    D = len(config)
    proofs, reads, units, seen, used = [], [], [], {}, set()
    for unit in closed['exchange_units']:
        u, slot = unit['unit'], unit['slot']
        if (not _same_typed(config[u], dict(unit=u, ranks=unit['ranks'], positions=unit['positions']))
                or unit['gather_axis'] != 1):
            raise ValueError('layernorm original unit/ranks/positions mismatch')
        alias_unit = _one((a for a in closed['units'] if a['unit'] == u and a['slot'] == slot
                          and a['sm_output_tid'] == unit['sm_output_tid']),
                         'layernorm selected global alias unit missing/ambiguous')
        global_alias = _alias(si, alias_unit['sm_output_ref'], closed)
        aliases = [_alias(pi, ref, closed) for ref in alias_unit['pm_output_refs']]
        selected, exchanges, _ = post._exchange(pi, aliases, tuple(unit['ranks']))
        if selected != slot:
            raise ValueError('layernorm selected alias slot mismatch')
        for step in exchanges:
            row = _one((r for r in closed['exchanges'] if tuple(r['source_step']['node']) == step.node),
                       'layernorm fresh exchange descriptor missing/ambiguous')
            if row['unit'] != u or not _same_typed(asdict(step), row['source_step']):
                raise ValueError('layernorm original exchange descriptor/unit mismatch')
        activation = global_alias.outputs[slot]
        local_activations = [s.outputs[0] for s in exchanges]
        B, S, H = unit['local_shape']; T = len(unit['ranks'])
        if (unit['global_shape'] != [B*D, S*T, H]
                or unit['positions'] != list(range(u*B, (u+1)*B))
                or activation.endpoint.shape != tuple(unit['global_shape'])
                or activation.endpoint.tid != unit['sm_output_tid']
                or [p.endpoint.tid for p in local_activations] != unit['pm_output_tids']
                or any(p.endpoint.shape != (B, S, H) for p in local_activations)):
            raise ValueError('layernorm predecessor strong shape/unit mismatch')
        global_ = _next(si, activation)
        locals_ = [_next(pi, p) for p in local_activations]
        if any(s.node in used for s in locals_):
            raise ValueError('layernorm duplicate/cross-unit local consumer')
        used.update(s.node for s in locals_)
        params = [_parameter(si, pi, lineages, specs, role, global_, locals_, unit, D) for role in (1, 2)]
        for view, label, step in [(sm, 'sm', global_), *((pm, 'pm', s) for s in locals_)]:
            key = (label, step.node)
            if key in seen:
                if not _same_typed(seen[key], step):
                    raise ValueError('layernorm shared global consumer ambiguity')
                continue
            proof, row = _read(view, label, step, order[label])
            proofs += proof; reads.append(row); seen[key] = step
        proof, row = _unit(unit, global_, locals_, params, D, len(specs))
        proofs += proof; units.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, aggregate cost and kernel verification.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-layernorm-values-emitted-uncompiled', reads=reads, units=units,
        lean_bytes=len(text.encode()), cost_scope='layernorm fragment only; excludes post-add/earlier predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
