"""Fresh FC1 frontier -> exact GELU source candidates, deliberately UNCOMPILED.

Only original source runs and fresh predecessor facts are authority. Parent
owns helper imports, canonical assembly, aggregate costs and kernel gates.
"""
from dataclasses import asdict

from Verdict import runtime_frontier_linear_values as predecessor
from Verdict import runtime_frontier_layernorm_values as frontier
from Verdict import runtime_frontier_alias_exchange_values as source
from Verdict import runtime_attention_residual_values as residual
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_embedding_routes as routes
from Verdict import graph_to_lean as compiler
from Verdict import runtime_add_values as adds
from Verdict.runtime_world import _ordinary
from Verdict.runtime_embedding_position_units import _list
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import Role, _Index, _same_typed, op
from Verdict.runtime_schedule import build


def _parameters(view, node):
    # Fail closed on missing approximate: this fragment does not authenticate
    # omitted Torch defaults from generated Python text.
    kw = view.node_kwargs(node)
    if (str(view.node_opname(node)).split('.')[-1] != 'FW_gelu'
            or len(view.node_inputs(node)) != 1 or len(view.node_outputs(node)) != 1
            or any(node in getattr(view, key, {}) for key in
                   ('collective_scopes', 'chunk_scopes', 'wred_scopes'))
            or type(kw) is not dict or set(kw) - {'approximate', '__consts'}
            or not _same_typed(kw.get('approximate'), 'none')
            or not _same_typed(kw.get('__consts', []), [])):
        raise ValueError('frontier-gelu exact original opcode/arity/scope/kwargs required')
    raw = compiler._get_node_params(view, node, num_parts=0)
    if raw is not None and not _same_typed(raw, []):
        raise ValueError('frontier-gelu empty original params required')
    params, status = _ordinary(view, node, lambda *a, **k: raw)
    if status is not None or not _same_typed(params, []):
        raise ValueError('frontier-gelu empty normalized params required')


def _next(index, activation):
    cell = _one(source._consumers(index, [activation]), 'frontier-gelu unique consumer required')
    node = residual._identity(index, cell)
    _parameters(index.view, node)
    if op(cell) != 'FW_gelu' or len(cell.inputs) != 1 or len(cell.outputs) != 1:
        raise ValueError('frontier-gelu original opcode/arity mismatch')
    inputs = source._ports(index, cell, 'inputs')
    outputs = source._ports(index, cell, 'outputs')
    source._edge(index, activation, cell._input_irs[0])
    return routes.Step(tuple(node), 'FW_gelu', inputs, outputs)


def _read(view, label, step, order):
    nodes = view.nodes()
    i, node = _one(((i, n) for i, n in enumerate(nodes) if _same_typed(tuple(n), step.node)),
                   'frontier-gelu original read node missing/ambiguous')
    _parameters(view, node)
    if step.op != 'FW_gelu' or len(step.inputs) != 1 or len(step.outputs) != 1:
        raise ValueError('frontier-gelu read original opcode/arity mismatch')
    for method, ports in [('node_inputs', step.inputs), ('node_outputs', step.outputs)]:
        if not _same_typed([(tuple(view.source_tensor(t)), t.tid) for t in getattr(view, method)(node)],
                           [(p.endpoint.ref, p.endpoint.tid) for p in ports]):
            raise ValueError('frontier-gelu read original ordered ports mismatch')
    if not _same_typed(order, build(view)):
        raise ValueError('frontier-gelu complete typed execution order mismatch')
    k = order['execution_to_source'].index(i)
    inp = step.inputs[0].endpoint.tid; out = step.outputs[0].endpoint.tid
    suffix = order['execution_to_source'][k:]
    for j in suffix:
        if inp in {t.tid for t in view.node_outputs(nodes[j])}:
            raise ValueError('frontier-gelu operand written by selected node or complete suffix')
    name = f'frontierGeluRead_{label}_{out}'; req = f'{label}InputRequests'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
        f'    t {out} = fw_gelu (t {inp}) := by',
        f'  apply SourceGeluRead.gelu_value_of_split {label}Graph {label}Scope {label}Peers {label}Graph.nodes',
        f'    {req} ({req}.take {k}) ({req}.drop {k+1}) {label}Node_{i}',
        f'    {node.rank} {inp} {out} s t rfl ?_ rfl ?_ h',
        '  · calc',
        f'      {req} = {req}.take {k} ++ {req}.drop {k} := (List.take_append_drop {k} {req}).symm',
        '      _ = _ := rfl',
        f'  · change ∀ row ∈ {req}.drop {k}, {inp} ∉ row.1.outs',
        '    decide', f'#print axioms {name}']
    return proof, dict(theorem=name, world=label, op='FW_gelu', node=list(step.node),
        source_index=i, execution_index=k, input_tids=[inp], output_tid=out,
        input_refs=[list(step.inputs[0].endpoint.ref)], output_refs=[list(step.outputs[0].endpoint.ref)],
        params=[], request='global', source_kwargs=dict(view.node_kwargs(node)),
        source_step=asdict(step), operand_nonwrite_source_indices=suffix)


def _unit(old, global_, locals_, names):
    D, T, B, S, H = (old['dimensions'][k] for k in ('D','T','B','S','H'))
    u = old['unit']; out = global_.outputs[0].endpoint
    name = f'frontierGeluUnitFacts_{out.tid}_{u}'
    row = dict(theorem=name, facts_theorem=name, predecessor=old['facts_theorem'],
        predecessor_facts=old['facts_theorem'],
        family='FW_gelu', unit=u, ranks=old['ranks'], positions=old['positions'],
        dimensions=dict(D=D,T=T,B=B,S=S,H=H), layout='sharded', gather_axis=1,
        input_gather_axis=1, output_gather_axis=1,
        global_shape=[B*D,S*T,H], local_shape=[B,S,H],
        input_shape=list(global_.inputs[0].endpoint.shape), local_input_shape=list(locals_[0].inputs[0].endpoint.shape),
        sm_output_tid=out.tid, sm_output_ref=list(out.ref), source_output_slot=0,
        pm_output_tids=[s.outputs[0].endpoint.tid for s in locals_],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_],
        source_step=asdict(global_), local_steps=[asdict(s) for s in locals_])
    middle._contract(row, global_.outputs[0], [s.outputs[0] for s in locals_])
    xs = _list(f'q {s.inputs[0].endpoint.tid}' for s in locals_)
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in locals_)
    pairs = 'List.Forall₂.nil'
    for s in reversed(locals_):
        pairs = f'List.Forall₂.cons ({names[s.node]} p q hp) ({pairs})'
    proof = [*source._facts_header(name, row),
        f'  have predecessor := {old["facts_theorem"]} s p t q hs hp hvalues',
        f'  have localReads : List.Forall₂ (fun x y => y = fw_gelu x) {xs} {ys} :=',
        f'    {pairs}',
        f'  exact TrainVerify.Denote.source_gelu_unit_output_reconstruct {D} {T} {B} {S} {H} {u}',
        f'    (t {global_.inputs[0].endpoint.tid}) (t {out.tid}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        '    predecessor.1 rfl predecessor.2.1 predecessor.2.2',
        f'    ({names[global_.node]} s t hs) localReads', f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Rebuild FC1 exactly once with the SAME six public objects; no receipt input."""
    try:
        _, closed = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed frontier-gelu original source: {exc}') from exc


def _render(sm, pm, lineages, validation, bound, order, closed):
    if not _same_typed(order, {'sm': build(sm), 'pm': build(pm)}):
        raise ValueError('frontier-gelu complete typed execution order mismatch')
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    adds._bound(lineages, bound)
    parameters = [l for l in lineages if l.role == Role.PARAMETER]
    if not _same_typed([r['lineage'] for r in bound['relations']], [asdict(l) for l in parameters]):
        raise ValueError('frontier-gelu canonical bound spec order mismatch')
    for row, parameter in zip(bound['relations'], parameters, strict=True):
        if not _same_typed([u['unit'] for u in row['units']], [u.unit for u in parameter.units]):
            raise ValueError('frontier-gelu canonical bound unit spec order mismatch')
    owners = validation._inputs[3]['config']['units']; D = len(owners)
    frontier._cover(closed, owners)
    proofs, reads, units, result, retained, deferred, consumed = [], [], [], [], [], [], []
    seen, names = {}, {}
    for i, old in enumerate(closed['frontier_units']):
        g = frontier._output(si, old['source_step'], old['sm_output_ref'])
        ps = [frontier._output(pi, s, ref) for s,ref in zip(old['local_steps'], old['pm_output_refs'], strict=True)]
        middle._contract(old, g, ps)
        B, S, H = old['local_shape']; T = len(ps); u = old['unit']
        if (not _same_typed(old['dimensions'], dict(D=D,T=T,B=B,S=S,H=H))
                or not _same_typed(old['positions'], list(range(u*B,(u+1)*B)))
                or type(old['source_output_slot']) is not int
                or not 0 <= old['source_output_slot'] < len(old['source_step']['outputs'])
                or not _same_typed(old['source_step']['outputs'][old['source_output_slot']]['endpoint']['ref'], g.endpoint.ref)
                or not _same_typed(old['sm_output_tid'], g.endpoint.tid)
                or not _same_typed(old['pm_output_tids'], [p.endpoint.tid for p in ps])):
            raise ValueError('frontier-gelu complete strong frontier dimensions/slot mismatch')
        consumers = [source._consumers(si, [g]), *[source._consumers(pi, [p]) for p in ps]]
        kinds = [[op(c) for c in cs] for cs in consumers]
        if old['gather_axis'] != 1:
            if all(ks == [] for ks in kinds) or all(ks == ['FW_add'] for ks in kinds):
                retained.append(old)
            else:
                deferred.append(dict(old, reason='unsupported hidden-frontier forward consumer', observed_consumer_ops=kinds))
            result.append(old)
            continue
        if not any('FW_gelu' in ks for ks in kinds):
            deferred.append(dict(old, reason='sequence frontier has no exact GELU consumer', observed_consumer_ops=kinds))
            result.append(old)
            continue
        if any(ks != ['FW_gelu'] for ks in kinds):
            raise ValueError('frontier-gelu partial or fan-out consumer cover unsupported')
        global_ = _next(si, g); locals_ = [_next(pi, p) for p in ps]
        parent = si.raw[global_.node]._output_irs[0].parent.tid
        if any(not _same_typed(pi.raw[s.node]._output_irs[0].parent.tid, parent) for s in locals_):
            raise ValueError('frontier-gelu original SM/PM output parent identity mismatch')
        for view, label, step in [(sm, 'sm', global_), *((pm, 'pm', s) for s in locals_)]:
            if step.node in seen:
                if label != 'sm' or not _same_typed(seen[step.node], step):
                    raise ValueError('frontier-gelu duplicate/cross-unit consumer')
                continue
            proof, row = _read(view, label, step, order[label])
            row.update(unit=u, frontier_index=i)
            proofs.extend(proof); reads.append(row); seen[step.node] = step; names[step.node] = row['theorem']
        proof, row = _unit(old, global_, locals_, names)
        row['frontier_index'] = i
        row['sm_consumers'] = [list(c.node) for c in source._consumers(si, global_.outputs)]
        row['pm_consumers'] = [list(c.node) for c in source._consumers(pi, [s.outputs[0] for s in locals_])]
        proofs.extend(proof); units.append(row); result.append(row); consumed.append(i)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, predecessors, frame, costs and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-frontier-gelu-values-emitted-uncompiled', reads=reads, units=units,
        frontier_units=result, consumed_frontier_indices=consumed, retained_units=retained, deferred_units=deferred,
        lean_bytes=len(text.encode()), cost_scope='frontier exact GELU fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
