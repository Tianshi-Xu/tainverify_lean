"""First original-source output projection, UNCOMPILED.

Fresh SAME-six axis-one predecessor facts and the same canonical parameter
bound are the only authorities. No following exchange or residual is advanced.
"""
from dataclasses import asdict

from Verdict import runtime_view_flatten_exchange_values as predecessor
from Verdict import runtime_projection_values as projection
from Verdict import runtime_add_values as adds
from Verdict import runtime_post_add_values as post
from Verdict import graph_to_lean as c
from Verdict.runtime_world import _ordinary
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_view_values as view
from Verdict.runtime_embedding_position_units import _list
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op


def _kwargs(kw):
    if (type(kw) is not dict or set(kw) - {'bias', '__consts'}
            or ('bias' in kw and kw['bias'] is not None)
            or ('__consts' in kw and not _same_typed(kw['__consts'], []))):
        raise ValueError('output-projection strict original kwargs/bias mismatch')


def _parameters(source, node):
    if (str(source.node_opname(node)).split('.')[-1] != 'FW_linear'
            or any(node in getattr(source, name, {}) for name in
                   ('collective_scopes', 'chunk_scopes', 'wred_scopes'))
            or len(source.node_inputs(node)) != 2 or len(source.node_outputs(node)) != 1):
        raise ValueError('output-projection original opcode/global request/arity mismatch')
    _kwargs(source.node_kwargs(node))
    raw = c._get_node_params(source, node, num_parts=0)
    # Existing Optional[List[int]] extractor uses None for parameter-free ops.
    if raw is not None and not _same_typed(raw, []):
        raise ValueError('output-projection original empty params required')
    params, status = _ordinary(source, node, lambda *a, **k: raw)
    if status is not None or not _same_typed(params, []):
        raise ValueError('output-projection original normalized params mismatch')


def _linear(index, activation):
    cell = view._consumer(index, activation)
    if op(cell) != 'FW_linear':
        raise ValueError('output-projection immediate original consumer must be linear')
    _kwargs(cell.kwargs)
    node = projection._node(index, cell)
    _parameters(index.view, node)
    if not _same_typed(tuple(cell.node), tuple(node)):
        raise ValueError('output-projection original typed node mismatch')
    for method, refs in [('node_inputs', cell.inputs), ('node_outputs', cell.outputs)]:
        if not _same_typed([tuple(index.view.source_tensor(t)) for t in getattr(index.view, method)(node)],
                           [tuple(r) for r in refs]):
            raise ValueError('output-projection original ordered fullrefs mismatch')
    snapshot = getattr(index.view, '_collective_source', None)
    if snapshot is not None:
        from trainverify.runtime_source_authority import writer_export_id
        writer = _one((w for w in snapshot['writers'] if _same_typed(
            (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
             w['ref']['source_cid'], w['source_irname']), tuple(node))),
            'output-projection original writer missing/ambiguous')
        ref = writer['ref']
        if (ref['op'] != op(cell) or type(ref['call_instance']) is not int
                or ref['call_instance'] < 0 or writer['export_id'] != writer_export_id(ref)):
            raise ValueError('output-projection original writer/export/call mismatch')
        fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
        for key in ('inputs', 'outputs'):
            if not _same_typed(writer[key], [dict(zip(fields, r, strict=True)) for r in getattr(cell, key)]):
                raise ValueError('output-projection writer ordered fullrefs mismatch')
    producer = index.raw[activation.endpoint.writer]
    originals = getattr(producer, '_output_irs', None)
    inputs = getattr(cell, '_input_irs', None); outputs = getattr(cell, '_output_irs', None)
    if (originals is None or len(originals) != len(producer.outputs) or any(ir is None for ir in originals)
            or inputs is None or len(inputs) != 2 or any(ir is None for ir in inputs)
            or outputs is None or len(outputs) != 1 or outputs[0] is None):
        raise ValueError('output-projection complete original producer/input/output metadata required')
    original = originals[list(map(tuple, producer.outputs)).index(activation.endpoint.ref)]
    if (any(type(ir.parent.tid) is not int for ir in [original, *inputs, *outputs])
            or not _same_typed(original.parent.tid, inputs[0].parent.tid)):
        raise ValueError('output-projection original producer/consumer parent identity mismatch')
    if not _same_typed(post._port(index, activation.endpoint.ref, original), activation):
        raise ValueError('output-projection original activation producer metadata mismatch')
    step = projection._linear(index, activation)
    x, w = step.inputs; y, = step.outputs
    if (not _same_typed(x.endpoint.ref[:3], tuple(node)[:3])
            or not _same_typed(y.endpoint.ref[:3], tuple(node)[:3])
            or not _same_typed(y.endpoint.writer, tuple(node))
            or w.endpoint.phase != 'initial' or w.endpoint.writer is not None):
        raise ValueError('output-projection original owner/writer/initial weight mismatch')
    return step


def _read(source, label, step, order):
    node = _one((n for n in source.nodes() if _same_typed(tuple(n), step.node)),
        'output-projection read original node missing/ambiguous')
    _parameters(source, node)
    if step.op != 'FW_linear':
        raise ValueError('output-projection read opcode mismatch')
    schedule = order['execution_to_source']
    if (any(type(n) is not int for n in schedule) or len(schedule) != len(source.nodes())
            or set(schedule) != set(range(len(source.nodes())))):
        raise ValueError('output-projection complete execution order required')
    proof, row = projection._read(source, label, step, order)
    name = f'outputProjectionRead_{label}_{step.outputs[0].endpoint.tid}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row['theorem'] = name
    return proof, row


def _parameter(si, pi, lineages, specs, global_, locals_, old):
    # norm._binding validates identities/roles/bound metadata. First ensure no
    # original weight occurrence can disappear through its legacy zip loop.
    for index, ports in ((si, [global_.inputs[1]]), (pi, [s.inputs[1] for s in locals_])):
        refs = {p.endpoint.ref for p in ports}
        for cell in index.raw.values():
            if not refs.intersection(map(tuple, cell.inputs)):
                continue
            irs = getattr(cell, '_input_irs', None)
            if irs is None or len(irs) != len(cell.inputs) or any(ir is None for ir in irs):
                raise ValueError('output-projection complete original weight occurrence metadata required')
            for ref, ir in zip(cell.inputs, irs, strict=True):
                if tuple(ref) in refs and (ir.is_param() is not True or ir.is_grad() is not False):
                    raise ValueError('output-projection original exact parameter role required')
    return projection._parameter(si, pi, lineages, specs, global_, locals_, old, False)


def _unit(old, global_, locals_, parameter, names, spec_count):
    D, T, B = (old['dimensions'][k] for k in ('D', 'T', 'B'))
    _, S, I = locals_[0].inputs[0].endpoint.shape
    O = parameter['sm_shape'][0]; u = old['unit']
    x = global_.inputs[0].endpoint.tid; w = parameter['sm_tid']; y = global_.outputs[0].endpoint.tid
    xs, ys, ws = (_list(f'q {tid}' for tid in tids) for tids in (
        [s.inputs[0].endpoint.tid for s in locals_],
        [s.outputs[0].endpoint.tid for s in locals_], parameter['pm_tids']))
    name = f'outputProjectionUnitFacts_{y}_{u}'
    row = dict(theorem=name, facts_theorem=name, predecessor=old['facts_theorem'],
        family='FW_linear', unit=u, ranks=old['ranks'], positions=old['positions'],
        dimensions=dict(D=D, T=T, B=B, S=S, I=I, O=O), layout='sharded',
        input_gather_axis=1, gather_axis=1, output_gather_axis=1,
        global_shape=[B*D, S*T, O], local_shape=[B, S, O],
        sm_output_tid=y, sm_output_ref=list(global_.outputs[0].endpoint.ref),
        pm_output_tids=[s.outputs[0].endpoint.tid for s in locals_],
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_],
        parameters=[parameter], source_step=asdict(global_), local_steps=[asdict(s) for s in locals_])
    middle._contract(row, global_.outputs[0], [s.outputs[0] for s in locals_])
    i = parameter['spec_index']
    selected = 'hrels' + '.2'*i + ('.1' if i < spec_count-1 else '')
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {y}).shape = {row["global_shape"]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {y}) = allGatherPrimDimN 1 {T} 0 {ys} := by',
        f'  have predecessor := {old["facts_theorem"]} s p t q hs hp hvalues',
        '  have hrels := initialParameterRelations_of_values t q (initialParameterValues_final s p t q hs hp hvalues)',
        f'  have weightRel : RelationCompiler.ReplicatedRel (t {w}) {ws} {parameter["sm_shape"]} := {selected}']
    for j, s in enumerate(locals_):
        a = s.inputs[0].endpoint.tid; b = s.outputs[0].endpoint.tid
        proof += [f'  have local{j} : q {b} = fw_linear (q {a}) (t {w}) :=',
            f'    ({names[s.node]} p q hp).trans (congrArg (fw_linear (q {a}))',
            f'      (weightRel.replica_values (q {parameter["pm_tids"][j]}) {adds._member(j)}))']
    pairs = 'List.Forall₂.nil'
    for j in reversed(range(T)):
        pairs = f'List.Forall₂.cons local{j} ({pairs})'
    proof += [f'  have localReads : List.Forall₂ (fun x y => y = fw_linear x (t {w})) {xs} {ys} :=',
        f'    {pairs}',
        f'  exact TrainVerify.Denote.source_linear_sequence_unit_output_reconstruct {D} {T} {B} {S} {I} {O} {u}',
        f'    (t {x}) (t {w}) (t {y}) {xs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        '    predecessor.1 rfl predecessor.2.1 weightRel.full_shape predecessor.2.2',
        f'    ({names[global_.node]} s t hs) localReads', f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """Reauthenticate the complete original graph; caller receipts are not inputs."""
    try:
        _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, lineages, validation, bound, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed output-projection original source: {exc}') from exc


def _render(sm, pm, lineages, validation, bound, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    specs = adds._bound(lineages, bound)
    proofs, reads, units, names, seen, identities = [], [], [], {}, {}, set()
    def emit(source, label, step, i, old):
        if step.node in seen:
            if label != 'sm' or not _same_typed(seen[step.node], step):
                raise ValueError('output-projection duplicate/cross-DP consumer')
            return
        proof, row = _read(source, label, step, order[label])
        row.update(unit=old['unit'], frontier_index=i)
        proofs.extend(proof); reads.append(row)
        seen[step.node] = step; names[step.node] = row['theorem']
    for i, old in enumerate(prior['frontier_units']):
        if old['layout'] != 'sharded' or not _same_typed(old['gather_axis'], 1):
            raise ValueError('output-projection requires axis1 sharded predecessor')
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], old['unit'])), 'output-projection DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (old['ranks'], old['positions'])):
            raise ValueError('output-projection original DP ownership/order mismatch')
        g = middle._output(si, old['source_step'])
        ports = [middle._output(pi, d) for d in old['local_steps']]
        middle._contract(old, g, ports)
        identity = (g.endpoint.ref, tuple(p.endpoint.ref for p in ports))
        if identity in identities:
            raise ValueError('output-projection duplicate frontier identity')
        identities.add(identity)
        global_ = _linear(si, g); locals_ = [_linear(pi, p) for p in ports]
        parameter = _parameter(si, pi, lineages, specs, global_, locals_, old)
        emit(sm, 'sm', global_, i, old)
        for s in locals_:
            emit(pm, 'pm', s, i, old)
        proof, row = _unit(old, global_, locals_, parameter, names, len(specs))
        row['frontier_index'] = i
        proofs.extend(proof); units.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent owns capture, assembly, imports and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-output-projection-values-emitted-uncompiled',
        reads=reads, units=units, frontier_units=units, deferred_units=[],
        consumed_frontier_indices=list(range(len(units))), lean_bytes=len(text.encode()),
        deferred_stage='after-output-projection: downstream unproved',
        cost_scope='new output projection fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
