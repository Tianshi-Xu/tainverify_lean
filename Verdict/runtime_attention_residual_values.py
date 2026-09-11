"""Rank-three hidden-sharded residual source candidates, deliberately UNCOMPILED.

The SAME six inputs freshly authenticate both branches. No caller receipt,
output premise, import, capture, kernel or public completion is authority here.
"""
from dataclasses import asdict

from Verdict import runtime_output_projection_exchange_values as exchange
from Verdict import runtime_post_add_values as post
from Verdict import runtime_add_values as adds
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_view_values as view
from Verdict import runtime_embedding_routes as routes
from Verdict import graph_to_lean as c
from Verdict.runtime_world import _ordinary
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed, op


def _identity(index, cell):
    node = _one((n for n in index.view.nodes() if _same_typed(tuple(n), tuple(cell.node))),
                'attention-residual original typed node missing/ambiguous')
    if (any(type(n) is not int or n < 0 for n in tuple(node)[1:4])
            or type(cell.rank) is not int or cell.rank != node.rank
            or op(cell) != str(index.view.node_opname(node)).split('.')[-1]
            or type(cell.kwargs) is not dict
            or not _same_typed(cell.kwargs, index.view.node_kwargs(node))):
        raise ValueError('attention-residual original opcode/owner/kwargs mismatch')
    for key in ('inputs', 'outputs'):
        refs = [tuple(r) for r in getattr(cell, key)]
        actual = [tuple(index.view.source_tensor(t)) for t in getattr(index.view, 'node_'+key)(node)]
        if (not _same_typed(refs, actual) or any(len(r) != 5 or type(r[0]) is not str
                or any(type(n) is not int for n in r[1:]) for r in refs)):
            raise ValueError('attention-residual original ordered fullrefs mismatch')
    snapshot = getattr(index.view, '_collective_source', None)
    # SM has no runtime writer snapshot in the established source contract.
    if snapshot is None:
        if node[0] != 's':
            raise ValueError('attention-residual PM original writer snapshot missing')
    else:
        from trainverify.runtime_source_authority import writer_export_id
        writer = _one((w for w in snapshot['writers'] if _same_typed(
            (w['ref']['world'], w['ref']['runtime_rank'], w['ref']['microbatch'],
             w['ref']['source_cid'], w['source_irname']), tuple(node))),
            'attention-residual original writer missing/ambiguous')
        ref = writer['ref']
        if (ref['op'] != op(cell) or type(ref['call_instance']) is not int
                or ref['call_instance'] < 0 or writer['export_id'] != writer_export_id(ref)):
            raise ValueError('attention-residual original writer/export/call mismatch')
        fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
        for key in ('inputs', 'outputs'):
            if not _same_typed(writer[key], [dict(zip(fields, r, strict=True)) for r in getattr(cell, key)]):
                raise ValueError('attention-residual writer ordered fullrefs mismatch')
    return node


def _port(index, ref, ir):
    # _metadata/post._port coerce raw shape elements; check BEFORE conversion.
    if (ir is None or len(ir.shape) != 3
            or any(type(n) is not int or n <= 0 for n in ir.shape)
            or type(ir.parent.tid) is not int):
        raise ValueError('attention-residual original rank-three shape/parent types required')
    return post._port(index, ref, ir)


def _ports(index, cell, field):
    refs = getattr(cell, field); irs = getattr(cell, '_'+field[:-1]+'_irs', None)
    if irs is None or len(irs) != len(refs) or any(ir is None for ir in irs):
        raise ValueError('attention-residual complete original metadata required')
    ports = tuple(_port(index, ref, ir) for ref, ir in zip(refs, irs, strict=True))
    if field == 'outputs':
        if any(not _same_typed(p.endpoint.writer, tuple(cell.node))
               or not _same_typed(p.endpoint.ref[:3], tuple(cell.node)[:3]) for p in ports):
            raise ValueError('attention-residual original output writer/owner mismatch')
    return ports


def _output(index, descriptor):
    cell = index.raw[tuple(descriptor['node'])]
    _identity(index, cell)
    _ports(index, cell, 'outputs')
    return middle._output(index, descriptor)


def _parameters(source, node):
    kw = source.node_kwargs(node)
    if (str(source.node_opname(node)).split('.')[-1] != 'FW_add'
            or any(node in getattr(source, key, {}) for key in ('collective_scopes', 'chunk_scopes', 'wred_scopes'))
            or len(source.node_inputs(node)) != 2 or len(source.node_outputs(node)) != 1
            or type(kw) is not dict or set(kw) - {'alpha', '__consts'}
            or not _same_typed(kw.get('alpha', 1), 1)
            or not _same_typed(kw.get('__consts', []), [])):
        raise ValueError('attention-residual original add opcode/arity/alpha/kwargs mismatch')
    raw = c._get_node_params(source, node, num_parts=0)
    if raw is not None and not _same_typed(raw, []):
        raise ValueError('attention-residual exact empty original params required')
    params, status = _ordinary(source, node, lambda *a, **k: raw)
    if status is not None or not _same_typed(params, []):
        raise ValueError('attention-residual exact empty normalized params required')


def _boundary(index, cell, ports):
    node = _identity(index, cell)
    _parameters(index.view, node)
    inputs, outputs = _ports(index, cell, 'inputs'), _ports(index, cell, 'outputs')
    if len(ports) != 2:
        raise ValueError('attention-residual complete original operands required')
    for p, ir in zip(ports, cell._input_irs, strict=True):
        producer = index.raw[p.endpoint.writer]
        _identity(index, producer)
        originals = _ports(index, producer, 'outputs')
        j = _one((j for j, original in enumerate(originals) if original.endpoint.ref == p.endpoint.ref),
                 'attention-residual producer ref missing/ambiguous')
        if (not _same_typed(originals[j], p)
                or not _same_typed(producer._output_irs[j].parent.tid, ir.parent.tid)):
            raise ValueError('attention-residual original producer/consumer parent identity mismatch')
        # A multiref transports each output's layout from its single input.
        if op(producer) == 'FW_multiref':
            source_ports = _ports(index, producer, 'inputs')
            if len(source_ports) != 1 or any(not _same_typed(post._layout(x), post._layout(source_ports[0])) for x in originals):
                raise ValueError('attention-residual complete multiref producer layout mismatch')
    step = routes.Step(tuple(node), 'FW_add', inputs, outputs)
    if any(not _same_typed(p.endpoint.ref[:3], tuple(node)[:3]) for p in inputs):
        raise ValueError('attention-residual original operand owner mismatch')
    adds._pointwise_layout(step, *ports)
    return step


def _read(source, label, step, order):
    schedule = order['execution_to_source']
    if (any(type(n) is not int for n in schedule) or len(schedule) != len(source.nodes())
            or set(schedule) != set(range(len(source.nodes())))):
        raise ValueError('attention-residual complete exact execution order required')
    node = _one((n for n in source.nodes() if _same_typed(tuple(n), step.node)),
                'attention-residual read typed source node missing/ambiguous')
    _parameters(source, node)
    proof, row = adds._read(source, label, step, order)
    if not _same_typed(order, adds.build(source)):
        raise ValueError('attention-residual execution order differs from original schedule')
    name = f'attentionResidualRead_{label}_{step.outputs[0].endpoint.tid}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row['theorem'] = name
    return proof, row


def _facts_header(name, row):
    D, T = (row['dimensions'][k] for k in ('D', 'T'))
    ys = _list(f'q {tid}' for tid in row['pm_output_tids'])
    return [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {row["sm_output_tid"]}).shape = {row["global_shape"]} ∧',
        f'    (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {row["unit"]} (t {row["sm_output_tid"]}) = allGatherPrimDimN 2 {T} 0 {ys} := by']


def _row(old, global_, locals_, source_step, local_steps, name):
    B, S, H = locals_[0].endpoint.shape
    D, T = old['dimensions']['D'], len(locals_)
    row = dict(theorem=name, facts_theorem=name, unit=old['unit'],
        ranks=old['ranks'], positions=old['positions'], dimensions=dict(D=D, T=T, B=B, S=S, H=H),
        layout='sharded', gather_axis=2, global_shape=[B*D, S, H*T], local_shape=[B, S, H],
        sm_output_tid=global_.endpoint.tid, sm_output_ref=list(global_.endpoint.ref),
        pm_output_tids=[p.endpoint.tid for p in locals_], pm_output_refs=[list(p.endpoint.ref) for p in locals_],
        source_step=asdict(source_step), local_steps=[asdict(s) for s in local_steps])
    middle._contract(row, global_, locals_)
    return row


def _alias(si, pi, old, selected, reads):
    producers = []
    for index, desc in [(si, old['source_step']), *((pi, d) for d in old['local_steps'])]:
        cell = index.raw[tuple(desc['node'])]
        producer = _boundary(index, cell, _ports(index, cell, 'inputs'))
        if not _same_typed(asdict(producer), desc):
            raise ValueError('attention-residual fresh old-add source mismatch')
        alias_cell = _one((c for c in index.raw.values() if op(c) == 'FW_multiref'
                          and producer.outputs[0].endpoint.ref in map(tuple, c.inputs)),
                         'attention-residual original multiref missing/ambiguous')
        _identity(index, alias_cell)
        alias_inputs = _ports(index, alias_cell, 'inputs')
        _ports(index, alias_cell, 'outputs')
        if (len(alias_inputs) != 1
                or not _same_typed(alias_inputs[0].endpoint.ref, producer.outputs[0].endpoint.ref)
                or not _same_typed(cell._output_irs[0].parent.tid, alias_cell._input_irs[0].parent.tid)):
            raise ValueError('attention-residual old-add/multiref edge parent identity mismatch')
        alias = post._next(index, producer.outputs[0])
        producers.append(alias)
    global_, *locals_ = producers
    slot = selected['slot']
    gps = global_.outputs[slot]; lps = [s.outputs[slot] for s in locals_]
    if not _same_typed((list(gps.endpoint.ref), [list(p.endpoint.ref) for p in lps]),
                       (selected['sm_output_ref'], selected['pm_output_refs'])):
        raise ValueError('attention-residual selected alias ordered fullrefs mismatch')
    name = f'attentionResidualAliasFacts_{gps.endpoint.tid}_{old["unit"]}'
    row = _row(old, gps, lps, global_, locals_, name)
    row.update(slot=slot, predecessor_facts=old['facts_theorem'], selected_output_ref=list(gps.endpoint.ref))
    rewrites = []
    for label, alias, out in [('sm', global_, gps), *(('pm', a, p) for a, p in zip(locals_, lps, strict=True))]:
        read = _one((r for r in reads if _same_typed(r['source_step'], asdict(alias)) and r['world'] == label),
                    'attention-residual fresh complete multiref read missing/ambiguous')
        store, initial, hyp = ('t', 's', 'hs') if label == 'sm' else ('q', 'p', 'hp')
        rewrites.append(f'{read["theorem"]} {initial} {store} {hyp} {out.endpoint.tid} {adds._member(slot)}')
    proof = [*_facts_header(name, row), '  rw ['+', '.join(rewrites)+']',
        f'  exact {old["facts_theorem"]} s p t q hs hp hvalues', f'#print axioms {name}']
    return proof, row, gps, lps


def _unit(old, global_, locals_, records, names):
    name = f'attentionResidualUnitFacts_{global_.outputs[0].endpoint.tid}_{old["unit"]}'
    row = _row(old, global_.outputs[0], [s.outputs[0] for s in locals_], global_, locals_, name)
    row['predecessors'] = [r['facts_theorem'] for r in records]
    D, T, B, S, H = (row['dimensions'][k] for k in ('D', 'T', 'B', 'S', 'H'))
    u = row['unit']; y = row['sm_output_tid']
    xs, zs = (_list(f'q {s.inputs[j].endpoint.tid}' for s in locals_) for j in range(2))
    ys = _list(f'q {s.outputs[0].endpoint.tid}' for s in locals_)
    terms = _list(f'elemwiseAdd (q {s.inputs[0].endpoint.tid}) (q {s.inputs[1].endpoint.tid})' for s in locals_)
    proof = [*_facts_header(name, row),
        f'  have a := {records[0]["facts_theorem"]} s p t q hs hp hvalues',
        f'  have b := {records[1]["facts_theorem"]} s p t q hs hp hvalues',
        f'  have localAdds : {ys} = List.zipWith elemwiseAdd {xs} {zs} := by',
        f'    change {ys} = {terms}',
        '    exact '+_cons_equal([f'{names[s.node]} p q hp' for s in locals_]),
        f'  exact TrainVerify.Denote.source_add_unit_output_facts {D} {T} {B} {S} {H} {u}',
        f'    (t {global_.inputs[0].endpoint.tid}) (t {global_.inputs[1].endpoint.tid}) (t {y}) {xs} {zs} {ys}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        '    a.1 b.1 rfl rfl (fun r hr => a.2.1 _ (List.get_mem _ _))',
        '    (fun r hr => b.2.1 _ (List.get_mem _ _)) a.2.2 b.2.2',
        f'    ({names[global_.node]} s t hs) localAdds', f'#print axioms {name}']
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    try:
        args = (sm, pm, lineages, validation, bound, execution_order)
        _, right = exchange.render(*args)
        _, aliases = post.render(*args)
        _, closed = adds.render(*args)
        return _render(sm, pm, validation, execution_order, right, aliases, closed)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed attention-residual original source: {exc}') from exc


def _render(sm, pm, validation, order, right, aliases, closed):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    owners = validation._inputs[3]['config']['units']
    groups = {}
    for old in right['frontier_units']:
        if (type(old['unit']) is not int or not _same_typed(old['dimensions']['D'], len(owners))
                or any(type(n) is not int or n < 0 for n in (*old['ranks'], *old['positions']))):
            raise ValueError('attention-residual exact DP dimensions/ranks/positions required')
        groups.setdefault(tuple(old['sm_output_ref']), []).append(old['unit'])
    if not groups or any(len(us) != len(owners) or len(set(us)) != len(us)
                         or set(us) != {o['unit'] for o in owners} for us in groups.values()):
        raise ValueError('attention-residual complete original DP unit cover required')
    proofs, reads, units, alias_units, names, used = [], [], [], [], {}, set()
    for i, old in enumerate(right['frontier_units']):
        if old['layout'] != 'sharded' or not _same_typed(old['gather_axis'], 2):
            raise ValueError('attention-residual requires hidden-sharded predecessor')
        owner = _one((u for u in validation._inputs[3]['config']['units'] if _same_typed(u['unit'], old['unit'])),
                     'attention-residual DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (old['ranks'], old['positions'])):
            raise ValueError('attention-residual DP ranks/positions mismatch')
        g = _output(si, old['source_step'])
        ps = [_output(pi, d) for d in old['local_steps']]
        middle._contract(old, g, ps)
        cell = view._consumer(si, g)
        selected = _one((a for a in aliases['units'] if _same_typed(a['unit'], old['unit'])
                         and tuple(a['sm_output_ref']) in map(tuple, cell.inputs)),
                        'attention-residual original skip alias missing/ambiguous')
        if not _same_typed((selected['ranks'], selected['positions']), (old['ranks'], old['positions'])):
            raise ValueError('attention-residual skip DP identity mismatch')
        prior = _one((a for a in closed['units'] if a['theorem'] == selected['predecessor']
                      and _same_typed(a['unit'], old['unit'])), 'attention-residual complete old-add facts missing/ambiguous')
        proof, alias, skip, skips = _alias(si, pi, prior, selected, aliases['reads'])
        proofs.extend(proof); alias_units.append(alias)
        candidates = [(skip, g), (g, skip)]
        ports = _one((p for p in candidates if _same_typed([x.endpoint.ref for x in p], [tuple(r) for r in cell.inputs])),
                     'attention-residual original SM operand order mismatch')
        skip_first = ports[0] == skip
        records = [alias, old] if skip_first else [old, alias]
        global_ = _boundary(si, cell, ports)
        locals_ = []
        for a, b in zip(skips, ps, strict=True):
            ports = (a, b) if skip_first else (b, a)
            pc = view._consumer(pi, b)
            local = _boundary(pi, pc, ports)
            if local.node in used:
                raise ValueError('attention-residual duplicate/cross-DP local add')
            used.add(local.node); locals_.append(local)
        for label, source, step in [('sm', sm, global_), *(('pm', pm, s) for s in locals_)]:
            if step.node not in names:
                proof, row = _read(source, label, step, order[label])
                row.update(unit=old['unit'], frontier_index=i)
                names[step.node] = row['theorem']; proofs.extend(proof); reads.append(row)
        proof, row = _unit(old, global_, locals_, records, names)
        row['frontier_index'] = i
        proofs.extend(proof); units.append(row)
    text = '\n'.join(['-- UNCOMPILED: parent owns imports, integration and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-attention-residual-values-emitted-uncompiled', reads=reads,
        units=units, alias_units=alias_units, frontier_units=units, deferred_units=[],
        consumed_frontier_indices=list(range(len(units))), lean_bytes=len(text.encode()),
        cost_scope='new residual fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
