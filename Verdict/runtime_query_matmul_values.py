"""First source query-axis matmul with replicated V; Lean remains UNCOMPILED.

Only fresh six-argument softmax-exchange authority can supply the frontier.
Right copies are consumed pairwise, never gathered or duplicated in the frontier.
"""
from dataclasses import asdict

from Verdict import runtime_softmax_exchange_values as predecessor
from Verdict import runtime_middle_exchange_values as middle
from Verdict import runtime_matmul_values as binary
from Verdict import runtime_post_add_values as post
from Verdict import runtime_embedding_routes as routes
from Verdict.runtime_embedding_position_units import _list, _cons_equal
from Verdict.runtime_embedding_units import _one
from Verdict.runtime_lineage import _Index, _same_typed


def _consumer(index, port, order):
    return binary._consumer(index, port, order)


def _read(source, label, step, order):
    proof, row = binary._read(source, label, step, order)
    name = f'queryMatmulRead_{label}_{step.outputs[0].endpoint.tid}'
    proof = [line.replace(row['theorem'], name) for line in proof]
    row['theorem'] = name
    return proof, row


def render(sm, pm, lineages, validation, bound, execution_order):
    """No externally supplied predecessor receipts, output facts, or schedules."""
    try:
        _, prior = predecessor.render(sm, pm, lineages, validation, bound, execution_order)
        return _render(sm, pm, validation, execution_order, prior)
    except (KeyError, TypeError, AttributeError, IndexError, StopIteration, OverflowError) as exc:
        raise ValueError(f'malformed query matmul original source: {exc}') from exc


def _matmul(index, cell, operands):
    """Derive output geometry exclusively from both actual input partitions."""
    if len(operands) != 2 or not _same_typed([p.endpoint.ref for p in operands],
            [tuple(r) for r in cell.inputs]):
        raise ValueError('matmul ordered local ports/source identity mismatch')
    irs = getattr(cell, '_input_irs', None)
    if irs is None or len(irs) != 2:
        raise ValueError('matmul requires complete paired input metadata')
    # Missing original producer metadata must not turn a present raw parent id
    # into an optional check. Require both producers before comparing either id.
    originals = []
    for p in operands:
        producer = index.raw[p.endpoint.writer]
        producer_irs = getattr(producer, '_output_irs', None)
        if (producer_irs is None or len(producer_irs) != len(producer.outputs)
                or any(ir is None for ir in producer_irs)):
            raise ValueError('query matmul complete original producer output metadata required')
        originals.append(producer_irs[list(map(tuple, producer.outputs)).index(p.endpoint.ref)])
    for p, ir, original in zip(operands, irs, originals, strict=True):
        if (not _same_typed(post._port(index, p.endpoint.ref, ir), p)
                or not _same_typed(post._port(index, p.endpoint.ref, original), p)):
            raise ValueError('matmul producer consumer paired metadata mismatch')
        if (type(ir.parent.tid) is not int or type(original.parent.tid) is not int
                or not _same_typed(ir.parent.tid, original.parent.tid)):
            raise ValueError('query matmul original producer/consumer parent identity mismatch')
    x, y = operands
    if (len(x.parent_shape) != 4 or len(y.parent_shape) != 4
            or len(x.endpoint.shape) != 4 or len(y.endpoint.shape) != 4
            or x.parent_shape[:2] != y.parent_shape[:2]
            or x.endpoint.shape[:2] != y.endpoint.shape[:2]
            or x.bounds[:2] != y.bounds[:2]
            or x.parent_shape[3] != y.parent_shape[2]
            or x.endpoint.shape[3] != y.endpoint.shape[2]
            or x.bounds[3] != (0, x.parent_shape[3])
            or y.bounds[2] != (0, y.parent_shape[2])
            or y.bounds[3] != (0, y.parent_shape[3])
            or not _same_typed(x.value_part, (0, 1))
            or not _same_typed(y.value_part, (0, 1))):
        raise ValueError('matmul unsupported broadcast/layout/contraction/value partition')
    whole = (*x.parent_shape[:3], y.parent_shape[3])
    bounds = (*x.bounds[:3], y.bounds[3])
    ep = index.endpoint(cell.outputs[0])
    shape = (*x.endpoint.shape[:3], y.endpoint.shape[3])
    if ep.shape != shape or any(type(d) is not int or d <= 0 for d in shape):
        raise ValueError('matmul input-derived output geometry mismatch')
    outs = getattr(cell, '_output_irs', None)
    if outs is None or len(outs) != 1:
        raise ValueError('matmul requires complete output metadata')
    actual = post._port(index, ep.ref, outs[0])
    derived = routes.Port(ep, actual.parent_name, whole, bounds, (0, 1))
    if not _same_typed(actual, derived):
        raise ValueError('matmul input-derived output parent/bounds/value mismatch')
    return routes.Step(tuple(cell.node), 'FW_matmul', tuple(operands), (derived,))

def _unit(left, right, global_, locals_, names, join):
    if (left['layout'] != 'sharded' or not _same_typed(left['gather_axis'], 2)
            or right['layout'] != 'replicated_within_dp' or right['gather_axis'] is not None):
        raise ValueError('query matmul unsupported ready predecessor layout')
    if not _same_typed((left['unit'], left['ranks'], left['positions'],
            [left['dimensions'][k] for k in ('D', 'T', 'B')]),
            (right['unit'], right['ranks'], right['positions'],
            [right['dimensions'][k] for k in ('D', 'T', 'B')])):
        raise ValueError('matmul mixed DP or ordered ranks')
    D, T, B = (left['dimensions'][k] for k in ('D', 'T', 'B'))
    u = left['unit']; _, H, Q, K = left['local_shape']; M = right['local_shape'][3]
    if any(type(n) is not int or n <= 0 for n in (D, T, B, H, Q, K, M)):
        raise ValueError('query matmul positive integer geometry required')
    if (left['local_shape'] != [B, H, Q, K] or right['local_shape'] != [B, H, K, M]
            or left['global_shape'] != [B*D, H, Q*T, K]
            or right['global_shape'] != [B*D, H, K, M]):
        raise ValueError('query matmul paired rank4 contraction geometry mismatch')
    out = global_.outputs[0].endpoint; name = f'queryMatmulUnitFacts_{out.tid}_{u}'
    row = dict(theorem=name, facts_theorem=name, family='FW_matmul', unit=u,
        ranks=left['ranks'], positions=left['positions'], layout='sharded', gather_axis=2,
        dimensions=dict(D=D, T=T, B=B, H=H, Q=Q, K=K, M=M),
        global_shape=[B*D, H, Q*T, M], local_shape=[B, H, Q, M],
        sm_output_ref=list(out.ref), sm_output_tid=out.tid,
        pm_output_refs=[list(s.outputs[0].endpoint.ref) for s in locals_],
        pm_output_tids=[s.outputs[0].endpoint.tid for s in locals_],
        predecessors=[left['facts_theorem'], right['facts_theorem']], ordered_join=join,
        source_step=asdict(global_), local_steps=[asdict(s) for s in locals_])
    middle._contract(row, global_.outputs[0], [s.outputs[0] for s in locals_])
    xs, ys = (_list(f'q {s.inputs[i].endpoint.tid}' for s in locals_) for i in (0, 1))
    zs = _list(f'q {s.outputs[0].endpoint.tid}' for s in locals_)
    terms = _list(f'fw_matmul (q {s.inputs[0].endpoint.tid}) (q {s.inputs[1].endpoint.tid})' for s in locals_)
    gx, gy = [p.endpoint.tid for p in global_.inputs]
    proof = [f'theorem {name} (s p t q : Store)',
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)',
        '    (hvalues : InitialParameterValues s p) :',
        f'    (t {out.tid}).shape = {row["global_shape"]} ∧',
        f'    (∀ z ∈ {zs}, z.shape = {row["local_shape"]}) ∧',
        f'    chunkPrimDimN 0 {D} {u} (t {out.tid}) = allGatherPrimDimN 2 {T} 0 {zs} := by',
        f'  have left := {left["facts_theorem"]} s p t q hs hp hvalues',
        f'  have right := {right["facts_theorem"]} s p t q hs hp hvalues',
        f'  have outputs : {zs} = List.zipWith fw_matmul {xs} {ys} := by',
        f'    change {zs} = {terms}',
        '    exact '+_cons_equal([f'{names[s.node]} p q hp' for s in locals_]),
        f'  exact TrainVerify.Denote.source_query_matmul_unit_output_reconstruct {D} {T} {B} {H} {Q} {K} {M} {u}',
        f'    (t {gx}) (t {gy}) (t {out.tid}) {xs} {ys} {zs}',
        '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
        '    left.1 right.1 rfl rfl left.2.1 right.2.2 left.2.2',
        f'    ({names[global_.node]} s t hs) outputs', f'#print axioms {name}']
    return proof, row

def _render(sm, pm, validation, order, prior):
    si, pi = (_Index(v, raw) for v, raw in zip((sm, pm), validation._inputs[:2], strict=True))
    old = prior['frontier_units']; entries, lookup = [], {}
    for i, u in enumerate(old):
        g = middle._output(si, u['source_step'])
        ps = [middle._output(pi, d) for d in u['local_steps']]
        middle._contract(u, g, ps)
        owner = _one((o for o in validation._inputs[3]['config']['units']
            if _same_typed(o['unit'], u['unit'])), 'matmul source DP owner missing/ambiguous')
        if not _same_typed((owner['ranks'], owner['positions']), (u['ranks'], u['positions'])):
            raise ValueError('matmul source DP ownership/ordered ranks mismatch')
        key = (g.endpoint.ref, u['unit'], tuple(u['ranks']))
        if key in lookup: raise ValueError('matmul duplicate original frontier identity')
        lookup[key] = i
        gc, gr = _consumer(si, g, order['sm'])
        consumers = [_consumer(pi, p, order['pm']) for p in ps]
        entries.append((g, ps, gc, gr, consumers))
    proofs, reads, units, deferred, frontier, joins = [], [], [], [], [], []
    consumed, names = set(), {}
    for i, u in enumerate(old):
        if i in consumed: continue
        g, ps, gc, gr, consumers = entries[i]
        keys = [(tuple(r), u['unit'], tuple(u['ranks'])) for r in gc.inputs]
        missing = [list(k[0]) for k in keys if k not in lookup]
        if missing:
            if any(not _same_typed(r['port_positions'], gr['port_positions']) for _, r in consumers):
                raise ValueError('matmul deferred original ordered port correspondence mismatch')
            deferred.append(dict(unit=u['unit'], predecessor=u['facts_theorem'], source_boundary=u,
                global_first_consumer=gr, first_consumers=[r for _, r in consumers],
                missing_operand_refs=missing, reason='first-original-FW_matmul-missing-operand',
                value_proved=False, frontier_index=i))
            frontier.append(u)
            continue
        pair = [lookup[k] for k in keys]
        if any(j in consumed for j in pair):
            raise ValueError('matmul overlapping original operand coverage')
        if any(tuple(entries[j][2].node) != tuple(gc.node) for j in pair):
            raise ValueError('matmul original SM operand first consumer mismatch')
        left, right = [old[j] for j in pair]
        global_ = _matmul(si, gc, [entries[j][0] for j in pair])
        locals_, local_rows = [], []
        for r in range(len(u['ranks'])):
            cells = [entries[j][4][r] for j in pair]
            if not _same_typed(tuple(cells[0][0].node), tuple(cells[1][0].node)):
                raise ValueError('matmul paired PM first consumer source identity mismatch')
            locals_.append(_matmul(pi, cells[0][0], [entries[j][1][r] for j in pair]))
            local_rows.append(cells[0][1])
        join = dict(frontier_indices=pair, emitted_at_frontier_index=i, unit=u['unit'], ranks=u['ranks'],
            sm_input_refs=[list(p.endpoint.ref) for p in global_.inputs],
            pm_ordered_input_refs=[[list(p.endpoint.ref) for p in s.inputs] for s in locals_],
            sm_node=list(global_.node), pm_nodes=[list(s.node) for s in locals_])
        for source, label, step, auth in [(sm, 'sm', global_, gr),
                *[(pm, 'pm', s, a) for s, a in zip(locals_, local_rows, strict=True)]]:
            if step.node in names:
                if label != 'sm': raise ValueError('matmul duplicate PM source operation')
                continue
            proof, row = _read(source, label, step, order[label])
            row.update(source_writer=auth['source_writer'], writer_ref=auth.get('writer_ref'),
                input_metadata='present', output_metadata='present', unit=u['unit'],
                input_parent_identity='both-present', frontier_index=i)
            names[step.node] = row['theorem']; reads.append(row); proofs.extend(proof)
        proof, unit = _unit(left, right, global_, locals_, names, join)
        proofs.extend(proof); units.append(unit); frontier.append(unit); joins.append(join)
        consumed.update(pair)
    # Ordered coverage is explicit: two operand positions may name the same
    # source tensor, but every original frontier entry is consumed at most once.
    if consumed | {d['frontier_index'] for d in deferred} != set(range(len(old))):
        raise ValueError('matmul incomplete original frontier coverage')
    text = '\n'.join(['-- UNCOMPILED: parent owns actual capture, caps, assembly and kernel gate.',
        'namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
        'set_option maxHeartbeats 500000', *proofs, 'end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return text, dict(status='source-query-matmul-values-emitted-uncompiled', reads=reads, units=units,
        deferred_units=deferred, frontier_units=frontier, ordered_joins=joins,
        consumed_frontier_indices=[i for i in range(len(old)) if i in consumed],
        lean_bytes=len(text.encode()), deferred_stage='after-first-query-matmul: downstream unproved',
        cost_scope='new query matmul fragment only; excludes predecessors, frame and imports',
        proof_admissible=False, kernel_value_proved=False, public_complete=False, torch_refinement=False)
