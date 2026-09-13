"""LN -> original inverse AA -> complete residual sum -> immediate BW_add.

Only same-final-Store equations under the original successful run are composed.
The accepted multiref root is referenced, not re-emitted. No later consumer is
visited and no cross-world gradient equality or refinement is claimed.
"""
from Verdict import graph_to_lean as compiler
from Verdict import runtime_backward_fc1_consumers as fc1
from Verdict import runtime_backward_layernorm_reads as layernorm
from Verdict import runtime_backward_collective_reads as collective
from Verdict import runtime_backward_residual_exchange_reads as residual_exchange
from Verdict import runtime_backward_multiref_reads as multiref
from Verdict import runtime_backward_add_reads as add
from Verdict.runtime_lineage import _same_typed

_FLAGS = ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement')


def _require(ok, reason):
    if not ok:
        raise ValueError('bw-residual-join ' + reason)


def _one(rows, reason):
    rows = list(rows)
    _require(len(rows) == 1, reason)
    return rows[0]


def _branch(read, port, expression, theorem, kind):
    scalar = 'output_ref' in read
    return dict(kind=kind, read=read, source_index=read['source_index'], port=port,
                output_ref=read['output_ref'] if scalar else read['output_refs'][port],
                output_tid=read['output_tid'] if scalar else read['output_tids'][port],
                expression=expression, theorem=theorem)


def _main(world, index, prior):
    """Narrow fresh AA boundary; prior holds only this stage's accepted LN RHSs."""
    view, cells, snapshot, order, label = world
    source, read = collective.render_read(view, cells, snapshot, index, order, label,
                                          layernorm.render_read, 0)

    scope = view.collective_scopes[cells[index].node]
    _require(label == 'pm' and read['opname'] == 'AllToAllPrim'
             and _same_typed(read['params'], list(scope.params))
             and _same_typed(read['ranks'], list(scope.ranks))
             and _same_typed(read['local_index'], scope.local_index)
             and _same_typed(read['input_tids'], [t.tid for t in view.node_inputs(cells[index].node)])
             and _same_typed(read['input_refs'], [list(view.source_tensor(t)) for t in view.node_inputs(cells[index].node)])
             and _same_typed(read['output_ref'], list(cells[index].outputs[0]))
             and _same_typed(read['output_tid'], view.node_outputs(cells[index].node)[0].tid)
             and _same_typed([p['output_refs'][0] for p in read['predecessors']], read['input_refs']),
             'original collective binding mismatch')
    contributions = []
    for peer in read['predecessors']:
        original = _one((r for r in prior if r['world'] == label
                         and _same_typed(r['layernorm']['source_index'], peer['source_index'])),
                        'complete selected-stage LN peer required')
        _require(_same_typed(original['layernorm'], peer), 'fresh original LN peer mismatch')
        contributions.append(_branch(peer, 0, original['layernorm_expressions'][0],
                                     original['layernorm_consumers'][0], 'layernorm'))
    idim, odim = read['params']
    expression = (f'AllToAllSourceFaithful.tensor {len(read["ranks"])} {read["local_index"]} {idim} {odim}'
                  + ' [' + ', '.join('(' + b['expression'] + ')' for b in contributions) + ']')
    name = read['theorems'][0] + '_contributions'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
             f'    t {read["output_tid"]} = {expression} := by',
             f'  rw [{read["theorems"][0]} s t h]',
             '  simp only [List.map_cons, List.map_nil]',
             '  rw [' + ', '.join(b['theorem'] + ' s t h' for b in contributions) + ']',
             f'#print axioms {name}']
    branch = _branch(read, 0, expression, name, 'collective')
    branch['contributions'] = contributions
    return '\n'.join(proof) + '\n', source, branch


def _join(world, index, branches):
    """Rebind the original sum and all ordered branch endpoints on every call.

    This is deliberately not a two-input lemma: every original input must have
    exactly one proved contribution; unsupported extra branches fail closed.
    """
    view, cells, snapshot, order, label = world
    _, merge = multiref.render_read(view, cells, snapshot, index, order, label)

    _require(len(branches) == len(merge['input_refs'])
             and len({tuple(b['output_ref']) for b in branches}) == len(branches)
             and _same_typed([b['output_ref'] for b in branches], merge['input_refs'])
             and _same_typed([b['output_tid'] for b in branches], merge['input_tids']),
             'complete ordered contributions required')
    for port, b in enumerate(branches):
        j, p = b['source_index'], b['port']
        _require(type(j) is int and 0 <= j < len(cells)
                 and type(p) is int and 0 <= p < len(cells[j].outputs), 'typed original branch port required')
        node = cells[j].node
        raw = merge['source_contract']['contributions'][port]
        read = b['read']
        scalar = 'output_ref' in read
        _require(_same_typed(j, raw['source_index'])
                 and _same_typed(j, read['source_index'])
                 and _same_typed(b['output_ref'], list(cells[j].outputs[p]))
                 and _same_typed(b['output_ref'], list(view.source_tensor(view.node_outputs(node)[p])))
                 and _same_typed(b['output_tid'], view.node_outputs(node)[p].tid)
                 and _same_typed(b['output_ref'], read['output_ref'] if scalar else read['output_refs'][p])
                 and _same_typed(b['output_tid'], read['output_tid'] if scalar else read['output_tids'][p])
                 and (not scalar or p == 0)
                 and cells[j].rank == cells[index].rank and cells[j].mb == cells[index].mb
                 and order['source_to_execution'][j] < merge['execution_index'],
                 'original branch endpoint/order mismatch')
    expression = 'tensorSum [' + ', '.join('(' + b['expression'] + ')' for b in branches) + ']'
    name = f'backwardResidualJoin_{label}_{index}'
    proof = [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
             f'    t {merge["output_tids"][0]} = {expression} := by',
             f'  rw [{merge["theorems"][0]} s t h]',
             '  simp only [List.map_cons, List.map_nil]',
             '  rw [' + ', '.join(b['theorem'] + ' s t h' for b in branches) + ']',
             f'#print axioms {name}']
    ai, ac = fc1._consumer(cells, cells[index], 0, 'BW_add')
    add_source, ar = add.render_read(view, cells, snapshot, ai, order, label)
    _require(_same_typed(ar['input_refs'][0], merge['output_refs'][0])
             and _same_typed(ar['input_tids'][0], merge['output_tids'][0])
             and _same_typed(ar['output_tids'], [t.tid for t in view.node_outputs(ac.node)])
             and ac.mb == cells[index].mb and merge['execution_index'] < ar['execution_index'],
             'original direct add cotangent/output/order mismatch')
    names, expressions = [], []
    for port, role in enumerate(('dleft', 'dright')):
        target = f'backwardResidualJoinAdd_{label}_{ai}_{role}'
        rhs = (f'(bw_add2 ({expression}) ' + ' '.join(f'(t {tid})' for tid in ar['input_tids'][1:])
               + f').{port+1}')
        proof += fc1._equation(target, label, ar['output_tids'][port], rhs, [ar['theorems'][port], name])
        names.append(target); expressions.append(rhs)
    return '\n'.join(proof) + '\n', add_source, dict(world=label, merge_read=merge,
        branches=branches, join_expression=expression, join_theorems=[name], add_read=ar,
        add_expressions=expressions, add_theorems=names)


def render(worlds, capture, rank_code):
    # Expensive upstream composition occurs once, with shared RHSs left intact.
    _, prior = fc1.render(worlds, capture, rank_code)
    _, retained = residual_exchange.render(worlds, capture, rank_code)
    fresh = compiler._load_chunk_source(capture, rank_code)
    pm = _one((w for w in worlds if w[-1] == 'pm'), 'unique PM world required')
    compiler.attach_collective_scopes(pm[0], fresh)
    bound_worlds = [(v, c, fresh if label == 'pm' else s, o, label)
                    for v, c, s, o, label in worlds]
    proofs, sources, add_sources, rows, main_reads = [], [], [], [], []
    pending = []
    # Emit the complete peer LN->AA wave before using it at the local joins.
    for previous in prior['reads']:
        world = _one((w for w in bound_worlds if w[-1] == previous['world']), 'unique original world required')
        view, cells, snapshot, order, label = world
        ln = previous['layernorm']
        _, checked_ln = layernorm.render_read(view, cells, snapshot, ln['source_index'], order, label)
        _require(_same_typed(checked_ln, ln), 'fresh selected LN mismatch')
        if label == 'pm':
            ci, _ = fc1._consumer(cells, cells[ln['source_index']], 0, 'AllToAllPrim')
            text, source, main = _main(world, ci, prior['reads'])
            proofs.append(text); sources.append(source); main_reads.append(main['read'])
        else:
            main = _branch(ln, 0, previous['layernorm_expressions'][0], previous['layernorm_consumers'][0], 'layernorm')
        mi, _ = fc1._consumer(cells, cells[main['source_index']], main['port'], 'BW_multiref')
        old_add = previous['prior']['add']
        if label == 'pm':
            ri, _ = fc1._consumer(cells, cells[old_add['source_index']], 0, 'AllToAllPrim')
            read = _one((r for r in retained['reads'] if _same_typed(r['source_index'], ri)),
                        'original retained exchange required')
            keep = _branch(read, 0, read['expression'], read['theorems'][1], 'retained_exchange')
        else:
            _, read = add.render_read(view, cells, snapshot, old_add['source_index'], order, label)
            _require(_same_typed(read, old_add), 'fresh retained add mismatch')
            rhs = '(bw_add2 ' + ' '.join(f'(t {tid})' for tid in read['input_tids']) + ').1'
            keep = _branch(read, 0, rhs, read['theorems'][0], 'retained_add')
        candidates = [main, keep]
        ordered = [_one((b for b in candidates if _same_typed(b['output_ref'], list(ref))),
                        'every original sum input needs one contribution') for ref in cells[mi].inputs]
        _require(len(ordered) == len(candidates), 'unconsumed residual branch')
        pending.append((world, mi, ordered, main, keep))
    for world, index, branches, main, keep in pending:
        text, source, row = _join(world, index, branches)
        row.update(main=main, retained=keep)
        proofs.append(text); add_sources.append(source); rows.append(row)
    return ''.join(proofs), dict(reads=rows, collective_reads=main_reads,
        collective_source=''.join(sources), add_source=''.join(add_sources),
        **{flag: False for flag in _FLAGS})
