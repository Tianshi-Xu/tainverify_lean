"""Original view -> AA -> contiguous -> AA -> transpose source-value chain.

Both exchanges use freshly authenticated effective backward contexts, not raw
forward dimensions. Equations share the original successful run and producer
RHSs. No new output equality assumptions, downstream traversal, or SM/PM gradient
claim. Private helpers accept renderer-owned RHSs, never public DTO authority.
"""
from Verdict import graph_to_lean as compiler
from Verdict import runtime_backward_attention_projection_consumers as projection
from Verdict import runtime_backward_view_reads as view_reads
from Verdict import runtime_backward_contiguous_reads as contiguous_reads
from Verdict import runtime_backward_transpose_reads as transpose_reads
from Verdict import runtime_backward_collective_reads as collective
from Verdict.runtime_backward_fc1_consumers import _consumer, _equation
from Verdict.runtime_backward_residual_join_consumers import _branch
from Verdict.runtime_lineage import _same_typed

_FLAGS = ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement')


def _require(ok, reason):
    if not ok:
        raise ValueError('bw-attention-layout ' + reason)


def _one(rows, reason):
    rows = list(rows)
    _require(len(rows) == 1, reason)
    return rows[0]


def _endpoint(world, branch, read, kind):
    """Bind a selected port to the actual source and lowered fullref/version."""
    view, cells, _, order, label = world
    j, port = branch['source_index'], branch['port']
    _require(type(j) is int and 0 <= j < len(cells)
             and type(port) is int and port == 0, 'typed original zero port required')
    node = cells[j].node
    _require(_same_typed(branch['read'], read)
             and _same_typed(branch['source_index'], read['source_index'])
             and read['world'] == label and branch['kind'] == kind
             and _same_typed(read['execution_index'], order['source_to_execution'][j])
             and _same_typed(branch['output_ref'], list(cells[j].outputs[0]))
             and _same_typed(branch['output_ref'], list(view.source_tensor(view.node_outputs(node)[0])))
             and _same_typed(branch['output_tid'], view.node_outputs(node)[0].tid)
             and _same_typed(branch, dict(_branch(read, 0, branch['expression'], branch['theorem'], kind),
                                          **({'contributions': branch['contributions']} if 'contributions' in branch else {}))),
             'fresh original branch endpoint/order mismatch')


def _exchange(world, index, producers, stage):
    """One AA with every ordered peer in the selected, already-rendered wave."""
    _require(stage in ('view', 'contiguous'), 'unsupported exchange stage')
    view, cells, snapshot, order, label = world
    reader = view_reads if stage == 'view' else contiguous_reads
    source, read = collective.render_read(view, cells, snapshot, index, order, label, reader.render_read, 0)
    node = cells[index].node
    scope = view.collective_scopes[node]
    _require(label == 'pm' and read['opname'] == 'AllToAllPrim'
             and _same_typed(read['source_index'], index)
             and _same_typed(read['output_port'], 0)
             and _same_typed(read['params'], list(scope.params)) and len(read['params']) == 2
             and _same_typed(read['ranks'], list(scope.ranks))
             and _same_typed(read['local_index'], scope.local_index)
             and _same_typed(read['input_refs'], [list(view.source_tensor(t)) for t in view.node_inputs(node)])
             and _same_typed(read['input_tids'], [t.tid for t in view.node_inputs(node)])
             and _same_typed(read['output_ref'], list(cells[index].outputs[0]))
             and _same_typed(read['output_tid'], view.node_outputs(node)[0].tid),
             'original effective collective binding mismatch')
    contributions = []
    for rank, peer in zip(read['ranks'], read['predecessors'], strict=True):
        branch = _one((b for b in producers if b['read']['world'] == label
                       and _same_typed(b['source_index'], peer['source_index'])),
                      'complete selected-stage peer required')
        _endpoint(world, branch, peer, stage)
        j = branch['source_index']
        _require(cells[j].rank == rank and cells[j].mb == cells[index].mb
                 and peer['execution_index'] < read['execution_index'], 'original peer rank/order/microbatch mismatch')
        ci, _ = _consumer(cells, cells[j], 0, 'AllToAllPrim')
        _require(_same_typed(view.collective_scopes[cells[ci].node].ranks, scope.ranks)
                 and _same_typed(view.collective_scopes[cells[ci].node].input_tids, scope.input_tids),
                 'original peer collective consumer mismatch')
        contributions.append(branch)
    _require(_same_typed([b['output_ref'] for b in contributions], read['input_refs'])
             and _same_typed([b['output_tid'] for b in contributions], read['input_tids']),
             'complete ordered peer endpoints required')
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


def _unary(world, index, gradient, stage):
    """A narrow unary boundary; PM must read the actual intervening AA."""
    _require(stage in ('contiguous', 'transpose'), 'unsupported unary stage')
    view, cells, snapshot, order, label = world
    reader = contiguous_reads if stage == 'contiguous' else transpose_reads
    predecessor_reader = view_reads if stage == 'contiguous' else contiguous_reads
    predecessor_kind = 'view' if stage == 'contiguous' else 'contiguous'
    source, read = reader.render_read(view, cells, snapshot, index, order, label)
    j = gradient['source_index']
    _require(type(j) is int and 0 <= j < len(cells), 'typed gradient source required')
    if label == 'pm':
        _, checked = collective.render_read(view, cells, snapshot, j, order, label, predecessor_reader.render_read, 0)
        _require(checked['opname'] == 'AllToAllPrim', 'original intervening AA required')
        kind = 'collective'
    else:
        _, checked = predecessor_reader.render_read(view, cells, snapshot, j, order, label)
        kind = predecessor_kind
    _endpoint(world, gradient, checked, kind)
    ci, _ = _consumer(cells, cells[j], 0, 'BW_' + stage)
    _require(_same_typed(ci, index)
             and _same_typed(gradient['output_ref'], read['input_refs'][0])
             and _same_typed(gradient['output_tid'], read['input_tids'][0])
             and cells[j].rank == cells[index].rank and cells[j].mb == cells[index].mb
             and checked['execution_index'] < read['execution_index'],
             'original unary cotangent endpoint/order mismatch')
    expression = gradient['expression']
    if stage == 'transpose':
        a, b = read['params']
        expression = f'transposeAxes {a} {b} ({expression})'
    name = f'backwardAttentionLayout_{label}_{index}_{stage}'
    proof = _equation(name, label, read['output_tids'][0], expression, [read['theorems'][0], gradient['theorem']])
    return '\n'.join(proof) + '\n', source, _branch(read, 0, expression, name, stage)


def render(worlds, capture, rank_code):
    # The expensive upstream render occurs once; its dW and Add.left metadata
    # remain intact. View expressions come from that renderer, never Lean parsing.
    _, prior = projection.render(worlds, capture, rank_code)
    fresh = compiler._load_chunk_source(capture, rank_code)
    pm = _one((w for w in worlds if w[-1] == 'pm'), 'unique PM world required')
    compiler.attach_collective_scopes(pm[0], fresh)
    bound = [(v, c, fresh if label == 'pm' else s, o, label) for v, c, s, o, label in worlds]
    view_text, views = view_reads.render_after_linear(bound, prior['reads'])
    rows, local_worlds, branches = [], [], []
    for p in views['reads']:
        world = _one((w for w in bound if w[-1] == p['world']), 'unique original world required')
        rows.append(dict(world=p['world'], prior=p, view_read=p['view_read'],
                         view_expression=p['expression'], view_theorems=p['theorems']))
        local_worlds.append(world)
        branches.append(_branch(p['view_read'], 0, p['expression'], p['theorems'][0], 'view'))
    proofs, collective_sources, contiguous_sources, transpose_sources, collective_rows = [], [], [], [], []
    # All peer AA outputs, then all contiguous outputs, then ALL second AA
    # outputs, finally all transposes. Never descend past the requested boundary.
    for predecessor_stage, stage, key, sources in (
            ('view', 'contiguous', 'before', contiguous_sources),
            ('contiguous', 'transpose', 'after', transpose_sources)):
        gradients = []
        for world, row, branch in zip(local_worlds, rows, branches, strict=True):
            _, cells, _, _, label = world
            if label == 'pm':
                ci, _ = _consumer(cells, cells[branch['source_index']], 0, 'AllToAllPrim')
                text, source, gradient = _exchange(world, ci, branches, predecessor_stage)
                proofs.append(text); collective_sources.append(source); collective_rows.append(gradient['read'])
            else:
                gradient = branch
            row[key] = gradient
            gradients.append(gradient)
        next_branches = []
        for world, row, gradient in zip(local_worlds, rows, gradients, strict=True):
            cells = world[1]
            ci, _ = _consumer(cells, cells[gradient['source_index']], 0, 'BW_' + stage)
            text, source, branch = _unary(world, ci, gradient, stage)
            proofs.append(text); sources.append(source); next_branches.append(branch)
            row.update({stage + '_read': branch['read'], stage + '_expression': branch['expression'],
                        stage + '_theorems': [branch['theorem']]})
        branches = next_branches
    return ''.join(proofs), dict(reads=rows, prior=prior, view_prior=views, view_compositions=view_text,
        collective_reads=collective_rows, collective_source=''.join(collective_sources),
        contiguous_source=''.join(contiguous_sources), transpose_source=''.join(transpose_sources),
        **{flag: False for flag in _FLAGS})
