"""Original reverse FFN source expressions, not SM-PM gradient equivalence."""
from Verdict import runtime_backward_gelu_reads as gelu
from Verdict import runtime_backward_linear_reads as linear
from Verdict import runtime_backward_add_reads as add
from Verdict.runtime_lineage import _same_typed


def _one(rows):
    rows = list(rows)
    if len(rows) != 1:
        raise ValueError('bw-ffn unique original reverse producer required')
    return rows[0]


def _read(renderer, view, cells, snapshot, index, order, label):
    _, row = renderer.render_read(view, cells, snapshot, index, order, label)
    node = cells[index].node
    for side in ('inputs', 'outputs'):
        expected = [t.tid for t in getattr(view, 'node_' + side)(node)]
        if not _same_typed(expected, row[side[:-1] + '_tids']):
            raise ValueError('bw-ffn original lowered source binding mismatch')
    return row


def render(worlds):
    proof, rows = [], []
    for view, cells, snapshot, order, label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            gi = next(i for i in order['execution_to_source']
                      if cells[i].rank == rank and cells[i].opname.name == 'BW_gelu')
            gr = _read(gelu, view, cells, snapshot, gi, order, label)
            li = _one(i for i, c in enumerate(cells)
                      if any(_same_typed(tuple(ref), tuple(cells[gi].inputs[0])) for ref in c.outputs))
            lr = _read(linear, view, cells, snapshot, li, order, label)
            ai = _one(i for i, c in enumerate(cells)
                      if any(_same_typed(tuple(ref), tuple(cells[li].inputs[0])) for ref in c.outputs))
            ar = _read(add, view, cells, snapshot, ai, order, label)
            gf, lf, af = (cells[r['source_contract']['fw_source_index']] for r in (gr, lr, ar))
            if (not _same_typed(gr['input_refs'][0], lr['output_refs'][0])
                    or not _same_typed(lr['input_refs'][0], ar['output_refs'][1])
                    or not _same_typed(tuple(gf.outputs[0]), tuple(lf.inputs[0]))
                    or not _same_typed(tuple(lf.outputs[0]), tuple(af.inputs[1]))
                    or not ar['execution_index'] < lr['execution_index'] < gr['execution_index']):
                raise ValueError('bw-ffn original reverse/FW mirror edges mismatch')
            add_expr = '(bw_add2 ' + ' '.join(f'(t {tid})' for tid in ar['input_tids']) + ').2'
            linear_expr = f'(bw_linear {add_expr} (t {lr["input_tids"][1]}) (t {lr["input_tids"][2]})).1'
            ln = f'backwardFfnLinearConsumer_{label}_{li}'
            gn = f'backwardFfnGeluConsumer_{label}_{gi}'
            proof += [f'theorem {ln} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
                      f'    t {lr["output_tids"][0]} = {linear_expr} := by',
                      f'  rw [{lr["theorems"][0]} s t h, {ar["theorems"][1]} s t h]',
                      f'#print axioms {ln}',
                      f'theorem {gn} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
                      f'    t {gr["output_tids"][0]} = bw_gelu ({linear_expr}) (t {gr["input_tids"][1]}) := by',
                      f'  rw [{gr["theorems"][0]} s t h, {ln} s t h]',
                      f'#print axioms {gn}']
            rows.append(dict(world=label, add=ar, linear=lr, gelu=gr, theorems=[ln, gn]))
    return '\n'.join(proof) + '\n', dict(reads=rows, proof_admissible=False,
        kernel_value_proved=False, public_complete=False, torch_refinement=False)
