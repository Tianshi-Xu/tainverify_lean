"""Compose original LN dX reads into both reverse residual outputs.

Only SAME-final-Store source expressions are proved here; neither cross-graph
saved-X values nor cross-graph LayerNorm dX equality are asserted.
"""
from Verdict import runtime_backward_layernorm_reads as layernorm
from Verdict import runtime_backward_add_reads as add
from Verdict.runtime_lineage import _same_typed


def render(worlds):
    proof, rows = [], []
    for view, cells, snapshot, order, label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            li = next(i for i in order['execution_to_source']
                      if cells[i].rank == rank and cells[i].opname.name == 'BW_layernorm')
            _, ln = layernorm.render_read(view, cells, snapshot, li, order, label)
            original = cells[li]
            expected_outputs = [t.tid for t in view.node_outputs(original.node)]
            expected_inputs = [t.tid for t in view.node_inputs(original.node)]
            lfi = ln['source_contract']['fw_source_index']
            if (not _same_typed(expected_outputs, ln['output_tids'])
                    or not _same_typed(expected_inputs, ln['input_tids'])
                    or type(lfi) is not int or not 0 <= lfi < len(cells)
                    or cells[lfi].ir is not original.ir.mirror):
                raise ValueError('bw-add-consumer original LN predecessor mismatch')
            matches = [(i, c) for i, c in enumerate(cells)
                       if any(_same_typed(tuple(ref), tuple(original.outputs[0])) for ref in c.inputs)]
            if len(matches) != 1:
                raise ValueError('bw-add-consumer unique original dX consumer required')
            i, cell = matches[0]
            _, row = add.render_read(view, cells, snapshot, i, order, label)
            fw = cells[row['source_contract']['fw_source_index']]
            if (cell.rank != rank or cell.mb != original.mb
                    or not _same_typed(row['input_tids'][0], ln['output_tids'][0])
                    or not _same_typed(tuple(cell.inputs[0]), tuple(original.outputs[0]))
                    or not _same_typed(tuple(fw.outputs[0]), tuple(original.inputs[1]))
                    or not _same_typed([t.tid for t in view.node_outputs(fw.node)], [ln['input_tids'][1]])
                    or order['execution_to_source'].index(li) >= row['execution_index']):
                raise ValueError('bw-add-consumer original reverse mirror edge mismatch')
            expr = '(bw_layernorm ' + ' '.join(f'(t {tid})' for tid in ln['input_tids']) + ').1'
            names = []
            for slot, role in enumerate(('dleft', 'dright')):
                name = f'backwardAddConsumer_{label}_{i}_{role}'; names.append(name)
                out = row['output_tids'][slot]
                proof += [f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
                          f'    t {out} = (bw_add2 {expr} (t {row["input_tids"][1]}) (t {row["input_tids"][2]})).{slot+1} := by',
                          f'  rw [{row["theorems"][slot]} s t h, {ln["theorems"][0]} s t h]',
                          f'#print axioms {name}']
            rows.append(dict(world=label, source_index=i, execution_index=row['execution_index'],
                             layernorm_read=ln, add_read=row, theorems=names))
    return '\n'.join(proof) + '\n', dict(reads=rows, proof_admissible=False,
        kernel_value_proved=False, public_complete=False, torch_refinement=False)
