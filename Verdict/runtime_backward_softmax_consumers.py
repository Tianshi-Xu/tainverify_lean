"""Original first matmul output -> BW_softmax, in one caller-owned final Store."""
from Verdict.runtime_lineage import _same_typed
from Verdict import runtime_backward_matmul_reads as matmul


def render(worlds):
    from Verdict import runtime_backward_softmax_reads as softmax
    proofs, sources, rows = [], [], []
    for view, cells, snapshot, order, label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            mi = next(i for i,c in enumerate(cells) if c.rank == rank and c.opname.name == 'BW_matmul')
            m = cells[mi]
            consumers = [(i,c) for i,c in enumerate(cells) if any(
                _same_typed(tuple(r),tuple(m.outputs[0])) for r in c.inputs)]
            if len(consumers) != 1 or consumers[0][1].opname.name != 'BW_softmax':
                raise ValueError('bw-softmax unique original matmul first-output consumer required')
            si, s = consumers[0]
            _, mr = matmul.render_read(view,cells,snapshot,mi,order,label)
            source, sr = softmax.render_read(view,cells,snapshot,si,order,label)
            if (not _same_typed(sr['input_refs'][0],mr['output_refs'][0])
                    or sr['input_tids'][0] != mr['output_tids'][0]):
                raise ValueError('bw-softmax original cotangent join mismatch')
            # The saved matmul left primal is this softmax's forward OUTPUT;
            # the softmax backward's saved operand remains forward INPUT logits.
            fw = cells[sr['source_contract']['fw_source_index']]
            if not _same_typed(tuple(m.inputs[1]),tuple(fw.outputs[0])):
                raise ValueError('bw-softmax original forward probability producer mismatch')
            expression = 'bw_softmax ((bw_matmul ' + ' '.join(f'(t {tid})' for tid in mr['input_tids']) + f').1) (t {sr["input_tids"][1]})'
            name = f'backwardMatmulSoftmax_{label}_{si}'
            proofs.extend([f'theorem {name} (s t : Store) (h : {label}DenoteWithInputs s = some t) :',
                f'    t {sr["output_tid"]} = {expression} := by',
                f'  rw [{sr["theorems"][0]} s t h, {mr["theorems"][0]} s t h]',
                f'#print axioms {name}'])
            sources.append(source)
            rows.append(dict(world=label,matmul=mr,softmax=sr,expression=expression,theorem=name))
    return '\n'.join(proofs)+'\n',dict(source_text=''.join(sources),reads=rows,
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
