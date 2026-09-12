"""Original dV contributions are summed then scattered, never parameter dW."""
from copy import copy
from Verdict import graph_to_lean as compiler
from Verdict import runtime_backward_matmul_reads as matmul
from Verdict import runtime_backward_collective_reads as collective
from Verdict.runtime_lineage import _same_typed


def render(worlds, capture_path, rank_code_directory):
    view,cells,_,order,label = worlds[1]
    if label != 'pm':
        raise ValueError('matmul-dv-reduction original PM world required')
    source = compiler._load_chunk_source(capture_path,rank_code_directory)
    checked = copy(view)
    compiler.attach_collective_scopes(checked,source)
    proofs,sources,rows=[],[],[]
    for rank in dict.fromkeys(c.rank for c in cells):
        mi = next(i for i,c in enumerate(cells) if c.rank==rank and c.opname.name=='BW_matmul')
        ref = cells[mi].outputs[1]
        candidates=[(i,c) for i,c in enumerate(cells) if c.rank==rank and any(
            _same_typed(tuple(r),tuple(ref)) for r in c.inputs)]
        if len(candidates)!=1 or candidates[0][1].opname.name!='ReduceScatterPrim':
            raise ValueError('matmul-dv-reduction unique original local second-output consumer required')
        i,_=candidates[0]
        text,row=collective.render_read(checked,cells,source,i,order,'pm',matmul.render_read,1)
        dim,=row['params']
        values=['(bw_matmul '+' '.join(f'(t {tid})' for tid in p['input_tids'])+').2' for p in row['predecessors']]
        expression=f'chunkPrimDimN {dim} {len(row["ranks"])} {row["local_index"]} (tensorSum ['+', '.join(values)+'])'
        name=f'backwardMatmulDVReduceScatter_pm_{i}'
        proofs.extend([f'theorem {name} (s t : Store) (h : pmDenoteWithInputs s = some t) :',
            f'    t {row["output_tid"]} = {expression} := by',
            f'  rw [{row["theorems"][0]} s t h]',
            '  simp only [List.map_cons,List.map_nil]',
            '  rw ['+', '.join(p['theorems'][1]+' s t h' for p in row['predecessors'])+']',
            f'#print axioms {name}'])
        sources.append(text);rows.append(dict(row,expression=expression,composition_theorem=name))
    return '\n'.join(proofs)+'\n',dict(source_text=''.join(sources),reads=rows,
        proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
