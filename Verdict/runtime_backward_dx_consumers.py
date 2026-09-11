"""Project reconstructed SM dX through its original PM ReduceScatter consumers."""
from pathlib import Path
from Verdict import runtime_backward_dx_values as dx
from Verdict import runtime_backward_reduce_scatter_reads as scatter
from Verdict import runtime_backward_linear_reads as linear
from Verdict.runtime_lineage import _same_typed


def render(worlds,config,prefix,rank_code,initial_relations):
    _,values=dx.render(worlds,config,prefix,rank_code,initial_relations)
    selected=[r['source_index'] for unit in values['units'] for r in unit['reads']]
    _,reads=scatter.render(worlds,selected,str(Path(config['pm_capture'])/'capture.pkl'),rank_code)
    view,cells,snapshot,order,label=worlds[0]
    index=next(i for i in order['execution_to_source'] if cells[i].opname.name=='BW_linear')
    _,sm=linear.render_read(view,cells,snapshot,index,order,label)
    return _compose(values,reads,sm)


def _compose(values,reads,sm):
    units=values['units']; d=len(units); g,x,w=sm['input_tids']; full_dx=sm['output_tids'][0]
    b,s,o=units[0]['gradients'][0]['shape']; i=units[0]['goal']['sm_shape'][1]
    common=['(s p t q : Store)', '    (hs : smSeededDenoteWithInputs s = some t)',
            '    (hp : pmSeededDenoteWithInputs p = some q)',
            '    (hv : InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p))',
            '    (hi : pmSeededPrefixInitShapes p)']
    proof=['theorem backwardFullDxShape '+'\n'.join(common)+' :',
           f'    (t {full_dx}).shape = {[b*d,s,i]} := by',
           '  have hsm := backwardSMShapesFromInitial s p t q hs hp hv',
           f'  have hw := backwardParameterShape_{w} t q (backwardParameterValuesFinal s p t q hs hp hv)',
           f'  rw [{sm["theorems"][0]} (smInitialWithSeeds s) t hs]',
           '  simp only [bw_linear, hsm.2.2, hsm.1, hw, Tensor.mkShape]',
           '#print axioms backwardFullDxShape']
    rows=[]
    for row in reads['reads']:
        candidates=[u for u in units if _same_typed(u['ranks'],row['ranks']) and _same_typed(u['dx_tids'],row['input_tids'])]
        if len(candidates)!=1:
            raise ValueError('bw-dx-consumer exact ordered source dX unit required')
        unit=candidates[0]; u=unit['unit']; k=len(row['ranks']); r=row['local_index']
        if (not _same_typed(row['params'],[1]) or not _same_typed(row['input_shape'],[b,s,i])
                or type(r) is not int or not 0<=r<k or s%k):
            raise ValueError('bw-dx-consumer exact sequence-scatter layout required')
        name=f'backwardDxConsumer_pm_{row["source_index"]}'
        proof+=['theorem '+name+' '+'\n'.join(common)+' :',
                f'    q {row["output_tid"]} = chunkPrimDimN 1 {k} {r} (chunkPrimDimN 0 {d} {u} (t {full_dx})) := by',
                f'  rw [{row["theorems"][0]} (pmInitialWithSeeds p) q hp]',
                '  simp only [List.map_cons, List.map_nil]',
                f'  rw [← backwardDxUnit_{u} s p t q hs hp hv hi]',f'#print axioms {name}',
                'theorem '+name+'_shape '+'\n'.join(common)+' :',
                f'    (q {row["output_tid"]}).shape = {[b,s//k,i]} := by',
                f'  rw [{name} s p t q hs hp hv hi]',
                f'  have hc : (chunkPrimDimN 0 {d} {u} (t {full_dx})).shape = {[b,s,i]} :=',
                f'    chunkPrimDimN_shape 0 {d} {u} (t {full_dx}) {[b*d,s,i]}',
                '      (backwardFullDxShape s p t q hs hp hv hi) (by decide)',
                f'  rw [chunkPrimDimN_shape 1 {k} {r} _ {[b,s,i]} hc (by decide)]',
                '  rfl',f'#print axioms {name}_shape']
        rows.append(dict(source_index=row['source_index'],output_tid=row['output_tid'],
                         unit=u,local_index=r,ranks=row['ranks'],theorem=name,
                         shape_theorem=name+'_shape',shape=[b,s//k,i]))
    return '\n'.join(proof)+'\n',dict(reads=rows,proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
