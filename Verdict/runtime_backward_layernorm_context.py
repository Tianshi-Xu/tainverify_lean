"""LayerNorm shape/affine-value projections on the existing original-run DAG.

No saved-X value relation is introduced. The initial-parameter inventory only
selects conjuncts of the imported, kernel-checked canonical input contract.
"""
from Verdict import runtime_backward_layernorm_reads as reads,runtime_backward_prefix_shapes as shapes
from Verdict.runtime_lineage import _same_typed


def render(worlds,prefix,initial_relations):
    bound=[]
    for view,cells,snapshot,order,label in worlds:
        for rank in dict.fromkeys(c.rank for c in cells):
            i=next(i for i in order['execution_to_source'] if cells[i].rank==rank and cells[i].opname.name=='BW_layernorm')
            _,row=reads.render_read(view,cells,snapshot,i,order,label); bound.append(row)
    sm,=[r for r in bound if r['world']=='sm']; pm=[r for r in bound if r['world']=='pm']
    text,shape_detail=shapes.render(worlds,[],prefix,layernorm_indices=[r['source_index'] for r in pm],include_run=False)
    common=['(s p t q : Store)','    (hs : smSeededDenoteWithInputs s = some t)',
            '    (hp : pmSeededDenoteWithInputs p = some q)',
            '    (hv : InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p))']
    fi=sm['source_contract']['fw_source_index']; smv=worlds[0][0]; node=smv.nodes()[fi]
    output,=smv.node_outputs(node); saved=sm['input_tids'][1]; shape=list(smv.tensor_shape(output))
    first_linear=next(c for c in worlds[0][1] if c.opname.name=='BW_linear')
    if not _same_typed(tuple(smv.source_tensor(output)),tuple(first_linear.inputs[1])):
        raise ValueError('bw-layernorm-context saved shape dependency is not original linear input')
    proof=['theorem backwardLayernormSMInputShape '+'\n'.join(common)+' :',
           f'    (t {saved}).shape = {shape} := by',
           '  have hshape := (backwardSMShapesFromInitial s p t q hs hp hv).1',
           f'  rw [backwardSMRead_{fi}_{output.tid} (smInitialWithSeeds s) t hs] at hshape',
           '  rw [SourceScopedPrefix.layernorm_shape] at hshape','  exact hshape',
           '#print axioms backwardLayernormSMInputShape']
    goals=[u['initial_goal'] for r in initial_relations['relations'] for u in r['units']]
    parameters=[]
    for row in pm:
        for pos,role in [(2,'gamma'),(3,'beta')]:
            stid=sm['input_tids'][pos]; tid=row['input_tids'][pos]
            candidates=[(r,u) for r in initial_relations['relations'] for u in r['units']
                        if _same_typed(r['sm_binding']['ref'],sm['input_refs'][pos])
                        and any(_same_typed(b['ref'],row['input_refs'][pos]) and _same_typed(b['tid'],tid) for b in u['bindings'])]
            if len(candidates)!=1: raise ValueError('bw-layernorm-context original affine parameter binding required')
            _,unit=candidates[0]; goal=unit['initial_goal']
            if goal['kind']!='replicated' or goal['sm_tid']!=stid or tid not in goal['pm_tids']:
                raise ValueError('bw-layernorm-context original replicated affine contract required')
            index=goals.index(goal); projection='h'+'.2'*index+('.1' if index<len(goals)-1 else '')
            sh=goal['sm_shape']; name=f'backwardLayernormParameter_{tid}'
            proof+=['theorem '+name+' '+'\n'.join(common)+' :',
                    f'    q {tid} = t {stid} ∧ (q {tid}).shape = {sh} ∧ (t {stid}).shape = {sh} := by',
                    '  have h := backwardParameterValuesFinal s p t q hs hp hv',
                    f'  have hspec : (t {stid}).shape = {sh} ∧ ∀ j ∈ ({goal["pm_tids"]} : List Tid), q j = t {stid} := {projection}',
                    f'  have heq := hspec.2 {tid} (by decide)',
                    '  exact ⟨heq, (congrArg Tensor.shape heq).trans hspec.1, hspec.1⟩',f'#print axioms {name}']
            parameters.append(dict(role=role,sm_tid=stid,pm_tid=tid,theorem=name,shape=sh))
    return text+'\n'.join(proof)+'\n',dict(sm_saved_tid=saved,sm_saved_shape=shape,sm_read=sm,pm_reads=pm,
        pm_saved_shapes=shape_detail['reads'],parameters=parameters,proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
