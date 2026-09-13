"""Reconstruct original final-LayerNorm dβ from source-bound DP/TP inputs.

Saved-X values are deliberately absent from the contract. Only the already
proved original cotangent values and saved/affine shapes feed the generic dβ
adapters. Exact original reducer order is retained; unsupported orders fail.
"""
from pathlib import Path
from Verdict import runtime_backward_layernorm_context as context
from Verdict import runtime_backward_layernorm_wred as wred
from Verdict import runtime_backward_dx_consumers as consumers
from Verdict.runtime_lineage import _same_typed


def render(worlds,config,prefix,rank_code,initial_relations):
    _,ctx=context.render(worlds,prefix,initial_relations)
    _,reds=wred.render(worlds,[r['source_index'] for r in ctx['pm_reads']],str(Path(config['pm_capture'])/'capture.pkl'),rank_code)
    _,dx=consumers.render(worlds,config,prefix,rank_code,initial_relations)
    return _compose(ctx,reds,dx)


def _membership(names):
    return ['(by', '  intro z hz',
            '  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz',
            '  rcases hz with '+' | '.join('rfl' for _ in names)]+[
            '  · exact '+name+(')' if j==len(names)-1 else '') for j,name in enumerate(names)]


def _compose(ctx,reds,dx):
    sm=ctx['sm_read']; g,x,gamma,beta=sm['input_tids']; db=sm['output_tids'][2]
    groups={}
    for c in dx['reads']: groups.setdefault(c['unit'],[]).append(c)
    D=len(groups)
    if sorted(groups)!=list(range(D)) or not D: raise ValueError('bw-dbeta complete original DP units required')
    betas=[r for r in reds['reads'] if r['role']=='dbeta']
    if not betas: raise ValueError('bw-dbeta original beta reducers required')
    local=[]; perunit=[]; coordinate_by_ref={tuple(c['gradient_ref']):coordinate for c,coordinate in zip(betas[0]['contributions'],betas[0]['coordinates'],strict=True)}
    for u in range(D):
        cs=sorted(groups[u],key=lambda c:c['local_index']); K=len(cs)
        if [c['local_index'] for c in cs]!=list(range(K)): raise ValueError('bw-dbeta complete ordered TP chunks required')
        entries=[]
        for c in cs:
            candidates=[r for r in ctx['pm_reads'] if r['input_tids'][0]==c['output_tid']]
            if len(candidates)!=1: raise ValueError('bw-dbeta original cotangent/LayerNorm read join required')
            row=candidates[0]
            coordinate=coordinate_by_ref.get(tuple(row['output_refs'][2]))
            if coordinate is None or type(coordinate[0]) is not int or coordinate[0]!=u:
                raise ValueError('bw-dbeta original affine/cotangent DP placement mismatch')
            entries.append((c,row)); local.append(row)
        perunit.append(entries)
    ordered=[r['output_tids'][2] for r in local]
    for r in betas:
        if not _same_typed(r['input_tids'],ordered): raise ValueError('bw-dbeta original reducer order must match proved DP/TP decomposition')
    B,S,H=dx['reads'][0]['shape']; T=len(perunit[0]); totalS=S*T
    if (any(len(xs)!=T for xs in perunit) or ctx['sm_saved_shape']!=[B*D,totalS,H]
            or any(not _same_typed(c['shape'],[B,S,H]) for c in dx['reads'])):
        raise ValueError('bw-dbeta exact uniform source shape decomposition required')
    common=['(s p t q : Store)','    (hs : smSeededDenoteWithInputs s = some t)',
            '    (hp : pmSeededDenoteWithInputs p = some q)',
            '    (hv : InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p))',
            '    (hi : pmSeededPrefixInitShapes p)']
    first=local[0]
    p=['theorem backwardLayernormDbetaShape '+'\n'.join(common)+' :',
       f'    (t {db}).shape = [{H}] := by',
       f'  rw [{sm["theorems"][2]} (smInitialWithSeeds s) t hs]',
       f'  exact (bw_layernorm_db_shape _ _ _ _ {H} [{totalS}, {B*D}]',
       '    (by rw [backwardLayernormSMInputShape s p t q hs hp hv]; rfl)).trans',
       f'    (backwardLayernormParameter_{first["input_tids"][3]} s p t q hs hp hv).2.2',
       '#print axioms backwardLayernormDbetaShape',
       'theorem backwardLayernormDbetaReconstruction '+'\n'.join(common)+' :',
       f'    t {db} = tensorSum ['+', '.join(f'q {tid}' for tid in ordered)+'] := by',
       f'  let full : DbetaSourceInput := ⟨t {g}, t {x}, t {gamma}, t {beta}⟩',
       f'  have hg : (t {g}).shape = {[B*D,totalS,H]} := backwardFullDxShape s p t q hs hp hv hi',
       f'  have hgamma := (backwardLayernormParameter_{first["input_tids"][2]} s p t q hs hp hv).2.2',
       f'  have hbeta := (backwardLayernormParameter_{first["input_tids"][3]} s p t q hs hp hv).2.2',
       f'  have hf : full.Shaped {B*D} {totalS} {H} :=',
       '    ⟨hg, backwardLayernormSMInputShape s p t q hs hp hv, hgamma, hbeta⟩']
    output_groups=[]
    for u,entries in enumerate(perunit):
        p += [f'  let unit{u} : DbetaSourceInput := ⟨chunkPrimDimN 0 {D} {u} (t {g}), zeroTensor {[B,totalS,H]}, t {gamma}, t {beta}⟩',
              f'  have hug{u} : (chunkPrimDimN 0 {D} {u} (t {g})).shape = {[B,totalS,H]} :=',
              f'    chunkPrimDimN_shape 0 {D} {u} _ {[B*D,totalS,H]} hg (by decide)',
              f'  have hu{u} : unit{u}.Shaped {B} {totalS} {H} := ⟨hug{u}, rfl, hgamma, hbeta⟩']
        names=[]; shapes=[]; outs=[]
        for c,row in entries:
            tag=str(row['source_index']); name='local'+tag; names.append(name); shapes.append('hl'+tag); outs.append(name+'.output')
            gi,xi,ga,be=row['input_tids']
            p += [f'  let {name} : DbetaSourceInput := ⟨q {gi}, q {xi}, q {ga}, q {be}⟩',
                  f'  have hl{tag} : {name}.Shaped {B} {S} {H} :=',
                  f'    ⟨{c["shape_theorem"]} s p t q hs hp hv hi,',
                  f'      backwardPrefixShape_pm_{tag}_saved_primal p q hi hp,',
                  f'      (backwardLayernormParameter_{ga} s p t q hs hp hv).2.1,',
                  f'      (backwardLayernormParameter_{be} s p t q hs hp hv).2.1⟩']
        ns='['+', '.join(names)+']'; output_groups.append('['+', '.join(outs)+']')
        p += [f'  have htpInput{u} : unit{u}.g = allGatherPrimDimN 1 {T} 0 ({ns}.map DbetaSourceInput.g) := by',
              f'    change chunkPrimDimN 0 {D} {u} (t {g}) = allGatherPrimDimN 1 {T} 0 ['+', '.join(f'q {row["input_tids"][0]}' for _,row in entries)+']',
              '    rw ['+', '.join(c['theorem']+' s p t q hs hp hv hi' for c,_ in entries)+']',
              f'    exact (allGatherPrimDimN_chunks_ofFn 1 {T} (chunkPrimDimN 0 {D} {u} (t {g}))',
              f'      (by decide) (by rw [hug{u}]; decide) (by rw [hug{u}]; decide)).symm',
              f'  have htp{u} := source_bw_layernorm_dbeta_sequence_reduction {T} {B} {S} {H} unit{u} {ns}',
              f'    (by decide) (by decide) (by decide) (by decide) hu{u} rfl']
        p += ['    '+line for line in _membership(shapes)]
        p[-1]+=f' htpInput{u}'
    unitlist='['+', '.join(f'unit{u}' for u in range(D))+']'
    p += [f'  have hdpInput : full.g = allGatherPrimDimN 0 {D} 0 ({unitlist}.map DbetaSourceInput.g) := by',
          f'    exact (allGatherPrimDimN_chunks_ofFn 0 {D} (t {g})',
          '      (by decide) (by rw [hg]; decide) (by rw [hg]; decide)).symm',
          f'  have hdp := source_bw_layernorm_dbeta_batch_reduction {D} {B} {totalS} {H} full {unitlist}',
          '    (by decide) (by decide) (by decide) (by decide) hf rfl']
    p += ['    '+line for line in _membership([f'hu{u}' for u in range(D)])]; p[-1]+=' hdpInput'
    p += [f'  rw [{sm["theorems"][2]} (smInitialWithSeeds s) t hs]',
          '  change full.output = _','  rw [hdp]',
          '  simp only [List.map_cons, List.map_nil]',
          '  rw ['+', '.join(f'htp{u}' for u in range(D))+']',
          '  simp only [List.map_cons, List.map_nil]',
          '  rw ['+', '.join(r['theorems'][2]+' (pmInitialWithSeeds p) q hp' for r in local)+']',
          '  apply source_tensorSum_groups ['+', '.join(output_groups)+f'] [{H}] (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])',
          '  · intro xs hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx',
          '    rcases hx with '+' | '.join('rfl' for _ in range(D))+' <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]',
          '  · intro xs hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx',
          '    rcases hx with '+' | '.join('rfl' for _ in range(D))]
    for entries in perunit:
        p += ['    · intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz',
              '      rcases hz with '+' | '.join('rfl' for _ in entries)]
        for _,row in entries:
            tag=str(row['source_index'])
            p += [f'      · exact (bw_layernorm_db_shape _ _ _ _ {H} [{S}, {B}]',
                  f'          (by change (local{tag}.x).shape.reverse = _; rw [hl{tag}.2.1]; rfl)).trans hl{tag}.2.2.2']
    p += ['#print axioms backwardLayernormDbetaReconstruction']
    for row in betas:
        name=f'backwardLayernormDbetaFinal_{row["output_tid"]}'
        p += ['theorem '+name+' '+'\n'.join(common)+' :',
              f'    q {row["output_tid"]} = t {db} := by',
              f'  rw [{row["theorems"][0]} (pmInitialWithSeeds p) q hp]',
              '  simp only [List.map_cons, List.map_nil]',
              '  exact (backwardLayernormDbetaReconstruction s p t q hs hp hv hi).symm',f'#print axioms {name}',
              'theorem '+name+'_shape '+'\n'.join(common)+' :',
              f'    (q {row["output_tid"]}).shape = [{H}] := by',
              f'  rw [{name} s p t q hs hp hv hi]',
              '  exact backwardLayernormDbetaShape s p t q hs hp hv hi',f'#print axioms {name}_shape']
    return '\n'.join(p)+'\n',dict(sm_output=db,ordered_contributions=ordered,outputs=[r['output_tid'] for r in betas],
        saved_value_premise=False,proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
