"""Compose original SM-PM dX values from shared source/shape/parameter facts.

Initial parameter inventories select projections of the imported canonical
contract, not proof authority. Every projection still requires kernel checking.
DP coordinates are rejoined to original reducer parameter placements; no rank
arithmetic, captured output equality, saved-X value premise or scaling default.
"""
from pathlib import Path
from Verdict import runtime_backward_sm_shapes as sm_shapes
from Verdict import runtime_backward_constant_cotangents as constants
from Verdict import runtime_backward_wred_reads as wred
from Verdict import runtime_backward_linear_reads as linear
from Verdict.runtime_lineage import _same_typed


def _one(rows, message):
    rows=list(rows)
    if len(rows)!=1: raise ValueError('bw-dx '+message)
    return rows[0]


def render(worlds, config, prefix, rank_code, initial_relations):
    _, sm = sm_shapes.render(worlds)
    _, cs = constants.render(worlds, config, prefix, rank_code)
    view,cells,snapshot,order,_=worlds[1]
    pm={}
    for c in cs['reads']:
        i=_one((i for i,cell in enumerate(cells) if cell.opname.name=='BW_linear'
                and list(cell.inputs[0])==c['ref']), 'unique original local linear required')
        _, pm[i]=linear.render_read(view,cells,snapshot,i,order,'pm')
    _, reducers=wred.render(worlds,list(pm),str(Path(config['pm_capture'])/'capture.pkl'),rank_code)
    placements={}
    for reducer in reducers['reads']:
        for c in reducer['contributions']:
            i=c['source_index']
            if i in placements and not _same_typed(placements[i],c):
                raise ValueError('bw-dx inconsistent original parameter placement')
            placements[i]=c
    return _compose(sm, cs, pm, placements, initial_relations)


def _compose(sm, cs, pm, placements, initial_relations):
    smread=sm['linear_binding']; g,x,w=smread['input_tids']; dx=smread['output_tids'][0]
    contract=_one((r for r in initial_relations['relations']
                   if _same_typed(r['sm_binding']['ref'],smread['input_refs'][2])),
                  'canonical initial parameter source missing/ambiguous')
    allgoals=[u['initial_goal'] for r in initial_relations['relations'] for u in r['units']]
    groups={}
    for c in cs['reads']:
        groups.setdefault(tuple(c['ranks']),[]).append(c)
    units=[]
    for ranks, gradients in groups.items():
        gradients=[_one((c for c in gradients if c['ref'][1]==rank),'ordered cotangent coverage') for rank in ranks]
        reads=[_one((v for v in pm.values() if _same_typed(v['input_refs'][0],c['ref'])), 'gradient-to-linear join') for c in gradients]
        original=[placements[r['source_index']] for r in reads]
        coords=[r['parameter_placement']['scale_unit'] for r in original]
        if any(type(u) is not int or u<0 for u in coords) or len(set(coords))!=1:
            raise ValueError('bw-dx TP peers must share strict original DP ownership')
        unit=coords[0]
        declared=_one((u for u in contract['units'] if type(u['unit']) is int and u['unit']==unit),'parameter DP unit required')
        goal=declared['initial_goal']
        bindings=declared['bindings']
        if len(bindings)!=len(reads): raise ValueError('bw-dx complete ordered parameter peers required')
        for binding,read,raw in zip(bindings,reads,original,strict=True):
            p=raw['parameter_placement']
            if (not _same_typed(binding['ref'],read['input_refs'][2])
                    or not _same_typed(binding['tid'],read['input_tids'][2])
                    or not _same_typed(binding['rank'],read['input_refs'][2][1])
                    or not _same_typed([binding['parent_tid'],binding['logical_name'],binding['full_shape'],binding['bounds'],binding['value_part']],
                                       [p['parent_tid'],p['name'],p['full_shape'],p['indmap'],p['valmap']])):
                raise ValueError('bw-dx original parameter identity/ordered placement mismatch')
        if (goal['kind']!='sharded' or not _same_typed(goal['dim'],0)
                or goal['sm_tid']!=w or goal['pm_tids']!=[r['input_tids'][2] for r in reads]):
            raise ValueError('bw-dx source output-row weight partition required')
        units.append(dict(unit=unit,ranks=list(ranks),reads=reads,gradients=gradients,
                          goal=goal,goal_index=allgoals.index(goal),dx_tids=[r['output_tids'][0] for r in reads]))
    units.sort(key=lambda r:r['unit']); d=len(units)
    if [u['unit'] for u in units]!=list(range(d)) or not d:
        raise ValueError('bw-dx complete original DP units required')
    shape={r['tid']:r['shape'] for r in sm['conclusions']}
    initial='InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p)'
    common=['(s p t q : Store)',
            '    (hs : smSeededDenoteWithInputs s = some t)',
            '    (hp : pmSeededDenoteWithInputs p = some q)',f'    (hv : {initial})']
    proof=['theorem backwardSMShapesFromInitial '+'\n'.join(common)+' :',
           '    '+' ∧ '.join(f'(t {r["tid"]}).shape = {r["shape"]}' for r in sm['conclusions'])+' := by',
           '  have h := backwardParameterValuesFinal s p t q hs hp hv',
           '  apply backwardSMShapes (smInitialWithSeeds s) t ?_ hs',
           '  exact ⟨'+', '.join(f'backwardParameterShape_{r["tid"]} t q h' for r in sm['parameter_shapes'])+'⟩',
           '#print axioms backwardSMShapesFromInitial']
    primal=sm['conclusions'][1]['tid']
    sumrow=_one((r for r in sm['reads'] if r['op']=='BW_sum'),'SM sum producer')
    proof+=['theorem backwardSMConstant '+'\n'.join(common)+' :',
            f'    t {g} = sourceConstantCotangent {shape[g]} (1 : Scalar) := by',
            f'  rw [backwardSeed_sm_{sumrow["source_index"]}_broadcast s t hs,',
            '    (backwardSMShapesFromInitial s p t q hs hp hv).2.1]',
            '#print axioms backwardSMConstant']
    for row in units:
        u=row['unit']; rs=row['reads']; grad=row['gradients']; goal=row['goal']; k=len(rs)
        b,s,o=grad[0]['shape']; i=goal['sm_shape'][1]
        if (any(c['shape']!=[b,s,o] for c in grad) or shape[g]!=[b*d,s,o*k]
                or shape[x]!=[b*d,s,i] or goal['sm_shape']!=[o*k,i] or goal['pm_shape']!=[o,i]
                or any(type(z) is not int or z<=0 for z in (b,s,o,i,k))):
            raise ValueError('bw-dx source rank3 shape/partition mismatch')
        def ts(pos): return '['+', '.join(f'q {r["input_tids"][pos]}' for r in rs)+']'
        gs,xs,ws=(ts(j) for j in range(3))
        name=f'backwardCotangentUnit_{u}'
        proof+=['theorem '+name+' '+'\n'.join(common),
                '    (hi : pmSeededPrefixInitShapes p) :',
                f'    chunkPrimDimN 0 {d} {u} (t {g}) = allGatherPrimDimN 2 {k} 0 {gs} := by',
                '  rw [backwardSMConstant s p t q hs hp hv, '+', '.join(c['theorem']+' p q hi hp' for c in grad)+']',
                f'  exact (source_constant_chunk0_rank3 {d} {b} {s} {o*k} {u} 1',
                '    (by decide) (by decide) (by decide) (by decide) (by decide)).trans',
                f'    (source_constant_gather2_rank3 {k} {b} {s} {o} 1',
                '      (by decide) (by decide) (by decide) (by decide)).symm',f'#print axioms {name}']
        idx=row['goal_index']; projection='hrels'+'.2'*idx+('.1' if idx<len(allgoals)-1 else '')
        name=f'backwardDxUnit_{u}'
        proof+=['theorem '+name+' '+'\n'.join(common),
                '    (hi : pmSeededPrefixInitShapes p) :',
                f'    chunkPrimDimN 0 {d} {u} (t {dx}) = tensorSum ['+', '.join(f'q {r["output_tids"][0]}' for r in rs)+'] := by',
                '  have hsm := backwardSMShapesFromInitial s p t q hs hp hv',
                '  have hrels := initialParameterRelations_of_values t q (backwardParameterValuesFinal s p t q hs hp hv)',
                f"  have hw : RelationCompiler.ShardedRel (t {w}) {ws} 0 {goal['sm_shape']} {goal['pm_shape']} := {projection}",
                f'  have hd := source_bw_linear_dx_batch_tp_unit {d} {k} {b} {s} {o} {i} {u}',
                f'    (t {g}) (t {x}) (t {w}) {gs} {xs} {ws}',
                '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)',
                '    hsm.2.2 hsm.1 hw.full_shape rfl rfl rfl']
        for role in ('cotangent','saved_primal'):
            proof+=['    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv',
                    '        rcases hv with '+' | '.join('rfl' for _ in rs)]
            proof+=['        · exact backwardPrefixShape_pm_'+str(r['source_index'])+'_'+role+' p q hi hp' for r in rs]
            proof[-1]+=')'
        proof+=['    hw.shard_shapes (backwardCotangentUnit_'+str(u)+' s p t q hs hp hv hi) hw.full_value',
                '  rw ['+smread['theorems'][0]+' (smInitialWithSeeds s) t hs, '+', '.join(r['theorems'][0]+' (pmInitialWithSeeds p) q hp' for r in rs)+']',
                '  exact hd',f'#print axioms {name}']
    return '\n'.join(proof)+'\n',dict(units=units,proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False)
