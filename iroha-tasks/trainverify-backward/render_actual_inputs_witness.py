"""Nonzero parameter-slice witness for the complete original backward caller."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OLD=Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/dp-prefix-cost-closure/output-projection/actual-output-projection1')
receipt=json.loads((OLD/'world-receipt.json').read_text())
goals=[u['initial_goal'] for row in receipt['initial_relations']['relations'] for u in row['units']]
sm={g['sm_tid']:g['sm_shape'] for g in goals}
sm_rows=', '.join(f'({tid}, {shape})' for tid,shape in sm.items())
pm={}
for g in goals:
    for rank,tid in enumerate(g['pm_tids']):
        value=(f"chunkPrimDimN {g['dim']} {len(g['pm_tids'])} {rank} (backwardSMWitness {g['sm_tid']})" if g['kind']=='sharded' else f"backwardSMWitness {g['sm_tid']}")
        assert tid not in pm or pm[tid]==value
        pm[tid]=value
text=['import RuntimeWorld','import ActualBWPrefixShapes',
      'namespace TrainVerify.Denote.RuntimeWorld','noncomputable section',
      'set_option maxRecDepth 4096',
      f'def backwardSMWitnessShapes : List (Tid × Shape) := [{sm_rows}]',
      'def backwardSMWitness (tid : Tid) : Tensor :=',
      '  Tensor.mkShape (((backwardSMWitnessShapes.find? (fun row => row.1 == tid)).map Prod.snd).getD []) (fun _ => 1)',
      'def backwardPMWitnessValues : List (Tid × Tensor) := [',
      ',\n'.join(f'({tid}, {value})' for tid,value in pm.items())+']',
      'def backwardPMWitness (tid : Tid) : Tensor :=',
      '  (((backwardPMWitnessValues.find? (fun row => row.1 == tid)).map Prod.snd).getD (zeroTensor []))',
      'theorem backwardWitnessParameters : InitialParameterValues',
      '    (smInitialWithSeeds backwardSMWitness) (pmInitialWithSeeds backwardPMWitness) := by',
      '  unfold InitialParameterValues',
      '  refine ⟨'+', '.join('?_ ' for _ in goals)+'⟩']
for g in goals:
    if g['kind']=='sharded': text+=['  · exact ⟨rfl, rfl⟩']
    else:
        branches=' | '.join('rfl' for _ in g['pm_tids'])
        text += ['  · refine ⟨rfl, ?_⟩','    intro tid h',
                 '    simp only [List.mem_cons, List.not_mem_nil, or_false] at h',
                 f'    rcases h with {branches} <;> rfl']
text += ['#print axioms backwardWitnessParameters',
         'theorem backwardWitnessPrefixShapes : pmSeededPrefixInitShapes backwardPMWitness := by',
         '  unfold pmSeededPrefixInitShapes',
         '  exact ⟨'+', '.join('rfl' for _ in receipt['scoped_prefix']['pm']['initial_premises'])+'⟩',
         '#print axioms backwardWitnessPrefixShapes',
         'theorem backwardInputsNonvacuous : ∃ s p t q : Store,',
         '    smSeededDenoteWithInputs s = some t ∧ pmSeededDenoteWithInputs p = some q ∧',
         '    InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p) ∧',
         '    pmSeededPrefixInitShapes p :=',
         '  ⟨backwardSMWitness, backwardPMWitness, _, _, smSeededWholeSuccess backwardSMWitness,',
         '    backwardPrefixRun_pm backwardPMWitness backwardWitnessPrefixShapes,',
         '    backwardWitnessParameters, backwardWitnessPrefixShapes⟩',
         '#print axioms backwardInputsNonvacuous','end','end TrainVerify.Denote.RuntimeWorld','']
path=ROOT/'.hermes/backward-kernel/ActualBWInputsWitness.lean'
path.write_text('\n'.join(text)); print(path)
