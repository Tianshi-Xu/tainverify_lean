"""Replay backward shape projections from the already accepted prefix DAG."""
import json
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_wred_reads import selected
from scripts.tests.test_runtime_backward_seed_reads import config
from Verdict.runtime_backward_prefix_shapes import render
ROOT=Path(__file__).resolve().parents[2];A=ROOT/'.hermes/backward-kernel'
OLD=Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/dp-prefix-cost-closure/output-projection/actual-output-projection1')
receipt=json.loads((OLD/'world-receipt.json').read_text())
w=worlds.__wrapped__(captured.__wrapped__())
for view,_,_,order,label in w:
    assert order['execution_to_source']==receipt['execution_order'][label]['execution_to_source']
    original={tuple(r['ref']):r for r in receipt['fullrefs'][label]}
    assert len(original)==len(view.tensors())
    for t in view.tensors():
        r=original[tuple(view.source_tensor(t))]
        assert r['tid']==t.tid and tuple(r['shape'])==tuple(view.tensor_shape(t))
text,detail=render(w,selected(w),receipt['scoped_prefix']['pm'],seed_config=config.__wrapped__())
header='import TrainVerifyRuntimeWorldData\nimport TrainVerifyRuntimePrefix0124\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n'
premises=receipt['scoped_prefix']['pm']['initial_premises']
table=', '.join(f"({p['tid']}, {p['shape']})" for p in premises)
witness='\n'.join([
    f'def backwardPrefixWitnessShapes : List (Tid × List Nat) := [{table}]',
    'def backwardPrefixWitnessInit (tid : Tid) : Tensor :=',
    '  zeroTensor (((backwardPrefixWitnessShapes.find? (fun row => row.1 == tid)).map Prod.snd).getD [])',
    'theorem backwardPrefixWitnessInitialShapes : pmSeededPrefixInitShapes backwardPrefixWitnessInit := by\n  unfold pmSeededPrefixInitShapes\n  exact ⟨'+', '.join('rfl' for _ in premises)+'⟩',
    '#print axioms backwardPrefixWitnessInitialShapes',
    'theorem backwardPrefixCallerNonvacuous : ∃ s t : Store, pmSeededPrefixInitShapes s ∧ pmSeededDenoteWithInputs s = some t :=',
    '  ⟨backwardPrefixWitnessInit, _, backwardPrefixWitnessInitialShapes,',
    '    backwardPrefixRun_pm backwardPrefixWitnessInit backwardPrefixWitnessInitialShapes⟩',
    '#print axioms backwardPrefixCallerNonvacuous',''])
(A/'ActualBWPrefixShapes.lean').write_text(header+text+witness+'end\nend TrainVerify.Denote.RuntimeWorld\n')
(A/'actual-prefix-shapes.json').write_text(json.dumps(detail,indent=2))
print('actual queries',len(detail['reads']),'frame edges',sum(len(row['frames']) for row in detail['reads']))
