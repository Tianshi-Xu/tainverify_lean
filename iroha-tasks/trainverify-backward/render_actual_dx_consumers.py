"""Replay original ReduceScatter values after SM-PM dX reconstruction."""
import json
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_seed_reads import config
from Verdict.runtime_backward_dx_consumers import render
ROOT=Path(__file__).resolve().parents[2]; A=ROOT/'.hermes/backward-kernel'
BASE=Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1')
r=json.loads((BASE/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
w=worlds.__wrapped__(captured.__wrapped__())
for view,_,_,order,label in w:
    assert order['execution_to_source']==r['execution_order'][label]['execution_to_source']
    originals={tuple(x['ref']):x for x in r['fullrefs'][label]}
    assert len(originals)==len(view.tensors())
    for tensor in view.tensors():
        row=originals[tuple(view.source_tensor(tensor))]
        assert row['tid']==tensor.tid and tuple(row['shape'])==tuple(view.tensor_shape(tensor))
text,detail=render(w,config.__wrapped__(),r['scoped_prefix']['pm'],str(BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'),r['initial_relations'])
header='import ActualBWDxValues\nimport ActualBWReduceScatterRead\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\n'
text+='''theorem backwardDxConsumerInputsNonvacuous : ∃ s p t q : Store,
    smSeededDenoteWithInputs s = some t ∧ pmSeededDenoteWithInputs p = some q ∧
    InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p) ∧ pmSeededPrefixInitShapes p :=
  backwardInputsNonvacuous
#print axioms backwardDxConsumerInputsNonvacuous
'''
(A/'ActualBWDxConsumers.lean').write_text(header+text+'end\nend TrainVerify.Denote.RuntimeWorld\n')
(A/'actual-dx-consumers.json').write_text(json.dumps(detail,indent=2))
print('original reconstructed consumers',len(detail['reads']))
