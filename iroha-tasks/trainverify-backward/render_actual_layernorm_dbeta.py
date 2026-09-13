"""Actual source-bound LayerNorm dβ global/reducer equality candidate."""
import json,os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_seed_reads import config
from Verdict.runtime_backward_layernorm_dbeta_values import render
ROOT=Path(__file__).resolve().parents[2]; OUT=ROOT/'.hermes/backward-kernel'
BASE=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])
r=json.loads((BASE/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
w=worlds.__wrapped__(captured.__wrapped__())
for view,_,_,order,label in w:
    assert order['execution_to_source']==r['execution_order'][label]['execution_to_source']
    refs={tuple(row['ref']):row for row in r['fullrefs'][label]}
    assert len(refs)==len(view.tensors())
    for tensor in view.tensors():
        row=refs[tuple(view.source_tensor(tensor))]
        assert row['tid']==tensor.tid and tuple(row['shape'])==tuple(view.tensor_shape(tensor))
text,detail=render(w,config.__wrapped__(),r['scoped_prefix']['pm'],str(BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'),r['initial_relations'])
imports=['ActualBWLayernormRead','ActualBWLayernormContext','ActualBWLayernormWRED','ActualBWDxConsumers','denote.SourceBWLayernormDbetaUnit','denote.SourceTensorSumGroups']
header=''.join(f'import {i}\n' for i in imports)+'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
text+='''theorem backwardLayernormDbetaInputsNonvacuous : ∃ s p t q : Store,
    smSeededDenoteWithInputs s = some t ∧ pmSeededDenoteWithInputs p = some q ∧
    InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p) ∧ pmSeededPrefixInitShapes p :=
  backwardInputsNonvacuous
#print axioms backwardLayernormDbetaInputsNonvacuous
'''
(OUT/'ActualBWLayernormDbeta.lean').write_text(header+text+'end\nend TrainVerify.Denote.RuntimeWorld\n')
(OUT/'ActualBWLayernormDbeta.json').write_text(json.dumps(detail,indent=2))
print('declarations',text.count('#print axioms'),'original final outputs',detail['outputs'])
