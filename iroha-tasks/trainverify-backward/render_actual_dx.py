"""Actual source-bound SM-PM dX composition using the accepted shared DAG."""
import json
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_seed_reads import config
from Verdict.runtime_backward_dx_values import render
from reuse_forward_entry import main as reuse
ROOT=Path(__file__).resolve().parents[2]
A=ROOT/'.hermes/backward-kernel'
BASE=Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1')
OLD=BASE/'dp-prefix-cost-closure/output-projection/actual-output-projection1'
reuse()
r=json.loads((OLD/'world-receipt.json').read_text())
w=worlds.__wrapped__(captured.__wrapped__())
for view,_,_,order,label in w:
    assert order['execution_to_source']==r['execution_order'][label]['execution_to_source']
    original={tuple(row['ref']):row for row in r['fullrefs'][label]}
    assert len(original)==len(view.tensors())
    for tensor in view.tensors():
        row=original[tuple(view.source_tensor(tensor))]
        assert row['tid']==tensor.tid and tuple(row['shape'])==tuple(view.tensor_shape(tensor))
rank_code=BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'
text,detail=render(w,config.__wrapped__(),r['scoped_prefix']['pm'],str(rank_code),r['initial_relations'])
imports=['ActualBWSMShapes','ActualBWParameters','ActualBWConstantCotangents','ActualBWInputsWitness','denote.SourceBWLinearDxUnit']
header=''.join(f'import {name}\n' for name in imports)+'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\n'
witness='''theorem backwardDxInputsNonvacuous : ∃ s p t q : Store,
    smSeededDenoteWithInputs s = some t ∧ pmSeededDenoteWithInputs p = some q ∧
    InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p) ∧ pmSeededPrefixInitShapes p :=
  backwardInputsNonvacuous
#print axioms backwardDxInputsNonvacuous
'''
(A/'ActualBWDxValues.lean').write_text(header+text+witness+'end\nend TrainVerify.Denote.RuntimeWorld\n')
(A/'actual-dx-values.json').write_text(json.dumps(detail,indent=2))
print('original dX unit projections',len(detail['units']))
