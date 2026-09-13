"""Actual constant PM cotangents, using accepted source/shape DAG imports."""
import json
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_seed_reads import config
from Verdict.runtime_backward_constant_cotangents import render
ROOT = Path(__file__).resolve().parents[2]
A = ROOT / '.hermes/backward-kernel'
BASE = Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1')
OLD = BASE / 'dp-prefix-cost-closure/output-projection/actual-output-projection1'
receipt = json.loads((OLD / 'world-receipt.json').read_text())
w = worlds.__wrapped__(captured.__wrapped__())
for view, _, _, order, label in w:
    assert order['execution_to_source'] == receipt['execution_order'][label]['execution_to_source']
    original = {tuple(r['ref']): r for r in receipt['fullrefs'][label]}
    assert len(original) == len(view.tensors())
    for tensor in view.tensors():
        row = original[tuple(view.source_tensor(tensor))]
        assert row['tid'] == tensor.tid and tuple(row['shape']) == tuple(view.tensor_shape(tensor))
rank_code = BASE / 'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'
text, detail = render(w, config.__wrapped__(), receipt['scoped_prefix']['pm'], str(rank_code))
header = ('import TrainVerifyRuntimeWorldData\nimport ActualBWCotangentRead\n'
          'import ActualBWPrefixShapes\nimport denote.SourceConstantCotangent\n'
          'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\n')
witness = '''theorem backwardConstantCallerNonvacuous :
    ∃ s t : Store, pmSeededPrefixInitShapes s ∧ pmSeededDenoteWithInputs s = some t :=
  backwardPrefixCallerNonvacuous
#print axioms backwardConstantCallerNonvacuous
'''
(A / 'ActualBWConstantCotangents.lean').write_text(header + text + witness + 'end\nend TrainVerify.Denote.RuntimeWorld\n')
(A / 'actual-constant-cotangents.json').write_text(json.dumps(detail, indent=2))
print('actual constant PM cotangents', len(detail['reads']))
