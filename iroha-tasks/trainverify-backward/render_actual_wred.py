"""Original dW -> parameter-owned DP WRED fragment on canonical graph data."""
import json
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_wred_reads import selected
from Verdict.runtime_backward_wred_reads import render
ROOT=Path(__file__).resolve().parents[2];A=ROOT/'.hermes/backward-kernel'
BASE=Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1')
old=BASE/'dp-prefix-cost-closure/output-projection/actual-output-projection1'
receipt=json.loads((old/'world-receipt.json').read_text())
w=worlds.__wrapped__(captured.__wrapped__())
for view,_,_,order,label in w:
    assert order['execution_to_source']==receipt['execution_order'][label]['execution_to_source']
    original={tuple(r['ref']):r for r in receipt['fullrefs'][label]}
    assert len(original)==len(view.tensors())
    for t in view.tensors():
        r=original[tuple(view.source_tensor(t))]
        assert r['tid']==t.tid and tuple(r['shape'])==tuple(view.tensor_shape(t))
capture=BASE/'p2-r4/capture.pkl';rank_code=BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'
text,detail=render(w,selected(w),str(capture),str(rank_code))
header='import TrainVerifyRuntimeWorldData\nimport ActualBWLinearRead\nimport denote.SourceWREDRead\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
(A/'ActualBWWREDRead.lean').write_text(header+text+'end\nend TrainVerify.Denote.RuntimeWorld\n')
(A/'actual-wred-reads.json').write_text(json.dumps(detail,indent=2))
print('actual WRED connections',len(detail['reads']),'theorems',sum(len(r['theorems']) for r in detail['reads']))
