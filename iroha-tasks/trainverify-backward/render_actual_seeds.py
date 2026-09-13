"""Rerender authenticated BW_sum/seed reads on unchanged canonical graph data."""
import json
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict.runtime_backward_seed_reads import render

ROOT=Path(__file__).resolve().parents[2]
A=ROOT/'.hermes/backward-kernel'
BASE=Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1')
old=BASE/'dp-prefix-cost-closure/output-projection/actual-output-projection1'
receipt=json.loads((old/'world-receipt.json').read_text())
w=worlds.__wrapped__(captured.__wrapped__())
for view,cells,snapshot,order,label in w:
    assert order['execution_to_source']==receipt['execution_order'][label]['execution_to_source']
    original={tuple(r['ref']):r for r in receipt['fullrefs'][label]}
    assert len(original)==len(view.tensors())
    for t in view.tensors():
        r=original[tuple(view.source_tensor(t))]
        assert r['tid']==t.tid and tuple(r['shape'])==tuple(view.tensor_shape(t))
config=json.loads((BASE/'dp-prefix-bwembedding-implementation/seed-config.json').read_text())
text,detail=render(w,config,config['pm_run'])
header='import TrainVerifyRuntimeWorldData\nimport TrainVerifyRuntimePrefix0000\nimport denote.SourceBWSumRead\nimport denote.SourceParameterFrame\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
(A/'ActualBWSeedRead.lean').write_text(header+text+'end\nend TrainVerify.Denote.RuntimeWorld\n')
(A/'actual-seed-reads.json').write_text(json.dumps(detail,indent=2))
print('authenticated reads',len(detail['reads']),'theorems',sum(len(r['theorems']) for r in detail['reads']))
