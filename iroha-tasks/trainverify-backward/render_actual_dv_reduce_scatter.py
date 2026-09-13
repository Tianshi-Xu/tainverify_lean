"""Reproduce the original five BW_matmul callers; no graph or source mutation."""
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict.runtime_backward_matmul_reduce_scatter_consumers import render
ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / '.hermes/backward-kernel'
BASE = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])
w = worlds.__wrapped__(captured.__wrapped__())
receipt = json.loads((BASE / 'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
for view, cells, _, order, label in w:
    assert order['execution_to_source'] == receipt['execution_order'][label]['execution_to_source']
    refs = {tuple(r['ref']): r for r in receipt['fullrefs'][label]}
    assert len(refs) == len(view.tensors())
    for tensor in view.tensors():
        row = refs[tuple(view.source_tensor(tensor))]
        assert row['tid'] == tensor.tid and tuple(row['shape']) == tuple(view.tensor_shape(tensor))
text, detail = render(w,str(BASE/'p2-r4/capture.pkl'),str(BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'))
header = 'import TrainVerifyRuntimeWorldData\nimport denote.SourceReduceScatterRead\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
OUT.mkdir(parents=True, exist_ok=True)
(OUT / 'ActualBWDVReduceScatterRead.lean').write_text(header + detail['source_text'] + 'end\nend TrainVerify.Denote.RuntimeWorld\n')
header = 'import TrainVerifyRuntimeWorldData\nimport ActualBWMatmulRead\nimport ActualBWDVReduceScatterRead\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
(OUT / 'ActualBWMatmulDVReduceScatter.lean').write_text(header + text + 'end\nend TrainVerify.Denote.RuntimeWorld\n')
(OUT / 'ActualBWMatmulDVReduceScatter.json').write_text(json.dumps(detail,indent=2))
print('dV ReduceScatter reads',len(detail['reads']),'compositions',text.count('#print axioms'))
