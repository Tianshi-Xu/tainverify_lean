"""Reproduce the original five BW_matmul callers; no graph or source mutation."""
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict.runtime_backward_score_consumers import render
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
OUT.mkdir(parents=True,exist_ok=True)
for key,module,helper in [('div','ActualBWDivRead','denote.SourceBWDivRead'),
                          ('collective','ActualBWScoreCollectiveRead','denote.SourcePrimitiveRead'),
                          ('matmul','ActualBWScoreMatmulRead','denote.SourceBWMatmulRead')]:
    header=f'import TrainVerifyRuntimeWorldData\nimport {helper}\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
    (OUT/(module+'.lean')).write_text(header+detail['sources'][key]+'end\nend TrainVerify.Denote.RuntimeWorld\n')
header='import TrainVerifyRuntimeWorldData\nimport ActualBWMatmulSoftmax\nimport ActualBWDivRead\nimport ActualBWScoreCollectiveRead\nimport ActualBWScoreMatmulRead\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
(OUT/'ActualBWScoreDAG.lean').write_text(header+text+'end\nend TrainVerify.Denote.RuntimeWorld\n')
(OUT/'ActualBWScoreDAG.json').write_text(json.dumps(detail,indent=2))
print('Score DAG',len(detail['dag']),'nodes',len(detail['targets']),'matmul projection targets',len(detail['collective_reads']),'original exchanges')
