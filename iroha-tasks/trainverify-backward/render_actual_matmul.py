"""Reproduce the original five BW_matmul callers; no graph or source mutation."""
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from scripts.tests.test_runtime_backward_matmul_reads import selected
from Verdict.runtime_backward_matmul_reads import render_read
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
parts, rows = [], []
for args in selected(w):
    text, row = render_read(*args)
    assert render_read(*args) == (text, row)
    parts.append(text); rows.append(row)
header = 'import TrainVerifyRuntimeWorldData\nimport denote.SourceBWMatmulRead\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
OUT.mkdir(parents=True, exist_ok=True)
text = header + ''.join(parts) + 'end\nend TrainVerify.Denote.RuntimeWorld\n'
(OUT / 'ActualBWMatmulRead.lean').write_text(text)
(OUT / 'ActualBWMatmulRead.json').write_text(json.dumps({'reads': rows}, indent=2))
print('ActualBWMatmulRead', len(rows), 'original nodes', text.count('#print axioms'), 'theorems')
