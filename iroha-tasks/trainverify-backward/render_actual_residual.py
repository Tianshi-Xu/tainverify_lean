"""Replay retained backward residual AA and complete multiref sum reads."""
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict.runtime_backward_residual_exchange_reads import render as exchange
from Verdict.runtime_backward_multiref_reads import render_read

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'.hermes/backward-kernel'
BASE = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])
receipt = json.loads((BASE/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
w = worlds.__wrapped__(captured.__wrapped__())
for view, cells, _, order, label in w:
    assert order['execution_to_source'] == receipt['execution_order'][label]['execution_to_source']
    refs = {tuple(r['ref']): r for r in receipt['fullrefs'][label]}
    assert len(refs) == len(view.tensors())
    for tensor in view.tensors():
        row = refs[tuple(view.source_tensor(tensor))]
        assert row['tid'] == tensor.tid and tuple(row['shape']) == tuple(view.tensor_shape(tensor))
ex, ex_detail = exchange(w, str(BASE/'p2-r4/capture.pkl'), str(BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'))
proof, rows = [], []
for view, cells, snapshot, order, label in w:
    for rank in dict.fromkeys(c.rank for c in cells):
        i = next(i for i in order['execution_to_source'] if cells[i].rank == rank and cells[i].opname.name == 'BW_multiref')
        text, row = render_read(view, cells, snapshot, i, order, label)
        proof.append(text); rows.append(row)


def save(name, imports, text, detail):
    header = ''.join(f'import {i}\n' for i in imports)
    header += 'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
    (OUT/(name+'.lean')).write_text(header+text+'end\nend TrainVerify.Denote.RuntimeWorld\n')
    (OUT/(name+'.json')).write_text(json.dumps(detail, indent=2))
    print(name, 'declarations', text.count('#print axioms'))


save('ActualBWResidualExchange', ['TrainVerifyRuntimeWorldData', 'ActualBWAddRead', 'denote.SourcePrimitiveRead'], ex, ex_detail)
save('ActualBWMultirefRead', ['TrainVerifyRuntimeWorldData', 'denote.SourceBWMultirefRead'], ''.join(proof), dict(reads=rows))
