"""Replay the next original BW_add and its LN cotangent, using old Data IDs."""
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict.runtime_backward_add_consumers import render

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / '.hermes/backward-kernel'
BASE = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])
receipt = json.loads((BASE / 'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
w = worlds.__wrapped__(captured.__wrapped__())
for view, cells, _, order, label in w:
    assert order['execution_to_source'] == receipt['execution_order'][label]['execution_to_source']
    rows = {tuple(r['ref']): r for r in receipt['fullrefs'][label]}
    assert len(rows) == len(view.tensors())
    for tensor in view.tensors():
        row = rows[tuple(view.source_tensor(tensor))]
        assert row['tid'] == tensor.tid and tuple(row['shape']) == tuple(view.tensor_shape(tensor))
text, detail = render(w)
from Verdict.runtime_backward_add_reads import render_read
reads = []
for row in detail['reads']:
    world = next(v for v in w if v[-1] == row['world'])
    view, cells, snapshot, order, label = world
    read, fresh = render_read(view, cells, snapshot, row['source_index'], order, label)
    assert fresh == row['add_read']
    reads.append(read)


def save(name, imports, proof, metadata):
    header = ''.join(f'import {i}\n' for i in imports)
    header += 'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
    (OUT / (name + '.lean')).write_text(header + proof + 'end\nend TrainVerify.Denote.RuntimeWorld\n')
    (OUT / (name + '.json')).write_text(json.dumps(metadata, indent=2))
    print(name, 'declarations', proof.count('#print axioms'))


save('ActualBWAddRead', ['TrainVerifyRuntimeWorldData', 'denote.SourceBWAddRead'], ''.join(reads), detail)
save('ActualBWAddConsumers', ['TrainVerifyRuntimeWorldData', 'ActualBWAddRead', 'ActualBWLayernormRead'], text, detail)
