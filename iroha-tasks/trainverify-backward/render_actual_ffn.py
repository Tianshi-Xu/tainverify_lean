"""Replay original residual-right/FC2/GELU and the replicated FC2 reducer."""
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict import runtime_backward_ffn_consumers as consumers
from Verdict import runtime_backward_linear_reads as linear
from Verdict import runtime_backward_gelu_reads as gelu
from Verdict import runtime_backward_wred_reads as wred

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
text, detail = consumers.render(w)
linear_proof, gelu_proof = [], []
for row in detail['reads']:
    view, cells, snapshot, order, label = next(world for world in w if world[-1] == row['world'])
    for module, key, parts in ((linear, 'linear', linear_proof), (gelu, 'gelu', gelu_proof)):
        proof, fresh = module.render_read(view, cells, snapshot, row[key]['source_index'], order, label)
        assert fresh == row[key]
        parts.append(proof)
indices = [r['linear']['source_index'] for r in detail['reads'] if r['world'] == 'pm']
red, red_detail = wred.render(w, indices, str(BASE/'p2-r4/capture.pkl'), str(BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'))


def save(name, imports, proof, metadata):
    header = ''.join(f'import {i}\n' for i in imports)
    header += 'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
    (OUT/(name+'.lean')).write_text(header+proof+'end\nend TrainVerify.Denote.RuntimeWorld\n')
    (OUT/(name+'.json')).write_text(json.dumps(metadata, indent=2))
    print(name, 'declarations', proof.count('#print axioms'))


save('ActualBWFFNLinearRead', ['TrainVerifyRuntimeWorldData', 'denote.SourceBWLinearRead'], ''.join(linear_proof), detail)
save('ActualBWGeluRead', ['TrainVerifyRuntimeWorldData', 'denote.SourceBWGeluRead'], ''.join(gelu_proof), detail)
save('ActualBWFFNConsumers', ['TrainVerifyRuntimeWorldData', 'ActualBWFFNLinearRead', 'ActualBWGeluRead', 'ActualBWAddRead'], text, detail)
save('ActualBWFC2WRED', ['TrainVerifyRuntimeWorldData', 'ActualBWFFNLinearRead', 'denote.SourceWREDRead'], red, red_detail)
