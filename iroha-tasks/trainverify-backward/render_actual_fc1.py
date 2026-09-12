"""Replay the original FC1 continuation on the accepted RuntimeWorld data.

--reads-only prepares independent source roots before the communication wave;
it does not claim that the complete continuation has been generated or checked.
"""
import argparse
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict import runtime_backward_fc1_consumers as consumers
from Verdict import runtime_backward_linear_reads as linear
from Verdict import runtime_backward_layernorm_reads as layernorm
from Verdict import runtime_backward_wred_reads as wred
from Verdict import runtime_backward_layernorm_wred as affine

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'.hermes/backward-kernel'
BASE = Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--reads-only', action='store_true')
args = parser.parse_args()
receipt = json.loads((BASE/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
w = worlds.__wrapped__(captured.__wrapped__())
for view, cells, _, order, label in w:
    assert order['execution_to_source'] == receipt['execution_order'][label]['execution_to_source']
    refs = {tuple(r['ref']): r for r in receipt['fullrefs'][label]}
    assert len(refs) == len(view.tensors())
    for tensor in view.tensors():
        row = refs[tuple(view.source_tensor(tensor))]
        assert row['tid'] == tensor.tid and tuple(row['shape']) == tuple(view.tensor_shape(tensor))
rows = consumers.discover(w)
parts = {'linear': [], 'layernorm': []}
for row in rows:
    view, cells, snapshot, order, label = next(world for world in w if world[-1] == row['world'])
    for module, key in ((linear, 'linear'), (layernorm, 'layernorm')):
        text, fresh = module.render_read(view, cells, snapshot, row[key]['source_index'], order, label)
        assert fresh == row[key]
        parts[key].append(text)
paths = str(BASE/'p2-r4/capture.pkl'), str(BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_')
indices = [r['linear']['source_index'] for r in rows if r['world'] == 'pm']
red, red_detail = wred.render(w, indices, *paths)
indices = [r['layernorm']['source_index'] for r in rows if r['world'] == 'pm']
lnred, lnred_detail = affine.render(w, indices, *paths)


def save(name, imports, text, detail):
    header = ''.join(f'import {i}\n' for i in imports)
    header += 'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
    (OUT/(name+'.lean')).write_text(header+text+'end\nend TrainVerify.Denote.RuntimeWorld\n')
    (OUT/(name+'.json')).write_text(json.dumps(detail, indent=2))
    print(name, 'declarations', text.count('#print axioms'))


save('ActualBWFC1LinearRead', ['TrainVerifyRuntimeWorldData','denote.SourceBWLinearRead'], ''.join(parts['linear']), {'reads': rows})
save('ActualBWFC1LayernormRead', ['TrainVerifyRuntimeWorldData','denote.SourceBWLayernormRead'], ''.join(parts['layernorm']), {'reads': rows})
save('ActualBWFC1WRED', ['TrainVerifyRuntimeWorldData','ActualBWFC1LinearRead','denote.SourceWREDRead'], red, red_detail)
save('ActualBWFC1LayernormWRED', ['TrainVerifyRuntimeWorldData','ActualBWFC1LayernormRead','denote.SourceWREDRead'], lnred, lnred_detail)
if not args.reads_only:
    text, detail = consumers.render(w, *paths)
    collective = detail.pop('collective_source')
    save('ActualBWFC1CollectiveRead', ['TrainVerifyRuntimeWorldData','denote.SourceAllGatherRead','denote.SourcePrimitiveRead'], collective, {'reads': detail['collective_reads']})
    save('ActualBWFC1Consumers', ['TrainVerifyRuntimeWorldData','ActualBWFFNConsumers','ActualBWFC1LinearRead','ActualBWFC1LayernormRead','ActualBWFC1CollectiveRead'], text, detail)
else:
    print('Source roots only; communication and composition wave not generated.')
