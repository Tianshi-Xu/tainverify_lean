"""Replay the full original residual join and its immediate Add consumer.

Reuse accepted FC1, retained residual and multiref roots. No new forward prefix,
no recursively expanded downstream scan, and no cross-graph equality claim.
"""
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict import runtime_backward_residual_join_consumers as consumers

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
        original = refs[tuple(view.source_tensor(tensor))]
        assert original['tid'] == tensor.tid and tuple(original['shape']) == tuple(view.tensor_shape(tensor))
text, detail = consumers.render(w, str(BASE/'p2-r4/capture.pkl'),
    str(BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'))
collective = detail.pop('collective_source')
add = detail.pop('add_source')


def save(name, imports, proof):
    header = ''.join(f'import {i}\n' for i in imports)
    header += 'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
    (OUT/(name+'.lean')).write_text(header+proof+'end\nend TrainVerify.Denote.RuntimeWorld\n')
    (OUT/(name+'.json')).write_text(json.dumps(detail, indent=2))
    print(name, 'declarations', proof.count('#print axioms'))


save('ActualBWResidualJoinRead', ['TrainVerifyRuntimeWorldData','denote.SourcePrimitiveRead'], collective)
save('ActualBWResidualJoinAddRead', ['TrainVerifyRuntimeWorldData','denote.SourceBWAddRead'], add)
save('ActualBWResidualJoinConsumers', ['TrainVerifyRuntimeWorldData','ActualBWFC1Consumers',
    'ActualBWResidualExchange','ActualBWMultirefRead','ActualBWResidualJoinRead','ActualBWResidualJoinAddRead'], text)
