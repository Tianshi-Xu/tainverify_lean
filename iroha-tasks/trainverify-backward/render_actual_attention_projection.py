"""Replay original attention projection and its inverse-view continuation."""
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict import runtime_backward_attention_projection_consumers as projection
from Verdict import runtime_backward_view_reads as view_reads

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'.hermes/backward-kernel'
BASE=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])
receipt=json.loads((BASE/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
w=worlds.__wrapped__(captured.__wrapped__())
for view,cells,_,order,label in w:
    assert order['execution_to_source']==receipt['execution_order'][label]['execution_to_source']
    refs={tuple(r['ref']):r for r in receipt['fullrefs'][label]}
    assert len(refs)==len(view.tensors())
    for tensor in view.tensors():
        row=refs[tuple(view.source_tensor(tensor))]
        assert row['tid']==tensor.tid and tuple(row['shape'])==tuple(view.tensor_shape(tensor))
text,detail=projection.render(w,str(BASE/'p2-r4/capture.pkl'),str(BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'))
collective=detail.pop('collective_source')
linear=detail.pop('linear_source')
views,view_detail=view_reads.render_after_linear(w,detail['reads'])
view_source=view_detail.pop('view_source')


def save(name,imports,proof,metadata):
    header=''.join(f'import {i}\n' for i in imports)
    header+='namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
    (OUT/(name+'.lean')).write_text(header+proof+'end\nend TrainVerify.Denote.RuntimeWorld\n')
    (OUT/(name+'.json')).write_text(json.dumps(metadata,indent=2))
    print(name,'declarations',proof.count('#print axioms'))


save('ActualBWAttentionProjectionCollectiveRead',['TrainVerifyRuntimeWorldData','denote.SourceAllGatherRead'],collective,detail)
save('ActualBWAttentionProjectionLinearRead',['TrainVerifyRuntimeWorldData','denote.SourceBWLinearRead'],linear,detail)
save('ActualBWAttentionProjectionConsumers',['TrainVerifyRuntimeWorldData','ActualBWResidualJoinConsumers','ActualBWAttentionProjectionCollectiveRead','ActualBWAttentionProjectionLinearRead'],text,detail)
save('ActualBWViewRead',['TrainVerifyRuntimeWorldData','denote.SourceBWViewRead'],view_source,view_detail)
save('ActualBWViewConsumers',['TrainVerifyRuntimeWorldData','ActualBWViewRead','ActualBWAttentionProjectionConsumers'],views,view_detail)
