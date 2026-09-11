"""Replay original LayerNorm reads, shared context, and affine SUM reducers."""
import json,os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict.runtime_backward_layernorm_reads import render_read
from Verdict.runtime_backward_layernorm_context import render as context
from Verdict.runtime_backward_layernorm_wred import render as wred
ROOT=Path(__file__).resolve().parents[2]; OUT=ROOT/'.hermes/backward-kernel'
BASE=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])
receipt=json.loads((BASE/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
w=worlds.__wrapped__(captured.__wrapped__())
for view,cells,_,order,label in w:
    assert order['execution_to_source']==receipt['execution_order'][label]['execution_to_source']
    rows={tuple(r['ref']):r for r in receipt['fullrefs'][label]}
    assert len(rows)==len(view.tensors())
    for tensor in view.tensors():
        row=rows[tuple(view.source_tensor(tensor))]
        assert row['tid']==tensor.tid and tuple(row['shape'])==tuple(view.tensor_shape(tensor))
proof=[]; reads=[]
for view,cells,snapshot,order,label in w:
    for rank in dict.fromkeys(c.rank for c in cells):
        i=next(i for i in order['execution_to_source'] if cells[i].rank==rank and cells[i].opname.name=='BW_layernorm')
        text,row=render_read(view,cells,snapshot,i,order,label); proof.append(text); reads.append(row)
ctx,ctx_detail=context(w,receipt['scoped_prefix']['pm'],receipt['initial_relations'])
indices=[r['source_index'] for r in reads if r['world']=='pm']
red,red_detail=wred(w,indices,str(BASE/'p2-r4/capture.pkl'),str(BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'))

def save(name,imports,text,detail):
    header=''.join(f'import {i}\n' for i in imports)+'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
    (OUT/(name+'.lean')).write_text(header+text+'end\nend TrainVerify.Denote.RuntimeWorld\n')
    (OUT/(name+'.json')).write_text(json.dumps(detail,indent=2))
    print(name,'declarations',text.count('#print axioms'))

save('ActualBWLayernormRead',['TrainVerifyRuntimeWorldData','denote.SourceBWLayernormRead'],''.join(proof),{'reads':reads})
ctx+='''theorem backwardLayernormContextNonvacuous : ∃ s p t q : Store,
    smSeededDenoteWithInputs s = some t ∧ pmSeededDenoteWithInputs p = some q ∧
    InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p) ∧ pmSeededPrefixInitShapes p :=
  backwardInputsNonvacuous
#print axioms backwardLayernormContextNonvacuous
'''
save('ActualBWLayernormContext',['TrainVerifyRuntimeWorldData','ActualBWDxValues'],ctx,ctx_detail)
save('ActualBWLayernormWRED',['TrainVerifyRuntimeWorldData','ActualBWLayernormRead','denote.SourceWREDRead'],red,red_detail)
