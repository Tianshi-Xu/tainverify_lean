"""Original attention layout source roots and same-Store composition."""
import argparse
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict import graph_to_lean as compiler
from Verdict import runtime_backward_view_reads as views
from Verdict import runtime_backward_contiguous_reads as contiguous
from Verdict import runtime_backward_transpose_reads as transpose
from Verdict import runtime_backward_collective_reads as collective
from Verdict.runtime_backward_fc1_consumers import _consumer
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'.hermes/backward-kernel'
BASE=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--sources-only',action='store_true')
args=parser.parse_args()
w=worlds.__wrapped__(captured.__wrapped__())
receipt=json.loads((BASE/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
for view,cells,_,order,label in w:
    assert order['execution_to_source']==receipt['execution_order'][label]['execution_to_source']
    refs={tuple(r['ref']):r for r in receipt['fullrefs'][label]}
    assert len(refs)==len(view.tensors())
    for tensor in view.tensors():
        row=refs[tuple(view.source_tensor(tensor))]
        assert row['tid']==tensor.tid and tuple(row['shape'])==tuple(view.tensor_shape(tensor))
paths=str(BASE/'p2-r4/capture.pkl'),str(BASE/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_')


def save(name,imports,text,detail):
    header=''.join(f'import {i}\n' for i in imports)
    header+='namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
    (OUT/(name+'.lean')).write_text(header+text+'end\nend TrainVerify.Denote.RuntimeWorld\n')
    (OUT/(name+'.json')).write_text(json.dumps(detail,indent=2))
    print(name,'declarations',text.count('#print axioms'),flush=True)


if args.sources_only:
    snapshot=compiler._load_chunk_source(*paths)
    compiler.attach_collective_scopes(w[1][0],snapshot)
    parts={'collective_source':[],'contiguous_source':[],'transpose_source':[]}
    rows=[]
    for view,cells,source,order,label in w:
        if label=='pm': source=snapshot
        for rank in dict.fromkeys(c.rank for c in cells):
            vi=next(i for i in order['execution_to_source'] if cells[i].rank==rank and cells[i].opname.name=='BW_view')
            previous=vi
            for reader,op,key in [(contiguous,'BW_contiguous','contiguous_source'),(transpose,'BW_transpose','transpose_source')]:
                if label=='pm':
                    ai,_=_consumer(cells,cells[previous],0,'AllToAllPrim')
                    producer=views if key=='contiguous_source' else contiguous
                    text,row=collective.render_read(view,cells,source,ai,order,label,producer.render_read,0)
                    parts['collective_source'].append(text);rows.append(row)
                    print('AA',ai,row['params'],row['input_tids'],row['output_tid'],flush=True)
                    previous=ai
                i,_=_consumer(cells,cells[previous],0,op)
                text,row=reader.render_read(view,cells,source,i,order,label)
                parts[key].append(text);rows.append(row);previous=i
    details={'reads':rows}
    parts={k:''.join(v) for k,v in parts.items()}
else:
    from Verdict import runtime_backward_attention_layout_consumers as consumers
    text,details=consumers.render(w,*paths)
    view_header='import TrainVerifyRuntimeWorldData\nimport ActualBWViewRead\nimport ActualBWAttentionProjectionConsumers\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
    assert (OUT/'ActualBWViewConsumers.lean').read_text()==view_header+details.pop('view_compositions')+'end\nend TrainVerify.Denote.RuntimeWorld\n'
    parts={k:details.pop(k) for k in ('collective_source','contiguous_source','transpose_source')}

save('ActualBWLayoutCollectiveRead',['TrainVerifyRuntimeWorldData','denote.SourcePrimitiveRead'],parts['collective_source'],details)
save('ActualBWContiguousRead',['TrainVerifyRuntimeWorldData','denote.SourceBWContiguousRead'],parts['contiguous_source'],details)
save('ActualBWTransposeRead',['TrainVerifyRuntimeWorldData','denote.SourceBWTransposeRead'],parts['transpose_source'],details)
if not args.sources_only:
    save('ActualBWAttentionLayoutConsumers',['TrainVerifyRuntimeWorldData','ActualBWViewConsumers','ActualBWLayoutCollectiveRead','ActualBWContiguousRead','ActualBWTransposeRead'],text,details)
