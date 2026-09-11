"""Exercise the new reader against unchanged canonical graph data, no recapture."""
import json
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict.runtime_backward_linear_reads import render_read

ROOT=Path(__file__).resolve().parents[2]
A=ROOT/'.hermes/backward-kernel'
OLD=Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/dp-prefix-cost-closure/output-projection/actual-output-projection1')
receipt=json.loads((OLD/'world-receipt.json').read_text())
proofs=[]; rows=[]
for view,cells,snapshot,order,label in worlds.__wrapped__(captured.__wrapped__()):
    # Authority cross-check before importing a historical canonical definition.
    assert order['execution_to_source']==receipt['execution_order'][label]['execution_to_source']
    by_ref={tuple(r['ref']):r for r in receipt['fullrefs'][label]}
    assert len(by_ref)==len(view.tensors())
    for t in view.tensors():
        row=by_ref[tuple(view.source_tensor(t))]
        assert row['tid']==t.tid and tuple(row['shape'])==tuple(view.tensor_shape(t))
    for rank in range(view.W.runtime_ndevs):
        i=next(i for i,c in enumerate(cells) if c.rank==rank and c.opname.name=='BW_linear')
        text,row=render_read(view,cells,snapshot,i,order,label)
        proofs.append(text); rows.append(row)
text='import TrainVerifyRuntimeWorldData\nimport denote.SourceBWLinearRead\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'+''.join(proofs)+'end\nend TrainVerify.Denote.RuntimeWorld\n'
(A/'ActualBWLinearRead.lean').write_text(text)
(A/'actual-reads.json').write_text(json.dumps(rows,indent=2))
print('actual reads',len(rows),'theorems',sum(len(r['theorems']) for r in rows),'bytes',len(text.encode()))
print([(r['world'],r['node'],r['source_index'],r['execution_index'],r['input_tids'],r['output_tids']) for r in rows])
