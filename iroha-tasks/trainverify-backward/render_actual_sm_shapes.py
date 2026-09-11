"""Replay sparse SM shapes against the unchanged canonical source receipt.

Default is read-only validation/rendering in memory. --output-dir explicitly
writes the uncompiled candidate and obligation JSON for the parent's serial gate.
No capture, Lean command, or canonical proof publication is performed.
"""
import argparse
import json
import os
from pathlib import Path
from scripts.tests.test_backward_linear_authority import captured
from scripts.tests.test_runtime_backward_linear_reads import worlds
from Verdict.runtime_backward_sm_shapes import render
from Verdict.runtime_lineage import _same_typed


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path)
    args=parser.parse_args()
    old=Path(os.environ['TRAINVERIFY_CAPTURE_ROOT'])/'dp-prefix-cost-closure/output-projection/actual-output-projection1'
    receipt=json.loads((old/'world-receipt.json').read_text())
    w=worlds.__wrapped__(captured.__wrapped__())
    for view,_,_,order,label in w:
        if not _same_typed(order['execution_to_source'],receipt['execution_order'][label]['execution_to_source']):
            raise ValueError('canonical execution order mismatch')
        rows=receipt['fullrefs'][label]
        original={tuple(row['ref']):row for row in rows}
        if len(rows)!=len(original) or len(original)!=len(view.tensors()):
            raise ValueError('canonical fullref inventory mismatch')
        for t in view.tensors():
            row=original[tuple(view.source_tensor(t))]
            if not _same_typed(row['tid'],t.tid) or not _same_typed(tuple(row['shape']),tuple(view.tensor_shape(t))):
                raise ValueError('canonical fullref/shape binding mismatch')
    text,detail=render(w)
    # Check exact selected source NodeDecl schema against unchanged Data bytes,
    # not merely the DTO used to choose lemma names. Kernel checking is later.
    data=(old/'TrainVerifyRuntimeWorldData.lean').read_text()
    view,cells,_,_,_=w[0]
    from Verdict.graph_to_lean import _get_node_params
    indices=set(detail['source_indices'])|{detail['linear_binding']['source_index'],detail['linear_binding']['source_contract']['fw_source_index']}
    # BW_sum's paired FW_sum is authentication-only, not a shape dependency.
    for row in detail['reads']:
        if row['op']=='BW_sum':
            indices.update(i for i,c in enumerate(cells) if c.ir is cells[row['source_index']].ir.mirror)
    for i in sorted(indices):
        c=cells[i]; ins=[t.tid for t in view.node_inputs(c.node)]; outs=[t.tid for t in view.node_outputs(c.node)]
        params=_get_node_params(view,c.node,num_parts=0) or []
        expected=f'def smNode_{i} : NodeDecl := {{rank := {c.rank}, op := "OpName.{c.opname.name}", ins := {ins}, outs := {outs}, params := {params}}}'
        if expected not in data.splitlines(): raise ValueError(f'canonical source NodeDecl mismatch: {i}')
    imports=['TrainVerifyRuntimeWorldData']+['denote.'+x for x in (
        'SourceInitialInputRead','SourceLayoutRead','SourceEmbeddingRead','SourceAddRead',
        'SourceLinearRead','SourceLayernormRead','SourceMultirefRead','SourceBWSumRead')]
    header=''.join(f'import {x}\n' for x in imports)+'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n'
    candidate=header+text+'end\nend TrainVerify.Denote.RuntimeWorld\n'
    if args.output_dir:
        args.output_dir.mkdir(parents=True,exist_ok=True)
        (args.output_dir/'ActualBWSMShapes.lean').write_text(candidate)
        (args.output_dir/'actual-sm-shapes.json').write_text(json.dumps(detail,indent=2)+'\n')
    print(json.dumps(dict(source_indices=detail['source_indices'],parameter_shapes=detail['parameter_shapes'],
        conclusions=detail['conclusions'],candidate_bytes=len(candidate.encode()),
        kernel_checked=False,output_dir=str(args.output_dir) if args.output_dir else None),indent=2))


if __name__=='__main__':
    main()
