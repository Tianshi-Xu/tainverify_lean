"""Read-only actual dX -> ReduceScatter replay; emits JSON or Lean to stdout.

No recapture, shared cache, graph entry changes, Lean invocation or disk output.
The --lean candidate imports existing graph/linear certificates for parent checks.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path

from Verdict.runtime_backward_reduce_scatter_reads import render
from Verdict.runtime_lineage import _same_typed


HEADER = ('import TrainVerifyRuntimeWorldData\nimport ActualBWLinearRead\n'
          'import denote.SourceReduceScatterRead\n'
          'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\n'
          'set_option maxHeartbeats 500000\n')


def replay(worlds, receipt, capture_path, rank_code_directory):
    """Bind the candidate to the earlier complete original graph receipt."""
    for view,_,_,order,label in worlds:
        if not _same_typed(order['execution_to_source'], receipt['execution_order'][label]['execution_to_source']):
            raise ValueError('reduce-scatter replay original execution order mismatch')
        original = {tuple(r['ref']): r for r in receipt['fullrefs'][label]}
        if len(original) != len(receipt['fullrefs'][label]) or len(original) != len(view.tensors()):
            raise ValueError('reduce-scatter replay original tensor inventory mismatch')
        for tensor in view.tensors():
            row = original.get(tuple(view.source_tensor(tensor)))
            if (row is None or not _same_typed(row['tid'], tensor.tid)
                    or not _same_typed(tuple(row['shape']), tuple(view.tensor_shape(tensor)))):
                raise ValueError('reduce-scatter replay original tensor/shape identity mismatch')
    _,cells,_,_,_ = worlds[1]
    # First BW_linear per original rank/microbatch; no rank or TID constants.
    units = dict.fromkeys((c.rank,c.mb) for c in cells if c.opname.name == 'BW_linear')
    indices = [next(i for i,c in enumerate(cells) if (c.rank,c.mb)==unit and c.opname.name=='BW_linear')
               for unit in units]
    fragment, detail = render(worlds, indices, capture_path, rank_code_directory)
    text = HEADER + fragment + 'end\nend TrainVerify.Denote.RuntimeWorld\n'
    detail.update(candidate_sha256=hashlib.sha256(text.encode()).hexdigest(),
                  candidate_bytes=len(text.encode()),
                  theorem_count=sum(len(r['theorems']) for r in detail['reads']),
                  source_execution_pairs=[[r['source_index'],r['execution_index']] for r in detail['reads']])
    return text,detail


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=os.environ.get('TRAINVERIFY_CAPTURE_ROOT'))
    parser.add_argument('--lean', action='store_true', help='print exact candidate Lean instead of JSON receipt')
    args = parser.parse_args()
    if args.root is None:
        parser.error('--root or TRAINVERIFY_CAPTURE_ROOT is required')
    os.environ['TRAINVERIFY_CAPTURE_ROOT'] = str(args.root)
    # Existing no-cache trusted-pickle graph loader. No backend capture pipeline.
    from scripts.tests.test_backward_linear_authority import captured
    from scripts.tests.test_runtime_backward_linear_reads import worlds
    world = worlds.__wrapped__(captured.__wrapped__())
    receipt = json.loads((args.root/'dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json').read_text())
    text,detail = replay(world, receipt, str(args.root/'p2-r4/capture.pkl'),
                        str(args.root/'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'))
    print(text if args.lean else json.dumps(detail, indent=2), end='' if args.lean else '\n')


if __name__ == '__main__':
    main()
