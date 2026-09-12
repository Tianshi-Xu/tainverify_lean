"""Render only the original V path after an exact runtime-receipt join.

Run in the pinned capture environment. The parent owns kernel-checking these
exact callers and the prior ActualBWMatmulRead/ActualBWMatmulDVReduceScatter.
"""
import json
import os
from pathlib import Path

from Verdict.runtime_backward_v_projection_consumers import render
from Verdict.runtime_lineage import _same_typed

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / '.hermes/backward-kernel'
RECEIPT = Path('dp-prefix-cost-closure/output-projection/actual-output-projection1/world-receipt.json')


def validate_receipt(worlds, receipt):
    """Join original fullrefs, lowered TIDs, shapes and both order directions."""
    for view, _, _, order, label in worlds:
        for field in ('execution_to_source', 'source_to_execution'):
            if not _same_typed(order[field], receipt['execution_order'][label][field]):
                raise ValueError('V projection runtime receipt execution order mismatch')
        original = receipt['fullrefs'][label]
        refs = {tuple(row['ref']): row for row in original}
        if len(refs) != len(original) or len(refs) != len(view.tensors()):
            raise ValueError('V projection runtime receipt fullref inventory mismatch')
        for tensor in view.tensors():
            ref = list(view.source_tensor(tensor))
            row = refs.get(tuple(ref))
            if (row is None or not _same_typed(row['ref'], ref)
                    or not _same_typed(row['tid'], tensor.tid)
                    or not _same_typed(row['shape'], list(view.tensor_shape(tensor)))):
                raise ValueError('V projection runtime receipt fullref/TID/shape mismatch')


def generate(worlds, base, output=OUT):
    base, output = Path(base), Path(output)
    receipt = json.loads((base / RECEIPT).read_text())
    validate_receipt(worlds, receipt)
    text, detail = render(worlds, str(base / 'p2-r4/capture.pkl'),
                          str(base / 'p2-r4/code/_parallel_modules/genmodel/model/gpt/GPT/_'))
    modules = {
        'ActualBWVTransposeRead': (['denote.SourceBWTransposeRead'], detail['transpose_source']),
        'ActualBWVViewRead': (['denote.SourceBWViewRead'], detail['view_source']),
        'ActualBWVCollectiveRead': (['denote.SourcePrimitiveRead', 'denote.SourceAllGatherRead'], detail['collective_source']),
        'ActualBWVLinearRead': (['denote.SourceBWLinearRead'], detail['linear_source']),
    }
    modules['ActualBWVProjectionDAG'] = (
        ['ActualBWMatmulRead', 'ActualBWMatmulDVReduceScatter', *modules], text)
    artifacts = {}
    for name, (imports, body) in modules.items():
        header = ''.join(f'import {module}\n' for module in ['TrainVerifyRuntimeWorldData', *imports])
        header += 'namespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\nset_option maxHeartbeats 500000\n'
        artifacts[name + '.lean'] = header + body + 'end\nend TrainVerify.Denote.RuntimeWorld\n'
    artifacts['ActualBWVProjectionDAG.json'] = json.dumps(detail, indent=2) + '\n'
    # No output creation until all original bindings and serialization succeed.
    output.mkdir(parents=True, exist_ok=True)
    for name, contents in artifacts.items():
        (output / name).write_text(contents)
    return text, detail


def main():
    from scripts.tests.test_backward_linear_authority import captured
    from scripts.tests.test_runtime_backward_linear_reads import worlds
    w = worlds.__wrapped__(captured.__wrapped__())
    text, detail = generate(w, Path(os.environ['TRAINVERIFY_CAPTURE_ROOT']))
    print('V projection DAG stages', len(detail['reads']), 'same-Store equations', text.count('#print axioms'),
          'linear callers', len(detail['linear_reads']), 'kernel-check required')


if __name__ == '__main__':
    main()
