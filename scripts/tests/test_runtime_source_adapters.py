"""Portable actual primitive/Cell constructions, not new GPU captures."""
from copy import deepcopy
from pathlib import Path
import json
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT), str(ROOT / 'Verdict')]


def adapter_fixture(op='AllGatherPrim', groups=((1, 0), (3, 2)), reverse_indmap=False):
    import torch
    from nnscaler.ir.tensor import IRFullTensor
    from nnscaler.ir.adapter import prim
    from nnscaler_backend.build_graph import Cell, _fuse_collective_inputs
    from nnscaler_backend.dfg import Node, Tensor
    from verdict.graph import World, WType
    from verdict.operators import OpName
    world = World(wtype=WType.P, plan_ndevs=2, runtime_ndevs=4, num_pp=1, num_mb=1)
    full = IRFullTensor((8, 8), name='x', dtype=torch.float32)
    out = IRFullTensor((8, 8), name='y', dtype=torch.float32)
    cells, sources = [], {}
    for group in groups:
        for slot, rank in enumerate(group):
            if reverse_indmap:
                slot = len(group) - 1 - slot
            x = full.select(((slot*4, (slot+1)*4), (0, 8)), (0, 1))
            y = out.select(((slot*4, (slot+1)*4), (0, 8)), (0, 1))
            kw = {'ranks': list(group)}
            if op in ('AllGatherPrim', 'ReduceScatterPrim'): kw['dim'] = 0
            if op == 'AllToAllPrim': kw.update(idim=0, odim=1)
            ir = getattr(prim, op)([x], [y], **kw)
            from nnscaler.ir.operator import IRFwOperation
            producer_ir = IRFwOperation('producer', 'torch.empty', [tuple(x.shape)], 1)
            producer_ir.set_output(0, x)
            producer = Cell(producer_ir, rank, WType.P)
            producer._output_irs = [x]
            producer.node = Node('p', rank, 0, 10, 'producer')
            producer.opname = OpName.FW_embedding
            producer.inputs = []
            producer.outputs = [Tensor('p', rank, 0, x.tid, 1)]
            c = Cell(ir, rank, WType.P)
            c.node = Node('p', rank, 0, 20, op)
            c.opname = getattr(OpName, op)
            c.inputs = list(producer.outputs)
            c.outputs = [Tensor('p', rank, 0, y.tid, 1)]
            c._input_irs, c._output_irs = [x], [y]
            c.kwargs = dict(kw)
            c._collective_group_id = (20, tuple(group))
            c._collective_indmap = {c.inputs[0]: x.indmap}
            cells.extend([producer, c])
            args = ', '.join(f'{k}={v!r}' for k,v in kw.items())
            sources[rank] = f'class GenModel:\n    rank = {rank}\n    world_size = 4\n    def __init__(self):\n        pass\n    def forward(self):\n        {x.name}_{x.tid} = torch.empty({tuple(x.shape)!r})\n        {y.name}_{y.tid} = {ir.signature}({x.name}_{x.tid}, {args})\n'
    # Keep the source read point before the real mutating fusion pass.
    return world, cells, sources


class AdapterSourceTests(unittest.TestCase):
    def test_four_primitives_bind_original_order_full_refs_and_current_writer(self):
        from nnscaler_backend import runtime_source_authority as backend
        self.assertTrue(hasattr(backend, "capture_adapter_source"), "missing prepared adapter source binding")
        from nnscaler_backend.runtime_source_authority import export_expanded_cells, capture_adapter_source
        from nnscaler_backend.build_graph import _fuse_collective_inputs
        from trainverify.runtime_source_authority import validate_snapshot
        for op in ('AllGatherPrim', 'AllReducePrim', 'ReduceScatterPrim', 'AllToAllPrim'):
            with self.subTest(op=op):
                world, cells, sources = adapter_fixture(op)
                evidence = capture_adapter_source(cells)
                _fuse_collective_inputs(cells)
                s = export_expanded_cells(world, cells, adapter_source=evidence)
                self.assertEqual(s['adapter_binding'], 'complete')
                self.assertEqual(s['adapter_generated_binding'], 'missing')
                for w in s['writers']:
                    if w['ref']['op'] != op: continue
                    a = w['adapter']
                    self.assertEqual(a['ordered_inputs'], w['inputs'])
                    self.assertEqual(a['ranks'], [r['runtime_rank'] for r in w['inputs']])
                    self.assertEqual(a['outputs'], w['outputs'])
                    self.assertTrue(all(p['writer'] is not None for p in a['read_points']))
                self.assertFalse(s['proof_admissible'])
                self.assertIn('global-batch', s['completeness']['missing'])
                validate_snapshot(json.loads(json.dumps(s)))

    def test_generated_calls_and_semantic_mutations_rebind_not_payload_compare(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells, capture_adapter_source
        from nnscaler_backend.build_graph import _fuse_collective_inputs
        from trainverify.runtime_source_authority import bind_adapters, build_snapshot, validate_snapshot
        for op in ('AllGatherPrim', 'AllReducePrim', 'ReduceScatterPrim', 'AllToAllPrim'):
            world, cells, sources = adapter_fixture(op)
            evidence = capture_adapter_source(cells)
            _fuse_collective_inputs(cells)
            baseline = export_expanded_cells(world, cells, rank_sources=sources, adapter_source=evidence)
            self.assertEqual(baseline['adapter_generated_binding'], 'complete')
            validate_snapshot(json.loads(json.dumps(baseline)))
            for mutation in ('coordinated_order', 'wrong_unit', 'version', 'current_writer',
                             'deleted_primitive', 'dim', 'idim', 'odim', 'source_call_deleted',
                             'source_ranks_missing', 'source_dim', 'source_wrong_input'):
                if mutation == 'dim' and op not in ('AllGatherPrim', 'ReduceScatterPrim'): continue
                if mutation in ('idim', 'odim') and op != 'AllToAllPrim': continue
                if mutation == 'source_dim' and op == 'AllReducePrim': continue
                bad = deepcopy(baseline)
                w = next(w for w in bad['writers'] if w['ref']['op'] == op)
                rank = str(w['ref']['runtime_rank'])
                if mutation == 'coordinated_order':
                    w['inputs'].reverse(); w['adapter_kwargs']['ranks'].reverse()
                elif mutation == 'wrong_unit':
                    w['inputs'][1]['runtime_rank'] += 2
                elif mutation == 'version':
                    for writer in bad['writers']:
                        if writer['ref']['op'] == op:
                            for t in writer['inputs']: t['version'] += 7
                    for row in bad['adapter_source']:
                        if row['ref']['op'] == op:
                            for t in row['inputs']: t['version'] += 7
                elif mutation == 'current_writer':
                    # Move the consumer before its producer in both inventories.
                    for stream in (bad['writers'], bad['adapter_source']):
                        stream[0], stream[1] = stream[1], stream[0]
                elif mutation == 'deleted_primitive': bad['writers'].remove(w)
                elif mutation in ('dim', 'idim', 'odim'):
                    w['adapter_kwargs'][mutation] += 1
                elif mutation == 'source_call_deleted':
                    bad['rank_sources'][rank] = '\n'.join(line for line in sources[int(rank)].splitlines() if 'nnscaler.runtime.adapter.' not in line) + '\n        pass\n'
                elif mutation == 'source_ranks_missing':
                    bad['rank_sources'][rank] = sources[int(rank)].replace('ranks=[1, 0], ', '').replace('ranks=[1, 0]', '')
                elif mutation == 'source_dim':
                    bad['rank_sources'][rank] = sources[int(rank)].replace('dim=0', 'dim=1')
                else:
                    bad['rank_sources'][rank] = sources[int(rank)].replace(evidence[1]['primitive']['generated_inputs'][0], 'wrong_999')
                # Re-intern and discard all derived bindings: fresh semantic check.
                bad['tensors'] = build_snapshot(bad['writers'])['tensors']
                for writer in bad['writers']: writer.pop('adapter', None)
                with self.subTest(op=op, mutation=mutation), self.assertRaises(ValueError):
                    bind_adapters(bad)

    def test_generated_inventory_survives_coordinated_primitive_deletion(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells, capture_adapter_source
        from nnscaler_backend.build_graph import _fuse_collective_inputs
        from trainverify.runtime_source_authority import bind_adapters, build_snapshot
        world, cells, sources = adapter_fixture()
        evidence = capture_adapter_source(cells)
        _fuse_collective_inputs(cells)
        s = export_expanded_cells(world, cells, rank_sources=sources, adapter_source=evidence)
        s['writers'] = [w for w in s['writers'] if w['ref']['op'] != 'AllGatherPrim']
        s['adapter_source'] = [w for w in s['adapter_source'] if w['ref']['op'] != 'AllGatherPrim']
        s['tensors'] = build_snapshot(s['writers'])['tensors']
        with self.assertRaisesRegex(ValueError, 'inventory'):
            bind_adapters(s)

    def test_backward_alltoall_exposes_effective_dimensions_without_rewriting_source(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells, capture_adapter_source
        from nnscaler_backend.build_graph import _fuse_collective_inputs
        from nnscaler.ir.adapter.prim import AllToAllAllToAllPrim
        world, cells, _ = adapter_fixture('AllToAllPrim')
        class BackwardAdapter:
            def isfw(self): return False
        for c in cells:
            if c.opname.name == 'AllToAllPrim':
                c.ir = AllToAllAllToAllPrim(c._input_irs, c._output_irs, **c.kwargs)
                c.adapter = BackwardAdapter()
        evidence = capture_adapter_source(cells)
        _fuse_collective_inputs(cells)
        s = export_expanded_cells(world, cells, adapter_source=evidence)
        a = s['writers'][1]['adapter']
        self.assertEqual(a['parameters'], {'idim': 1, 'odim': 0})
        self.assertEqual(s['writers'][1]['adapter_kwargs'], {'ranks': [1, 0], 'idim': 0, 'odim': 1})

    def test_translation_mismatch_retains_fused_order_and_fails_closed(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells, capture_adapter_source
        from nnscaler_backend.build_graph import _fuse_collective_inputs
        from trainverify.runtime_source_authority import bind_adapters, validate_snapshot
        world, cells, _ = adapter_fixture(reverse_indmap=True)
        evidence = capture_adapter_source(cells)
        # Real fusion sorts the reversed source indmaps, against primitive order.
        _fuse_collective_inputs(cells)
        s = export_expanded_cells(world, cells, adapter_source=evidence)
        self.assertEqual(s['adapter_binding'], 'translation-mismatch')
        self.assertEqual(s['writers'][1]['inputs'][0]['runtime_rank'], 0)
        self.assertIn('ordered-adapters', s['completeness']['missing'])
        validate_snapshot(json.loads(json.dumps(s)))
        with self.assertRaisesRegex(ValueError, 'translation mismatch'): bind_adapters(s)


if __name__ == '__main__':
    unittest.main()
