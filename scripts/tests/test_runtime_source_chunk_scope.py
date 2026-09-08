"""Portable real ChunkPrim/Cell fixtures; independent generated source."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT), str(ROOT / 'Verdict')]


def fixture():
    import torch
    from nnscaler.ir.tensor import IRFullTensor
    from nnscaler.ir.adapter.prim import ChunkPrim
    from nnscaler.ir.operator import IRFwOperation
    from nnscaler_backend.build_graph import Cell
    from nnscaler_backend.dfg import Node, Tensor
    from verdict.graph import World, WType
    from verdict.operators import OpName
    world = World(wtype=WType.P, plan_ndevs=2, runtime_ndevs=4, num_pp=1, num_mb=1)
    x = IRFullTensor((4, 8), name='x', dtype=torch.float32).tosub()
    y = IRFullTensor((4, 4), name='y', dtype=torch.float32).tosub()
    ir = IRFwOperation('producer', 'torch.empty', [(4, 8)], 1)
    ir.set_output(0, x)
    p = Cell(ir, 2, WType.P)
    p.node = Node('p', 2, 0, 10, 'producer'); p.opname = OpName.FW_embedding
    p.inputs = []; p.outputs = [Tensor('p', 2, 0, x.tid, 1)]
    p._output_irs = [x]
    c = Cell(ChunkPrim([x], [y], dim=1, ranks=[2, 3]), 2, WType.P)
    c.node = Node('p', 2, 0, 20, 'ChunkPrim'); c.opname = OpName.ChunkPrim
    c.inputs = list(p.outputs); c.outputs = [Tensor('p', 2, 0, y.tid, 1)]
    c._input_irs, c._output_irs = [x], [y]; c.kwargs = dict(dim=1, ranks=[2, 3])
    source = f'class GenModel:\n    rank = 2\n    world_size = 4\n    def __init__(self):\n        pass\n    def forward(self):\n        x_{x.tid} = torch.empty((4, 8))\n        y_{y.tid} = nnscaler.runtime.adapter.chunk(x_{x.tid}, dim=1, ranks=[2, 3])\n'
    sources = {r: f'class GenModel:\n    rank = {r}\n    world_size = 4\n    def __init__(self):\n        pass\n' for r in range(4)}
    sources[2] = source
    return world, [p, c], sources


def baseline():
    from nnscaler_backend.runtime_source_authority import capture_adapter_source, export_expanded_cells
    world, cells, sources = fixture()
    return export_expanded_cells(world, cells, rank_sources=sources,
                                 adapter_source=capture_adapter_source(cells))


class ChunkScopeTests(unittest.TestCase):
    def test_actual_chunk_singleton_scope_and_current_fullrefs(self):
        from trainverify.runtime_source_authority import validate_snapshot
        s = baseline()
        self.assertIn('chunk_scope', s['writers'][1], 'missing actual ChunkPrim scope')
        c = s['writers'][1]['chunk_scope']
        self.assertEqual((c['ranks'], c['cardinality'], c['local_index'], c['dim']), ([2, 3], 2, 0, 1))
        self.assertEqual(c['inputs'], s['writers'][1]['inputs'])
        self.assertEqual(c['outputs'], s['writers'][1]['outputs'])
        self.assertEqual(c['local_read_points'][0]['writer'], s['writers'][0]['export_id'])
        self.assertEqual(c['generated_read_binding'], 'complete')
        self.assertEqual(s['chunk_scope_binding'], 'complete')
        self.assertNotIn('adapter', s['writers'][1])
        self.assertFalse(s['proof_admissible'])
        validate_snapshot(json.loads(json.dumps(s)))

    def test_source_ir_and_derived_counterexamples_fail_closed(self):
        from trainverify.runtime_source_authority import bind_adapters, validate_snapshot
        mutations = ('ranks', 'order', 'dim', 'call', 'unit', 'mb', 'version', 'local_index',
                     'generated_dim', 'generated_order', 'generated_input', 'duplicate_call',
                     'runtime_index', 'runtime_cardinality', 'unknown_runtime', 'producer', 'cfg')
        for mutation in mutations:
            s = baseline(); w = s['writers'][1]; row = s['adapter_source'][1]
            with self.subTest(mutation=mutation):
                if mutation in ('ranks', 'order', 'dim'):
                    row['primitive']['kwargs'][{'order': 'ranks'}.get(mutation, mutation)] = {'ranks': [0, 1], 'order': [3, 2], 'dim': 0}[mutation]
                elif mutation in ('call', 'unit', 'mb'):
                    row['ref'][{'call': 'call_instance', 'unit': 'runtime_rank', 'mb': 'microbatch'}[mutation]] += 1
                elif mutation == 'version':
                    row['inputs'][0]['version'] += 1; w['inputs'][0]['version'] += 1
                elif mutation == 'local_index':
                    w['chunk_scope']['local_index'] = 2
                    with self.assertRaises(ValueError): validate_snapshot(s)
                    continue
                elif mutation.startswith('runtime_') or mutation == 'unknown_runtime':
                    src = row['primitive']['runtime']['source']
                    if mutation == 'runtime_index': src = src.replace('get_rank(group)', 'get_rank()')
                    elif mutation == 'runtime_cardinality': src = src.replace('len(ranks)', '4')
                    else: src = 'def chunk(itensor, dim, ranks, async_op=False):\n    return itensor\n'
                    row['primitive']['runtime']['source'] = src
                else:
                    text = s['rank_sources']['2']; line = text.splitlines()[-1] + '\n'
                    if mutation == 'generated_dim': text = text.replace('dim=1', 'dim=0')
                    elif mutation == 'generated_order': text = text.replace('[2, 3]', '[3, 2]')
                    elif mutation == 'generated_input': text = text.replace('.chunk(x_', '.chunk(z_')
                    elif mutation == 'duplicate_call': text += line
                    elif mutation == 'producer': text = text.replace('torch.empty', 'torch.ones')
                    elif mutation == 'cfg': text = text.replace(line, '        if True:\n    ' + line)
                    s['rank_sources']['2'] = text
                try: bind_adapters(s, allow_translation_mismatch=True)
                except ValueError: continue
                self.assertNotEqual(s['chunk_scope_binding'], 'complete')
                validate_snapshot(json.loads(json.dumps(s)))

    def test_read_summary_covers_supported_and_unsupported_chunks(self):
        from trainverify.runtime_source_authority import (
            bind_adapters, build_snapshot, validate_snapshot, writer_export_id)
        s = baseline()
        writer = deepcopy(s['writers'][1])
        row = deepcopy(s['adapter_source'][1])
        for item in (writer, row):
            item['ref']['source_cid'] += 1000
            item['outputs'][0]['source_tid'] += 1000
        del writer['chunk_scope']
        writer['export_id'] = writer_export_id(writer['ref'])
        row['primitive']['generated_outputs'] = ['z_second']
        name = row['primitive']['generated_inputs'][0]
        s['rank_sources']['2'] += f'        z_second = nnscaler.runtime.adapter.chunk({name}, dim=1, ranks=[2, 3])\n'
        s['writers'].append(writer)
        s['adapter_source'].append(row)
        s['tensors'] = build_snapshot(s['writers'])['tensors']
        bind_adapters(s, allow_translation_mismatch=True)
        validate_snapshot(s)
        self.assertEqual(s['chunk_scope_generated_read_binding'], 'complete')
        for rejected in (False, True):
            bad = deepcopy(s)
            bad['adapter_source'][-1]['primitive']['runtime']['source'] = (
                'def chunk(itensor, dim, ranks, async_op=False):\n    return itensor\n')
            if rejected:
                bad['rank_sources']['2'] = bad['rank_sources']['2'].replace('torch.empty', 'torch.ones')
            bind_adapters(bad, allow_translation_mismatch=True)
            validate_snapshot(bad)
            self.assertEqual(bad['writers'][-1]['chunk_scope']['generated_read_binding'], 'missing')
            self.assertEqual(bad['chunk_scope_binding'], 'missing')
            with self.subTest(rejected=rejected):
                self.assertEqual(bad['chunk_scope_generated_read_binding'], 'rejected' if rejected else 'missing')

    def test_legacy_snapshot_without_chunk_claim_remains_unclaimed(self):
        from trainverify.runtime_source_authority import bind_adapters, validate_snapshot
        s = baseline()
        # The pre-Chunk exporter retained the row but no primitive/scope claim.
        del s['adapter_source'][1]['primitive']
        del s['writers'][1]['adapter_kwargs']
        del s['writers'][1]['chunk_scope']
        del s['chunk_scope_binding']
        del s['chunk_scope_generated_read_binding']
        validate_snapshot(s)
        bind_adapters(s, allow_translation_mismatch=True)
        self.assertNotIn('chunk_scope', s['writers'][1])
        self.assertNotIn('chunk_scope_binding', s)
        self.assertFalse(s['proof_admissible'])

    def test_derived_read_summary_cannot_be_forged(self):
        from trainverify.runtime_source_authority import validate_snapshot
        s = baseline()
        s['chunk_scope_generated_read_binding'] = 'rejected'
        with self.assertRaises(ValueError):
            validate_snapshot(s)

    def test_noncontiguous_membership_and_permuted_source_boundary(self):
        from trainverify.runtime_source_authority import bind_adapters, validate_snapshot
        for ranks, index, status in (([0, 2, 3], 1, 'complete'), ([3, 2], 1, 'missing')):
            s = baseline()
            s['adapter_source'][1]['primitive']['kwargs']['ranks'] = ranks
            s['writers'][1]['adapter_kwargs']['ranks'] = ranks
            s['rank_sources']['2'] = s['rank_sources']['2'].replace('[2, 3]', repr(ranks))
            bind_adapters(s, allow_translation_mismatch=True)
            self.assertEqual(s['writers'][1]['chunk_scope']['local_index'], index)
            self.assertEqual(s['chunk_scope_binding'], status)
            validate_snapshot(s)

    def test_missing_primitive_or_generated_source_stays_missing(self):
        from trainverify.runtime_source_authority import bind_adapters
        for missing in ('primitive', 'rank_sources'):
            s = baseline()
            if missing == 'primitive': del s['adapter_source'][1]['primitive']
            else: del s['rank_sources']
            bind_adapters(s, allow_translation_mismatch=True)
            self.assertEqual(s['chunk_scope_binding'], 'missing')
            self.assertFalse(s['proof_admissible'])

    def test_unknown_nested_chunk_effect_is_not_inventory_complete(self):
        from trainverify.runtime_source_authority import bind_adapters
        s = baseline()
        s['rank_sources']['2'] += '        ignored = consume(nnscaler.runtime.adapter.chunk(other, dim=1, ranks=[2, 3]))\n'
        with self.assertRaisesRegex(ValueError, 'chunk.*inventory'):
            bind_adapters(s, allow_translation_mismatch=True)


if __name__ == '__main__':
    unittest.main()
