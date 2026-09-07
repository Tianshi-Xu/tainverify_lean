"""Portable actual-Cell reducer fixtures, not host capture fixtures."""
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT), str(ROOT / 'Verdict')]
from test_runtime_source_authority import source_cells


def reducer_fixture():
    import torch
    from nnscaler.ir.tensor import IRFullTensor
    from nnscaler.ir.adapter.adapter import IRWeightReducer
    from nnscaler_backend.build_graph import Cell, _fuse_collective_inputs
    from nnscaler_backend.dfg import Node, Tensor
    from verdict.graph import WType
    from verdict.operators import OpName
    world, _, _ = source_cells()
    shard = IRFullTensor((8, 4), name='weight', dtype=torch.float32, requires_grad=True).as_param().select(((0, 8), (0, 2)), (0, 1))
    world = replace(world, num_pp=1, num_mb=1, gbs=2)
    full = IRFullTensor((4,), name='position.weight', dtype=torch.float32, requires_grad=True).as_param().tosub()
    cells, sources = [], {}
    for rank in range(4):
        weights = [full, shard] if rank % 2 == 0 else [full, shard.parent.select(((0, 8), (2, 4)), (0, 1))]
        lines = ['class GenModel:', f'    rank = {rank}', '    world_size = 4', '    def __init__(self):']
        for index, weight in enumerate(weights):
            weight.grad = weight.parent.grad.select(weight.indmap, (0, 1))
            ranks = [0, 1, 2, 3] if index == 0 else [rank % 2, rank % 2 + 2]
            name = f'weight_{weight.tid}'
            slices = ', '.join(f'slice({a}, {b}, None)' for a, b in weight.indmap)
            lines += [f"        self.register_parameter('{name}', torch.nn.Parameter(torch.empty(1)))",
                      f"        self.add_full_map('{name}', {weight.parent.tid}, True, {weight.parent.name!r}, {weight.parent.shape!r}, ({slices},), 1)",
                      f"        self.wreducer{index} = nnscaler.runtime.adapter.Reducer(ranks={ranks}, reduce_op='sum', zero=0, nreplicas=1)",
                      f'        self.wreducer{index}.add_param(self.{name})',
                      f'        self.add_reducer(self.wreducer{index})']
            fw = Cell(None, rank, WType.P)
            fw.node = Node('p', rank, 0, 100 + index, 'weight-use')
            fw.opname = OpName.FW_embedding
            fw.inputs = [Tensor('p', rank, -1, weight.tid, 0)]
            fw.outputs = [Tensor('p', rank, -1, weight.grad.tid, 1)]
            fw._input_irs = [weight]
            fw._gid2wid = {weight.grad.tid: weight.tid}
            cells.append(fw)
            ir = IRWeightReducer([weight]); ir.device = ranks
            ir._id = index
            red = Cell(ir, rank, WType.P)
            red.node = Node('p', rank, 0, index, f'reducer-w{weight.tid}')
            red.opname = OpName.CROSS_DP_WRED
            red.inputs = list(fw.outputs)
            red.outputs = [fw.outputs[0]._replace(v=2)]
            red._input_irs = [weight]
            red._wred_wid = weight.tid
            red._collective_group_id = (index, weight.tid)
            red._collective_indmap = {red.inputs[0]: weight.indmap}
            cells.append(red)
        sources[rank] = '\n'.join(lines)
    return world, _fuse_collective_inputs(cells)[0], sources


class ReducerSourceTests(unittest.TestCase):
    def test_actual_cells_bind_full_and_sharded_parameters_to_ordered_gradients(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells
        from trainverify.runtime_source_authority import validate_snapshot
        world, cells, sources = reducer_fixture()
        snapshot = export_expanded_cells(world, cells, rank_sources=sources)
        validate_snapshot(json.loads(json.dumps(snapshot)))
        self.assertEqual(snapshot['reducer_binding'], 'complete')
        self.assertEqual(snapshot['completeness']['status'], 'incomplete')
        self.assertIn('ordered-adapters', snapshot['completeness']['missing'])
        self.assertIn('global-batch', snapshot['completeness']['missing'])
        self.assertIn('loss-normalization', snapshot['completeness']['missing'])
        self.assertIs(snapshot['proof_admissible'], False)
        reducers = [w for w in snapshot['writers'] if 'reducer' in w]
        self.assertEqual(len(reducers), 8)
        for w in reducers:
            r = w['reducer']; rank = w['ref']['runtime_rank']
            expected = [0, 1, 2, 3] if r['parameter']['source_tid'] == cells[0].inputs[0].tid else [rank % 2, rank % 2 + 2]
            self.assertEqual(r['ranks'], expected)
            self.assertEqual([t['runtime_rank'] for t in r['ordered_inputs']], expected)
            self.assertEqual(r['outputs'], w['outputs'])
            self.assertEqual(r['grad_input']['runtime_rank'], rank)
            self.assertEqual(r['grad_output']['version'], r['grad_input']['version'] + 1)
            self.assertEqual((r['reduce_op'], r['zero'], r['nreplicas']), ('sum', 0, 1))

    def test_mutations_of_valid_source_never_pass_complete(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells
        from trainverify.runtime_source_authority import validate_snapshot, bind_reducers, build_snapshot
        world, cells, sources = reducer_fixture()
        baseline = export_expanded_cells(world, cells, rank_sources=sources)
        for field in ("reduce_op='sum', ", 'nreplicas=1', 'zero=0, '):
            bad = deepcopy(baseline)
            bad['rank_sources']['0'] = bad['rank_sources']['0'].replace(field, '')
            with self.subTest(missing=field), self.assertRaises(ValueError):
                validate_snapshot(bad)
        for old, new in (("'sum'", "'avg'"), ('zero=0', 'zero=1'), ('nreplicas=1', 'nreplicas=2'),
                         ('ranks=[0, 1, 2, 3]', 'ranks=[3, 2, 1, 0]')):
            bad = deepcopy(baseline)
            bad['rank_sources']['0'] = bad['rank_sources']['0'].replace(old, new)
            with self.subTest(source_change=old), self.assertRaises(ValueError):
                validate_snapshot(bad)
        for mutation in ('parameter', 'reducer_missing', 'coordinated_order', 'remote_input', 'stale_gradient', 'grad_map'):
            bad = deepcopy(baseline)
            red = next(w for w in bad['writers'] if 'reducer' in w)
            if mutation == 'parameter':
                red['reducer']['parameter'] = bad['writers'][2]['inputs'][0]
            elif mutation == 'reducer_missing':
                bad['writers'].remove(red)
            elif mutation == 'coordinated_order':
                red['reducer']['ranks'].reverse()
                red['reducer']['ordered_inputs'].reverse()
            elif mutation == 'remote_input':
                red['inputs'][1] = dict(red['inputs'][1], source_tid=999999)
                # Re-intern identities and re-derive authority: not a stale-link test.
                old_tensors = {t['export_id']: t for t in bad['tensors']}
                bad['tensors'] = [old_tensors.get(t['export_id'], t) for t in build_snapshot(bad['writers'])['tensors']]
            elif mutation == 'stale_gradient':
                for t in red['inputs'] + red['outputs']:
                    t['version'] += 10
            else:
                bad['writers'][0]['parameter_grad_tids'][0][1] = 999999
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                # Rebinding itself must reject remote refs, not just compare payloads.
                if mutation == 'remote_input':
                    bind_reducers(bad)
                else:
                    validate_snapshot(bad)
        missing = {r: '\n'.join(line for line in src.splitlines() if '.add_param(' not in line)
                   for r, src in sources.items()}
        with self.assertRaises(ValueError):
            export_expanded_cells(world, cells, rank_sources=missing)

    def test_rebinding_rejects_coordinated_stale_gradient_versions(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells
        from trainverify.runtime_source_authority import bind_reducers
        world, cells, sources = reducer_fixture()
        snapshot = json.loads(json.dumps(export_expanded_cells(world, cells, rank_sources=sources)))
        for writer in snapshot['writers']:
            if 'reducer' in writer:
                for ref in writer['inputs'] + writer['outputs']:
                    ref['version'] += 10
        with self.assertRaisesRegex(ValueError, 'current gradient'):
            bind_reducers(snapshot)

    def test_rebinding_does_not_collapse_parameter_versions(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells
        from trainverify.runtime_source_authority import bind_reducers, tensor_export_id
        world, cells, sources = reducer_fixture()
        snapshot = export_expanded_cells(world, cells, rank_sources=sources)
        param = deepcopy(next(t for t in snapshot['tensors'] if t.get('placement', {}).get('is_param')))
        param['ref']['version'] = 7
        param['export_id'] = tensor_export_id(param['ref'])
        snapshot['tensors'].append(param)
        with self.assertRaisesRegex(ValueError, 'ambiguous parameter'):
            bind_reducers(snapshot)

    def test_source_parameter_map_and_unsupported_world_rejected(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells
        world, cells, sources = reducer_fixture()
        for bad_world in (replace(world, num_pp=2), replace(world, num_mb=2), replace(world, plan_ndevs=3)):
            with self.subTest(world=bad_world), self.assertRaisesRegex(ValueError, 'not-supported'):
                export_expanded_cells(bad_world, cells, rank_sources=sources)
        bad_sources = {r: text.replace("'position.weight'", "'wrong.weight'") for r, text in sources.items()}
        with self.assertRaisesRegex(ValueError, 'parameter full map'):
            export_expanded_cells(world, cells, rank_sources=bad_sources)

    def test_builder_copy_loses_ir_and_requires_actual_scaled_reducer_source(self):
        from copy import copy
        from nnscaler_backend.runtime_source_authority import export_expanded_cells
        world, cells, sources = reducer_fixture()
        irs = {(c.rank, c.ir.cid): c.ir for c in cells if c.ir is not None}
        for i, cell in enumerate(cells):
            if cell.ir is not None:
                replacement = copy(cell)
                self.assertIsNone(replacement.ir)
                replacement._input_irs = cell._input_irs
                replacement._wred_wid = cell._wred_wid
                cells[i] = replacement
        with self.assertRaisesRegex(ValueError, 'missing reducer IR'):
            export_expanded_cells(world, cells, rank_sources=sources)
        snapshot = export_expanded_cells(world, cells, rank_sources=sources, reducer_irs=irs)
        self.assertEqual(snapshot['reducer_binding'], 'complete')

    def test_identity_only_cannot_claim_collective_completeness(self):
        from nnscaler_backend.runtime_source_authority import export_expanded_cells
        from trainverify.runtime_source_authority import validate_snapshot
        world, cells, _ = reducer_fixture()
        snapshot = export_expanded_cells(world, cells)
        self.assertEqual(snapshot['completeness']['status'], 'incomplete')
        self.assertIn('parameter-reducers', snapshot['completeness']['missing'])
        snapshot['reducer_binding'] = 'complete'
        with self.assertRaises(ValueError):
            validate_snapshot(snapshot)


if __name__ == '__main__':
    unittest.main()
