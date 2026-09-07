"""Exercise real nnScaler segment/adapter/scale APIs, on CPU without captures."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT), str(ROOT / 'Verdict')]


def source_fixture(plan=2, runtime=6):
    import torch
    from nnscaler.ir.tensor import IRFullTensor
    from nnscaler.ir.cten import IRCell
    from nnscaler.ir.adapter import IRAdapter
    from nnscaler.ir.adapter.prim import AllToAllAllToAllPrim
    from nnscaler.graph.graph import IRGraph, IRSegment
    from nnscaler.execplan.execplan import ExecutionPlan, ExeReuseCell
    from nnscaler.codegen.module.module import ModuleCodeGen
    from verdict.graph import World, WType

    nodes, sequence, leaves = [], [], {}
    for rank in range(plan):
        x = IRFullTensor((8, 8), name='x', dtype=torch.float32, requires_grad=True).tosub()
        y = IRFullTensor((8, 8), name='y', dtype=torch.float32, requires_grad=True).tosub()
        x.grad = x.parent.grad.tosub()
        y.grad = y.parent.grad.tosub()
        fw, bw = IRAdapter([x], [y]), IRAdapter([y.grad], [x.grad])
        for adapter in (fw, bw):
            adapter.device = [rank]
            adapter.prims = [AllToAllAllToAllPrim(adapter.inputs(), adapter.outputs(),
                                                 ranks=list(reversed(range(plan))), idim=0, odim=1)]
            adapter.differentiable = True
        IRCell.make_pair(fw, bw)
        fseg = IRSegment([fw], [x], [y], 'forward')
        bseg = IRSegment([bw], [y.grad], [x.grad], 'backward')
        IRCell.make_pair(fseg, bseg)
        nodes.extend([fseg, bseg])
        sequence.extend([fseg, bseg, ExeReuseCell(fseg, fseg.inputs(), fseg.outputs()),
                         ExeReuseCell(bseg, bseg.inputs(), bseg.outputs())])
        leaves[rank] = (fw, bw)
    graph = IRGraph(nodes, [], [], 'scaling_fixture')
    mg = ModuleCodeGen(ExecutionPlan(graph, sequence), runtime_ndevs=runtime)
    world = World(wtype=WType.P, plan_ndevs=plan, runtime_ndevs=runtime,
                  num_pp=1, num_tp=plan, num_dp=runtime // plan, num_mb=2)
    return world, mg, leaves


class BackwardSourceScalingTests(unittest.TestCase):
    def test_backward_segment_uses_actual_leaf_scale_in_every_unit(self):
        from nnscaler_backend.build_graph import _prepare_rank_cells
        for plan, runtime in ((2, 6), (3, 6), (1, 3)):
            world, mg, leaves = source_fixture(plan, runtime)
            before = {r: [deepcopy(a.prims[0].kwargs) for a in pair]
                      for r, pair in leaves.items()}
            for rank in range(runtime):
                cells = _prepare_rank_cells(world, mg, rank)
                self.assertEqual(len(cells), 4)
                for c, (mb, forward) in zip(cells, ((0, True), (0, False), (1, True), (1, False))):
                    leaf = leaves[rank % plan][0 if forward else 1]
                    expected = mg.scale(leaf, rank)
                    with self.subTest(plan=plan, runtime=runtime, rank=rank, forward=forward, mb=mb):
                        self.assertEqual({k: v for k, v in c.ir.kwargs.items() if k != '__consts'},
                                         {k: v for k, v in expected.prims[0].kwargs.items() if k != '__consts'})
                        self.assertEqual(c.adapter.isfw(), forward)
                        self.assertEqual((c.node.cid, c.mb, c.node.mb), (leaf.cid, mb, mb))
                        self.assertEqual([t.tid for t in c._input_irs], [t.tid for t in leaf.inputs()])
                        self.assertEqual([t.tid for t in c._output_irs], [t.tid for t in leaf.outputs()])
                with self.subTest(source_unmodified=True, rank=rank):
                    self.assertEqual(before, {r: [a.prims[0].kwargs for a in pair]
                                              for r, pair in leaves.items()})

    def test_transport_leaf_metadata_and_sequence_survive_expansion(self):
        from nnscaler.ir.adapter import IRAdapter
        from nnscaler.ir.adapter.prim import MovePrim, BroadcastPrim
        from nnscaler.graph.graph import IRSegment
        from nnscaler_backend.build_graph import (
            Cell, _flatten_exereuse_then_scale, _set_mb, _flatten_segment,
            _flatten_adapter, _set_node_SSA,
        )
        world, mg, leaves = source_fixture()
        for forward in (True, False):
            leaf = leaves[0][0 if forward else 1]
            adapter = IRAdapter(leaf.inputs(), leaf.outputs())
            adapter.device = [0]
            adapter.prims = [
                MovePrim(adapter.inputs(), adapter.outputs(), shape=(8, 8),
                         dtype='torch.float32', src=0, dst=1),
                BroadcastPrim(adapter.inputs(), adapter.outputs(), shape=(8, 8),
                              dtype='torch.float32', src=0, ranks=[1, 0]),
            ]
            segment = IRSegment([adapter, leaf], adapter.inputs(), leaf.outputs())
            if not forward:
                from nnscaler.ir.cten import IRCell
                fw = leaves[0][0]
                IRCell.make_pair(IRSegment([fw], fw.inputs(), fw.outputs()), segment)
            before = deepcopy([p.kwargs for p in adapter.prims])
            for rank in range(world.runtime_ndevs):
                expanded = _flatten_exereuse_then_scale([segment, segment], mg, rank)
                cells = _set_mb([Cell(ir, rank, world.wtype) for ir in expanded])
                cells = _set_node_SSA(_flatten_adapter(_flatten_segment(cells, mg)))
                expected = mg.scale(adapter, rank).prims + mg.scale(leaf, rank).prims
                self.assertEqual([type(c.ir) for c in cells], [type(p) for p in expected] * 2)
                self.assertEqual([c.ir.kwargs for c in cells], [p.kwargs for p in expected] * 2)
                self.assertEqual([c.mb for c in cells], [0, 0, 0, 1, 1, 1])
                self.assertEqual([c.node.cid for c in cells], [adapter.cid, adapter.cid, leaf.cid] * 2)
                self.assertTrue(all(c.adapter.isfw() == forward for c in cells))
                self.assertEqual([p.kwargs for p in adapter.prims], before)


if __name__ == '__main__':
    unittest.main()
