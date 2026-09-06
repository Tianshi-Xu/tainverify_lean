"""Exercise the real translator's dispatch against installed nnScaler classes."""
from types import SimpleNamespace
import pytest


@pytest.mark.parametrize('name,forward,expected', [
    ('ReduceScatterAllGatherPrim', True, 'ReduceScatterPrim'),
    ('ReduceScatterAllGatherPrim', False, 'AllGatherPrim'),
    ('AllGatherReduceScatterPrim', True, 'AllGatherPrim'),
    ('AllGatherReduceScatterPrim', False, 'ReduceScatterPrim'),
])
def test_fused_adapter_direction(name, forward, expected):
    pytest.importorskip('nnscaler')
    from Verdict.nnscaler_backend.build_graph import _set_node_opname, PTypes, OpName
    # Dispatch reads the real primitive's type and adapter direction only.
    primitive = object.__new__(getattr(PTypes, name))
    cell = SimpleNamespace(ir=primitive, adapter=SimpleNamespace(isfw=lambda: forward))
    assert _set_node_opname([cell])[0].opname is getattr(OpName, expected)


def test_reduce_scatter_collects_actual_inputs_from_every_rank():
    pytest.importorskip('nnscaler')
    from Verdict.nnscaler_backend.build_graph import (
        _set_collective_group_id, _fuse_collective_inputs, OpName, World,
    )
    from collections import namedtuple
    Tensor = namedtuple('Tensor', 'rank tid')
    cells = [SimpleNamespace(
        opname=OpName.ReduceScatterPrim, node=SimpleNamespace(cid=17), rank=rank,
        mb=0, inputs=[Tensor(rank, 100+rank)],
        _input_irs=[SimpleNamespace(indmap=((0, 8),))],
        _collective_group_id=None, _collective_indmap={},
    ) for rank in range(2)]
    world = World(plan_ndevs=2, runtime_ndevs=2, num_tp=2, num_pp=1, num_dp=1)
    _set_collective_group_id(cells, world)
    fused, _ = _fuse_collective_inputs(cells)
    assert all([(t.rank, t.tid) for t in c.inputs] == [(0, 100), (1, 101)] for c in fused)
