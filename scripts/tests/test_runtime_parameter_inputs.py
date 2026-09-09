"""Current-run parameter equality needs exact values AND original fullrefs."""
import copy
import torch
import pytest
from Verdict import graph_to_lean as c
from scripts.tests.test_graph_to_lean_runtime_lineage import fixture, IR


def observation():
    sm, pm, _ = fixture(2, 2)
    sm.W.runtime_ndevs = 1
    full = torch.arange(192, dtype=torch.float32).reshape(32, 6)
    actuals = {}; sources = {}
    for label, graph in [('sm', sm), ('pm', pm)]:
        actuals[label] = []; sources[label] = {}
        for rank in range(graph.W.runtime_ndevs):
            cell = next(x for x in graph.cells if x.rank == rank and x.opname == 'FW_embedding')
            ir = cell._input_irs[1]; bounds = ir.indmap
            slices = ', '.join(f'slice({a}, {b}, None)' for a, b in bounds)
            sources[label][rank] = ('class GenModel:\n'
                f'    rank = {rank}\n    world_size = {graph.W.runtime_ndevs}\n'
                '    def __init__(self):\n'
                "        self.register_parameter('weight_20', None)\n"
                f"        self.add_full_map('weight_20', 20, True, 'weight', (32, 6), ({slices}), 1)\n")
            actuals[label].append(dict(metadata={'weight_20':dict(orig_name='weight', shape=[32,6],
                slicers=[[a,b,None] for a,b in bounds], val_chunks=1)},
                initialized={'weight_20':full[tuple(slice(a,b) for a,b in bounds)].clone()}))
    return sm, pm, actuals, sources, {'state': {'weight': full}}


def bind(sm, pm, actuals, sources, reference):
    from Verdict.runtime_parameter_inputs import validate
    sv, pv = c._lower_runtime_graphs(sm, pm)
    return validate(sv, pv, sm.cells, pm.cells, actuals, reference, sources)


def test_current_parameter_values_bind_all_original_fullrefs():
    result = bind(*observation())
    assert result['status'] == 'current-run-parameter-values-validated'
    assert len(result['bindings']) == 5
    assert len({tuple(r['ref']) for r in result['bindings']}) == 5
    assert result['kernel_value_proved'] is False
    assert result['proof_admissible'] is False


@pytest.mark.parametrize('fault', ['value', 'swap', 'wrong-owner', 'metadata'])
def test_parameter_binding_rejects_equal_shape_or_equal_value_forgeries(fault):
    sm, pm, actuals, sources, reference = observation()
    if fault == 'value': actuals['pm'][0]['initialized']['weight_20'][0,0] += 1
    elif fault == 'swap': actuals['pm'][0]['initialized']['weight_20'] = actuals['pm'][1]['initialized']['weight_20'].clone()
    elif fault == 'metadata': actuals['pm'][0]['metadata']['weight_20']['slicers'][1] = [3,6,None]
    else:
        # Rank2 has exactly the same shard values as rank0, but is not its ref.
        cell = next(x for x in pm.cells if x.rank == 0 and x.opname == 'FW_embedding')
        cell.inputs[1] = cell.inputs[1]._replace(rank=2)
    with pytest.raises(ValueError): bind(sm, pm, actuals, sources, reference)
