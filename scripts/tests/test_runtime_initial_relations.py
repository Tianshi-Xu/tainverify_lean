"""Join actual parameter observation DTOs to independently retraced targets."""
import copy
from dataclasses import asdict, replace
import importlib
import importlib.util

import pytest

from Verdict import graph_to_lean as c
from Verdict.runtime_lineage import Role, trace
from scripts.tests.test_runtime_parameter_inputs import observation, bind as observe
from scripts.tests.test_graph_to_lean_runtime_lineage import fixture


def setup(copies=False, uneven=False):
    sm, pm, actuals, sources, reference = observation()
    if copies or uneven:
        for cell in pm.cells:
            if cell.opname != 'FW_embedding':
                continue
            bounds = (0, 6) if copies else ((0, 2), (2, 6))[cell.rank % 2]
            for ref, ir in [(cell.inputs[1], cell._input_irs[1]), (cell.outputs[0], cell._output_irs[0])]:
                ir.indmap = (*ir.indmap[:-1], bounds)
                ir.shape = tuple(b-a for a, b in ir.indmap)
                pm.shapes[ref] = ir.shape
            rank = cell.rank
            a, b = bounds
            actuals['pm'][rank]['initialized']['weight_20'] = reference['state']['weight'][:, a:b].clone()
            actuals['pm'][rank]['metadata']['weight_20']['slicers'][1] = [a, b, None]
            old = 'slice(0, 3, None)' if rank % 2 == 0 else 'slice(3, 6, None)'
            sources['pm'][rank] = sources['pm'][rank].replace(old, f'slice({a}, {b}, None)')
    parameters = observe(sm, pm, actuals, sources, reference)
    _, _, authority = fixture(2, 2)
    if copies or uneven: authority = (authority[0], copy.deepcopy(pm.cells), *authority[2:])
    sv, pv = c._lower_runtime_graphs(sm, pm)
    lineages, _, validation = trace(sv, pv, *authority)
    return sv, pv, parameters, lineages, validation


def compiler():
    assert importlib.util.find_spec('Verdict.runtime_initial_relations') is not None, 'initial relation binding compiler missing'
    return importlib.import_module('Verdict.runtime_initial_relations').bind


def test_actual_parameter_format_binds_original_dp_unit_targets():
    sv, pv, parameters, lineages, validation = setup()
    result = compiler()(sv, pv, parameters, lineages, validation)
    assert result['status'] == 'initial-parameter-relations-bound'
    assert len(result['relations']) == 1
    relation = result['relations'][0]
    assert relation['lineage'] == asdict(lineages[2])
    assert relation['sm_binding'] == parameters['bindings'][0]
    assert [[b['rank'] for b in u['bindings']] for u in relation['units']] == [[0, 1], [2, 3]]
    assert [u['initial_goal']['pm_tids'] for u in relation['units']] == [
        [p.endpoint.tid for p in u.pieces] for u in lineages[2].units]
    assert relation['units'][0]['initial_goal'] == dict(kind='sharded', sm_tid=lineages[2].target.tid,
        pm_tids=[p.endpoint.tid for p in lineages[2].units[0].pieces], dim=1,
        sm_shape=[32, 6], pm_shape=[32, 3])
    assert result['unbound_parameter_refs'] == []
    for flag in ('proof_admissible', 'public_complete', 'kernel_value_proved', 'torch_refinement'):
        assert result[flag] is False
    assert result['unproved_value_obligations'] == ['initial-parameter-value-equality-unproved']

@pytest.mark.parametrize('fault', ['wrong-group', 'cross-dp-gather', 'version', 'parent', 'logical',
    'slice', 'sm-ref', 'tid', 'runtime-name', 'omit-binding', 'duplicate', 'omit-target',
    'unit-order', 'piece-order', 'coordinated-permutation', 'bool-unit', 'plain-validation',
    'stale-raw', 'stale-source', 'stale-topology', 'proof-flag'])
def test_rejects_forged_evidence_or_targets_against_live_authority(fault):
    sv, pv, parameters, lineages, validation = setup()
    target = lineages[2]; unit = target.units[0]
    row = parameters['bindings'][1]
    if fault == 'wrong-group': target = replace(target, units=(replace(unit, unit=1), *target.units[1:]))
    elif fault == 'cross-dp-gather': target = replace(target, units=(replace(unit, pieces=tuple(p for u in target.units for p in u.pieces)),))
    elif fault == 'unit-order': target = replace(target, units=tuple(reversed(target.units)))
    elif fault == 'piece-order': target = replace(target, units=(replace(unit, pieces=tuple(reversed(unit.pieces))), *target.units[1:]))
    elif fault == 'bool-unit': target = replace(target, units=(replace(unit, unit=False), *target.units[1:]))
    elif fault == 'version': row['ref'][-1] = 1
    elif fault == 'parent': row['parent_tid'] += 1
    elif fault == 'logical': row['logical_name'] = 'other'
    elif fault == 'slice': row['bounds'][1] = [3, 6]
    elif fault == 'sm-ref': row['sm_ref'][-1] = 1
    elif fault == 'tid': row['tid'] += 1
    elif fault == 'runtime-name': row['runtime_name'] = 'weight_999'
    elif fault == 'omit-binding': parameters['bindings'].pop()
    elif fault == 'duplicate': parameters['bindings'].append(copy.deepcopy(row))
    elif fault == 'omit-target': lineages = tuple(l for l in lineages if l.role != Role.PARAMETER)
    elif fault == 'plain-validation': validation = dict(validation)
    elif fault == 'stale-raw': validation._inputs[1][1]._input_irs[1].parent.name = 'other'
    elif fault == 'stale-source': validation._inputs[2]['rank_sources']['0'] = 'class GenModel: pass'
    elif fault == 'stale-topology': pv.W.plan_ndevs = 4
    elif fault == 'proof-flag': parameters['proof_admissible'] = True
    else:
        # Change target ownership AND evidence together; identical replicas do
        # not authorize replacing ranks0/1 with ranks2/3 in DP unit0.
        target = replace(target, units=(replace(unit, pieces=target.units[1].pieces),
            replace(target.units[1], pieces=unit.pieces)))
        parameters['bindings'][1:3], parameters['bindings'][3:5] = parameters['bindings'][3:5], parameters['bindings'][1:3]
    if fault != 'omit-target': lineages = (*lineages[:2], target, *lineages[3:])
    with pytest.raises(ValueError): compiler()(sv, pv, parameters, lineages, validation)


def test_replicated_parameters_are_copy_relations_not_allgather():
    args = setup(copies=True)
    result = compiler()(*args)
    relation, = result['relations']
    assert relation['lineage']['units'][0]['reconstruction'] == 'tp-copy-obligation'
    for unit in relation['units']:
        goal = unit['initial_goal']
        assert goal['kind'] == 'replicated'
        assert goal['dim'] is None
        assert goal['pm_shape'] == goal['sm_shape'] == [32, 6]
        assert goal['pm_tids'] == [b['tid'] for b in unit['bindings']]


def test_unequal_pieces_cannot_be_mislabeled_as_uniform_typed_shards():
    with pytest.raises(ValueError, match='uniform'):
        compiler()(*setup(uneven=True))
