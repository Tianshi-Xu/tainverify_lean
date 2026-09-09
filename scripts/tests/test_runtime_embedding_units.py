"""Connected source embedding unit values; generated Lean awaits parent kernel build."""
import importlib
import importlib.util

from scripts.tests.test_runtime_initial_relations import setup, compiler
from Verdict.runtime_lineage import Role
from dataclasses import replace
import pytest


def api():
    assert importlib.util.find_spec('Verdict.runtime_embedding_units'), 'embedding unit renderer missing'
    return importlib.import_module('Verdict.runtime_embedding_units').render


def prepared():
    sm, pm, parameters, lineages, validation = setup()
    return sm, pm, lineages, compiler()(sm, pm, parameters, lineages, validation)


def test_source_connected_two_dp_units():
    sm, pm, lineages, bound = prepared()
    text, detail = api()(sm, pm, lineages, bound)
    activation = next(l for l in lineages if l.role == Role.ACTIVATION)
    ids = next(l for l in lineages if l.role == Role.BATCH)
    assert len(detail['units']) == 2
    assert text.count('fw_embedding_dp_tp_unit_of_source_eqs') == 2
    for i, unit in enumerate(activation.units):
        outs = [p.endpoint.tid for p in unit.pieces]
        weights = bound['relations'][0]['units'][i]['initial_goal']['pm_tids']
        row = detail['units'][i]
        assert row['unit'] == i and row['spec_index'] == i
        assert row['pm_output_tids'] == outs and row['pm_weight_tids'] == weights
        assert f'chunkPrimDimN 0 2 {i} (t {activation.target.tid}) =\n    allGatherPrimDimN 2 2 0 [' in text
        for lane, piece in enumerate(unit.pieces):
            assert f'embeddingRead_{piece.endpoint.tid} p q hp' in text
            assert f'inputStoreRelation_{ids.target.tid}_{lane} s p t q hs hp' in text
        assert f'(h : InitialParameterValues s p)' in text
    assert 'initialParameterValues_final s p t q hs hp h' in text
    assert 'initialParameterRelations_of_values t q' in text
    assert 'hrels.1' in text and 'hrels.2' in text
    assert '.shard_shapes' in text and '.full_value' in text and '.chunk_values' in text
    assert '(s p t q : Store)' in text
    assert '.chunk_values 0 (by change 0 < 2; decide)' in text
    assert '.chunk_values 1 (by change 1 < 2; decide)' in text
    assert detail['lean_bytes'] == len(text.encode('utf-8'))
    assert detail['status'] == 'source-embedding-unit-values-emitted-uncompiled'
    for flag in ('kernel_value_proved', 'proof_admissible', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False


@pytest.mark.parametrize('fault', ['copy', 'sequence', 'input-unit-order', 'bool-unit',
    'wrong-unit', 'wrong-weight', 'wrong-ids', 'wrong-output-ref', 'wrong-goal',
    'cross-dp-gather', 'offset', 'goal-shape'])
def test_rejects_wrong_layout_unit_or_original_operand_mapping(fault):
    sm, pm, lineages, bound = prepared()
    activation = lineages[-1]
    unit = activation.units[0]
    if fault == 'copy':
        unit = replace(unit, reconstruction='tp-copy-obligation')
    elif fault == 'sequence':
        unit = replace(unit, reconstruction='tp-axis-gather:1')
    elif fault == 'input-unit-order':
        lineages = (replace(lineages[0], units=tuple(reversed(lineages[0].units))), *lineages[1:])
    elif fault == 'bool-unit':
        unit = replace(unit, unit=False)
    elif fault == 'wrong-unit':
        unit = replace(unit, pieces=activation.units[1].pieces)
    elif fault == 'cross-dp-gather':
        unit = replace(unit, pieces=tuple(p for u in activation.units for p in u.pieces))
    elif fault == 'wrong-output-ref':
        p = unit.pieces[0]
        unit = replace(unit, pieces=(replace(p, endpoint=replace(p.endpoint,
            ref=(*p.endpoint.ref[:-1], 99))), *unit.pieces[1:]))
    elif fault in ('wrong-weight', 'wrong-ids', 'offset'):
        # Mutate the live original source view, retaining identical operand shapes.
        cell = next(c for c in pm.source.cells if c.opname == 'FW_embedding')
        if fault == 'offset':
            cell.kwargs['start'] = 1
        elif fault == 'wrong-ids':
            pm.node_inputs(cell.node)[0] = pm._lowered[cell.inputs[0]._replace(tid=11)]
        else:
            pm.node_inputs(cell.node)[1] = pm._lowered[cell.inputs[1]._replace(rank=2)]
    elif fault == 'goal-shape':
        bound['relations'][0]['units'][0]['initial_goal']['pm_shape'] = [32, 99]
    else:
        bound['relations'][0]['units'][0]['initial_goal']['pm_tids'].reverse()
    lineages = (*lineages[:-1], replace(activation, units=(unit, *activation.units[1:])))
    with pytest.raises(ValueError):
        api()(sm, pm, lineages, bound)


def test_rejects_actual_copied_embedding_layout():
    sm, pm, params, lineages, validation = setup(copies=True)
    bound = compiler()(sm, pm, params, lineages, validation)
    with pytest.raises(ValueError, match='unsupported.*hidden'):
        api()(sm, pm, lineages, bound)


def test_canonical_feed_entry_connects_units_and_keeps_compaction_lossless(tmp_path):
    from Verdict.runtime_initial_relations import attach
    from Verdict.runtime_relation_source import expand
    from Verdict.runtime_world import _proof_bundle
    from scripts.tests.test_runtime_input_relations import fed
    original, _ = fed(tmp_path)
    sm, pm, parameters, lineages, validation = setup()
    result = attach(original, sm, pm, parameters, lineages, validation)
    assert result.supporting_sources == original.supporting_sources
    assert len(result.receipt['embedding_units']['units']) == 2
    text = expand(result.lean)
    assert text.count('theorem embeddingUnit_') == 2
    assert 'initialParameterValues_final s p t q hs hp h' in text
    assert result.receipt['proof_bundle'] == _proof_bundle(result.lean, result.supporting_sources)
    assert not result.receipt['public_complete'] and not result.receipt['proof_admissible']


def test_lineage_order_is_not_operand_identity():
    sm, pm, lineages, bound = prepared()
    expected = api()(sm, pm, lineages, bound)
    assert api()(sm, pm, tuple(reversed(lineages)), bound) == expected


def test_spec_projection_uses_bound_order_not_dp_unit_index():
    sm, pm, lineages, bound = prepared()
    bound['relations'][0]['units'].reverse()
    text, detail = api()(sm, pm, lineages, bound)
    assert [u['spec_index'] for u in detail['units']] == [1, 0]
    theorem0, theorem1 = text.split('theorem embeddingUnit_')[1:]
    assert ':= hrels.2' in theorem0 and ':= hrels.1' in theorem1
