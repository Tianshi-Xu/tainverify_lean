"""Portable source adapters; generated Lean remains UNCOMPILED until parent build."""
import importlib
import importlib.util
from dataclasses import replace

import pytest

from Verdict.runtime_initial_relations import bind
from Verdict.runtime_lineage import Role, _Index
from scripts.tests.test_runtime_embedding_routes import adapter_fixture, discover


def api():
    assert importlib.util.find_spec('Verdict.runtime_embedding_position_units'), 'position unit renderer missing'
    return importlib.import_module('Verdict.runtime_embedding_position_units').render


def prepared(D=2, T=2, seqlen=2):
    sm, pm, authority = adapter_fixture(D, T, seqlen)
    sm, pm, lineages, validation, _ = discover(sm, pm, authority)
    # Structural observation DTO only: no tensor-value claim and no new capture.
    bindings = []
    for world, view, raw in [('sm', sm, authority[0]), ('pm', pm, authority[1])]:
        index = _Index(view, raw)
        for lineage in lineages:
            if lineage.role != Role.PARAMETER:
                continue
            endpoints = [lineage.target] if world == 'sm' else [
                p.endpoint for u in lineage.units for p in u.pieces]
            for ep in endpoints:
                meta = index.meta[ep.ref]
                bindings.append(dict(world=world, rank=ep.ref[1], ref=list(ep.ref), tid=ep.tid,
                    sm_ref=list(lineage.target.ref), logical_name=meta[0], parent_tid=ep.ref[3],
                    full_shape=list(meta[1]), bounds=[list(b) for b in meta[2]],
                    value_part=list(meta[3]), shape=list(ep.shape), runtime_name=f'weight_{ep.ref[3]}'))
    parameters = dict(status='current-run-parameter-values-validated', bindings=bindings,
        proof_admissible=False, kernel_value_proved=False, torch_refinement=False)
    return sm, pm, lineages, validation, bind(sm, pm, parameters, lineages, validation)


@pytest.mark.parametrize('D,T,seqlen', [(2, 2, 2), (3, 2, 2), (2, 1, 2), (2, 3, 6)])
def test_source_connected_position_units(D, T, seqlen):
    args = prepared(D, T, seqlen)
    text, detail = api()(*args)
    assert len(detail['units']) == D
    assert text.count('fw_embedding_dp_tp_position_unit_facts_of_source_eqs') == D
    assert detail['status'] == 'source-embedding-position-unit-values-emitted-uncompiled'
    assert detail['lean_bytes'] == len(text.encode())
    assert 'UNCOMPILED' in text
    for flag in ('kernel_value_proved', 'proof_admissible', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for row in detail['units']:
        assert row['dimensions']['T'] == T and row['dimensions']['S'] == seqlen // T
        assert len(row['pm_output_tids']) == T
        u = row['unit']; out = row['sm_output_tid']; ids = row['sm_input_tid']
        header = (f'theorem embeddingPositionUnit_{out}_{u} (s p t q : Store)\n'
            '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)\n'
            '    (h : InitialParameterValues s p) :\n'
            f'    chunkPrimDimN 0 {D} {u} (t {out}) =\n'
            f'    allGatherPrimDimN 2 {T} 0 [' + ', '.join(f'q {t}' for t in row['pm_output_tids']) + '] := by')
        assert header in text
        assert f'.chunk_values {u} (by change {u} < {D}; decide)' in text
        assert f'embeddingRouteRead_sm_{out} s t hs' in text
        for lane in row['input_lanes']:
            assert f'inputStoreRelation_{ids}_{lane} s p t q hs hp' in text
        for tid in row['pm_chunk_tids'] + row['pm_embedding_tids'] + row['pm_output_tids']:
            assert f'embeddingRouteRead_pm_{tid} p q hp' in text
        assert len(row['routes']) == T
        for rank in row['routes']:
            assert [p[1] for p in rank['exchange']['peers']] == row['pm_embedding_tids']
    for phrase in ('TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn', 'chunkPrimDimN_shape',
        'RelationCompiler.ReplicatedRel', 'weights.replica_values', 'weights.full_shape',
        'initialParameterValues_final s p t q hs hp h', 'List.Forall₂.cons', 'List.ofFn',
        'change [', '#print axioms embeddingPositionUnit_'):
        assert phrase in text
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom embedding', 'hactivation', 'hshape :'):
        assert forbidden not in text


@pytest.mark.parametrize('fault', ['weight-order', 'weight-ref', 'weight-shape', 'weight-parent',
    'weight-goal', 'weight-sm', 'weight-bool', 'bound-unit', 'bound-unit-bool', 'bound-lineage',
    'bound-status', 'input-unit', 'lineage-shape', 'peer-order', 'layout', 'group',
    'stale-raw', 'stale-source', 'plain-validation'])
def test_wrong_binding_or_live_identity_fails_closed(fault):
    sm, pm, lineages, validation, bound = prepared()
    relation = bound['relations'][-1]
    unit = relation['units'][0]
    if fault == 'weight-order': unit['bindings'].reverse()
    elif fault == 'weight-ref': unit['bindings'][0]['ref'][-1] += 1
    elif fault == 'weight-shape': unit['bindings'][0]['shape'][-1] += 1
    elif fault == 'weight-parent': unit['bindings'][0]['parent_tid'] += 1
    elif fault == 'weight-goal': unit['initial_goal']['pm_tids'].reverse()
    elif fault == 'weight-sm': relation['sm_binding']['tid'] += 1
    elif fault == 'weight-bool': unit['bindings'][0]['ref'][1] = False
    elif fault == 'bound-unit': unit['unit'] = 1
    elif fault == 'bound-unit-bool': unit['unit'] = False
    elif fault == 'bound-lineage': relation['lineage']['target']['tid'] += 1
    elif fault == 'bound-status': bound['status'] = 'saved-receipt'
    elif fault == 'input-unit':
        ids = lineages[1]
        lineages = (lineages[0], replace(ids, units=tuple(reversed(ids.units))), *lineages[2:])
    elif fault == 'lineage-shape':
        ids = lineages[1]
        lineages = (lineages[0], replace(ids, target=replace(ids.target, shape=(2, 99))), *lineages[2:])
    elif fault == 'peer-order':
        node = next(iter(pm.collective_scopes))
        pm._node2inputs[node].reverse()
    elif fault == 'layout':
        node = next(iter(pm.collective_scopes))
        pm.collective_scopes[node] = replace(pm.collective_scopes[node], params=(2, 1))
    elif fault == 'group':
        node = next(iter(pm.chunk_scopes))
        pm.chunk_scopes[node] = replace(pm.chunk_scopes[node], ranks=(2, 3))
    elif fault == 'stale-raw':
        cell = next(c for c in validation._inputs[1] if c.node.cid == 13)
        cell.inputs.reverse()
    elif fault == 'stale-source': validation._inputs[2]['rank_sources']['0'] = 'class GenModel: pass'
    else: validation = dict(validation)
    with pytest.raises(ValueError):
        api()(sm, pm, lineages, validation, bound)


def test_real_opname_enum_matches_string_fixture():
    from verdict.operators import OpName
    args = prepared()
    expected = api()(*args)
    for raw in args[3]._inputs[:2]:
        for cell in raw:
            if cell.opname == 'FW_embedding':
                cell.opname = OpName.FW_embedding
    assert api()(*args) == expected


def test_projection_follows_bound_spec_order_not_unit_index():
    sm, pm, lineages, validation, bound = prepared(3, 2)
    bound['relations'].reverse()
    bound['relations'][0]['units'].reverse()
    text, detail = api()(sm, pm, lineages, validation, bound)
    assert [u['spec_index'] for u in detail['units']] == [2, 1, 0]
    bodies = text.split('theorem embeddingPositionUnitFacts_')[1:]
    for body, projection in zip(bodies, ['hrels.2.2.1', 'hrels.2.1', 'hrels.1'], strict=True):
        assert f':= {projection}\n' in body


def test_each_call_reauthenticates_and_preserves_raw_refs_and_order():
    from Verdict.runtime_embedding_routes import census
    args = prepared()
    before = census(*args[:4])
    text, detail = api()(*args)
    from dataclasses import asdict
    complex_routes = [r for r in before.routes if r.ranks[0].chunk is not None]
    for record, route in zip(detail['units'], complex_routes, strict=True):
        assert record['routes'] == [asdict(r) for r in route.ranks]
        assert record['global_embedding'] == asdict(route.global_embedding)
    assert api()(*args) == (text, detail)
    args[3]._inputs[2]['rank_sources']['0'] = 'class GenModel: pass'
    with pytest.raises(ValueError):
        api()(*args)
