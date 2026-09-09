"""Complete ordinary worlds use the same authenticated input-request evaluator."""
from scripts.tests.test_runtime_scoped_prefix import collective_world, proof_text


def test_sm_without_collectives_gets_whole_fold_not_an_unavailable_prefix(tmp_path):
    fed = collective_world(tmp_path, 2)
    sm = fed.receipt['scoped_prefix']['sm']
    assert sm['status'] == 'ordinary-fold-emitted'
    assert sm['prefix_nodes'] == fed.receipt['execution_order']['sm']['execution_to_source']
    assert sm['frontier'] is None
    assert sm['kernel_checked'] is False
    text = proof_text(fed)
    for suffix in ('Success', 'Frame'):
        assert 'smWhole' + suffix in sm['kernel_checks']
    assert 'smDenoteWithInputs init = some (smWholeState init)' in text
    assert 'stepWithInputs smGraph' in text
    assert fed.receipt['proof_admissible'] is False


def test_ordinary_fold_does_not_hide_an_unknown_request(tmp_path):
    from Verdict import graph_to_lean as c
    from Verdict.runtime_world import render
    from Verdict.runtime_input_feed import bind
    from scripts.tests.test_graph_to_lean_runtime_lineage import fixture
    from scripts.tests.test_runtime_input_feed import observed
    sm, pm, _ = fixture(1, 2)
    sm.cells[1].opname = 'FW_dropout'
    sm.cells[1].kwargs = {}
    sv, pv = c._lower_runtime_graphs(sm, pm)
    world = render(sv, pv, sm.cells, pm.cells)
    fed = bind(world, sv, pv, sm.cells, pm.cells, *observed(tmp_path, 1, 2), tmp_path)
    assert fed.receipt['scoped_prefix']['sm']['status'] == 'prefix-proof-unavailable'
    text = proof_text(fed)
    assert 'smNode_1_blocked' in text
    assert 'smWholeSuccess' not in text
    assert fed.receipt['sm_nodes'] == 2
    assert fed.receipt['proof_admissible'] is False


def test_ordinary_fold_requires_each_loader_payload():
    from Verdict import graph_to_lean as c
    from Verdict.runtime_world import render
    from Verdict.runtime_ordinary_fold import render as total
    from scripts.tests.test_graph_to_lean_runtime_lineage import fixture
    sm, pm, _ = fixture(1, 2)
    sv, pv = c._lower_runtime_graphs(sm, pm)
    world = render(sv, pv, sm.cells, pm.cells)
    text, detail = total('sm', sv, world, [])
    assert text == ''
    assert detail['status'] == 'prefix-proof-unavailable'
