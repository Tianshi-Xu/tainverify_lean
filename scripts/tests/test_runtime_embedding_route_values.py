"""Original-authority route reads; generated Lean is deliberately UNCOMPILED."""
import copy
import importlib.util
from dataclasses import replace
import json
from collections import Counter

import pytest

from Verdict.runtime_schedule import build
from scripts.tests.test_runtime_embedding_routes import adapter_fixture, discover


def setup(units=2, tp=2):
    sm, pm, authority = adapter_fixture(units, tp)
    sv, pv, ls, validation, _ = discover(sm, pm, authority)
    return sv, pv, ls, validation, {'sm': build(sv), 'pm': build(pv)}


def renderer():
    assert importlib.util.find_spec('Verdict.runtime_embedding_route_values'), 'missing route value renderer'
    from Verdict.runtime_embedding_route_values import render
    return render


@pytest.mark.parametrize('units,tp', [(2, 2), (3, 2), (2, 1)])
def test_original_complex_reads_only(units, tp):
    args = setup(units, tp)
    text, metadata = renderer()(*args)
    reads = metadata['reads']
    assert len(reads) == 1 + 3 * units * tp
    assert Counter(r['op'] for r in reads) == {'FW_embedding': 1 + units * tp,
        'ChunkPrim': units * tp, 'AllToAllPrim': units * tp}
    assert len({tuple(r['ref']) for r in reads}) == len(reads)
    assert all(r['ref'][3] in (50, 51, 52) for r in reads)
    assert len(metadata['routes']) == units
    assert metadata['lean_bytes'] == len(text.encode())
    json.dumps(metadata)
    for name in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert metadata[name] is False
    assert 'uncompiled' in metadata['status']
    assert 'desired_activation_equality' not in json.dumps(metadata)
    assert 'set_option maxHeartbeats 500000' in text
    assert 'native_decide' not in text and 'sorry' not in text and 'axiom ' not in text
    assert text.count('SourcePrimitiveRead.chunk_value_of_split') == units * tp
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == units * tp
    for row in reads:
        view = args[0 if row['world'] == 'sm' else 1]
        node = view.nodes()[row['source_index']]
        assert tuple(node) == tuple(row['node'])
        assert args[4][row['world']]['execution_to_source'][row['execution_index']] == row['source_index']
        assert row['input_tids'] == [x.tid for x in view.node_inputs(node)]
        assert row['input_refs'] == [list(view.source_tensor(x)) for x in view.node_inputs(node)]
        header = next(line for line in text.splitlines() if line.startswith('theorem ' + row['theorem'] + ' '))
        assert header == (f"theorem {row['theorem']} (s t : Store) "
            f"(h : {row['world']}DenoteWithInputs s = some t) :")
        if row['op'] != 'FW_embedding':
            assert row['ranks'][row['local_index']] == node.rank
        if row['op'] == 'AllToAllPrim':
            assert row['peers'] == [list(x) for x in zip(row['ranks'], row['input_tids'])]
            assert f"∀ tid ∈ ({row['input_tids']} : List Tid)" in text
        assert f"{row['world']}InputRequests.drop {row['execution_index']}," in text


@pytest.mark.parametrize('fault', ['reverse', 'source-cids', 'duplicate', 'inverse', 'bool'])
def test_wrong_execution_order_rejected(fault):
    sv, pv, ls, validation, order = setup()
    order = copy.deepcopy(order)
    if fault == 'reverse': order['pm']['execution_to_source'].reverse()
    elif fault == 'source-cids': order['pm']['execution_to_source'] = [n.cid for n in pv.nodes()]
    elif fault == 'duplicate': order['pm']['execution_to_source'][-1] = 0
    elif fault == 'inverse': order['pm']['source_to_execution'].reverse()
    else: order['pm']['execution_to_source'][0] = False
    with pytest.raises(ValueError, match='execution order'):
        renderer()(sv, pv, ls, validation, order)


@pytest.mark.parametrize('kind,port', [('chunk', 0), ('embedding', 0), ('embedding', 1), ('exchange', 0), ('exchange', 1)])
@pytest.mark.parametrize('where', ['selected', 'suffix'])
def test_python_checks_every_operand_against_late_write(kind, port, where):
    # Exercise the independent liveness guard even if upstream census/scheduling
    # guards are bypassed: one genuine route, with an injected suffix write.
    sv, pv, ls, validation, order = setup()
    from Verdict.runtime_embedding_routes import census
    from Verdict.runtime_embedding_route_values import _read
    route = next(r for r in census(sv, pv, ls, validation).routes if r.ranks[0].chunk)
    step = getattr(route.ranks[0], kind)
    tid = step.inputs[port].endpoint.tid
    late = pv.nodes()[order['pm']['execution_to_source'][-1]]
    tensor = next(t for t in pv.tensors() if t.tid == tid)
    if where == 'selected':
        late = next(n for n in pv.nodes() if tuple(n) == step.node)
        step = replace(step, outputs=(step.inputs[port],))
        pv._node2outputs[late] = [tensor]
    else:
        pv._node2outputs[late] = [*pv.node_outputs(late), tensor]
    with pytest.raises(ValueError, match='operand is written by node or suffix'):
        _read(pv, 'pm', step, order['pm'])


@pytest.mark.parametrize('fault', ['plain-validation', 'raw-port', 'scope', 'peer-order'])
def test_original_authority_and_peer_identity_rejected(fault):
    sv, pv, ls, validation, order = setup()
    if fault == 'plain-validation': validation = dict(validation)
    elif fault == 'raw-port':
        next(c for c in validation._inputs[1] if c.node.cid == 13).inputs.reverse()
    else:
        node = next(iter(pv.collective_scopes))
        if fault == 'scope':
            pv.collective_scopes[node] = replace(pv.collective_scopes[node], ranks=(1, 0))
        else: pv._node2inputs[node].reverse()
    with pytest.raises(ValueError):
        renderer()(sv, pv, ls, validation, order)
