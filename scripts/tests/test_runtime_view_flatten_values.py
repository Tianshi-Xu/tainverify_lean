"""Portable source flatten tests. No captures or kernel claims."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_contiguous_exchange_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_contiguous_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_view_flatten_values'), 'flatten renderer missing'
    return importlib.import_module('Verdict.runtime_view_flatten_values')


def fixture(D=2, tp=2, seqlen=2, inferred=False):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = previous.fixture(D, tp, seqlen)
    old = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        terminal = [c for c in graph.cells if c.opname == ('FW_contiguous' if world == 's' else 'AllToAllPrim')
            and not any(c.outputs[0] in n.inputs and not n.opname.startswith('BW_') for n in graph.cells)]
        for j, producer in enumerate(terminal):
            x = producer._output_irs[0]; cid = 21000+j
            shape = (*x.parent.shape[:2], x.parent.shape[2]*x.parent.shape[3])
            bounds = (*x.indmap[:2], tuple(n*x.parent.shape[3] for n in x.indmap[2]))
            out = IR(cid, 'new.flatten.result', shape, bounds)
            size = list(out.shape)
            if inferred: size[-1] = -1
            cell = NS(node=N(world, producer.rank, 0, cid, 'view'), rank=producer.rank,
                opname='FW_view', inputs=[producer.outputs[0]], outputs=[T(world, producer.rank, 0, cid, 1)],
                kwargs=dict(size=size, __consts=[]), _input_irs=[copy.deepcopy(x)], _output_irs=[out])
            cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs,
                outputs=lambda c=cell: c._output_irs)
            graph.cells.append(cell); graph.shapes[cell.outputs[0]] = out.shape
            if world == 'p':
                rows.append(dict(ref=dict(world=world, runtime_rank=cell.rank, microbatch=0,
                    source_cid=cid, call_instance=0, op=cell.opname, origin='fixture'),
                    source_irname=cell.node[-1], inputs=[tref(t) for t in cell.inputs],
                    outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[]))
        graph.cells.sort(key=lambda c: (c.rank, c.opname.startswith('BW_')))
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: old[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*old['adapter_source'], *copy.deepcopy(rows)]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, inferred=False):
    f = fixture(D, tp, seqlen, inferred)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(D, tp, seqlen)


def test_flatten_source_tracer():
    args = prepared(); prior = predecessor.render(*args)[1]; before = copy.deepcopy(args[-1])
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1 and all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'frontier_units', 'deferred_units')] == [5, 2, 2, 0]
    assert [r['world'] for r in detail['reads']] == ['sm', 'pm', 'pm', 'pm', 'pm']
    assert detail['consumed_frontier_indices'] == [0, 1] and args[-1] == before
    assert text.count('SourceLayoutRead.view_value_of_split') == 5
    assert text.count('source_view_flatten_head_unit_output_reconstruct') == 2
    for old, new in zip(prior['frontier_units'], detail['units'], strict=True):
        assert new['layout'] == 'sharded' and new['gather_axis'] == 2
        assert new['ranks'] == old['ranks'] and new['positions'] == old['positions']
        B, S, H, C = old['local_shape']; T = old['dimensions']['T']; D = old['dimensions']['D']
        assert new['dimensions'] == dict(D=D, T=T, B=B, S=S, H=H, C=C)
        assert new['global_shape'] == [B*D, S, H*T*C] and new['local_shape'] == [B, S, H*C]
        assert new['source_step']['op'] == 'FW_view' and 'slot' not in new
        assert new['facts_theorem'].startswith('viewFlattenUnitFacts_')
        fragment = text.split('theorem '+new['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert fragment.split(' := by')[0].count('(h') == 3
        assert old['facts_theorem']+' s p t q hs hp hvalues' in fragment
        assert 'List.Forall₂' in fragment and 'predecessor.1 rfl predecessor.2.1 predecessor.2.2' in fragment
    for row in detail['reads']:
        assert row['theorem'].startswith('viewFlattenRead_') and row['request'] == 'global'
        assert row['params'] == row['source_kwargs']['size'] and len(row['params']) == 3
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
    assert detail['reads'][0]['unit'] == 0 and detail['reads'][0]['frontier_index'] == 0
    assert any(r['source_index'] != r['execution_index'] for r in detail['reads'])
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :', 'fw_matmul'):
        assert forbidden not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def seam(args, prior, label='pm', unit=0, peer=0):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    from Verdict import runtime_view_values as view
    j = 0 if label == 'sm' else 1
    index = _Index(args[j], args[3]._inputs[j]); old = prior['frontier_units'][unit]
    port = middle._output(index, old['source_step'] if label == 'sm' else old['local_steps'][peer])
    return index, view._consumer(index, port), port


@pytest.mark.parametrize('label', ['sm', 'pm'])
@pytest.mark.parametrize('parent', [123456, True])
def test_parent_identity_fresh_accepted(baseline, label, parent):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior, label)
    cell._input_irs = copy.deepcopy(cell._input_irs); cell._input_irs[0].parent.tid = parent
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='parent identity'): api().render(*args)


def test_reachable_AA_output_boolean_parent_fresh_accepted(baseline):
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    producer = index.raw[port.endpoint.writer]
    producer._output_irs = copy.deepcopy(producer._output_irs)
    producer._output_irs[0].parent.tid = True
    cell._input_irs = copy.deepcopy(cell._input_irs); cell._input_irs[0].parent.tid = True
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='parent identity'): api().render(*args)


@pytest.mark.parametrize('fault', ['bounds', 'shape', 'value', 'name'])
def test_output_metadata_fresh_accepted(baseline, fault):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    cell._output_irs = copy.deepcopy(cell._output_irs); out = cell._output_irs[0]
    if fault == 'bounds':
        a, b = out.indmap[2]; out.indmap = (*out.indmap[:2], (a+1, b+1))
    elif fault == 'shape': out.parent.shape = (*out.parent.shape[:2], out.parent.shape[2]+1)
    elif fault == 'value': out.valmap = (1, 2)
    else: out.parent.name = 'unrelated-result'
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('size', [[True, 4, 4], [1.0, 4, 4], [1, 4, 5], [1, 4], [1, -1, -1], [1, 0, 4], [1, 3, -1], '1,4,4'])
def test_raw_size_fresh_accepted(baseline, size):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    # Canonical params come from outputs, so raw size errors are reachable here.
    cell.kwargs = dict(size=size, __consts=[])
    args[1].source.cell(cell.node).kwargs = copy.deepcopy(cell.kwargs)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('bad', [False, 0, (), '', [True, 4, 4], [1.0, 4, 4], [1, 4, 5]])
def test_params_precoercion_fresh_attribution(baseline, bad):
    from Verdict import graph_to_lean as c
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    original = c._get_node_params
    def extract(source, node, num_parts=0):
        if tuple(node) == tuple(cell.node): return bad
        return original(source, node, num_parts=num_parts)
    with patch.object(c, '_get_node_params', side_effect=extract):
        assert predecessor.render(*args)[1]['frontier_units']
        with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('which', ['producer', 'input', 'output'])
@pytest.mark.parametrize('missing', ['absent', 'none', 'empty'])
def test_missing_metadata_attribution(baseline, which, missing):
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    target = index.raw[port.endpoint.writer] if which == 'producer' else cell
    field = '_input_irs' if which == 'input' else '_output_irs'
    if missing == 'absent': delattr(target, field)
    else: setattr(target, field, None if missing == 'none' else [])
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError, match='complete original'): api()._unary(index, cell, port)


@pytest.mark.parametrize('fault', ['ranks', 'positions', 'cross-DP', 'duplicate', 'axis', 'bool-axis', 'cover'])
def test_private_frontier_integrity(baseline, fault):
    args, prior = copy.deepcopy(baseline); old = prior['frontier_units'][0]
    assert predecessor.render(*args)[1]['frontier_units']
    if fault == 'ranks': old['ranks'].reverse()
    elif fault == 'positions': old['positions'] = [99]
    elif fault == 'cross-DP': old['local_steps'] = prior['frontier_units'][1]['local_steps']
    elif fault == 'duplicate': prior['frontier_units'].append(copy.deepcopy(old))
    elif fault == 'cover': old['local_steps'] = old['local_steps'][:1]
    else: old['gather_axis'] = True if fault == 'bool-axis' else 1
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('fault', ['order', 'positions', 'owner', 'export', 'call', 'fullref', 'op'])
def test_upstream_authority_attribution(baseline, fault):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    writer = next(w for w in args[1]._collective_source['writers']
        if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    if fault == 'order': args[-1]['pm']['execution_to_source'].reverse()
    elif fault == 'positions': args[3]._inputs[3]['config']['units'][0]['positions'] = [99]
    elif fault == 'owner': args[3]._inputs[3]['config']['units'][0]['ranks'].reverse()
    elif fault == 'export': writer['export_id'] = 'bad-export'
    elif fault == 'call': writer['ref']['call_instance'] += 1
    elif fault == 'fullref': writer['inputs'][0]['version'] += 1
    else: cell.opname = 'FW_contiguous'
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('where', ['selected', 'last'])
def test_private_selected_and_entire_BW_suffix(baseline, where):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    assert predecessor.render(*args)[1]['frontier_units']
    step = api()._unary(index, cell, port); source = args[1]
    _, row = api()._read(source, 'pm', step, args[-1]['pm'])
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if where == 'selected' else source.nodes()[args[-1]['pm']['execution_to_source'][-1]]
    if where == 'last': assert source.node_opname(target).startswith('BW_')
    assert source.nodes().index(target) in row['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[0]]
    if where == 'selected': step = replace(step, outputs=(port,))
    with pytest.raises(ValueError, match='operand.*written'): api()._read(source, 'pm', step, args[-1]['pm'])


def test_public_T3_nonsymmetric_inferred_equivalence_and_order():
    args = prepared(2, 3, 9, inferred=True)
    prior = predecessor.render(*args)[1]; text, detail = api().render(*args)
    assert len(detail['reads']) == 7 and len(detail['units']) == 2
    for u in detail['units']:
        assert u['dimensions'] == dict(D=2, T=3, B=1, S=9, H=2, C=6)
        assert u['global_shape'] == [2, 9, 36] and u['local_shape'] == [1, 9, 12]
    assert all(r['source_kwargs']['size'][-1] == -1 and r['params'][-1] > 0 for r in detail['reads'])
    explicit_text, _ = api().render(*prepared(2, 3, 9))
    assert text == explicit_text
    prior['frontier_units'].reverse()
    _, reordered = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [u['unit'] for u in reordered['units']] == [1, 0]
    assert reordered['reads'][0]['unit'] == 1 and reordered['reads'][0]['frontier_index'] == 0


def test_T1_public_fixture_honestly_unsupported():
    with pytest.raises(StopIteration): prepared(2, 1, 2)


def test_shared_SM_coherence(baseline):
    args, prior = copy.deepcopy(baseline)
    prior['frontier_units'][1]['source_step']['outputs'][0]['value_part'] = (1, 2)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('consts', [False, (), [1]])
def test_raw_consts_private_and_public_attribution(baseline, consts):
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    cell.kwargs = dict(cell.kwargs, __consts=consts)
    args[1].source.cell(cell.node).kwargs = copy.deepcopy(cell.kwargs)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError, match='kwargs'): api()._unary(index, cell, port)


def test_private_global_request_gate(baseline):
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    step = api()._unary(index, cell, port)
    node = next(n for n in args[1].nodes() if tuple(n) == step.node)
    args[1].collective_scopes[node] = NS(op='AllGatherPrim')
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError): api()._read(args[1], 'pm', step, args[-1]['pm'])


def test_T1_private_geometry_not_public_support(baseline):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    si, sc, sp = seam(args, prior, 'sm'); pi, pc, pp = seam(args, prior)
    global_ = api()._unary(si, sc, sp); local = api()._unary(pi, pc, pp)
    old = prior['frontier_units'][0]
    old['dimensions']['T'] = 1; old['ranks'] = old['ranks'][:1]; old['positions'] = old['positions'][:1]
    old['pm_output_refs'] = old['pm_output_refs'][:1]
    old['local_shape'] = [1, *old['global_shape'][1:]]
    def whole(p):
        shape = p.parent_shape
        return replace(p, endpoint=replace(p.endpoint, shape=shape), bounds=tuple((0, d) for d in shape))
    local = replace(local, inputs=(whole(local.inputs[0]),), outputs=(whole(local.outputs[0]),))
    proof, unit = api()._unit(old, global_, [local], {global_.node: 'globalRead', local.node: 'localRead'})
    assert unit['dimensions']['T'] == 1 and 'allGatherPrimDimN 2 1 0' in '\n'.join(proof)


def test_input_element_count_not_output_metadata_authority(baseline):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    node = next(n for n in args[1].nodes() if tuple(n) == tuple(cell.node))
    out = args[1].node_outputs(node)[0]
    original = args[1].tensor_shape
    actual = tuple(original(out)); bad = (*actual[:2], actual[2]+1)
    with patch.object(args[1], 'tensor_shape', side_effect=lambda t: bad if t == out else original(t)):
        with pytest.raises(ValueError, match='input-derived'): api()._parameters(args[1], node)


@pytest.mark.parametrize('bad', [True, 1.0])
def test_output_shape_before_extractor_integer_coercion(baseline, bad):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    node = next(n for n in args[1].nodes() if tuple(n) == tuple(cell.node))
    out = args[1].node_outputs(node)[0]; original = args[1].tensor_shape
    shape = tuple(original(out)); malformed = (bad, *shape[1:])
    with patch.object(args[1], 'tensor_shape', side_effect=lambda t: malformed if t == out else original(t)):
        # Complete upstream shape authentication rejects this publicly.
        with pytest.raises(ValueError): predecessor.render(*args)
        with pytest.raises(ValueError): api().render(*args)
        with pytest.raises(ValueError): api()._parameters(args[1], node)
