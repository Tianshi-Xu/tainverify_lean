"""Portable contiguous source evidence; no capture or kernel claim."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_query_transpose_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_query_transpose_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_contiguous_values'), 'contiguous renderer missing'
    return importlib.import_module('Verdict.runtime_contiguous_values')


def fixture(D=2, tp=2, seqlen=2, consts=False):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = previous.fixture(D, tp, seqlen)
    old = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        terminal = [c for c in graph.cells if c.opname == 'FW_transpose'
            and not any(c.outputs[0] in n.inputs and not n.opname.startswith('BW_') for n in graph.cells)]
        for j, producer in enumerate(terminal):
            x = producer._output_irs[0]; cid = 17000+j
            out = IR(cid, 'new.contiguous.result', x.parent.shape, x.indmap)
            cell = NS(node=N(world, producer.rank, 0, cid, 'contiguous' if consts else 'FW_contiguous'), rank=producer.rank,
                opname='FW_contiguous', inputs=[producer.outputs[0]],
                outputs=[T(world, producer.rank, 0, cid, 1)], kwargs={'__consts': []} if consts else {},
                _input_irs=[copy.deepcopy(x)], _output_irs=[out])
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


def prepared(D=2, tp=2, seqlen=2, consts=False):
    f = fixture(D, tp, seqlen, consts)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(D, tp, seqlen)


def test_first_contiguous_tracer():
    args = prepared(); prior = predecessor.render(*args)[1]; before = copy.deepcopy(args[-1])
    assert len(prior['frontier_units']) == 2
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1 and all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'frontier_units', 'deferred_units')] == [5, 2, 2, 0]
    assert [r['world'] for r in detail['reads']] == ['sm', 'pm', 'pm', 'pm', 'pm']
    assert detail['consumed_frontier_indices'] == [0, 1]
    assert text.count('SourceContiguousRead.contiguous_value_of_split') == 5
    assert text.count('  exact predecessor') == 2
    assert args[-1] == before
    for old, new in zip(prior['frontier_units'], detail['frontier_units'], strict=True):
        assert new['layout'] == 'sharded' and new['gather_axis'] == 1
        assert new['input_gather_axis'] == old['gather_axis']
        assert new['dimensions'] == old['dimensions']
        assert new['ranks'] == old['ranks'] and new['positions'] == old['positions']
        assert new['unit'] == old['unit'] and new['predecessor'] == old['facts_theorem']
        assert new['local_shape'] == old['local_shape']
        assert new['global_shape'] == old['global_shape']
        assert new['source_step']['op'] == 'FW_contiguous' and 'slot' not in new
        assert new['facts_theorem'].startswith('contiguousUnitFacts_')
        fragment = text.split('theorem '+new['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert fragment.split(' := by')[0].count('(h') == 3
        assert 'rw [' in fragment and 'exact predecessor' in fragment
    for row in detail['reads']:
        assert row['theorem'].startswith('contiguousRead_')
        assert row['params'] == [] and row['request'] == 'global'
        assert row['input_parent_identity'] == 'both-present'
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
    assert detail['reads'][0]['frontier_index'] == 0 and detail['reads'][0]['unit'] == 0
    assert any(r['source_index'] != r['execution_index'] for r in detail['reads'])
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :'):
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
    index = _Index(args[j], args[3]._inputs[j])
    old = prior['frontier_units'][unit]
    port = middle._output(index, old['source_step'] if label == 'sm' else old['local_steps'][peer])
    return index, view._consumer(index, port), port


@pytest.mark.parametrize('label', ['sm', 'pm'])
@pytest.mark.parametrize('parent', [123456, True])
def test_raw_parent_identity_after_fresh_predecessor_acceptance(baseline, label, parent):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior, label)
    cell._input_irs = copy.deepcopy(cell._input_irs)
    cell._input_irs[0].parent.tid = parent
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='parent identity'): api().render(*args)


@pytest.mark.parametrize('label', ['sm', 'pm'])
@pytest.mark.parametrize('fault', ['output-bounds', 'output-parent', 'value-part'])
def test_new_boundary_metadata_after_fresh_predecessor(baseline, label, fault):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior, label)
    cell._output_irs = copy.deepcopy(cell._output_irs); out = cell._output_irs[0]
    if fault == 'output-bounds':
        bounds = list(out.indmap); a, b = bounds[1]; bounds[1] = (a+1, b+1); out.indmap = tuple(bounds)
    elif fault == 'output-parent': out.parent.shape = (out.parent.shape[0]+1, *out.parent.shape[1:])
    else: out.valmap = (1, 2)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['ranks', 'positions', 'cross-DP', 'duplicate', 'axis'])
def test_private_frontier_authentication(baseline, fault):
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['frontier_units']
    u = prior['frontier_units'][0]
    if fault == 'ranks': u['ranks'].reverse()
    elif fault == 'positions': u['positions'] = ['not-the-owner-position']
    elif fault == 'cross-DP': u['local_steps'] = prior['frontier_units'][1]['local_steps']
    elif fault == 'duplicate': prior['frontier_units'].append(copy.deepcopy(u))
    else: u['gather_axis'] = 2
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


def test_T3_nonsymmetric_geometry_and_reordered_frontier():
    args = prepared(2, 3, 9); prior = predecessor.render(*args)[1]
    text, detail = api().render(*args)
    assert len(detail['reads']) == 7 and len(detail['units']) == 2
    for u in detail['units']:
        assert u['dimensions'] == dict(D=2, T=3, B=1, S=6, H=3, C=6)
        assert u['global_shape'] == [2, 9, 6, 6] and u['local_shape'] == [1, 3, 6, 6]
        assert 'allGatherPrimDimN 1 3 0' in text
    prior['frontier_units'].reverse()
    _, reordered = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [u['unit'] for u in reordered['units']] == [1, 0]
    assert reordered['reads'][0]['unit'] == 1 and reordered['reads'][0]['frontier_index'] == 0
    assert [u['ranks'] for u in reordered['units']] == [u['ranks'] for u in prior['frontier_units']]


@pytest.mark.parametrize('where', ['selected', 'last'])
def test_complete_selected_and_backward_suffix_nonwrites(baseline, where):
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


def test_T1_private_unit_only_not_upstream_fixture_support(baseline):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    si, sc, sp = seam(args, prior, 'sm'); pi, pc, pp = seam(args, prior)
    global_ = api()._unary(si, sc, sp); local = api()._unary(pi, pc, pp)
    old = prior['frontier_units'][0]
    old['dimensions']['T'] = 1; old['ranks'] = old['ranks'][:1]; old['positions'] = old['positions'][:1]
    old['pm_output_refs'] = old['pm_output_refs'][:1]
    old['local_shape'] = [1, *old['global_shape'][1:]]
    def whole(p):
        shape = (1, *p.parent_shape[1:])
        return replace(p, endpoint=replace(p.endpoint, shape=shape), bounds=tuple((0, d) for d in shape))
    local = replace(local, inputs=(whole(local.inputs[0]),), outputs=(whole(local.outputs[0]),))
    proof, unit = api()._unit(old, global_, [local], {global_.node: 'globalRead', local.node: 'localRead'})
    assert unit['dimensions'] == dict(D=2, T=1, B=1, S=4, H=1, C=4)
    assert 'allGatherPrimDimN 1 1 0' in '\n'.join(proof)
    # The older fixture does not support T=1; this is only private geometry.
    with pytest.raises(StopIteration): prepared(2, 1, 2)


@pytest.mark.parametrize('which', ['producer', 'input', 'output'])
@pytest.mark.parametrize('missing', ['absent', 'none'])
def test_complete_metadata_no_absent_producer_bypass(baseline, which, missing):
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    target = index.raw[port.endpoint.writer] if which == 'producer' else cell
    field = '_input_irs' if which == 'input' else '_output_irs'
    if missing == 'absent': delattr(target, field)
    else: setattr(target, field, None)
    # This source alteration is already rejected by the complete predecessor.
    # Independently test the new boundary without claiming public reachability.
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError, match='complete original'):
        api()._unary(index, cell, port)


@pytest.mark.parametrize('fault', ['export', 'call', 'fullref', 'owner', 'raw-op'])
def test_upstream_source_authority_rejections(baseline, fault):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    writer = next(w for w in args[1]._collective_source['writers']
        if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    if fault == 'export': writer['export_id'] = 'not-the-export'
    elif fault == 'call': writer['ref']['call_instance'] += 1
    elif fault == 'fullref': writer['inputs'][0]['version'] += 1
    elif fault == 'owner': args[3]._inputs[3]['config']['units'][0]['ranks'].reverse()
    else: cell.opname = 'FW_view'
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('bad', [False, 0, (), '', [True], [1]])
def test_raw_extractor_params_before_or_normalization(baseline, bad):
    args, prior = copy.deepcopy(baseline)
    from Verdict import graph_to_lean as c
    original = c._get_node_params
    def extract(source, node, num_parts=0):
        if str(source.node_opname(node)).split('.')[-1] == 'FW_contiguous': return bad
        return original(source, node, num_parts=num_parts)
    with patch.object(c, '_get_node_params', side_effect=extract):
        # All six malformed extractor payloads are accepted upstream; the new
        # boundary must reject them before the ordinary `or []` normalization.
        assert predecessor.render(*args)[1]['frontier_units']
        with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('kwargs', [{'__consts': False}, {'__consts': ()}, {'memory_format': None}, {'unknown': 0}])
def test_strict_raw_kwargs_attribution(baseline, kwargs):
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    cell.kwargs = kwargs
    # The complete predecessor rejects these raw/source kwargs mismatches.
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError, match='kwargs'): api()._unary(index, cell, port)


def test_private_unary_authenticates_raw_opcode_and_arity(baseline):
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    assert predecessor.render(*args)[1]['frontier_units']
    cell.opname = 'FW_view'
    with pytest.raises(ValueError, match='opcode'):
        api()._unary(index, cell, port)


def test_global_scope_private_and_public_attribution(baseline):
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    step = api()._unary(index, cell, port)
    node = next(n for n in args[1].nodes() if tuple(n) == step.node)
    args[1].collective_scopes[node] = NS(op='AllGatherPrim')
    with pytest.raises(ValueError): api()._read(args[1], 'pm', step, args[-1]['pm'])
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('kwargs', [[], ()])
def test_raw_kwargs_container_not_normalized_to_empty_dict(baseline, kwargs):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    cell.kwargs = kwargs
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='kwargs'): api().render(*args)


@pytest.mark.parametrize('label', ['sm', 'pm'])
def test_output_name_may_change_but_cross_world_relationship_is_required(baseline, label):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior, label)
    cell._output_irs = copy.deepcopy(cell._output_irs)
    assert cell._output_irs[0].parent.name != cell._input_irs[0].parent.name
    cell._output_irs[0].parent.name = 'unrelated.output.logical.parent'
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='contract'): api().render(*args)


def test_shared_SM_step_coherence_not_just_tid_dedup(baseline):
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['frontier_units']
    prior['frontier_units'][1]['source_step']['outputs'][0]['value_part'] = (1, 2)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


def test_actual_census_kwargs_and_distinct_irname_public_positive():
    # In-memory graph, not a new capture. Payload form inspected in parent's census.
    args = prepared(consts=True)
    text, detail = api().render(*args)
    assert [len(detail[k]) for k in ('reads', 'units', 'frontier_units', 'deferred_units')] == [5, 2, 2, 0]
    assert all(r['source_kwargs'] == {'__consts': []} and r['params'] == [] for r in detail['reads'])
    assert all(r['node'][-1] == 'contiguous' for r in detail['reads'])
    assert text.count('SourceContiguousRead.contiguous_value_of_split') == 5
