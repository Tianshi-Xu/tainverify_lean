"""Portable first output-projection source tests, not capture/kernel evidence."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_view_flatten_exchange_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_view_flatten_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_output_projection_values'), 'output projection renderer missing'
    return importlib.import_module('Verdict.runtime_output_projection_values')


def fixture(D=2, tp=2, seqlen=2):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = previous.fixture(D, tp, seqlen)
    old = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        producers = [c for c in graph.cells if c.opname == ('FW_view' if world == 's' else 'AllToAllPrim')
            and len(c._output_irs[0].shape) == 3 and c._output_irs[0].parent.name == 'new.flatten.result'
            and not any(c.outputs[0] in n.inputs and not n.opname.startswith('BW_') for n in graph.cells)]
        for producer in producers:
            x = producer._output_irs[0]; O = 7; I = x.shape[-1]
            weight = IR(24000, 'arbitrary.output.weight', (O, I), param=True)
            y = IR(24001, 'arbitrary.output.result', (*x.parent.shape[:2], O), (*x.indmap[:2], (0, O)))
            cell = NS(node=N(world, producer.rank, 0, 24001, 'FW_linear'), rank=producer.rank,
                opname='FW_linear', inputs=[producer.outputs[0], T(world, producer.rank, -1, 24000, 0)],
                outputs=[T(world, producer.rank, 0, 24001, 1)], kwargs=dict(bias=None, __consts=[]),
                _input_irs=[copy.deepcopy(x), weight], _output_irs=[y])
            cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs, outputs=lambda c=cell: c._output_irs)
            graph.cells.append(cell)
            graph.shapes.update({cell.inputs[1]: weight.shape, cell.outputs[0]: y.shape})
            if world == 'p':
                rows.append(dict(ref=dict(world=world, runtime_rank=cell.rank, microbatch=0,
                    source_cid=24001, call_instance=0, op=cell.opname, origin='fixture'),
                    source_irname=cell.node.irname, inputs=[tref(t) for t in cell.inputs],
                    outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[]))
        graph.cells.sort(key=lambda c: (c.rank, c.opname.startswith('BW_')))
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: old[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*old['adapter_source'], *copy.deepcopy(rows)]
    for rank in range(D*tp):
        snapshot['rank_sources'][str(rank)] = snapshot['rank_sources'][str(rank)].replace(
            '\ndef _train_step', '\n        projected = torch.nn.functional.linear(hidden_exchanged, self.weight_24000, bias=None)\ndef _train_step')
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2):
    f = fixture(D, tp, seqlen)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(D, tp, seqlen)


def test_output_projection_source_tracer():
    args = prepared(); prior = predecessor.render(*args)[1]; before = copy.deepcopy(args[-1])
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1 and all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'frontier_units', 'deferred_units')] == [5, 2, 2, 0]
    assert [r['world'] for r in detail['reads']] == ['sm', 'pm', 'pm', 'pm', 'pm']
    assert detail['consumed_frontier_indices'] == [0, 1] and args[-1] == before
    assert text.count('SourceLinearRead.linear_value_of_split') == 5
    assert text.count('source_linear_sequence_unit_output_reconstruct') == 2
    for old, new in zip(prior['frontier_units'], detail['units'], strict=True):
        assert new['ranks'] == old['ranks'] and new['positions'] == old['positions']
        assert new['layout'] == 'sharded' and new['gather_axis'] == 1 and 'slot' not in new
        B, S, I = old['local_shape']; D = old['dimensions']['D']; T = old['dimensions']['T']
        assert new['dimensions'] == dict(D=D, T=T, B=B, S=S, I=I, O=7)
        assert new['global_shape'] == [B*D, S*T, 7] and new['local_shape'] == [B, S, 7]
        assert new['facts_theorem'].startswith('outputProjectionUnitFacts_')
        frag = text.split('theorem '+new['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert frag.split(' := by')[0].count('(h') == 3
        assert old['facts_theorem']+' s p t q hs hp hvalues' in frag
        assert 'initialParameterRelations_of_values t q (initialParameterValues_final s p t q hs hp hvalues)' in frag
        assert 'predecessor.1 rfl predecessor.2.1 weightRel.full_shape predecessor.2.2' in frag
        assert frag.count('weightRel.replica_values') == T and 'List.Forall₂' in frag
        assert new['parameters'][0]['kind'] == 'replicated'
    for row in detail['reads']:
        assert row['theorem'].startswith('outputProjectionRead_') and row['request'] == 'global'
        assert row['params'] == [] and len(row['input_refs']) == 2
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
        assert f'{row["world"]}Node_{row["source_index"]}' in text
    assert detail['reads'][0]['unit'] == 0 and detail['reads'][0]['frontier_index'] == 0
    assert any(r['source_index'] != r['execution_index'] for r in detail['reads'])
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :', 'fw_matmul', 'slot'):
        assert forbidden not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def seam(args, prior, label='pm'):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    from Verdict import runtime_view_values as view
    j = 0 if label == 'sm' else 1
    index = _Index(args[j], args[3]._inputs[j]); old = prior['frontier_units'][0]
    port = middle._output(index, old['source_step'] if j == 0 else old['local_steps'][0])
    return index, view._consumer(index, port), port


@pytest.mark.parametrize('parent', [True, 999999])
def test_activation_parent_fresh_predecessor_accepts(baseline, parent):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    cell._input_irs[0].parent.tid = parent
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='parent'): api().render(*args)


@pytest.mark.parametrize('field,fault', [('_input_irs', 'bounds'), ('_input_irs', 'value'),
    ('_input_irs', 'shape'), ('_output_irs', 'bounds'), ('_output_irs', 'value'),
    ('_output_irs', 'shape'), ('_output_irs', 'bool-parent'), ('_output_irs', 'bool-shape')])
def test_geometry_fresh_predecessor_accepts(baseline, field, fault):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    ir = getattr(cell, field)[0]
    if fault == 'bounds': ir.indmap = (*ir.indmap[:2], (1, ir.parent.shape[-1]+1))
    elif fault == 'value': ir.valmap = (1, 2)
    elif fault == 'shape': ir.parent.shape = (*ir.parent.shape[:2], ir.parent.shape[-1]+1)
    elif fault == 'bool-parent': ir.parent.tid = True
    else: ir.parent.shape = (True, *ir.parent.shape[1:])
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('value', [False, 0, '', None, (), {}])
def test_raw_consts_fresh_predecessor_accepts(baseline, value):
    args, prior = copy.deepcopy(baseline); index, cell, _ = seam(args, prior)
    cell.kwargs['__consts'] = value
    index.view.source.cell(cell.node).kwargs['__consts'] = value
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('value', [False, 0, '', (), {}])
def test_raw_params_before_coercion_fresh_predecessor_accepts(baseline, value):
    from Verdict import graph_to_lean as c
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    original = c._get_node_params
    def params(v, n, **kw):
        return value if tuple(n) == tuple(cell.node) else original(v, n, **kw)
    with patch.object(c, '_get_node_params', side_effect=params):
        assert predecessor.render(*args)[1]['frontier_units']
        with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['binding-parent', 'binding-shape', 'binding-ref', 'binding-order', 'param-role', 'param-parent'])
def test_weight_binding_fresh_predecessor_accepts(baseline, fault):
    args, prior = copy.deepcopy(baseline); _, cell, _ = seam(args, prior)
    row = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == 24000)
    binding = row['units'][0]['bindings'][0]
    if fault == 'binding-parent': binding['parent_tid'] += 1
    elif fault == 'binding-shape': binding['shape'][0] += 1
    elif fault == 'binding-ref': binding['ref'][1] += 1
    elif fault == 'binding-order': row['units'][0]['bindings'].reverse()
    elif fault == 'param-role': cell._input_irs[1].param = False
    else: cell._input_irs[1].parent.tid = True
    if fault == 'param-role':
        with pytest.raises(ValueError): predecessor.render(*args)
    else:
        assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['ranks', 'positions', 'order', 'call', 'export', 'fullref', 'arity', 'bias', 'kwargs', 'input-order'])
def test_upstream_rejection_attribution(baseline, fault):
    args, prior = copy.deepcopy(baseline); index, cell, _ = seam(args, prior)
    writer = next(w for w in args[1]._collective_source['writers']
        if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    if fault == 'ranks': args[3]._inputs[3]['config']['units'][0]['ranks'].reverse()
    elif fault == 'positions': args[3]._inputs[3]['config']['units'][0]['positions'] = [99]
    elif fault == 'order': args[-1]['pm']['execution_to_source'].reverse()
    elif fault == 'call': writer['ref']['call_instance'] += 1
    elif fault == 'export': writer['export_id'] = 'wrong'
    elif fault == 'fullref': writer['inputs'][1]['version'] += 1
    elif fault == 'arity': cell.inputs.pop()
    elif fault == 'input-order': cell.inputs.reverse()
    else:
        cell.kwargs['bias' if fault == 'bias' else 'unknown'] = False
        index.view.source.cell(cell.node).kwargs.update(cell.kwargs)
    if fault in ('bias', 'kwargs'):
        assert predecessor.render(*args)[1]['frontier_units']
    else:
        with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('operand', [0, 1])
@pytest.mark.parametrize('where', ['selected', 'last'])
def test_private_both_operands_entire_BW_suffix(baseline, operand, where):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    assert predecessor.render(*args)[1]['frontier_units']
    step = api()._linear(index, port)
    source = args[1]; _, row = api()._read(source, 'pm', step, args[-1]['pm'])
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if where == 'selected' else source.nodes()[args[-1]['pm']['execution_to_source'][-1]]
    if where == 'last': assert source.node_opname(target).startswith('BW_')
    assert source.nodes().index(target) in row['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[operand]]
    if where == 'selected': step = replace(step, outputs=(step.inputs[operand],))
    with pytest.raises(ValueError, match='operand.*written'): api()._read(source, 'pm', step, args[-1]['pm'])


@pytest.mark.parametrize('fault', ['ranks', 'positions', 'cross-DP', 'duplicate', 'axis', 'bool-axis', 'cover'])
def test_private_frontier_not_public_authority(baseline, fault):
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['frontier_units']
    old = prior['frontier_units'][0]
    if fault == 'ranks': old['ranks'].reverse()
    elif fault == 'positions': old['positions'] = [99]
    elif fault == 'cross-DP': old['local_steps'] = prior['frontier_units'][1]['local_steps']
    elif fault == 'duplicate': prior['frontier_units'].append(copy.deepcopy(old))
    elif fault == 'cover': old['local_steps'] = old['local_steps'][:1]
    else: old['gather_axis'] = True if fault == 'bool-axis' else 2
    with pytest.raises(ValueError): api()._render(*args, prior)


def test_public_T3_nonsymmetric():
    args = prepared(2, 3, 9)
    text, detail = api().render(*args)
    assert [len(detail[k]) for k in ('reads', 'units', 'frontier_units', 'deferred_units')] == [7, 2, 2, 0]
    assert all(u['global_shape'] == [2, 9, 7] and u['local_shape'] == [1, 3, 7] for u in detail['units'])
    assert all(u['dimensions']['I'] == 36 for u in detail['units'])
    assert 'allGatherPrimDimN 1 3 0' in text


def test_T1_public_fixture_honestly_unsupported():
    with pytest.raises(StopIteration): prepared(2, 1, 2)


@pytest.mark.parametrize('fault', ['producer-absent', 'producer-partial', 'input-absent', 'input-partial',
    'output-absent', 'output-extra', 'global-request', 'raw-op', 'typed-node', 'unsupported-first'])
def test_private_original_metadata_and_immediate_frontier(baseline, fault):
    args, prior = copy.deepcopy(baseline); index, cell, port = seam(args, prior)
    assert predecessor.render(*args)[1]['frontier_units']
    producer = index.raw[port.endpoint.writer]
    if fault == 'producer-absent': del producer._output_irs
    elif fault == 'producer-partial': producer._output_irs = [None]
    elif fault == 'input-absent': del cell._input_irs
    elif fault == 'input-partial': cell._input_irs.pop()
    elif fault == 'output-absent': del cell._output_irs
    elif fault == 'output-extra': cell._output_irs.append(copy.deepcopy(cell._output_irs[0]))
    elif fault == 'global-request': index.view.collective_scopes[cell.node] = NS()
    elif fault == 'raw-op': cell.opname = 'FW_add'
    elif fault == 'typed-node': cell.node = cell.node._replace(rank=False)
    else:
        other = copy.copy(cell); other.node = other.node._replace(cid=99999); other.opname = 'FW_contiguous'
        index.raw[tuple(other.node)] = other
    with pytest.raises((ValueError, AttributeError)): api()._linear(index, port)


@pytest.mark.parametrize('fault', ['partial', 'absent', 'extra', 'nonboolean-role'])
def test_weight_every_occurrence_complete_private_after_fresh_accept(baseline, fault):
    args, prior = copy.deepcopy(baseline); pi, cell, port = seam(args, prior)
    si, _, gp = seam(args, prior, 'sm')
    renderer = api(); global_ = renderer._linear(si, gp)
    from Verdict import runtime_middle_exchange_values as middle
    from Verdict import runtime_add_values as adds
    old = prior['frontier_units'][0]
    locals_ = [renderer._linear(pi, middle._output(pi, d)) for d in old['local_steps']]
    assert predecessor.render(*args)[1]['frontier_units']
    # An additional saved-primal occurrence must not be hidden by zip truncation.
    other = copy.copy(cell); other.node = other.node._replace(cid=99999); other.opname = 'BW_linear'
    other.inputs = list(cell.inputs); other._input_irs = copy.deepcopy(cell._input_irs)
    if fault == 'partial': other._input_irs = other._input_irs[:1]
    elif fault == 'absent': del other._input_irs
    elif fault == 'extra': other._input_irs.append(copy.deepcopy(other._input_irs[1]))
    else: other._input_irs[1].param = 1
    pi.raw[tuple(other.node)] = other
    assert callable(getattr(renderer, '_parameter', None)), 'complete weight occurrence guard missing'
    with pytest.raises(ValueError):
        renderer._parameter(si, pi, args[2], adds._bound(args[2], args[4]), global_, locals_, old)


def test_spec_order_and_SM_first_annotation_coherence(baseline):
    args, prior = copy.deepcopy(baseline)
    # Canonical frame and renderer consume the exact same original bound order.
    text, detail = api().render(*args)
    specs = api().adds._bound(args[2], args[4])
    for unit in detail['units']:
        i = unit['parameters'][0]['spec_index']
        projection = 'hrels' + '.2'*i + ('.1' if i < len(specs)-1 else '')
        fragment = text.split('theorem '+unit['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert ':= '+projection in fragment
    prior['frontier_units'].reverse()
    _, reordered = api()._render(*args, prior)
    assert [u['unit'] for u in reordered['units']] == [1, 0]
    assert reordered['reads'][0]['unit'] == 1 and reordered['reads'][0]['frontier_index'] == 0
    assert sum(r['world'] == 'sm' for r in reordered['reads']) == 1
    # A differently ordered caller bound is upstream-rejected, not new authority.
    args[4]['relations'].reverse()
    with pytest.raises(ValueError, match='spec order'): predecessor.render(*args)
    with pytest.raises(ValueError, match='spec order'): api().render(*args)
