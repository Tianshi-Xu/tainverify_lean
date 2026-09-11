"""Fresh portable residual graphs; emitted candidates are not kernel evidence."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_output_projection_exchange_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_output_projection_exchange_values as exchange
from Verdict import runtime_post_add_values as post
from Verdict import runtime_add_values as adds


def api():
    assert importlib.util.find_spec('Verdict.runtime_attention_residual_values'), 'attention residual renderer missing'
    return importlib.import_module('Verdict.runtime_attention_residual_values')


def fixture(D=2, tp=2, seqlen=2, reverse=False):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = previous.fixture(D, tp, seqlen)
    # Modify the original graph BEFORE lowering/binding: output width must match
    # the skip, unlike the output-exchange fixture's deliberately different width.
    for graph in (sm, pm):
        for cell in graph.cells:
            for ir in [*cell._input_irs, *cell._output_irs]:
                if ir.parent.name == 'arbitrary.output.weight':
                    ir.parent.shape = (3*tp, ir.parent.shape[1])
                    ir.indmap = tuple((0, d) for d in ir.parent.shape)
                elif ir.parent.name == 'arbitrary.output.result':
                    ir.parent.shape = (*ir.parent.shape[:2], 3*tp)
                    lo, hi = ir.indmap[2]
                    ir.indmap = (*ir.indmap[:2], (lo//5*3, hi//5*3))
                ir.shape = tuple(b-a for a, b in ir.indmap)
            for ref, ir in zip(cell.inputs, cell._input_irs):
                graph.shapes[ref] = ir.shape
            for ref, ir in zip(cell.outputs, cell._output_irs, strict=True):
                graph.shapes[ref] = ir.shape
    old = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        rights = [c for c in graph.cells if c.opname == ('FW_linear' if world == 's' else 'AllToAllPrim')
                  and c._output_irs[0].parent.name == 'arbitrary.output.result']
        for right in rights:
            alias = next(c for c in graph.cells if c.rank == right.rank and c.node.cid == 17)
            skip = 1
            inputs = [alias.outputs[skip], right.outputs[0]]
            irs = [copy.deepcopy(alias._output_irs[skip]), copy.deepcopy(right._output_irs[0])]
            assert irs[0].shape == irs[1].shape and irs[0].indmap == irs[1].indmap
            if reverse: inputs.reverse(); irs.reverse()
            y = IR(26000, 'residual.result', irs[0].parent.shape, irs[0].indmap)
            cell = NS(node=N(world, right.rank, 0, 26000, 'FW_add'), rank=right.rank,
                opname='FW_add', inputs=inputs, outputs=[T(world, right.rank, 0, 26000, 1)],
                kwargs=dict(alpha=1, __consts=[]), _input_irs=irs, _output_irs=[y])
            cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs,
                          outputs=lambda c=cell: c._output_irs)
            # Preserve all existing relative order, inserting before this rank's BW.
            at = next((i for i, c in enumerate(graph.cells) if c.rank == cell.rank and c.opname.startswith('BW_')), len(graph.cells))
            graph.cells.insert(at, cell); graph.shapes[cell.outputs[0]] = y.shape
            if world == 'p':
                rows.append(dict(ref=dict(world=world, runtime_rank=cell.rank, microbatch=0,
                    source_cid=26000, call_instance=0, op='FW_add', origin='fixture'),
                    source_irname=cell.node.irname, inputs=[tref(t) for t in inputs],
                    outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[]))
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: old[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*old['adapter_source'], *copy.deepcopy(rows)]
    for rank, source in snapshot['rank_sources'].items():
        args = 'output_exchanged, postadd_71' if reverse else 'postadd_71, output_exchanged'
        snapshot['rank_sources'][rank] = source.replace('\ndef _train_step', f'\n        residual = torch.add({args}, alpha=1)\ndef _train_step')
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, reverse=False):
    f = fixture(D, tp, seqlen, reverse)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(D, tp, seqlen)


def test_attention_residual_tracer():
    args = prepared(); before = copy.deepcopy(args[-2:])
    with patch.object(exchange, 'render', wraps=exchange.render) as fresh:
        text, result = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert args[-2:] == before
    assert [len(result[k]) for k in ('reads', 'units', 'alias_units', 'frontier_units', 'deferred_units')] == [5, 2, 2, 2, 0]
    assert text.count('SourceAddRead.add_value_of_split') == 5
    assert text.count('source_add_unit_output_facts') == 2
    for unit in result['units']:
        assert unit['global_shape'] == [2, 2, 6] and unit['local_shape'] == [1, 2, 3]
        assert unit['layout'] == 'sharded' and unit['gather_axis'] == 2
        assert unit['facts_theorem'].startswith('attentionResidualUnitFacts_')
        assert unit['source_step']['op'] == 'FW_add' and len(unit['local_steps']) == 2
    for alias in result['alias_units']:
        assert alias['facts_theorem'].startswith('attentionResidualAliasFacts_')
        assert alias['predecessor_facts'].startswith('addUnitFacts_')
        fragment = text.split('theorem '+alias['facts_theorem'], 1)[1].split('#print axioms')[0]
        assert alias['predecessor_facts']+' s p t q hs hp hvalues' in fragment
        assert 'postAddMultirefRead_' in fragment and 'postAddAliasUnit_' not in fragment
    for read in result['reads']:
        assert read['theorem'].startswith('attentionResidualRead_')
        assert read['operand_nonwrite_source_indices'] == args[-1][read['world']]['execution_to_source'][read['execution_index']:]
    assert any(r['source_index'] != r['execution_index'] for r in result['reads'])
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert result[flag] is False
    for bad in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :'):
        assert bad not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, exchange.render(*args)[1], post.render(*args)[1], adds.render(*args)[1]


def seam(args, label='pm'):
    from Verdict.runtime_lineage import _Index

    j = 0 if label == 'sm' else 1
    index = _Index(args[j], args[3]._inputs[j])
    cell = next(c for c in index.raw.values() if c.node[3] == 26000)
    ports = []
    for ref in cell.inputs:
        ep = index.endpoint(ref); prod = index.raw[ep.writer]
        ir = prod._output_irs[list(map(tuple, prod.outputs)).index(tuple(ref))]
        ports.append(post._port(index, ref, ir))
    return index, cell, ports


@pytest.mark.parametrize('label', ['sm', 'pm'])
@pytest.mark.parametrize('field', ['_input_irs', '_output_irs', 'producer'])
@pytest.mark.parametrize('fault', ['bool-irshape', 'float-irshape', 'bool-parent', 'parent-id', 'parent-shape', 'bounds', 'value', 'missing', 'partial'])
def test_strict_raw_metadata(baseline, label, field, fault):
    args, *_ = copy.deepcopy(baseline); index, cell, ports = seam(args, label)
    target = cell
    if field == 'producer':
        cell = index.raw[ports[0].endpoint.writer]; field = '_output_irs'
    irs = getattr(cell, field)
    ir = irs[list(map(tuple, cell.outputs)).index(ports[0].endpoint.ref)] if cell is not target else irs[0]
    if fault == 'bool-irshape': ir.shape = (True, *ir.shape[1:])
    elif fault == 'float-irshape': ir.shape = (float(ir.shape[0]), *ir.shape[1:])
    elif fault == 'bool-parent': ir.parent.tid = True
    elif fault == 'parent-id':
        if field == '_output_irs' and cell.node[3] == 26000:
            ir.parent.tid = False
        else: ir.parent.tid += 999
    elif fault == 'parent-shape': ir.parent.shape = (True, *ir.parent.shape[1:])
    elif fault == 'bounds': ir.indmap = ((False, ir.indmap[0][1]), *ir.indmap[1:])
    elif fault == 'value': ir.valmap = (False, 1)
    elif fault == 'missing': delattr(cell, field)
    else: setattr(cell, field, [*irs, None])
    # Boundary has to validate the fresh originals, not trust pre-converted ports.
    with pytest.raises(ValueError): api()._boundary(index, target, ports)


@pytest.mark.parametrize('label', ['sm', 'pm'])
@pytest.mark.parametrize('fault', ['typed-node', 'raw-op', 'raw-kwargs', 'alpha-bool', 'alpha-float', 'consts', 'extra-kw', 'fullrefs', 'arity'])
def test_original_identity(baseline, label, fault):
    args, *_ = copy.deepcopy(baseline); index, cell, ports = seam(args, label)
    if fault == 'typed-node': cell.node = cell.node._replace(rank=float(cell.rank))
    elif fault == 'raw-op': cell.opname = 'FW_mul'
    elif fault == 'raw-kwargs': cell.kwargs = dict(alpha=2)
    elif fault == 'alpha-bool': cell.kwargs = dict(alpha=True)
    elif fault == 'alpha-float': cell.kwargs = dict(alpha=1.0)
    elif fault == 'consts': cell.kwargs = dict(alpha=1, __consts=False)
    elif fault == 'extra-kw': cell.kwargs = dict(alpha=1, extra=None)
    elif fault == 'fullrefs': cell.inputs[0] = cell.inputs[0]._replace(v=2)
    else: cell.outputs.append(cell.outputs[0])
    with pytest.raises(ValueError): api()._boundary(index, cell, ports)


@pytest.mark.parametrize('fault', ['call', 'export', 'op', 'fullref'])
def test_writer_identity(baseline, fault):
    args, *_ = copy.deepcopy(baseline); index, cell, ports = seam(args)
    writer = next(w for w in args[1]._collective_source['writers'] if w['ref']['source_cid'] == 26000 and w['ref']['runtime_rank'] == cell.rank)
    if fault == 'call': writer['ref']['call_instance'] = True
    elif fault == 'export': writer['export_id'] = 'wrong'
    elif fault == 'op': writer['ref']['op'] = 'FW_mul'
    else: writer['inputs'][0]['version'] += 1
    with pytest.raises(ValueError): api()._boundary(index, cell, ports)


@pytest.mark.parametrize('value', [False, 0, '', (), {}, [True]])
def test_exact_empty_parameters(baseline, value):
    from Verdict import graph_to_lean as c
    args, *_ = copy.deepcopy(baseline); index, cell, ports = seam(args)
    original = c._get_node_params
    def params(v, n, **kw):
        return value if tuple(n) == tuple(cell.node) else original(v, n, **kw)
    with patch.object(c, '_get_node_params', side_effect=params):
        with pytest.raises(ValueError): api()._boundary(index, cell, ports)


@pytest.mark.parametrize('fault', ['partial', 'duplicate', 'bool', 'reversed'])
def test_complete_execution_order(baseline, fault):
    args, *_ = copy.deepcopy(baseline); index, cell, ports = seam(args)
    step = api()._boundary(index, cell, ports); order = args[-1]['pm']
    if fault == 'partial': order['execution_to_source'].pop()
    elif fault == 'duplicate': order['execution_to_source'].append(order['execution_to_source'][-1])
    elif fault == 'bool': order['execution_to_source'][0] = False
    else: order['execution_to_source'].reverse()
    with pytest.raises(ValueError): api()._read(args[1], 'pm', step, order)


@pytest.mark.parametrize('label', ['sm', 'pm'])
@pytest.mark.parametrize('operand', [0, 1])
@pytest.mark.parametrize('where', ['selected', 'last'])
def test_selected_and_entire_BW_suffix(baseline, label, operand, where):
    from dataclasses import replace
    args, *_ = copy.deepcopy(baseline); index, cell, ports = seam(args, label)
    step = api()._boundary(index, cell, ports); source = index.view; order = args[-1][label]
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if where == 'selected' else source.nodes()[order['execution_to_source'][-1]]
    if where == 'last': assert source.node_opname(target).startswith('BW_')
    source._node2outputs[target] = [source.node_inputs(node)[operand]]
    if where == 'selected': step = replace(step, outputs=step.inputs[operand:operand+1])
    with pytest.raises(ValueError, match='operand.*written'): api()._read(source, label, step, order)


@pytest.mark.parametrize('fault', ['missing-unit', 'duplicate', 'ranks', 'positions', 'cross-DP', 'partial-locals', 'axis', 'bool-unit'])
def test_private_frontier_cannot_drop_or_repair_units(baseline, fault):
    args, right, aliases, closed = copy.deepcopy(baseline); old = right['frontier_units'][0]
    if fault == 'missing-unit': right['frontier_units'].pop()
    elif fault == 'duplicate': right['frontier_units'].append(copy.deepcopy(old))
    elif fault == 'ranks': old['ranks'].reverse()
    elif fault == 'positions': old['positions'] = [99]
    elif fault == 'cross-DP': old['local_steps'] = right['frontier_units'][1]['local_steps']
    elif fault == 'partial-locals': old['local_steps'].pop()
    elif fault == 'axis': old['gather_axis'] = True
    else: old['unit'] = False
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], right, aliases, closed)


@pytest.mark.parametrize('fault', ['operand-order', 'shape-type', 'float-shape-type', 'kwargs'])
def test_public_rejection_attribution(baseline, fault):
    args, *_ = copy.deepcopy(baseline); _, cell, _ = seam(args)
    if fault == 'operand-order': cell.inputs.reverse(); cell._input_irs.reverse()
    elif fault == 'shape-type': cell._output_irs[0].shape = (True, *cell._output_irs[0].shape[1:])
    elif fault == 'float-shape-type': cell._output_irs[0].shape = (1.0, *cell._output_irs[0].shape[1:])
    else: cell.kwargs['alpha'] = True
    if fault == 'operand-order':
        # The independent source census already binds ordered fullrefs.
        with pytest.raises(ValueError, match='ordered fullref'): exchange.render(*args)
        with pytest.raises(ValueError): api().render(*args)
        return
    assert exchange.render(*args)[1]['frontier_units']
    assert post.render(*args)[1]['units'] and adds.render(*args)[1]['units']
    with pytest.raises(ValueError): api().render(*args)


def test_public_T3_nonsymmetric_reversed_operands():
    args = prepared(2, 3, 6, reverse=True)
    text, result = api().render(*args)
    assert len(result['reads']) == 7 and len(result['units']) == 2
    for u in result['units']:
        assert u['global_shape'] == [2, 6, 9] and u['local_shape'] == [1, 6, 3]
        assert u['predecessors'][0].startswith('outputProjectionExchangeUnitFacts_')
        assert u['dimensions'] == dict(D=2, T=3, B=1, S=6, H=3)
    assert 'postAddAliasUnit_' not in text


def test_T1_fixture_honest_limitation():
    with pytest.raises(StopIteration): prepared(2, 1, 2)


@pytest.mark.parametrize('producer', ['alias', 'exchange'])
def test_raw_shape_checked_before_lossy_port_conversion(baseline, producer):
    args, right, aliases, closed = copy.deepcopy(baseline)
    index, cell, ports = seam(args)
    p = ports[0 if producer == 'alias' else 1]
    original = index.raw[p.endpoint.writer]
    ir = original._output_irs[list(map(tuple, original.outputs)).index(p.endpoint.ref)]
    ir.shape = (True, *ir.shape[1:])
    convert = post._port
    def checked(i, r, raw):
        assert raw is not ir, 'raw shape reached lossy conversion before type check'
        return convert(i, r, raw)
    with patch.object(post, '_port', side_effect=checked):
        with pytest.raises(ValueError, match='shape'):
            api()._render(args[0], args[1], args[3], args[-1], right, aliases, closed)


def test_order_not_sorted_and_fresh_all_three_sources(baseline):
    args, right, aliases, closed = copy.deepcopy(baseline)
    right['frontier_units'].reverse()
    _, result = api()._render(args[0], args[1], args[3], args[-1], right, aliases, closed)
    assert [u['unit'] for u in result['units']] == [1, 0]
    with patch.object(post, 'render', wraps=post.render) as ap, patch.object(adds, 'render', wraps=adds.render) as ad:
        api().render(*args)
    for fresh in (ap, ad):
        assert fresh.call_count >= 1
        assert all(all(a is b for a, b in zip(call.args, args, strict=True)) for call in fresh.call_args_list)


def test_parent_identity_is_edge_identity_not_source_tid(baseline):
    args, *_ = copy.deepcopy(baseline)
    index, cell, ports = seam(args)
    for p, consumer, parent_id in zip(ports, cell._input_irs, (376, 69), strict=True):
        producer = index.raw[p.endpoint.writer]
        ir = producer._output_irs[list(map(tuple, producer.outputs)).index(p.endpoint.ref)]
        ir.parent.tid = parent_id; consumer.parent.tid = parent_id
        assert parent_id != consumer.tid
    cell._output_irs[0].parent.tid = 71
    assert api()._boundary(index, cell, ports).op == 'FW_add'


@pytest.mark.parametrize('label', ['sm', 'pm'])
def test_old_add_to_multiref_parent_identity_public_after_all_predecessors(baseline, label):
    args, *_ = copy.deepcopy(baseline)
    index, _, ports = seam(args, label)
    alias = index.raw[ports[0].endpoint.writer]
    producer = index.raw[index.endpoint(alias.inputs[0]).writer]
    assert alias.opname == 'FW_multiref' and producer.opname == 'FW_add'
    assert tuple(producer.outputs[0]) == tuple(alias.inputs[0])
    assert producer._output_irs[0].parent.tid == alias._input_irs[0].parent.tid
    alias._input_irs[0].parent.tid += 999
    for predecessor in (exchange, post, adds):
        assert predecessor.render(*args)[1]['units']
    with pytest.raises(ValueError, match='old-add.*parent identity'):
        api().render(*args)
