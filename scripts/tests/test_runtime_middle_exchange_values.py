"""Portable source-only middle-exchange checkpoint, not a kernel/capture test."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest

from scripts.tests import test_runtime_post_transpose_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_post_transpose_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_middle_exchange_values'), 'middle-exchange renderer missing'
    return importlib.import_module('Verdict.runtime_middle_exchange_values')


def fixture(D=2, tp=2, seqlen=2, branches=3, saved=False):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = copy.deepcopy(previous.fixture(D, tp, seqlen, branches, saved))
    old = copy.deepcopy(authority[2]); rows, adapters = [], []

    def append(graph, world, producer, out, opname, cid, kwargs, inputs=None, irs=None):
        cell = NS(node=N(world, producer.rank, 0, cid, opname), rank=producer.rank,
            opname=opname, inputs=list(producer.outputs) if inputs is None else inputs,
            outputs=[T(world, producer.rank, 0, out.tid, 1)],
            _input_irs=copy.deepcopy(producer._output_irs if irs is None else irs),
            _output_irs=[out], kwargs=kwargs)
        cell.ir = NS(signature=opname, inputs=lambda c=cell: c._input_irs,
            outputs=lambda c=cell: c._output_irs)
        graph.cells.append(cell); graph.shapes[cell.outputs[0]] = out.shape
        if world == 'p':
            row = dict(ref=dict(world='p', runtime_rank=cell.rank, microbatch=0,
                source_cid=cid, call_instance=0, op=opname, origin='fixture'),
                source_irname=cell.node.irname, inputs=[tref(t) for t in cell.inputs],
                outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[])
            if opname == 'AllToAllPrim': row['adapter_kwargs'] = copy.deepcopy(kwargs)
            rows.append(row); adapter = copy.deepcopy(row)
            if opname == 'AllToAllPrim':
                adapter['inputs'] = [tref(t) for t in cell.inputs if t.rank == cell.rank]
                adapter['primitive'] = dict(kind=opname, forward=True, kwargs=copy.deepcopy(kwargs),
                    signature='nnscaler.runtime.adapter.all_to_all',
                    generated_inputs=[f'next_{producer.outputs[0].tid}'], generated_outputs=[f'middle_{out.tid}'])
                params = ', '.join(f'{k}={v!r}' for k, v in kwargs.items())
                line = f'        middle_{out.tid} = nnscaler.runtime.adapter.all_to_all(next_{producer.outputs[0].tid}, {params})'
                old['rank_sources'][str(cell.rank)] = old['rank_sources'][str(cell.rank)].replace(
                    '\ndef _train_step', '\n'+line+'\ndef _train_step')
            adapters.append(adapter)
        return cell

    for producer in list(pm.cells):
        if producer.opname != 'FW_transpose' or producer.kwargs != dict(dim0=2, dim1=3): continue
        x = producer._output_irs[0]; ranks = list(range(producer.rank//tp*tp, (producer.rank//tp+1)*tp))
        j = ranks.index(producer.rank); bounds = list(x.indmap)
        bounds[2] = (0, x.parent.shape[2]); width = x.parent.shape[1]//tp
        bounds[1] = (j*width, (j+1)*width)
        out = IR(x.tid+300, x.parent.name, x.parent.shape, tuple(bounds))
        inputs = [T('p', r, 0, x.tid, 1) for r in ranks]
        append(pm, 'p', producer, out, 'AllToAllPrim', producer.node.cid+600,
            dict(ranks=ranks, idim=2, odim=1), inputs)
        pm.shapes.update({r: x.shape for r in inputs})
    # A source boundary only: these synthetic matmuls are not value-proof fixtures.
    # Repeated operand refs deliberately exercise complete port-position reporting.
    for world, graph in [('s', sm), ('p', pm)]:
        terminal = [c for c in graph.cells if c.opname in ('FW_transpose', 'AllToAllPrim', 'AllGatherPrim')
            and not any(d.rank == c.rank and any(t in d.inputs for t in c.outputs)
                and not d.opname.startswith('BW_') for d in graph.cells)]
        for i, producer in enumerate(terminal):
            x = producer._output_irs[0]
            out = IR(3000+i, 'deferred.matmul', x.parent.shape, x.indmap)
            append(graph, world, producer, out, 'FW_matmul', 3000+i, {},
                list(producer.outputs)*2, producer._output_irs*2)
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*old['adapter_source'], *adapters]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, branches=3, saved=False):
    data = fixture(D, tp, seqlen, branches, saved)
    base = previous.previous.existing.existing.projection.norm.post.base
    with patch.object(base, 'add_fixture', return_value=data):
        return base.prepared(D, tp, seqlen)


def test_middle_exchange_tracer():
    args = prepared()
    prior = predecessor.render(*args)[1]
    assert len(prior['units']) == 6
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'deferred_units', 'frontier_units')] == [4, 2, 4, 6]
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 4
    assert text.count('SourceRank4MiddleExchange.axis2_output_facts') == 2
    for old, current in zip(prior['units'], detail['frontier_units'], strict=True):
        if old['gather_axis'] != 2:
            assert current == old
        else:
            assert current['predecessor'] == old['facts_theorem']
            assert current['gather_axis'] == 1
    for unit in detail['deferred_units']:
        assert unit['reason'] == 'first-original-FW_matmul-value-boundary-unproved'
        assert unit['first_consumers'] and all(c['op'] == 'FW_matmul' for c in unit['first_consumers'])
        assert all(c['port_positions'] == [0, 1] for c in unit['first_consumers'])
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    assert 'UNCOMPILED' in text
    assert 'fw_matmul' not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared(saved=True)
    return args, predecessor.render(*args)[1]


def selected(args, prior, family='AllToAllPrim'):
    from Verdict.runtime_lineage import _Index
    index = _Index(args[1], args[3]._inputs[1])
    for unit in prior['units']:
        ports = [api()._output(index, d) for d in unit['local_steps']]
        cell = api().view._consumer(index, ports[0])
        if cell.opname == family:
            return index, unit, ports, cell
    raise AssertionError('fixture missing family')


@pytest.mark.parametrize('D,tp,seqlen,branches,saved', [
    (2, 2, 2, 3, True), (3, 2, 6, 4, False), (2, 3, 6, 5, False), (1, 2, 6, 1, False)])
def test_variable_dimensions_order_and_strong_facts(D, tp, seqlen, branches, saved):
    args = prepared(D, tp, seqlen, branches, saved)
    before = copy.deepcopy(args[-1]); prior = predecessor.render(*args)[1]
    text, detail = api().render(*args)
    new = [u for u in prior['units'] if u['gather_axis'] == 2]
    assert len(detail['units']) == len(new)
    assert len(detail['reads']) == sum(len(u['ranks']) for u in new)
    assert len(detail['frontier_units']) == D*branches
    assert len(detail['deferred_units']) == D*branches-len(new)
    assert detail['lean_bytes'] == len(text.encode()) and before == args[-1]
    for old, unit in zip(prior['units'], detail['frontier_units'], strict=True):
        assert unit['sm_output_ref'] == old['sm_output_ref']
        if old['gather_axis'] != 2:
            assert unit == old and 'theorem '+old['facts_theorem']+' ' not in text
            continue
        assert unit['input_refs'] == old['pm_output_refs']
        assert unit['local_shape'] == [old['local_shape'][0], old['local_shape'][1]//tp,
            old['local_shape'][2]*tp, old['local_shape'][3]]
        fragment = text.split('theorem '+unit['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
        assert fragment.split(' := by')[0].count('(h') == 3
        assert unit['predecessor']+' s p t q hs hp hvalues' in fragment
        assert 'predecessor.2.1 predecessor.1 predecessor.2.2 outputs' in fragment
        for step in unit['local_steps']:
            read = next(r for r in detail['reads'] if tuple(r['node']) == tuple(step['node']))
            assert read['theorem']+' p q hp' in fragment
            assert read['params'] == [2, 1]
            assert read['gather_axis'] == 2 and read['split_axis'] == 1
            assert read['output_gather_axis'] == 1
            assert read['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][read['execution_index']:]
    if saved:
        for source, label in zip(args[:2], ('sm', 'pm'), strict=True):
            bw = {i for i, n in enumerate(source.nodes()) if source.node_opname(n).startswith('BW_')}
            assert bw and bw <= set(args[-1][label]['execution_to_source'])
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', '(hshape :', '(houtput :'):
        assert forbidden not in text


@pytest.mark.parametrize('coverage', ['absent', 'local-only', 'all-peers'])
def test_optional_metadata_truthful(baseline, coverage):
    args, prior = copy.deepcopy(baseline)
    index, unit, ports, _ = selected(args, prior)
    originals = [copy.deepcopy(api().view._consumer(index, p)._input_irs[0]) for p in ports]
    for p in ports:
        cell = api().view._consumer(index, p)
        if coverage == 'absent': del cell._input_irs; del cell._output_irs
        elif coverage == 'all-peers': cell._input_irs = copy.deepcopy(originals)
    assert predecessor.render(*args)[1]['units']
    _, detail = api().render(*args)
    rows = [r for r in detail['reads'] if r['unit'] == unit['unit']]
    assert rows and all(r['input_metadata'] == coverage for r in rows)
    assert all(r['output_metadata'] == ('absent' if coverage == 'absent' else 'present') for r in rows)


@pytest.mark.parametrize('fault', ['input-parent', 'input-value', 'output-parent', 'output-bounds',
    'output-value', 'output-tid', 'bool', 'partial', 'wrong-local', 'joint-bounds', 'joint-value'])
def test_paired_metadata_after_predecessor(baseline, fault):
    args, prior = copy.deepcopy(baseline)
    index, unit, ports, cell = selected(args, prior)
    field = '_input_irs' if fault.startswith('input') or fault == 'wrong-local' else '_output_irs'
    cells = [api().view._consumer(index, p) for p in ports] if fault.startswith('joint') else [cell]
    for cell in cells:
        irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs); ir = irs[0]
        if fault.endswith('parent'): ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
        elif fault.endswith('value'): ir.valmap = (1, 2)
        elif fault == 'bool': ir.valmap = (False, 1)
        elif fault in ('output-bounds', 'joint-bounds'):
            ir.indmap = ((1, ir.indmap[0][1]+1), *ir.indmap[1:])
        elif fault == 'output-tid': ir.tid += 1
        elif fault == 'partial': irs.clear()
        elif fault == 'wrong-local': cell._input_irs = copy.deepcopy(api().view._consumer(index, ports[-1])._input_irs)
    assert predecessor.render(*args)[1]['units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('family', ['AllToAllPrim', 'FW_matmul'])
@pytest.mark.parametrize('fault', ['inputs', 'outputs', 'call', 'export'])
def test_source_writer_authentication_from_accepted_baseline(baseline, family, fault):
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['units']  # Accepted baseline before authority tampering.
    _, _, _, cell = selected(args, prior, family)
    writer = next(w for w in args[1]._collective_source['writers']
        if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    if fault in ('inputs', 'outputs'): writer[fault][0]['version'] += 1
    elif fault == 'call': writer['ref']['call_instance'] += 1
    else: writer['export_id'] = 'forged-nonempty-export'
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['unknown', 'mixed', 'missing', 'ambiguous', 'version', 'owner',
    'bool', 'float', 'extra', 'missing-kw', 'axes', 'ranks', 'ordered-fullrefs', 'deferred-op'])
def test_frontier_routecoverage_and_exact_kwargs_from_accepted_baseline(baseline, fault):
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['units']  # Accepted baseline before authority tampering.
    index, unit, ports, cell = selected(args, prior, 'FW_matmul' if fault == 'deferred-op' else 'AllToAllPrim')
    raw = args[3]._inputs[1]
    if fault in ('unknown', 'deferred-op'): cell.opname = 'FW_contiguous'
    elif fault == 'mixed': cell.opname = 'FW_matmul'
    elif fault == 'missing': raw.remove(cell)
    elif fault == 'ambiguous':
        # A competing raw consumer has a distinct identity, not a duplicate index entry.
        other = copy.copy(cell); other.node = other.node._replace(cid=99999); raw.append(other)
    elif fault == 'version': cell.inputs[0] = cell.inputs[0]._replace(v=0)
    elif fault == 'ordered-fullrefs': cell.inputs.reverse()
    elif fault == 'owner': cell.rank += 1
    else:
        changes = {'bool': dict(idim=True), 'float': dict(idim=2.0), 'extra': dict(extra=1),
            'axes': dict(odim=2), 'ranks': dict(ranks=list(reversed(unit['ranks'])))}
        if fault == 'missing-kw': cell.kwargs.pop('idim')
        else: cell.kwargs.update(changes[fault])
        node = next(n for n in args[1].nodes() if tuple(n) == tuple(cell.node))
        kwargs = copy.deepcopy(cell.kwargs)
        args[1].node_kwargs(node).clear(); args[1].node_kwargs(node).update(kwargs)
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('fault', ['export', 'local-index', 'ranks', 'joint-permutation'])
def test_scope_and_order_from_accepted_baseline(baseline, fault):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['units']  # Accepted baseline before authority tampering.
    index, unit, ports, cell = selected(args, prior)
    node = next(n for n in args[1].collective_scopes if tuple(n) == tuple(cell.node))
    scope = args[1].collective_scopes[node]
    if fault == 'export': scope = replace(scope, source_writer='nonempty-forgery')
    elif fault == 'local-index': scope = replace(scope, local_index=True)
    elif fault == 'ranks': scope = replace(scope, ranks=tuple(reversed(scope.ranks)))
    else:
        scope = replace(scope, input_tids=tuple(reversed(scope.input_tids)))
        cell.inputs.reverse()
        writer = next(w for w in args[1]._collective_source['writers'] if w['export_id'] == scope.source_writer)
        writer['inputs'].reverse()
    args[1].collective_scopes[node] = scope
    with pytest.raises(ValueError): api().render(*args)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('selected_writer', [False, True])
def test_complete_selected_and_bw_suffix_nonwrite(baseline, selected_writer):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    index, unit, ports, cell = selected(args, prior)
    assert predecessor.render(*args)[1]['units']
    step, _ = api()._boundary(index, cell, ports, unit['ranks'], 0)
    source, order = args[1], args[-1]['pm']
    _, row = api()._read(source, step, order)
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if selected_writer else source.nodes()[order['execution_to_source'][-1]]
    assert source.nodes().index(target) in row['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[-1]]
    if selected_writer: step = replace(step, outputs=(step.inputs[-1],))
    with pytest.raises(ValueError, match='operand.*written'): api()._read(source, step, order)


@pytest.mark.parametrize('fault', ['nondivisible', 'gap', 'partial-input', 'batch', 'value', 'rank'])
def test_input_derived_geometry_after_accepted_predecessor(baseline, fault):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['units']
    index, unit, ports, cell = selected(args, prior)
    if fault == 'partial-input':
        # T=2 has no intermediate length: empty is a strict partial report.
        cell._input_irs = []
    else:
        del cell._input_irs; del cell._output_irs
        if fault == 'nondivisible':
            changed = []
            for p in ports:
                sh = list(p.parent_shape); sh[1] += 1
                local = list(p.endpoint.shape); local[1] += 1
                bounds = list(p.bounds); bounds[1] = (0, sh[1])
                changed.append(replace(p, parent_shape=tuple(sh), bounds=tuple(bounds),
                    endpoint=replace(p.endpoint, shape=tuple(local))))
            ports = changed
            node = next(n for n in args[1].collective_scopes if tuple(n) == tuple(cell.node))
            args[1].collective_scopes[node] = replace(args[1].collective_scopes[node], input_shape=ports[0].endpoint.shape)
        elif fault == 'gap':
            p = ports[-1]; bounds = list(p.bounds); bounds[2] = (bounds[2][0]+1, bounds[2][1]+1)
            ports[-1] = replace(p, bounds=tuple(bounds))
        elif fault == 'batch':
            p = ports[-1]; bounds = list(p.bounds); bounds[0] = (1, p.parent_shape[0]+1)
            ports[-1] = replace(p, bounds=tuple(bounds))
        elif fault == 'value': ports[-1] = replace(ports[-1], value_part=(1, 2))
        elif fault == 'rank': ports = [replace(p, parent_shape=p.parent_shape[:3]) for p in ports]
    with pytest.raises(ValueError): api()._boundary(index, cell, ports, unit['ranks'], 0)


@pytest.mark.parametrize('fault', ['layout', 'axis', 'duplicate-unit', 'replicated-shape', 'replicated-value'])
def test_no_slot_identity_or_fake_replicated_gather(baseline, fault):
    args, prior = copy.deepcopy(baseline)
    assert predecessor.render(*args)[1]['units']
    if fault == 'duplicate-unit':
        prior['units'].append(copy.deepcopy(prior['units'][0]))
        prior['units'][-1]['slot'] += 100
    elif fault in ('layout', 'axis'):
        unit = next(u for u in prior['units'] if u['gather_axis'] == 2)
        unit['layout' if fault == 'layout' else 'gather_axis'] = 'replicated_within_dp' if fault == 'layout' else 1
    else:
        unit = next(u for u in prior['units'] if u['gather_axis'] is None)
        if fault == 'replicated-shape': unit['local_shape'][2] += 1
        else:
            unit['local_steps'][0]['outputs'][0]['value_part'] = (1, 2)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


def test_replicated_predecessor_optional_outputs_stay_replicated(baseline):
    args, prior = copy.deepcopy(baseline)
    for unit in prior['units']:
        if unit['gather_axis'] is not None: continue
        for descriptor in unit['local_steps']:
            cell = next(c for c in args[3]._inputs[1] if tuple(c.node) == tuple(descriptor['node']))
            del cell._output_irs
    fresh = predecessor.render(*args)[1]
    _, detail = api().render(*args)
    for old, unit in zip(fresh['units'], detail['frontier_units'], strict=True):
        if old['gather_axis'] is None: assert unit == old
