"""Own copy/extension of the portable original first-transpose fixture."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest

from scripts.tests import test_runtime_transpose_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_transpose_values as transpose


def api():
    assert importlib.util.find_spec('Verdict.runtime_post_transpose_values'), 'post-transpose renderer missing'
    return importlib.import_module('Verdict.runtime_post_transpose_values')


def fixture(D=2, tp=2, seqlen=2, branches=3, saved=False):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = copy.deepcopy(previous.fixture(D, tp, seqlen, branches, saved))
    old = copy.deepcopy(authority[2])
    rows, adapters = [], []
    for producer in list(pm.cells):
        if producer.opname != 'FW_transpose' or producer.kwargs != dict(dim0=1, dim1=2):
            continue
        x = producer._output_irs[0]
        if any(c.rank == producer.rank and producer.outputs[0] in c.inputs and
               not c.opname.startswith('BW_') for c in pm.cells):
            continue
        ranks = list(range(producer.rank//tp*tp, (producer.rank//tp+1)*tp))
        j = ranks.index(producer.rank)
        axis = next(d for d in (2, 3) if x.indmap[d] != (0, x.parent.shape[d]))
        bounds = list(x.indmap); bounds[axis] = (0, x.parent.shape[axis])
        if axis == 3:
            # Derive the split from the actual post-transpose head extent.
            width = x.parent.shape[1]//tp
            bounds[1] = (j*width, (j+1)*width)
            opname, kwargs, function = 'AllToAllPrim', dict(ranks=ranks, idim=3, odim=1), 'all_to_all'
        else:
            opname, kwargs, function = 'AllGatherPrim', dict(ranks=ranks, dim=2), 'all_gather'
        out = IR(x.tid+200, x.parent.name, x.parent.shape, tuple(bounds))
        cell = NS(node=N('p', producer.rank, 0, producer.node.cid+200, opname),
            rank=producer.rank, opname=opname, inputs=[T('p', r, 0, x.tid, 1) for r in ranks],
            outputs=[T('p', producer.rank, 0, out.tid, 1)],
            _input_irs=copy.deepcopy([x]), _output_irs=[out], kwargs=kwargs)
        cell.ir = NS(signature=opname, inputs=lambda c=cell: c._input_irs, outputs=lambda c=cell: c._output_irs)
        pm.cells.append(cell)
        pm.shapes.update({r: x.shape for r in cell.inputs}); pm.shapes[cell.outputs[0]] = out.shape
        row = dict(ref=dict(world='p', runtime_rank=cell.rank, microbatch=0,
            source_cid=cell.node.cid, call_instance=0, op=opname, origin='fixture'),
            source_irname=cell.node.irname, inputs=[tref(t) for t in cell.inputs],
            outputs=[tref(t) for t in cell.outputs], parameter_grad_tids=[], adapter_kwargs=copy.deepcopy(kwargs))
        adapter = copy.deepcopy(row)
        adapter['inputs'] = [tref(t) for t in cell.inputs if t.rank == cell.rank]
        adapter['primitive'] = dict(kind=opname, forward=True, kwargs=copy.deepcopy(kwargs),
            signature='nnscaler.runtime.adapter.'+function, generated_inputs=[f'first_{x.tid}'],
            generated_outputs=[f'next_{out.tid}'])
        rows.append(row); adapters.append(adapter)
        params = ', '.join(f'{k}={v!r}' for k, v in kwargs.items())
        line = f'        next_{out.tid} = nnscaler.runtime.adapter.{function}(first_{x.tid}, {params})'
        old['rank_sources'][str(cell.rank)] = old['rank_sources'][str(cell.rank)].replace(
            '\ndef _train_step', '\n'+line+'\ndef _train_step')
    snapshot = build_snapshot([*copy.deepcopy(old['writers']), *rows])
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = [*copy.deepcopy(old['adapter_source']), *adapters]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, branches=3, saved=False):
    data = fixture(D, tp, seqlen, branches, saved)
    base = previous.existing.existing.projection.norm.post.base
    with patch.object(base, 'add_fixture', return_value=data):
        return base.prepared(D, tp, seqlen)


def set_transpose_axes(source, cell, axes):
    kwargs = dict(dim0=axes[0], dim1=axes[1], __consts=[])
    cell.kwargs = copy.deepcopy(kwargs)
    node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
    source.node_kwargs(node).clear()
    source.node_kwargs(node).update(copy.deepcopy(kwargs))
    return kwargs


@pytest.fixture(scope='module')
def axis_admission_baseline():
    args = prepared()
    return args, api().render(*args)


@pytest.mark.parametrize('axes', [(-2, -1), (2, -1), (-2, 3)])
def test_transpose_axis_spellings_full_render(axis_admission_baseline, axes):
    original, (baseline_text, baseline) = axis_admission_baseline
    args = copy.deepcopy(original)
    nodes = {tuple(r['node']) for r in baseline['reads'] if r['op'] == 'FW_transpose'}
    changed = []
    for source, raw in zip(args[:2], args[3]._inputs[:2], strict=True):
        for cell in raw:
            if tuple(cell.node) in nodes:
                kwargs = set_transpose_axes(source, cell, axes)
                changed.append((source, cell, kwargs))
    assert len(changed) == 5
    assert sum(cell.node[0] == 's' for _, cell, _ in changed) == 1
    assert transpose.render(*args)[1]['units']  # Fresh predecessor accepts the actual spelling.
    with patch.object(transpose, 'render', wraps=transpose.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1
    assert fresh.call_args.args[-2] is args[-2] and fresh.call_args.args[-1] is args[-1]
    assert text == baseline_text
    assert detail['units'] == baseline['units']
    for row, expected in zip(detail['reads'], baseline['reads'], strict=True):
        if tuple(row['node']) in nodes:
            assert row['params'] == [2, 3]
            assert row['source_kwargs'] == dict(dim0=axes[0], dim1=axes[1], __consts=[])
            assert {k: v for k, v in row.items() if k != 'source_kwargs'} == {
                k: v for k, v in expected.items() if k != 'source_kwargs'}
        else:
            assert row == expected
    for source, cell, kwargs in changed:
        assert cell.kwargs == kwargs
        assert source.node_kwargs(cell.node) == kwargs


@pytest.mark.parametrize('axes', [(-6, -1), (-2, -5), (4, -1), (-2, 4),
    (True, -1), (-2, False), (2.0, -1), (-2, 3.0), (3, 2), (-1, -2)])
def test_transpose_axis_admission_rejects_invalid(axis_admission_baseline, axes):
    from Verdict.runtime_lineage import _Index
    original, (_, baseline) = axis_admission_baseline
    args = copy.deepcopy(original)
    row = next(r for r in baseline['reads'] if r['op'] == 'FW_transpose' and r['world'] == 'pm')
    index = _Index(args[1], args[3]._inputs[1])
    cell = next(c for c in args[3]._inputs[1] if tuple(c.node) == tuple(row['node']))
    producer = api().post._port(index, cell.inputs[0], cell._input_irs[0])
    set_transpose_axes(args[1], cell, axes)
    with pytest.raises(ValueError):
        api()._transpose(index, cell, producer)


@pytest.mark.parametrize('tp', [2, 3])
def test_replicated_membership_eliminates_empty_tail(tp):
    text, detail = api().render(*prepared(tp=tp, seqlen=6))
    replicated = [u for u in detail['units'] if u['layout'] == 'replicated_within_dp']
    assert replicated
    for unit in replicated:
        proof = text.split('theorem '+unit['theorem']+' ', 1)[1].split('#print axioms', 1)[0]
        assert 'simp only [List.mem_cons, List.not_mem_nil, or_false] at hy' in proof
        assert 'rcases hy with '+ ' | '.join(['rfl']*tp) in proof


def test_mixed_frontier_tracer():
    args = prepared()
    prior = transpose.render(*args)[1]
    assert len(prior['reads']) == 19 and len(prior['units']) == 6
    text, detail = api().render(*args)
    assert len(detail['reads']) == 13 and len(detail['units']) == 6
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 4
    assert text.count('SourceLayoutRead.transposeAxes_value_of_split') == 5
    assert text.count('SourceAllGatherRead.allGather_value_of_split') == 4
    assert [(u['unit'], u['slot']) for u in detail['units']] == [(u['unit'], u['slot']) for u in prior['units']]
    assert {u['layout'] for u in detail['units']} == {'sharded', 'replicated_within_dp'}
    assert {u['gather_axis'] for u in detail['units']} == {1, 2, None}
    assert 'SourceRank4ReverseExchange.axis3_output_facts' in text
    assert 'source_transpose23_inner_unit_output_reconstruct' in text
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False


def selected(args, kind='AllToAllPrim'):
    from Verdict.runtime_lineage import _Index
    prior = transpose.render(*args)[1]
    index = _Index(args[1], args[3]._inputs[1])
    for unit in prior['units']:
        ports = [transpose._output(index, d) for d in unit['local_steps']]
        cell = api().view._consumer(index, ports[0])
        if cell.opname == kind:
            return index, unit, ports, cell
    raise AssertionError('fixture family missing')


@pytest.mark.parametrize('fault', ['inputs', 'outputs'])
def test_writer_fullrefs_are_independently_authenticated(fault):
    args = prepared()
    index, unit, ports, cell = selected(args)
    writer = next(w for w in args[1]._collective_source['writers']
        if w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    writer[fault][0]['version'] += 1
    with pytest.raises(ValueError, match='writer'):
        api()._boundary(index, cell, ports, unit['ranks'], 0)


@pytest.mark.parametrize('D,tp,seqlen,branches,saved', [
    (2, 2, 2, 3, True), (3, 2, 6, 4, False), (2, 3, 6, 5, False), (1, 2, 6, 1, False)])
def test_portable_variable_asymmetric_saved(D, tp, seqlen, branches, saved):
    args = prepared(D, tp, seqlen, branches, saved)
    before = copy.deepcopy(args[-1])
    with patch.object(transpose, 'render', wraps=transpose.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1
    assert fresh.call_args.args[-2] is args[-2] and fresh.call_args.args[-1] is args[-1]
    assert before == args[-1]
    assert len(detail['units']) == D*branches
    assert len(detail['reads']) == D*tp*branches + int(branches > 1)
    assert detail['lean_bytes'] == len(text.encode())
    for unit in detail['units']:
        fragment = text.split('theorem '+unit['theorem']+' ')[1].split('#print axioms')[0]
        assert fragment.split(' := by')[0].count('(h') == 3
        assert unit['predecessor']+' s p t q hs hp hvalues' in fragment
        assert '(∀ y ∈ ' in fragment
        assert unit['global_shape'][0] == D*unit['local_shape'][0]
        for step in unit['local_steps']:
            read = next(r for r in detail['reads'] if tuple(r['node']) == tuple(step['node']))
            assert read['theorem']+' p q hp' in fragment
        if unit['layout'] == 'replicated_within_dp':
            assert unit['gather_axis'] is None
            statement = fragment.split(' := by')[0]
            assert '∀ y ∈ ' in statement and 'y = chunkPrimDimN 0 ' in statement
            assert 'allGatherPrimDimN' not in statement
    for read in detail['reads']:
        assert read['operand_nonwrite_source_indices'] == args[-1][read['world']]['execution_to_source'][read['execution_index']:]
        assert len(read['input_refs']) == len(read['source_step']['inputs'])
        assert read['dimensions'] and 'gather_axis' in read and 'layout' in read
    if saved:
        for source, label in zip(args[:2], ['sm', 'pm']):
            bw = {i for i, n in enumerate(source.nodes()) if source.node_opname(n).startswith('BW_')}
            assert bw and bw <= set(args[-1][label]['execution_to_source'])
    for bad in ('sorry', 'admit', 'native_decide', '(hshape :', '(houtput :', 'axiom '):
        assert bad not in text


@pytest.mark.parametrize('kind', ['AllToAllPrim', 'AllGatherPrim'])
@pytest.mark.parametrize('fault', ['input-parent', 'input-value', 'output-parent', 'output-bounds',
    'output-value', 'output-tid', 'bool', 'partial', 'wrong-local'])
def test_metadata_rejects_after_fresh_predecessor_acceptance(kind, fault):
    args = prepared()
    index, unit, ports, cell = selected(args, kind)
    field = '_input_irs' if fault.startswith('input') or fault == 'wrong-local' else '_output_irs'
    irs = copy.deepcopy(getattr(cell, field)); setattr(cell, field, irs); ir = irs[0]
    if fault.endswith('parent'): ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
    elif fault.endswith('value'): ir.valmap = (1, 2)
    elif fault == 'bool': ir.valmap = (False, 1)
    elif fault == 'output-bounds': ir.indmap = ((1, ir.indmap[0][1]+1), *ir.indmap[1:])
    elif fault == 'output-tid': ir.tid += 1
    elif fault == 'partial': irs.clear()
    else:
        other = api().view._consumer(index, ports[-1])
        cell._input_irs = copy.deepcopy(other._input_irs)
    assert transpose.render(*args)[1]['units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('kind', ['AllToAllPrim', 'AllGatherPrim'])
@pytest.mark.parametrize('coverage', ['absent', 'local-only', 'all-peers'])
def test_optional_metadata_coverage(kind, coverage):
    args = prepared()
    index, unit, ports, first = selected(args, kind)
    originals = [copy.deepcopy(api().view._consumer(index, p)._input_irs[0]) for p in ports]
    for p in ports:
        cell = api().view._consumer(index, p)
        if coverage == 'absent': del cell._input_irs; del cell._output_irs
        elif coverage == 'all-peers': cell._input_irs = copy.deepcopy(originals)
    _, detail = api().render(*args)
    rows = [r for r in detail['reads'] if r['op'] == kind and r['unit'] == unit['unit']]
    assert rows and all(r['input_metadata'] == coverage for r in rows)


@pytest.mark.parametrize('fault', ['unknown', 'mixed', 'missing', 'ambiguous', 'version', 'owner',
    'bool', 'float', 'extra', 'missing-kw', 'axes', 'ranks'])
def test_frontier_and_exact_kwargs(fault):
    args = prepared()
    index, unit, ports, cell = selected(args)
    prior = transpose.render(*args)[1]
    raw = args[3]._inputs[1]
    if fault == 'unknown': cell.opname = 'FW_contiguous'
    elif fault == 'mixed': cell.opname = 'AllGatherPrim'
    elif fault == 'missing': raw.remove(cell)
    elif fault == 'ambiguous': raw.append(copy.copy(cell))
    elif fault == 'version': cell.inputs[0] = cell.inputs[0]._replace(v=0)
    elif fault == 'owner': cell.rank += 1
    else:
        changes = {'bool': dict(idim=True), 'float': dict(idim=3.0), 'extra': dict(extra=1),
            'axes': dict(odim=2), 'ranks': dict(ranks=list(reversed(unit['ranks'])))}
        if fault == 'missing-kw': cell.kwargs.pop('idim')
        else: cell.kwargs.update(changes[fault])
        node = next(n for n in args[1].nodes() if tuple(n) == tuple(cell.node))
        kwargs = copy.deepcopy(cell.kwargs)
        args[1].node_kwargs(node).clear(); args[1].node_kwargs(node).update(kwargs)
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('kind', ['AllToAllPrim', 'AllGatherPrim', 'FW_transpose'])
@pytest.mark.parametrize('selected_writer', [False, True])
def test_all_ports_selected_and_full_suffix_nonwrites(kind, selected_writer):
    from dataclasses import replace
    args = prepared(saved=True)
    index, unit, ports, cell = selected(args, kind)
    step = (api()._transpose(index, cell, ports[0]) if kind == 'FW_transpose'
        else api()._boundary(index, cell, ports, unit['ranks'], 0)[0])
    source, order = args[1], args[-1]['pm']
    _, healthy = api()._read(source, 'pm', step, order)
    node = next(n for n in source.nodes() if tuple(n) == step.node)
    target = node if selected_writer else source.nodes()[order['execution_to_source'][-1]]
    assert source.nodes().index(target) in healthy['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[-1]]
    if selected_writer: step = replace(step, outputs=(step.inputs[-1],))
    with pytest.raises(ValueError, match='operand.*written'): api()._read(source, 'pm', step, order)


@pytest.mark.parametrize('fault', ['bounds', 'parent', 'value'])
def test_joint_transpose23_outputs_cannot_replace_coordinate_transport(fault):
    args = prepared()
    for raw in args[3]._inputs[:2]:
        for cell in raw:
            if cell.opname != 'FW_transpose' or cell.node.cid != 601: continue
            ir = cell._output_irs[0]
            if fault == 'value': ir.valmap = (1, 2)
            elif fault == 'parent': ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
            else: ir.indmap = (*ir.indmap[:-1], (1, ir.indmap[-1][1]+1))
    assert transpose.render(*args)[1]['units']
    with pytest.raises(ValueError): api().render(*args)


def test_shared_global_read_retains_first_emission_annotations():
    _, detail = api().render(*prepared())
    read = next(r for r in detail['reads'] if r['world'] == 'sm')
    owner = next(u for u in detail['units'] if u['unit'] == read['unit'] and u['slot'] == read['slot'])
    assert read['dimensions'] is owner['dimensions']


@pytest.mark.parametrize('kind', ['AllToAllPrim', 'AllGatherPrim'])
@pytest.mark.parametrize('fault', ['export', 'call', 'local-index', 'ranks', 'joint-permutation'])
def test_scope_identity_and_order_guards(kind, fault):
    from dataclasses import replace
    args = prepared()
    index, unit, ports, cell = selected(args, kind)
    node = next(n for n in args[1].collective_scopes if tuple(n) == tuple(cell.node))
    scope = args[1].collective_scopes[node]
    if fault == 'export': scope = replace(scope, source_writer='nonempty-forgery')
    elif fault == 'local-index': scope = replace(scope, local_index=True)
    elif fault == 'ranks': scope = replace(scope, ranks=tuple(reversed(scope.ranks)))
    elif fault == 'call':
        writer = next(w for w in args[1]._collective_source['writers'] if w['export_id'] == scope.source_writer)
        writer['ref']['call_instance'] += 1
    else:
        ports = list(reversed(ports))
        scope = replace(scope, input_tids=tuple(p.endpoint.tid for p in ports))
        cell.inputs.reverse(); cell._input_irs = list(reversed(copy.deepcopy([
            api().view._consumer(index, p)._input_irs[0] for p in reversed(ports)])))
    args[1].collective_scopes[node] = scope
    with pytest.raises(ValueError): api()._boundary(index, cell, ports, unit['ranks'], 0)
