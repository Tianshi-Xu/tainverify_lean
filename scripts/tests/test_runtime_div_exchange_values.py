"""Original post-matmul AA source tests; no capture or kernel claims."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_div_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_div_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_div_exchange_values'), 'matmul exchange renderer missing'
    return importlib.import_module('Verdict.runtime_div_exchange_values')


def fixture(D=2, tp=2, seqlen=2, branches=3):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters
    sm, pm, authority = previous.fixture(D, tp, seqlen, branches)
    old = copy.deepcopy(authority[2]); rows, adapters = [], []
    for producer in list(pm.cells):
        if producer.node.cid != 9600: continue
        x = producer._output_irs[0]
        ranks = list(range(producer.rank//tp*tp, (producer.rank//tp+1)*tp))
        j = ranks.index(producer.rank); bounds = list(x.indmap)
        bounds[3] = (0, x.parent.shape[3]); width = x.parent.shape[1]//tp
        bounds[1] = (j*width, (j+1)*width)
        out = IR(9800, x.parent.name, x.parent.shape, tuple(bounds))
        kwargs = dict(ranks=ranks, idim=3, odim=1)
        peers = [next(c for c in pm.cells if c.rank == r and c.node.cid == 9600) for r in ranks]
        cell = NS(node=N('p', producer.rank, 0, 9800, 'AllToAllPrim'), rank=producer.rank,
            opname='AllToAllPrim', inputs=[p.outputs[0] for p in peers],
            outputs=[T('p', producer.rank, 0, 9800, 1)], kwargs=kwargs,
            _input_irs=[copy.deepcopy(p._output_irs[0]) for p in peers], _output_irs=[out])
        cell.ir = NS(signature=cell.opname, inputs=lambda c=cell: c._input_irs,
            outputs=lambda c=cell: c._output_irs)
        # Rewire the actual PM forward consumers, retaining their schedule.
        for consumer in pm.cells:
            if consumer.rank == producer.rank and producer.outputs[0] in consumer.inputs and not consumer.opname.startswith('BW_'):
                for i, ref in enumerate(consumer.inputs):
                    if ref == producer.outputs[0]:
                        consumer.inputs[i] = cell.outputs[0]
                        consumer._input_irs[i] = copy.deepcopy(out)
                        for w in old['writers'] + old['adapter_source']:
                            if w['ref']['runtime_rank'] == consumer.rank and w['ref']['source_cid'] == consumer.node.cid:
                                w['inputs'][i] = tref(cell.outputs[0])
        pm.cells.append(cell); pm.shapes[cell.outputs[0]] = out.shape
        row = dict(ref=dict(world='p', runtime_rank=cell.rank, microbatch=0, source_cid=9800,
            call_instance=0, op='AllToAllPrim', origin='fixture'), source_irname='AllToAllPrim',
            inputs=[tref(t) for t in cell.inputs], outputs=[tref(t) for t in cell.outputs],
            parameter_grad_tids=[], adapter_kwargs=copy.deepcopy(kwargs))
        rows.append(row); adapter = copy.deepcopy(row)
        adapter['inputs'] = [tref(producer.outputs[0])]
        adapter['primitive'] = dict(kind='AllToAllPrim', forward=True, kwargs=copy.deepcopy(kwargs),
            signature='nnscaler.runtime.adapter.all_to_all', generated_inputs=['scaled'], generated_outputs=['headscore'])
        params = ', '.join(f'{k}={v!r}' for k, v in kwargs.items())
        old['rank_sources'][str(cell.rank)] = old['rank_sources'][str(cell.rank)].replace(
            '\ndef _train_step', '\n        headscore = nnscaler.runtime.adapter.all_to_all(scaled, '+params+')\ndef _train_step')
        adapters.append(adapter)
    def interleave(original, extra):
        # All peer matmuls must precede the collective's expanded input reads.
        early = [w for w in original if not w['ref']['op'].startswith('BW_')
            and (w['ref']['source_cid'] < 9100 or w['ref']['source_cid'] in (9500, 9600))]
        late = [w for w in original if w not in early]
        return [*early, *extra, *late]
    early = [c for c in pm.cells if not c.opname.startswith('BW_')
        and (c.node.cid < 9100 or c.node.cid in (9500, 9600))]
    exchanges = [c for c in pm.cells if c.node.cid == 9800]
    pm.cells[:] = early + exchanges + [c for c in pm.cells if c not in early and c not in exchanges]
    snapshot = build_snapshot(interleave(old['writers'], rows))
    snapshot.update({k: copy.deepcopy(old[k]) for k in ('source', 'runtime_ndevs', 'rank_sources')})
    snapshot['adapter_source'] = interleave(old['adapter_source'], adapters)
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(D=2, tp=2, seqlen=2, branches=3):
    base = previous.previous.previous.previous.previous.previous.existing.existing.projection.norm.post.base
    with patch.object(base, 'add_fixture', return_value=fixture(D, tp, seqlen, branches)):
        return base.prepared(D, tp, seqlen)


def test_next_pm_tracer():
    args = prepared(); prior = predecessor.render(*args)[1]
    before = copy.deepcopy(args[-1])
    with patch.object(predecessor, 'render', wraps=predecessor.render) as fresh:
        text, detail = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a, b in zip(fresh.call_args.args, args, strict=True))
    assert [len(detail[k]) for k in ('reads', 'units', 'deferred_units', 'frontier_units')] == [4, 2, 2, 4]
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 4
    assert text.count('SourceRank4ReverseExchange.axis3_output_facts') == 2
    assert args[-1] == before
    for old, new in zip(prior['frontier_units'], detail['frontier_units'], strict=True):
        if old['gather_axis'] is None:
            assert new == old and new['layout'] == 'replicated_within_dp'
        else:
            assert 'slot' not in new
            assert new['predecessor'] == old['facts_theorem']
            assert new['sm_output_ref'] == old['sm_output_ref']
            assert new['source_step'] == old['source_step']
            assert new['source_step']['op'] == 'FW_div'
            assert new['global_shape'] == [2, 4, 2, 2]
            assert new['local_shape'] == [1, 2, 2, 2]
            assert new['gather_axis'] == 1
            fragment = text.split('theorem '+new['facts_theorem']+' ', 1)[1].split('#print axioms')[0]
            assert fragment.split(' := by')[0].count('(h') == 3
            assert old['facts_theorem']+' s p t q hs hp hvalues' in fragment
    for r in detail['reads']:
        assert (r['world'], r['gather_axis'], r['output_gather_axis'], r['params']) == ('pm', 3, 1, [3, 1])
        assert r['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][r['execution_index']:]
    assert all(not d['value_proved'] and d['first_consumers'] for d in detail['deferred_units'])
    assert 'UNCOMPILED' in text
    for flag in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement'):
        assert detail[flag] is False
    for forbidden in ('sorry', 'admit', 'native_decide', 'axiom ', 'fw_div', 'fw_softmax', '(hshape :', '(houtput :'):
        assert forbidden not in text


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def cells(args):
    return [c for c in args[3]._inputs[1] if c.node.cid == 9800]


@pytest.mark.parametrize('D,tp,seqlen,branches', [(3, 2, 6, 4), (2, 3, 6, 5), (3, 3, 9, 3), (1, 2, 4, 2)])
def test_dimensions_and_complete_order(D, tp, seqlen, branches):
    args = prepared(D, tp, seqlen, branches)
    prior = predecessor.render(*args)[1]
    if any(u['gather_axis'] not in (3, None) for u in prior['frontier_units']):
        # Extra synthetic branches are sharded, not replicated V. A new
        # unsupported frontier must fail closed, never disappear or change kind.
        with pytest.raises(ValueError, match='deferred.*replicated'):
            api().render(*args)
        return
    text, detail = api().render(*args)
    assert len(detail['reads']) == D*tp
    assert len(detail['units']) == D
    assert len(detail['deferred_units']) == D*(branches-2)
    assert len(detail['frontier_units']) == D*(branches-1)
    for u in detail['units']:
        assert u['global_shape'] == [D, 2*tp, seqlen, seqlen]
        assert u['local_shape'] == [1, 2, seqlen, seqlen]
        assert u['dimensions']['S'] == 2 and u['dimensions']['H'] == seqlen
        assert f"axis3_output_facts {D} {u['unit']} {tp} 1 2 {seqlen} {seqlen//tp}" in text
    for source, label in zip(args[:2], ('sm', 'pm'), strict=True):
        bw = {i for i, n in enumerate(source.nodes()) if source.node_opname(n).startswith('BW_')}
        assert bw and bw <= set(args[-1][label]['execution_to_source'])


@pytest.mark.parametrize('mode', ['absent', 'local-only', 'all-peers'])
def test_optional_raw_ir_truthful(baseline, mode):
    args, _ = copy.deepcopy(baseline)
    for c in cells(args):
        if mode == 'absent':
            del c._input_irs; del c._output_irs
        elif mode == 'local-only':
            c._input_irs = [c._input_irs[c.rank % 2]]
    assert predecessor.render(*args)[1]['frontier_units']
    _, detail = api().render(*args)
    assert {r['input_metadata'] for r in detail['reads']} == {mode}
    assert {r['output_metadata'] for r in detail['reads']} == {'absent' if mode == 'absent' else 'present'}


@pytest.mark.parametrize('field', ['_input_irs', '_output_irs'])
@pytest.mark.parametrize('fault', ['name', 'parent', 'bounds', 'batch', 'value', 'shape', 'empty'])
def test_new_paired_metadata_guard_after_accepted_predecessor(baseline, field, fault):
    args, _ = copy.deepcopy(baseline); c = cells(args)[0]
    irs = copy.deepcopy(getattr(c, field)); setattr(c, field, irs)
    ir = irs[-1]
    if fault == 'empty': setattr(c, field, [])
    elif fault == 'name': ir.parent.name = 'wrong-parent'
    elif fault == 'parent': ir.parent.shape = (*ir.parent.shape[:-1], ir.parent.shape[-1]+1)
    elif fault == 'value': ir.valmap = (1, 2)
    elif fault == 'shape': ir.indmap = (*ir.indmap[:-1], (0, 99))
    else:
        bounds = list(ir.indmap); axis = 0 if fault == 'batch' else 3
        lo, hi = bounds[axis]; bounds[axis] = (lo+1, hi+1); ir.indmap = tuple(bounds)
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


def test_partial_peer_metadata_after_accepted_predecessor():
    args = prepared(tp=3, seqlen=6)
    cells(args)[0]._input_irs = cells(args)[0]._input_irs[:2]
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='partial'): api().render(*args)


@pytest.mark.parametrize('fault', ['inputs', 'outputs', 'call', 'export', 'scope', 'ranks', 'local-index', 'params', 'kwargs'])
def test_authority_mutants_report_upstream_rejection(baseline, fault):
    from dataclasses import replace
    args, _ = copy.deepcopy(baseline); c = cells(args)[0]; source = args[1]
    node = next(n for n in source.nodes() if tuple(n) == tuple(c.node))
    writer = next(w for w in source._collective_source['writers'] if w['ref']['runtime_rank'] == c.rank and w['ref']['source_cid'] == c.node.cid)
    if fault in ('inputs', 'outputs'): writer[fault][0]['version'] += 1
    elif fault == 'call': writer['ref']['call_instance'] += 1
    elif fault == 'export': writer['export_id'] = 'forged'
    elif fault == 'scope': source.collective_scopes[node] = replace(source.collective_scopes[node], source_writer='forged')
    elif fault == 'ranks': source.collective_scopes[node] = replace(source.collective_scopes[node], ranks=(1, 0))
    elif fault == 'local-index': source.collective_scopes[node] = replace(source.collective_scopes[node], local_index=1)
    elif fault == 'params': source.collective_scopes[node] = replace(source.collective_scopes[node], params=(2, 3))
    else: c.kwargs['extra'] = 1
    if fault == 'kwargs':
        assert predecessor.render(*args)[1]['frontier_units']
    else:
        with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault', ['missing', 'unknown', 'mixed', 'duplicate'])
def test_consumer_upstream_rejection_and_private_new_guard(baseline, fault):
    args, prior = copy.deepcopy(baseline); cs = cells(args)
    if fault == 'missing': args[3]._inputs[1].remove(cs[0])
    elif fault == 'duplicate':
        c = copy.deepcopy(cs[0]); c.node = N('p', c.rank, 0, 9900, c.opname)
        args[3]._inputs[1].append(c)
    else:
        for c in (cs if fault == 'unknown' else cs[:1]): c.opname = 'FW_unknown'
    with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)
    # Isolate the new discovery guard too, without claiming upstream acceptance.
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


def seam(args, prior):
    from Verdict.runtime_lineage import _Index
    from Verdict import runtime_middle_exchange_values as middle
    index = _Index(args[1], args[3]._inputs[1])
    old = next(u for u in prior['frontier_units'] if u['gather_axis'] == 3)
    ports = [middle._output(index, s) for s in old['local_steps']]
    return index, old, ports, cells(args)[0]


@pytest.mark.parametrize('fault', ['order', 'owner', 'batch', 'other-axis', 'cover', 'split', 'value'])
def test_boundary_independent_input_geometry(baseline, fault):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    index, old, ports, c = seam(args, prior)
    if fault == 'order': ports.reverse()
    elif fault == 'owner':
        with pytest.raises(ValueError): api()._boundary(index, c, ports, old['ranks'], 1)
        return
    else:
        p = ports[-1]; bounds = list(p.bounds); parent = p.parent_shape
        if fault == 'batch': bounds[0] = (1, 2)
        elif fault == 'other-axis': bounds[2] = (1, 3)
        elif fault == 'cover': bounds[3] = (1, 3)
        elif fault == 'split': parent = (parent[0], 3, *parent[2:])
        ports[-1] = replace(p, bounds=tuple(bounds), parent_shape=parent,
            value_part=(1, 2) if fault == 'value' else p.value_part)
    with pytest.raises(ValueError): api()._boundary(index, c, ports, old['ranks'], 0)


@pytest.mark.parametrize('selected', [False, True])
@pytest.mark.parametrize('position', [0, 1])
def test_actual_all_peer_read_selected_and_full_suffix_nonwrites(baseline, selected, position):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    index, old, ports, c = seam(args, prior)
    step, _ = api()._boundary(index, c, ports, old['ranks'], 0)
    source = args[1]; node = next(n for n in source.nodes() if tuple(n) == step.node)
    _, read = api()._read(source, step, args[-1]['pm'])
    target = node if selected else source.nodes()[args[-1]['pm']['execution_to_source'][-1]]
    assert source.nodes().index(target) in read['operand_nonwrite_source_indices']
    source._node2outputs[target] = [source.node_inputs(node)[position]]
    if selected: step = replace(step, outputs=(step.inputs[position],))
    with pytest.raises(ValueError, match='operand.*written'): api()._read(source, step, args[-1]['pm'])


def test_order_is_all_old_frontier_not_slots(baseline):
    args, prior = copy.deepcopy(baseline)
    prior['frontier_units'].reverse()
    _, detail = api()._render(args[0], args[1], args[3], args[-1], prior)
    assert [u['gather_axis'] for u in detail['frontier_units']] == [None, 1, None, 1]
    for old, new in zip(prior['frontier_units'], detail['frontier_units'], strict=True):
        assert new['sm_output_ref'] == old['sm_output_ref']
        if old['gather_axis'] is None: assert new is old


@pytest.mark.parametrize('fault', ['rank-order', 'DP-owner', 'layout', 'duplicate'])
def test_private_inventory_guards(baseline, fault):
    args, prior = copy.deepcopy(baseline)
    old = prior['frontier_units'][0]
    if fault == 'rank-order': old['ranks'].reverse()
    elif fault == 'DP-owner': old['positions'] = [99]
    elif fault == 'layout': old['layout'] = 'replicated_within_dp'
    else: prior['frontier_units'].append(copy.deepcopy(old))
    with pytest.raises(ValueError): api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('fault', ['idim', 'odim', 'ranks', 'consts', 'bool'])
def test_raw_kwargs_new_guard_after_accepted_predecessor(baseline, fault):
    args, _ = copy.deepcopy(baseline); c = cells(args)[0]
    if fault == 'consts': c.kwargs['__consts'] = [4]
    elif fault == 'bool': c.kwargs['idim'] = True
    elif fault == 'ranks': c.kwargs['ranks'] = list(reversed(c.kwargs['ranks']))
    else: c.kwargs[fault] = 2
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('width', [0, 3])
def test_positive_exact_split_guard_not_peer_mismatch(baseline, width):
    from dataclasses import replace
    args, prior = copy.deepcopy(baseline)
    index, old, ports, c = seam(args, prior)
    ports = [replace(p, parent_shape=(p.parent_shape[0], width, *p.parent_shape[2:]),
        bounds=(p.bounds[0], (0, width), *p.bounds[2:]),
        endpoint=replace(p.endpoint, shape=(p.endpoint.shape[0], width, *p.endpoint.shape[2:]))) for p in ports]
    node = next(n for n in args[1].nodes() if tuple(n) == tuple(c.node))
    args[1].collective_scopes[node] = replace(args[1].collective_scopes[node], input_shape=ports[0].endpoint.shape)
    with pytest.raises(ValueError, match='nondivisible actual split'):
        api()._boundary(index, c, ports, old['ranks'], 0)


def test_coordinated_output_owner_swap_after_accepted_predecessor(baseline):
    args, _ = copy.deepcopy(baseline)
    for c in cells(args):
        ir = copy.deepcopy(c._output_irs[0]); c._output_irs = [ir]
        lo, hi = ir.indmap[1]; width = hi-lo
        other = (c.rank % 2+1) % 2
        ir.indmap = (ir.indmap[0], (other*width, (other+1)*width), *ir.indmap[2:])
    assert predecessor.render(*args)[1]['frontier_units']
    with pytest.raises(ValueError, match='original paired metadata'): api().render(*args)


def test_value_order_oracle_is_split_each_source_then_concat():
    # CPU index-formula replay, not execution of a distributed runtime/kernel.
    import numpy as np
    D, Tn, B, S, H, C = 3, 3, 2, 2, 5, 4
    global_ = np.arange(D*B*S*Tn*H*C*Tn).reshape(D*B, S*Tn, H, C*Tn)
    for u in range(D):
        batch = global_[u*B:(u+1)*B]
        inputs = np.split(batch, Tn, axis=3)
        outputs = [np.concatenate([np.split(x, Tn, axis=1)[j] for x in inputs], axis=3) for j in range(Tn)]
        assert all(y.shape == (B, S, H, C*Tn) for y in outputs)
        assert np.array_equal(np.concatenate(outputs, axis=1), batch)
        assert not np.array_equal(np.concatenate(outputs[::-1], axis=1), batch)
        wrong = [np.concatenate([np.split(x, Tn, axis=1)[j] for x in inputs[::-1]], axis=3) for j in range(Tn)]
        assert not np.array_equal(np.concatenate(wrong, axis=1), batch)


def test_deferred_requires_exact_replicated_none(baseline):
    args, prior = copy.deepcopy(baseline)
    # Private receipt seam: a singleton replica also satisfies sharded shape
    # equations. Not a claim of public acceptance of a forged unit config.
    old = next(u for u in prior['frontier_units'] if u['gather_axis'] is None)
    prior['frontier_units'] = [old]
    old['dimensions']['T'] = 1
    for key in ('ranks', 'positions', 'local_steps', 'pm_output_refs', 'pm_output_tids'):
        old[key] = old[key][:1]
    owner = next(u for u in args[3]._inputs[3]['config']['units'] if u['unit'] == old['unit'])
    owner['ranks'] = old['ranks']; owner['positions'] = old['positions']
    old['layout'] = 'sharded'; old['gather_axis'] = 1
    with pytest.raises(ValueError, match='deferred.*replicated'):
        api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('fault', ['owner', 'positions', 'execution-order', 'output-arity', 'input-arity'])
def test_original_authority_rejects_mutation(baseline, fault):
    args, _ = copy.deepcopy(baseline); c = cells(args)[0]
    if fault in ('owner', 'positions'):
        unit = args[3]._inputs[3]['config']['units'][0]
        if fault == 'owner': unit['ranks'].reverse()
        else: unit['positions'] = [99]
    elif fault == 'execution-order': args[-1]['pm']['execution_to_source'].reverse()
    elif fault == 'output-arity': c.outputs.append(c.outputs[0])
    else: c.inputs.append(c.inputs[0])
    if fault in ('output-arity', 'input-arity'):
        assert predecessor.render(*args)[1]['frontier_units']
    else:
        with pytest.raises(ValueError): predecessor.render(*args)
    with pytest.raises(ValueError): api().render(*args)


def test_deferred_original_sm_pm_port_correspondence(baseline):
    args, prior = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 9200)
    cell.inputs.reverse(); cell._input_irs.reverse()
    source = args[1]; node = next(n for n in source.nodes() if tuple(n) == tuple(cell.node))
    source._node2inputs[node].reverse()
    writer = next(w for w in source._collective_source['writers']
        if w['ref']['source_cid'] == cell.node.cid and w['ref']['runtime_rank'] == cell.rank)
    writer['inputs'].reverse()
    # Private binding seam, not public snapshot acceptance.
    with pytest.raises(ValueError, match='deferred.*port'):
        api()._render(args[0], args[1], args[3], args[-1], prior)


@pytest.mark.parametrize('position', [0, 1])
def test_actual_backward_suffix_nonwrite(baseline, position):
    args, prior = copy.deepcopy(baseline)
    index, old, ports, c = seam(args, prior)
    step, _ = api()._boundary(index, c, ports, old['ranks'], 0)
    source = args[1]
    _, read = api()._read(source, step, args[-1]['pm'])
    bw = next(n for i, n in enumerate(source.nodes()) if source.node_opname(n).startswith('BW_')
        and i in read['operand_nonwrite_source_indices'])
    source._node2outputs[bw] = [source.node_inputs(next(n for n in source.nodes() if tuple(n) == step.node))[position]]
    with pytest.raises(ValueError, match='operand.*written'):
        api()._read(source, step, args[-1]['pm'])


def test_complete_requests_and_unadvanced_sm_softmax(baseline):
    args, prior = copy.deepcopy(baseline)
    before = [(list(s.nodes()), copy.deepcopy(o)) for s, o in zip(args[:2], (args[-1]['sm'], args[-1]['pm']))]
    assert any(s['op'] == 'FW_div' for u in prior['units'] for s in [u['source_step']])
    assert any(args[0].node_opname(n) == 'FW_softmax' for n in args[0].nodes())
    # Unproved softmax metadata is neither an input equation nor an output
    # shape hypothesis at this communication checkpoint.
    cell = next(c for c in args[3]._inputs[0] if c.opname == 'FW_softmax')
    cell._output_irs[0].parent.name = 'unproved-softmax-output'
    assert predecessor.render(*args)[1]['frontier_units']
    text, detail = api().render(*args)
    assert all(u['source_step']['op'] == 'FW_div' for u in detail['units'])
    assert 'fw_softmax' not in text
    for source, (nodes, order), label in zip(args[:2], before, ('sm', 'pm')):
        assert source.nodes() == nodes and args[-1][label] == order
        assert sorted(order['execution_to_source']) == list(range(len(nodes)))
