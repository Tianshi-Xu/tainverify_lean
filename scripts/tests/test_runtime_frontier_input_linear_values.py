"""Portable source-backed input-column linear/RS tracer; no kernel claim."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_projection_exchange_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_projection_exchange_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_input_linear_values'), 'input linear renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_input_linear_values')


def fixture(D=2, tp=2, seqlen=2, alias_tid=271003, metadata='local-only'):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D=D, tp=tp, seqlen=seqlen, alias_tid=alias_tid, metadata=metadata)
    old = copy.deepcopy(authority[2]); rows = []; adapters = []
    for slot in (1, 2):
        full = next(c for c in sm.cells if c.node.cid == alias_tid+2000+slot)
        full.ir.signature = 'torch.nn.functional.linear'
        full._output_irs[0] = IR(full.outputs[0].tid, f'projection.output.{slot}', (D,seqlen,3*tp))
        full._output_irs[0].parent.tid = alias_tid+6000+slot
        sm.shapes[full.outputs[0]] = full._output_irs[0].shape
        for rank in range(D*tp):
            linear = next(c for c in pm.cells if c.rank == rank and c.node.cid == alias_tid+6000+slot)
            linear.ir.signature = 'torch.nn.functional.linear'
            linear._output_irs[0].parent.shape = (*linear._input_irs[0].parent.shape[:2],3*tp)
            linear._output_irs[0].valmap = (rank % tp, tp)
            ranks = list(range(rank//tp*tp,(rank//tp+1)*tp)); j = ranks.index(rank)
            axis = slot; x = linear._output_irs[0]; bounds = list(x.indmap)
            width = x.shape[axis]//tp; bounds[axis] = (j*width,(j+1)*width)
            y = IR(alias_tid+7000+slot,x.parent.name,x.parent.shape,tuple(bounds)); y.parent.tid = x.parent.tid
            refs = [linear.outputs[0]._replace(rank=r) for r in ranks]
            cell = NS(node=N('p',rank,0,y.tid,'ReduceScatterPrim'),rank=rank,opname='ReduceScatterPrim',
                inputs=refs,outputs=[T('p',rank,0,y.tid,1)],kwargs=dict(ranks=ranks,dim=axis),
                _input_irs=[copy.deepcopy(x)],_output_irs=[y])
            cell.ir = NS(signature=cell.opname,inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
            pm.cells.insert(pm.cells.index(linear)+1,cell); pm.shapes[cell.outputs[0]] = y.shape
            row = dict(ref=dict(world='p',runtime_rank=rank,microbatch=0,source_cid=y.tid,
                call_instance=0,op=cell.opname,origin='fixture'),source_irname=cell.node.irname,
                inputs=[tref(r) for r in refs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[],
                adapter_kwargs=copy.deepcopy(cell.kwargs))
            rows.append(row); adapter = copy.deepcopy(row); adapter['inputs'] = [tref(refs[j])]
            adapter['primitive'] = dict(kind=cell.node.irname,forward=True,kwargs=copy.deepcopy(cell.kwargs),
                signature='nnscaler.runtime.adapter.reduce_scatter',generated_inputs=[f'projection_{slot}'],
                generated_outputs=[f'reduced_{slot}'])
            adapters.append(adapter)
            old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                f'\n        reduced_{slot} = nnscaler.runtime.adapter.reduce_scatter(projection_{slot}, dim={axis}, ranks={ranks})\ndef _train_step')
    if metadata == 'all-peers':
        for cell in pm.cells:
            if cell.opname != 'ReduceScatterPrim': continue
            cell._input_irs = [copy.deepcopy(next(ir for c in pm.cells for ref,ir in zip(c.outputs,c._output_irs,strict=True) if ref == r)) for r in cell.inputs]
    snapshot = build_snapshot([*old['writers'],*rows])
    snapshot.update({k:old[k] for k in ('source','runtime_ndevs','rank_sources')})
    by_id = {writer_export_id(w['ref']):w for w in [*old['adapter_source'],*adapters]}
    snapshot['adapter_source'] = [by_id[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm,pm,(copy.deepcopy(sm.cells),copy.deepcopy(pm.cells),snapshot,*authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous,'fixture',return_value=f):
        return previous.prepared(D=kwargs.get('D',2),tp=kwargs.get('tp',2),seqlen=kwargs.get('seqlen',2))


def test_public_real_input_linear_reduce_scatter_tracer():
    args = prepared(); observed = []; original = predecessor.render
    def fresh(*six):
        result = original(*six); observed.append(result); return result
    with patch.object(predecessor,'render',side_effect=fresh) as refresh:
        text,result = api().render(*args)
    assert refresh.call_count == 1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    closed = observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [18,4,8,2,2]
    assert result['consumed_frontier_indices'] == [1,2,5,6]
    for i,(old,new) in enumerate(zip(closed['frontier_units'],result['frontier_units'],strict=True)):
        if i not in result['consumed_frontier_indices']:
            assert new is old
        else:
            assert new['predecessor_facts'] == old['facts_theorem']
            assert new['global_shape'] == [2,2,6]
            assert new['local_shape'] == ([1,1,6] if i in (1,5) else [1,2,3])
            assert new['gather_axis'] == (1 if i in (1,5) else 2)
            assert new['source_output_slot'] == 0
            assert all(s['op'] == 'ReduceScatterPrim' for s in new['local_steps'])
            assert new['parameters'][0]['dim'] == 1
            assert [s['outputs'][0]['value_part'] for s in new['partial_steps']] == [(0,2),(1,2)]
    assert result['retained_units'] == closed['retained_units']
    assert result['deferred_units'] == closed['deferred_units']
    assert text.count('source_linear_input_unit_output_reduce') == 4
    assert text.count('SourceReduceScatterRead.reduceScatter_value_of_split') == 8
    assert text.count('SourceLinearRead.linear_value_of_split') == 10
    assert 'allGatherPrimDimN_chunks_ofFn' in text
    assert 'SourceAllGatherRead' not in text
    for row in result['reads']:
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    assert result['lean_bytes'] == len(text.encode())
    with pytest.raises(TypeError): api().render(*args,closed)


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args,predecessor.render(*args)[1]


def transport(args,closed):
    # Negative seam only: original source authentication is never mocked.
    with patch.object(predecessor,'render',return_value=('',closed)) as fresh:
        answer = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a,b in zip(fresh.call_args.args,args,strict=True))
    return answer


def selected(args,kind='FW_linear',rank=3,slot=1):
    cid = 271003+(6000 if kind == 'FW_linear' else 7000)+slot
    return next(c for c in args[3]._inputs[1] if c.node.cid == cid and c.rank == rank)


@pytest.mark.parametrize('fault',['weight-axis','weight-ref','weight-parent','weight-param-bool',
    'weight-grad-bool','weight-float-bound','weight-value','partial-unit','partial-swapped','partial-float',
    'activation-fullref','output-shape','output-parent','kwargs','consts','metadata-missing'])
def test_linear_raw_authentication(baseline,fault):
    args,closed = copy.deepcopy(baseline); cell = selected(args); w = cell._input_irs[1]
    if fault == 'weight-axis': w.indmap = ((3,6),(0,3))
    elif fault == 'weight-ref': cell.inputs[1] = cell.inputs[1]._replace(v=1)
    elif fault == 'weight-parent': w.parent.tid += 1
    elif fault == 'weight-param-bool': w.param = 1
    elif fault == 'weight-grad-bool': w.is_grad = lambda: 0
    elif fault == 'weight-float-bound': w.indmap = ((0.0,6),(3,6))
    elif fault == 'weight-value': w.valmap = (1,2)
    elif fault == 'partial-unit': cell._output_irs[0].valmap = (0,1)
    elif fault == 'partial-swapped': cell._output_irs[0].valmap = (0,2)
    elif fault == 'partial-float': cell._output_irs[0].valmap = (1.0,2)
    elif fault == 'activation-fullref': cell.inputs[0] = cell.inputs[0]._replace(rank=1)
    elif fault == 'output-shape': cell._output_irs[0].shape = (1,2,3)
    elif fault == 'output-parent': cell._output_irs[0].parent.tid += 1
    elif fault == 'kwargs': cell.kwargs['bias'] = True
    elif fault == 'consts': cell.kwargs['__consts'] = [0]
    else: cell._input_irs = None
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',['wrong-function','missing-ir'])
def test_original_linear_function_not_just_stored_opcode(baseline,world,fault):
    args,closed = copy.deepcopy(baseline)
    transport(args,closed)
    if world == 'pm':
        cell = selected(args)
    else:
        ref = tuple(closed['frontier_units'][1]['sm_output_ref'])
        cell = next(c for c in args[3]._inputs[0]
                    if c.opname == 'FW_linear' and tuple(c.inputs[0]) == ref)
    assert cell.ir.signature == 'torch.nn.functional.linear'
    if fault == 'wrong-function': cell.ir.signature = 'torch.mul'
    else: cell.ir = None
    with pytest.raises(ValueError,match='input-linear original function'):
        transport(args,closed)


@pytest.mark.parametrize('slot',[1,2])
@pytest.mark.parametrize('fault',['scope-world-rank','scope-order','scope-axis','scope-shape','scope-writer',
    'raw-order','raw-dim','input-missing','input-localwrong','input-parent','output-value','output-shape','output-parent'])
def test_reduce_scatter_original_sources(baseline,slot,fault):
    from dataclasses import replace
    args,closed = copy.deepcopy(baseline); cell = selected(args,'ReduceScatterPrim',slot=slot)
    view = args[1]; scope = view.collective_scopes[cell.node]
    if fault.startswith('scope-'):
        changes = {'scope-world-rank':dict(local_index=3),'scope-order':dict(input_tids=scope.input_tids[::-1]),
            'scope-axis':dict(params=(2 if slot == 1 else 1,)),'scope-shape':dict(input_shape=(1,1,6)),
            'scope-writer':dict(source_writer='forged')}
        view.collective_scopes[cell.node] = replace(scope,**changes[fault])
    elif fault == 'raw-order': cell.inputs.reverse()
    elif fault == 'raw-dim': cell.kwargs['dim'] = True
    elif fault == 'input-missing': cell._input_irs = None
    elif fault == 'input-localwrong': cell._input_irs[0].valmap = (0,2)
    elif fault == 'input-parent': cell._input_irs[0].parent.tid += 1
    elif fault == 'output-value': cell._output_irs[0].valmap = (1,2)
    elif fault == 'output-shape': cell._output_irs[0].shape = (True,*cell._output_irs[0].shape[1:])
    else: cell._output_irs[0].parent.tid += 1
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('fault',['bound-axis','bound-parent','bound-order','bound-local-ref',
    'descriptor-input','descriptor-slot','all-q-missing','all-k-missing','all-skip-missing',
    'partial-order','ranks','positions','schedule','inverse','rs-bw-suffix','linear-bw-suffix'])
def test_complete_frontier_binding_and_schedule(baseline,fault):
    args,closed = copy.deepcopy(baseline); row = closed['frontier_units'][5]
    bound = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == 276004)
    if fault == 'bound-axis': bound['units'][1]['initial_goal']['dim'] = 0
    elif fault == 'bound-parent': bound['sm_binding']['parent_tid'] += 1
    elif fault == 'bound-order': args[4]['relations'].reverse()
    elif fault == 'bound-local-ref': bound['units'][1]['bindings'][1]['ref'][1] = 1
    elif fault == 'descriptor-input': row['local_steps'][0]['inputs'][0]['endpoint']['ref'] = ('p',0,0,271004,1)
    elif fault == 'descriptor-slot': row['slot'] = 2
    elif fault in ('all-q-missing','all-k-missing','all-skip-missing'):
        slot = {'all-q-missing':0,'all-k-missing':1,'all-skip-missing':3}[fault]
        closed['frontier_units'] = [r for i,r in enumerate(closed['frontier_units']) if i % 4 != slot]
    elif fault == 'partial-order': row['local_steps'].reverse()
    elif fault == 'ranks': row['ranks'].reverse()
    elif fault == 'positions': row['positions'][0] = False
    elif fault == 'schedule': args[-1]['pm']['execution_to_source'].reverse()
    elif fault == 'inverse': args[-1]['pm']['source_to_execution'].reverse()
    else:
        cell = selected(args,'ReduceScatterPrim' if fault == 'rs-bw-suffix' else 'FW_linear')
        backward = next(n for n in reversed(args[1].nodes()) if args[1].node_opname(n).startswith('BW_'))
        args[1]._node2outputs[backward] = [args[1].node_inputs(cell.node)[0]]
    with pytest.raises(ValueError): transport(args,closed)


def test_dynamic_three_peers_public():
    args = prepared(D=1,tp=3,seqlen=6,alias_tid=381003,metadata='all-peers')
    text,result = api().render(*args)
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [14,2,4,1,1]
    assert [u['local_shape'] for u in result['units']] == [[1,2,9],[1,6,3]]
    for u in result['units']:
        assert [s['outputs'][0]['value_part'] for s in u['partial_steps']] == [(0,3),(1,3),(2,3)]
    assert all(r['input_metadata'] == 'all-peers' for r in result['reads'] if r['op'] == 'ReduceScatterPrim')
    assert text.count('source_linear_input_unit_output_reduce') == 2
