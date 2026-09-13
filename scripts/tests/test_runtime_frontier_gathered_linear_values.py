"""Portable original-function, canonical row-weight tracer. No kernel claim."""
import copy
import importlib
import importlib.util
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_input_linear_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_input_linear_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_gathered_linear_values'), 'gathered linear renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_gathered_linear_values')


def fixture(D=2, tp=2, seqlen=2, alias_tid=271003, metadata='local-only'):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D=D,tp=tp,seqlen=seqlen,alias_tid=alias_tid,metadata=metadata)
    old = copy.deepcopy(authority[2]); rows = []; adapters = []
    for world, graph in [('s',sm),('p',pm)]:
        q = [c for c in graph.cells if c.node.cid == alias_tid+(2000 if world == 's' else 6000)]
        for cell in q:
            cell.ir.signature = 'torch.nn.functional.linear'
            w = cell._input_irs[1]
            if world == 'p':
                j = cell.rank % tp
                w.indmap = ((j*3,(j+1)*3),(0,3*tp)); w.shape = (3,3*tp)
                y = cell._output_irs[0]
                y.parent.shape = (*cell._input_irs[0].parent.shape[:2],3*tp)
                y.indmap = (*y.indmap[:2],(j*3,(j+1)*3)); y.shape = (1,seqlen,3)
            cell._output_irs[0].parent.name = 'arbitrary.row_projection.output'
            cell._output_irs[0].parent.tid = alias_tid+6000
            graph.shapes.update({r:ir.shape for r,ir in zip(cell.inputs+cell.outputs,cell._input_irs+cell._output_irs,strict=True)})
        # Q's actual next PM boundary is AA(2,1), deliberately NOT consumed.
        for producer in q:
            x = producer._output_irs[0]; rank = producer.rank; ranks = list(range(rank//tp*tp,(rank//tp+1)*tp))
            kind = 'FW_view' if world == 's' else 'AllToAllPrim'
            bounds = x.indmap if world == 's' else (x.indmap[0],((rank%tp)*seqlen//tp,(rank%tp+1)*seqlen//tp),(0,3*tp))
            y = IR(alias_tid+9000,x.parent.name,x.parent.shape,bounds); y.parent.tid = x.parent.tid
            refs = producer.outputs[:] if world == 's' else [producer.outputs[0]._replace(rank=r) for r in ranks]
            cell = NS(node=N(world,rank,0,y.tid,kind),rank=rank,opname=kind,
                inputs=refs,outputs=[T(world,rank,0,y.tid,1)],
                kwargs=dict(size=list(y.shape)) if world == 's' else dict(ranks=ranks,idim=2,odim=1),
                _input_irs=[copy.deepcopy(x)],_output_irs=[y])
            cell.ir = NS(signature=kind,inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
            graph.cells.insert(graph.cells.index(producer)+1,cell); graph.shapes[cell.outputs[0]] = y.shape
            if world == 'p':
                row = dict(ref=dict(world=world,runtime_rank=rank,microbatch=0,source_cid=y.tid,
                    call_instance=0,op=kind,origin='fixture'),source_irname=kind,
                    inputs=[tref(r) for r in refs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[],adapter_kwargs=copy.deepcopy(cell.kwargs))
                rows.append(row); adapter = copy.deepcopy(row); adapter['inputs'] = [tref(producer.outputs[0])]
                adapter['primitive'] = dict(kind=kind,forward=True,kwargs=copy.deepcopy(cell.kwargs),
                    signature='nnscaler.runtime.adapter.all_to_all',generated_inputs=['projection_0'],generated_outputs=['next_q_exchange'])
                adapters.append(adapter)
                old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                    f'\n        next_q_exchange = nnscaler.runtime.adapter.all_to_all(projection_0, ranks={ranks}, idim=2, odim=1)\ndef _train_step')
        # Original next-view boundaries for K/V, not terminal/skipped rows.
        for slot in (1,2):
            for producer in [c for c in graph.cells if c.node.cid == alias_tid+(2000 if world == 's' else 7000)+slot]:
                x = producer._output_irs[0]; y = IR(alias_tid+8000+slot,'next.view',x.parent.shape,x.indmap)
                cell = NS(node=N(world,producer.rank,0,y.tid,'FW_view'),rank=producer.rank,opname='FW_view',
                    inputs=producer.outputs[:],outputs=[T(world,producer.rank,0,y.tid,1)],kwargs=dict(size=list(y.shape)),
                    _input_irs=[copy.deepcopy(x)],_output_irs=[y])
                cell.ir = NS(signature='torch.Tensor.view',inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
                graph.cells.insert(graph.cells.index(producer)+1,cell); graph.shapes[cell.outputs[0]] = y.shape
                if world == 'p':
                    rows.append(dict(ref=dict(world=world,runtime_rank=cell.rank,microbatch=0,source_cid=y.tid,
                        call_instance=0,op=cell.opname,origin='fixture'),source_irname=cell.node.irname,
                        inputs=[tref(r) for r in cell.inputs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[]))
                    old['rank_sources'][str(cell.rank)] = old['rank_sources'][str(cell.rank)].replace('\ndef _train_step',
                        f'\n        next_view_{slot} = reduced_{slot}.view({", ".join(map(str,y.shape))})\ndef _train_step')
    snapshot = build_snapshot([*old['writers'],*rows])
    snapshot.update({k:old[k] for k in ('source','runtime_ndevs','rank_sources')})
    by_id = {writer_export_id(w['ref']):w for w in [*old['adapter_source'],*rows,*adapters]}
    snapshot['adapter_source'] = [by_id[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm,pm,(copy.deepcopy(sm.cells),copy.deepcopy(pm.cells),snapshot,*authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous,'fixture',return_value=f):
        return previous.prepared(D=kwargs.get('D',2),tp=kwargs.get('tp',2),seqlen=kwargs.get('seqlen',2))


def test_public_gathered_row_linear_tracer():
    subject = api(); args = prepared(); observed = []; original = predecessor.render
    def fresh(*six):
        result = original(*six); observed.append(result); return result
    with patch.object(predecessor,'render',side_effect=fresh) as refresh:
        text,result = subject.render(*args)
    assert refresh.call_count == 1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    closed = observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [9,2,8,2,4]
    assert result['consumed_frontier_indices'] == [0,4]
    for i,(old,new) in enumerate(zip(closed['frontier_units'],result['frontier_units'],strict=True)):
        if i not in (0,4): assert new is old
        else:
            assert new['predecessor_facts'] == old['facts_theorem']
            assert new['global_shape'] == [2,2,6] and new['local_shape'] == [1,2,3]
            assert new['dimensions'] == dict(D=2,T=2,B=1,S=2,H=3)
            assert new['source_output_slot'] == 0 and new['gather_axis'] == 2
            assert new['parameters'][0]['kind'] == 'sharded'
            assert new['observed_consumer_ops'] == [['FW_view'],['AllToAllPrim']*2,['AllToAllPrim']*2]
            assert len(new['sm_consumers']) == 1 and len(new['pm_consumers']) == 2
    assert result['retained_units'] == closed['retained_units']
    for row in result['deferred_units']:
        assert row['facts_theorem'] in [r['facts_theorem'] for r in closed['units']]
        assert row['observed_consumer_ops'] == [['FW_view'],['FW_view'],['FW_view']]
        assert 'FW_view' in row['reason']
    assert text.count('source_linear_weight_unit_output_reconstruct') == 2
    assert text.count('SourceAllGatherRead.allGather_value_of_split') == 4
    assert text.count('SourceLinearRead.linear_value_of_split') == 5
    assert 'SourceMultirefRead' not in text
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :'): assert bad not in text
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    with pytest.raises(TypeError): subject.render(*args,closed)


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args,predecessor.render(*args)[1]


def transport(args,closed):
    # Negative seam only. Every source adapter and canonical binder stays real.
    with patch.object(predecessor,'render',return_value=('',closed)) as fresh:
        result = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a,b in zip(fresh.call_args.args,args,strict=True))
    return result


def selected(args,kind='FW_linear',rank=3,slot=0):
    offset = {'FW_linear':6000,'AllGatherPrim':2000,'ReduceScatterPrim':7000}[kind]
    return next(c for c in args[3]._inputs[1] if c.node.cid == 271003+offset+slot and c.rank == rank)


@pytest.mark.parametrize('world',['sm','pm'])
@pytest.mark.parametrize('fault',['wrong-function','fixture-tag','missing-ir'])
def test_original_live_linear_signature(baseline,world,fault):
    args,closed = copy.deepcopy(baseline)
    cell = selected(args) if world == 'pm' else next(c for c in args[3]._inputs[0] if c.node.cid == 273003)
    assert cell.ir.signature == 'torch.nn.functional.linear'
    if fault == 'missing-ir': cell.ir = None
    else: cell.ir.signature = 'torch.mul' if fault == 'wrong-function' else 'FW_linear'
    with pytest.raises(ValueError,match='gathered-linear original function'): transport(args,closed)


@pytest.mark.parametrize('fault',['row-vs-column','weight-parent','weight-param','weight-grad','weight-shape-bool',
    'weight-bound-float','weight-value','weight-missing','activation-ref','activation-parent','activation-shape',
    'output-parent','output-shape','output-value','bias','consts','occurrence-parent','occurrence-param'])
def test_linear_raw_authority(baseline,fault):
    args,closed = copy.deepcopy(baseline); cell = selected(args); w = cell._input_irs[1]
    if fault == 'row-vs-column': w.indmap = ((0,6),(3,6)); w.shape = (6,3)
    elif fault == 'weight-parent': w.parent.tid += 1
    elif fault == 'weight-param': w.param = 1
    elif fault == 'weight-grad': w.is_grad = lambda: 0
    elif fault == 'weight-shape-bool': w.shape = (True,6)
    elif fault == 'weight-bound-float': w.indmap = ((3.0,6),(0,6))
    elif fault == 'weight-value': w.valmap = (1,2)
    elif fault == 'weight-missing': cell._input_irs = None
    elif fault == 'activation-ref': cell.inputs[0] = cell.inputs[0]._replace(rank=1)
    elif fault == 'activation-parent': cell._input_irs[0].parent.tid += 1
    elif fault == 'activation-shape': cell._input_irs[0].shape = (True,2,6)
    elif fault == 'output-parent': cell._output_irs[0].parent.tid += 1
    elif fault == 'output-shape': cell._output_irs[0].shape = (1,2,6)
    elif fault == 'output-value': cell._output_irs[0].valmap = (0.0,1)
    elif fault == 'bias': cell.kwargs['bias'] = True
    elif fault == 'consts': cell.kwargs['__consts'] = [1]
    else:
        # Existing BW node now names this parameter with malformed original IR.
        other = next(c for c in reversed(args[3]._inputs[1]) if c.rank == 3 and c.opname.startswith('BW_'))
        other.inputs.append(cell.inputs[1]); other._input_irs.append(copy.deepcopy(w))
        if fault == 'occurrence-parent': other._input_irs[-1].parent.tid += 1
        else: other._input_irs[-1].param = 1
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('fault',['scope-local','scope-order','scope-axis','scope-ranks','scope-shape','scope-writer',
    'raw-order','raw-ref','raw-ranks','raw-axis','input-absent','input-empty','input-partial','input-wrong-peer',
    'input-parent','input-float','output-absent','output-parent','output-value','peer-parent','peer-shape','writer-call','writer-ref'])
def test_allgather_ordered_source_authority(baseline,fault):
    from dataclasses import replace
    args,closed = copy.deepcopy(baseline); cell = selected(args,'AllGatherPrim'); view = args[1]
    if fault.startswith('scope-'):
        scope = view.collective_scopes[cell.node]
        changes = {'scope-local':dict(local_index=True),'scope-order':dict(input_tids=scope.input_tids[::-1]),
            'scope-axis':dict(params=(2,)),'scope-ranks':dict(ranks=(1,3)),
            'scope-shape':dict(input_shape=(1,2,6)),'scope-writer':dict(source_writer='forged')}
        view.collective_scopes[cell.node] = replace(scope,**changes[fault])
    elif fault == 'raw-order': cell.inputs.reverse()
    elif fault == 'raw-ref': cell.inputs[0] = cell.inputs[0]._replace(mb=1)
    elif fault == 'raw-ranks': cell.kwargs['ranks'].reverse()
    elif fault == 'raw-axis': cell.kwargs['dim'] = True
    elif fault == 'input-absent': cell._input_irs = None
    elif fault == 'input-empty': cell._input_irs = []
    elif fault == 'input-partial': cell._input_irs *= 3
    elif fault == 'input-wrong-peer': cell._input_irs = copy.deepcopy(selected(args,'AllGatherPrim',rank=2)._input_irs)
    elif fault == 'input-parent': cell._input_irs[0].parent.tid += 1
    elif fault == 'input-float': cell._input_irs[0].valmap = (0.0,1)
    elif fault == 'output-absent': cell._output_irs = None
    elif fault == 'output-parent': cell._output_irs[0].parent.tid += 1
    elif fault == 'output-value': cell._output_irs[0].valmap = (1,2)
    elif fault.startswith('peer-'):
        peer = next(c for c in args[3]._inputs[1] if c.node.cid == 271002 and c.rank == 2)
        if fault == 'peer-parent': peer._output_irs[0].parent.tid += 1
        else: peer._output_irs[0].shape = (1,9,6)
    else:
        w = next(w for w in view._collective_source['writers'] if w['ref']['source_cid'] == cell.node.cid and w['ref']['runtime_rank'] == 3)
        if fault == 'writer-call': w['ref']['call_instance'] += 1
        else: w['inputs'].reverse()
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('fault',['bound-axis','bound-parent','bound-order','bound-fullref','bound-unit-order',
    'descriptor-input','descriptor-slot','descriptor-order','descriptor-gather-axis',
    'drop-q','drop-k','drop-v','drop-skip','kv-as-skip','skip-as-deferred','frontier-order',
    'partial-descriptor','drop-partial','previous-slot','old-rs-descriptor','old-rs-raw','schedule','inverse','ag-bw-suffix','linear-bw-suffix'])
def test_boundary_canonical_cover_and_full_suffix(baseline,fault):
    args,closed = copy.deepcopy(baseline); row = closed['frontier_units'][4]
    bound = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == 276003)
    if fault == 'bound-axis': bound['units'][1]['initial_goal']['dim'] = 1
    elif fault == 'bound-parent': bound['sm_binding']['parent_tid'] += 1
    elif fault == 'bound-order': args[4]['relations'].reverse()
    elif fault == 'bound-fullref': bound['units'][1]['bindings'][1]['ref'][1] = 1
    elif fault == 'bound-unit-order': bound['units'].reverse()
    elif fault == 'descriptor-input': row['source_step']['inputs'][0]['endpoint']['ref'] = ('s',0,0,271004,1)
    elif fault == 'descriptor-slot': row['source_output_slot'] = 1
    elif fault == 'descriptor-order': row['local_steps'].reverse()
    elif fault == 'descriptor-gather-axis': row['gather_axis'] = 2
    elif fault in ('drop-q','drop-k','drop-v','drop-skip'):
        slot = {'drop-q':0,'drop-k':1,'drop-v':2,'drop-skip':3}[fault]
        closed['frontier_units'] = [r for i,r in enumerate(closed['frontier_units']) if i % 4 != slot]
    elif fault == 'kv-as-skip': closed['retained_units'].append(closed['frontier_units'][1])
    elif fault == 'skip-as-deferred': closed['deferred_units'].append(closed['retained_units'].pop())
    elif fault == 'frontier-order': closed['frontier_units'][0],closed['frontier_units'][3] = closed['frontier_units'][3],closed['frontier_units'][0]
    elif fault == 'drop-partial': closed['frontier_units'][5]['partial_steps'].pop()
    elif fault == 'previous-slot': closed['frontier_units'][5]['predecessor_source_output_slot'] = 0
    elif fault == 'partial-descriptor': closed['frontier_units'][5]['partial_steps'][0]['inputs'][1]['endpoint']['tid'] += 1
    elif fault == 'old-rs-descriptor':
        d = closed['frontier_units'][5]['local_steps'][0]; d['inputs'] = d['inputs'][::-1]
    elif fault == 'old-rs-raw': selected(args,'ReduceScatterPrim',slot=1)._input_irs[0].valmap = (0,1)
    elif fault == 'schedule': args[-1]['pm']['execution_to_source'].reverse()
    elif fault == 'inverse': args[-1]['pm']['source_to_execution'].reverse()
    else:
        cell = selected(args,'AllGatherPrim' if fault == 'ag-bw-suffix' else 'FW_linear')
        backward = next(n for n in reversed(args[1].nodes()) if args[1].node_opname(n).startswith('BW_'))
        args[1]._node2outputs[backward] = [args[1].node_inputs(cell.node)[0]]
    with pytest.raises(ValueError): transport(args,closed)


def test_dynamic_three_peer_all_metadata_public():
    args = prepared(D=1,tp=3,seqlen=6,alias_tid=381003,metadata='all-peers')
    text,result = api().render(*args)
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [7,1,4,1,2]
    assert result['consumed_frontier_indices'] == [0]
    assert result['units'][0]['local_shape'] == [1,6,3]
    assert result['units'][0]['global_shape'] == [1,6,9]
    assert result['units'][0]['dimensions'] == dict(D=1,T=3,B=1,S=6,H=3)
    assert all(r['input_metadata'] == 'all-peers' for r in result['reads'] if r['op'] == 'AllGatherPrim')
    for r in result['reads']:
        assert r['operand_nonwrite_source_indices'] == args[-1][r['world']]['execution_to_source'][r['execution_index']:]
    assert 'source_linear_weight_unit_output_reconstruct 1 3 1 6 9 3 0' in text
