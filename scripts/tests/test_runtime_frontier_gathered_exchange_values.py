"""Portable public gathered-output exchange tracer; candidate-only, no kernel claim."""
import copy
import importlib
import importlib.util
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_gathered_linear_values as previous
from Verdict import runtime_frontier_gathered_linear_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_gathered_exchange_values'), 'gathered exchange renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_gathered_exchange_values')


def fixture(**kwargs):
    from types import SimpleNamespace as NS
    from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
    from scripts.tests.test_graph_to_lean_collective_scope import tref
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(**kwargs)
    old = copy.deepcopy(authority[2]); rows = []
    for producer in [c for c in pm.cells if c.opname == 'AllToAllPrim' and c.kwargs['idim'] == 2
                     and c.node.cid == kwargs.get('alias_tid',271003)+9000]:
        x = producer._output_irs[0]; y = IR(x.tid+1000,'next.q.view',x.parent.shape,x.indmap)
        cell = NS(node=N('p',producer.rank,0,y.tid,'FW_view'),rank=producer.rank,opname='FW_view',
            inputs=producer.outputs[:],outputs=[T('p',producer.rank,0,y.tid,1)],kwargs=dict(size=list(y.shape)),
            _input_irs=[copy.deepcopy(x)],_output_irs=[y])
        cell.ir = NS(signature='torch.Tensor.view',inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
        pm.cells.insert(pm.cells.index(producer)+1,cell); pm.shapes[cell.outputs[0]] = y.shape
        rows.append(dict(ref=dict(world='p',runtime_rank=cell.rank,microbatch=0,source_cid=y.tid,
            call_instance=0,op=cell.opname,origin='fixture'),source_irname=cell.node.irname,
            inputs=[tref(r) for r in cell.inputs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[]))
        old['rank_sources'][str(cell.rank)] = old['rank_sources'][str(cell.rank)].replace('\ndef _train_step',
            f'\n        next_q_view = next_q_exchange.view({", ".join(map(str,y.shape))})\ndef _train_step')
        if kwargs.get('metadata') == 'all-peers':
            producer._input_irs = [copy.deepcopy(next(ir for c in pm.cells for ref,ir in
                zip(c.outputs,c._output_irs,strict=True) if ref == r)) for r in producer.inputs]
    snapshot = build_snapshot([*old['writers'],*rows])
    snapshot.update({k:old[k] for k in ('source','runtime_ndevs','rank_sources')})
    by_id = {writer_export_id(w['ref']):w for w in [*old['adapter_source'],*rows]}
    snapshot['adapter_source'] = [by_id[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm,pm,(copy.deepcopy(sm.cells),copy.deepcopy(pm.cells),snapshot,*authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous,'fixture',return_value=f):
        return previous.prepared(**kwargs)


def test_public_gathered_exchange_tracer():
    subject = api(); args = prepared(); observed = []; original = predecessor.render
    def fresh(*six):
        result = original(*six); observed.append(result); return result
    with patch.object(predecessor, 'render', side_effect=fresh) as refresh:
        text, result = subject.render(*args)
    assert refresh.call_count == 1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    closed = observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [4,2,8,2,4]
    assert result['consumed_frontier_indices'] == [0,4]
    for i,(old,new) in enumerate(zip(closed['frontier_units'],result['frontier_units'],strict=True)):
        if i not in result['consumed_frontier_indices']: assert new is old
        else:
            assert new['predecessor_facts'] == old['facts_theorem']
            assert new['global_shape'] == [2,2,6] and new['local_shape'] == [1,1,6]
            assert new['dimensions'] == dict(D=2,T=2,B=1,S=1,H=6)
            assert new['source_output_slot'] == old['source_output_slot'] and new['gather_axis'] == 1
    assert result['retained_units'] == closed['retained_units']
    assert text.count('SourceHiddenSequenceExchange.output_facts') == 2
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    for bad in ('sorry','admit','native_decide','axiom '): assert bad not in text
    with pytest.raises(TypeError): subject.render(*args,closed)
    for new in result['units']:
        assert new['observed_consumer_ops'] == [['FW_view'],['FW_view'],['FW_view']]
        assert len(new['sm_consumers']) == 1 and len(new['pm_consumers']) == 2
        assert new['source_step'] == closed['frontier_units'][new['frontier_index']]['source_step']
    for read in result['reads']:
        assert read['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][read['execution_index']:]
        assert read['input_metadata'] == 'local-only' and read['output_metadata'] == 'present'
        assert read['producer_metadata'] == 'all-peers' and read['input_parent_identity'] == 'local-only'


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args,predecessor.render(*args)[1]


def transport(args,closed):
    # Negative seam only; the happy public chain is never replaced.
    with patch.object(predecessor,'render',return_value=('',closed)) as fresh:
        result = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a,b in zip(fresh.call_args.args,args,strict=True))
    return result


def selected(args,rank=3):
    return next(c for c in args[3]._inputs[1] if c.node.cid == 280003 and c.rank == rank)


@pytest.mark.parametrize('fault',['scope-local-bool','scope-rank-position','scope-reverse','scope-group','scope-axis',
    'scope-shape','scope-writer','raw-order','raw-ref','raw-ranks','raw-axis-float','raw-axis-bool','raw-kwargs',
    'input-absent','input-empty','input-partial','input-wrong-peer','input-parent','input-bound-float','input-value-float',
    'output-absent','output-empty','output-parent','output-shape-bool','output-bound-bool','output-value',
    'peer-parent','peer-value','writer-ref','writer-call','coherent-reversal'])
def test_exchange_original_authority(baseline,fault):
    from dataclasses import replace
    args,closed = copy.deepcopy(baseline); cell = selected(args); view = args[1]
    scope = view.collective_scopes[cell.node]
    if fault.startswith('scope-'):
        changes = {'scope-local-bool':dict(local_index=True),'scope-rank-position':dict(local_index=3),
            'scope-reverse':dict(input_tids=scope.input_tids[::-1]),'scope-group':dict(ranks=(1,3)),
            'scope-axis':dict(params=(1,2)),'scope-shape':dict(input_shape=(1,2,6)),
            'scope-writer':dict(source_writer='forged')}
        view.collective_scopes[cell.node] = replace(scope,**changes[fault])
    elif fault == 'raw-order': cell.inputs.reverse()
    elif fault == 'raw-ref': cell.inputs[0] = cell.inputs[0]._replace(mb=1)
    elif fault == 'raw-ranks': cell.kwargs['ranks'] = [1,3]
    elif fault == 'raw-axis-float': cell.kwargs['idim'] = 2.0
    elif fault == 'raw-axis-bool': cell.kwargs['odim'] = True
    elif fault == 'raw-kwargs': cell.kwargs['unknown'] = 1
    elif fault == 'input-absent': cell._input_irs = None
    elif fault == 'input-empty': cell._input_irs = []
    elif fault == 'input-partial': cell._input_irs *= 3
    elif fault == 'input-wrong-peer': cell._input_irs = copy.deepcopy(selected(args,2)._input_irs)
    elif fault == 'input-parent': cell._input_irs[0].parent.tid += 1
    elif fault == 'input-bound-float': cell._input_irs[0].indmap = ((0,1),(0,2),(3.0,6))
    elif fault == 'input-value-float': cell._input_irs[0].valmap = (0.0,1)
    elif fault == 'output-absent': cell._output_irs = None
    elif fault == 'output-empty': cell._output_irs = []
    elif fault == 'output-parent': cell._output_irs[0].parent.tid += 1
    elif fault == 'output-shape-bool': cell._output_irs[0].shape = (True,1,6)
    elif fault == 'output-bound-bool': cell._output_irs[0].indmap = ((0,1),(True,2),(0,6))
    elif fault == 'output-value': cell._output_irs[0].valmap = (1,2)
    elif fault.startswith('peer-'):
        peer = previous.selected(args,rank=2)
        if fault == 'peer-parent': peer._output_irs[0].parent.tid += 1
        else: peer._output_irs[0].valmap = (1,2)
    else:
        writer = next(w for w in view._collective_source['writers'] if w['ref']['source_cid'] == cell.node.cid and w['ref']['runtime_rank'] == 3)
        if fault == 'writer-ref': writer['inputs'].reverse()
        elif fault == 'writer-call': writer['ref']['call_instance'] += 1
        else:
            cell.inputs.reverse(); cell.kwargs['ranks'].reverse()
            view.collective_scopes[cell.node] = replace(scope,ranks=scope.ranks[::-1],input_tids=scope.input_tids[::-1],local_index=0)
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('fault',['drop-q','drop-k','drop-v','drop-skip','reverse-rows','kv-as-skip','skip-as-deferred',
    'drop-deferred','descriptor-input','descriptor-output','descriptor-local','source-slot','previous-slot','dimensions',
    'partial-descriptor','drop-partial','parameter-descriptor','gather-descriptor','drop-gather','canonical-axis',
    'canonical-parent','canonical-order','linear-signature','linear-param','linear-parent','linear-bound-float',
    'schedule','inverse','exchange-bw-suffix','linear-bw-suffix','gather-bw-suffix','partial-bw-suffix'])
def test_mixed_boundary_and_provenance(baseline,fault):
    args,closed = copy.deepcopy(baseline); row = closed['frontier_units'][4]
    if fault.startswith('drop-') and fault in ('drop-q','drop-k','drop-v','drop-skip'):
        slot = {'drop-q':0,'drop-k':1,'drop-v':2,'drop-skip':3}[fault]
        closed['frontier_units'] = [r for i,r in enumerate(closed['frontier_units']) if i%4 != slot]
    elif fault == 'reverse-rows': closed['frontier_units'].reverse()
    elif fault == 'kv-as-skip': closed['retained_units'].append(closed['frontier_units'][5])
    elif fault == 'skip-as-deferred': closed['deferred_units'].append(closed['retained_units'].pop())
    elif fault == 'drop-deferred': closed['deferred_units'].pop()
    elif fault == 'descriptor-input': row['source_step']['inputs'][1]['endpoint']['tid'] += 1
    elif fault == 'descriptor-output': row['source_step']['outputs'] = ()
    elif fault == 'descriptor-local': row['local_steps'][0]['inputs'] = row['local_steps'][0]['inputs'][:1]
    elif fault == 'source-slot': row['source_output_slot'] = True
    elif fault == 'previous-slot': row['predecessor_source_output_slot'] = 1
    elif fault == 'dimensions': row['dimensions']['H'] = True
    elif fault == 'partial-descriptor': closed['frontier_units'][5]['partial_steps'][0]['inputs'][1]['endpoint']['tid'] += 1
    elif fault == 'drop-partial': closed['frontier_units'][5]['partial_steps'].pop()
    elif fault == 'parameter-descriptor': row['parameters'][0]['sm_tid'] += 1
    elif fault == 'gather-descriptor': row['gather_steps'][0]['inputs'] = ()
    elif fault == 'drop-gather': row['gather_steps'].pop()
    elif fault.startswith('canonical-'):
        bound = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == 276003)
        if fault == 'canonical-axis': bound['units'][1]['initial_goal']['dim'] = 1
        elif fault == 'canonical-parent': bound['sm_binding']['parent_tid'] += 1
        else: args[4]['relations'].reverse()
    elif fault == 'linear-signature': previous.selected(args).ir.signature = 'torch.mul'
    elif fault == 'linear-param': previous.selected(args)._input_irs[1].param = 1
    elif fault == 'linear-parent': previous.selected(args)._input_irs[1].parent.tid += 1
    elif fault == 'linear-bound-float': previous.selected(args)._input_irs[1].indmap = ((3.0,6),(0,6))
    elif fault == 'schedule': args[-1]['pm']['execution_to_source'].reverse()
    elif fault == 'inverse': args[-1]['pm']['source_to_execution'].reverse()
    else:
        cell = selected(args) if fault == 'exchange-bw-suffix' else previous.selected(args,
            kind='AllGatherPrim' if fault == 'gather-bw-suffix' else 'FW_linear',slot=1 if fault == 'partial-bw-suffix' else 0)
        backward = next(n for n in reversed(args[1].nodes()) if args[1].node_opname(n).startswith('BW_'))
        args[1]._node2outputs[backward] = [args[1].node_inputs(cell.node)[0]]
    with pytest.raises(ValueError): transport(args,closed)


def test_dynamic_three_peers_all_metadata_public():
    args = prepared(D=1,tp=3,seqlen=3,alias_tid=390019,metadata='all-peers')
    text,result = api().render(*args)
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [3,1,4,1,2]
    row, = result['units']
    assert row['local_shape'] == [1,1,9] and row['dimensions'] == dict(D=1,T=3,B=1,S=1,H=9)
    assert all(r['input_metadata'] == 'all-peers' for r in result['reads'])
    assert 'SourceHiddenSequenceExchange.output_facts 1 0 3 1 1 3' in text


@pytest.mark.parametrize('kinds,expected',[
    ([['FW_view'],['FW_view'],['FW_view']], 'next FW_view frontier deferred'),
    ([['FW_view'],[],[]], 'unsupported complete forward consumer frontier deferred'),
    ([['FW_contiguous'],['FW_contiguous']], 'unsupported complete forward consumer frontier deferred'),
])
def test_truthful_deferred_inventory(kinds,expected):
    assert api()._deferred_reason(kinds) == expected


@pytest.mark.parametrize('fault',['skip-output','kv-source-input','kv-partial-input','kv-partial-parameter',
    'kv-partial-raw','q-source-output-parent','output-absent-no-consumer','source-ports','drop-receiver'])
def test_nonconsumed_complete_original_ports(baseline,fault):
    args,closed = copy.deepcopy(baseline)
    if fault == 'skip-output':
        closed['frontier_units'][7]['source_step']['outputs'] = closed['frontier_units'][7]['source_step']['outputs'][:1]
    elif fault == 'kv-source-input': closed['frontier_units'][5]['source_step']['inputs'] = ()
    elif fault == 'kv-partial-input': closed['frontier_units'][5]['partial_steps'][0]['inputs'] = ()
    elif fault == 'kv-partial-parameter': closed['frontier_units'][5]['parameters'][0]['pm_tids'].reverse()
    elif fault == 'kv-partial-raw': previous.selected(args,slot=1)._output_irs[0].valmap = (0,1)
    elif fault == 'q-source-output-parent':
        next(c for c in args[3]._inputs[0] if c.node.cid == 273003)._output_irs[0].parent.tid += 1
    elif fault == 'output-absent-no-consumer':
        # Absence must fail even when no future consumer happens to expose it.
        cell = selected(args); cell._output_irs = None
        for n in args[1].nodes():
            if args[1].node_opname(n) == 'FW_view' and n.rank == 3 and n.cid == 281003:
                args[1]._node2inputs[n] = []
    elif fault == 'source-ports':
        closed['frontier_units'][4]['source_step']['inputs'] = closed['frontier_units'][4]['source_step']['inputs'][:1]
    else:
        cell = selected(args)
        args[1]._node2inputs[cell.node] = []
    with pytest.raises(ValueError): transport(args,closed)
