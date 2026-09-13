"""Portable Q/AG + K,V/AA frontier; no raw capture or kernel claim.

Local B=1 and inherited hidden width=3*TP. Only predecessor.render is mocked
in transport negatives; the public tracer runs the real six-input pipeline.
"""
import copy
import importlib
import importlib.util
import re
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_sequence_alias_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_sequence_alias_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_projection_exchange_values'), 'projection exchange renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_projection_exchange_values')


def fixture(D=2, tp=2, seqlen=2, alias_tid=271003, metadata='local-only', aa_slots=(1,2), **kwargs):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm,pm,authority = previous.fixture(D=D,tp=tp,seqlen=seqlen,alias_tid=alias_tid,
        successor='AllGatherPrim',metadata=metadata,**kwargs)
    old = copy.deepcopy(authority[2]); rows = []; adapters = []
    targets = {alias_tid+2000+j:j for j in range(3)}
    old_writers = [w for w in old['writers'] if w['ref']['source_cid'] not in targets]
    old_adapters = [w for w in old['adapter_source'] if w['ref']['source_cid'] not in targets]
    for world,graph in [('s',sm),('p',pm)]:
        for cell in list(graph.cells):
            if cell.node.cid not in targets: continue
            slot = targets[cell.node.cid]; rank = cell.rank
            x = cell._input_irs[0]; y = cell._output_irs[0]
            wtid = alias_tid+5000+slot
            w = IR(wtid,f'projection.weight.{slot}',(3*tp,3*tp),param=True)
            if world == 'p':
                ranks = cell.kwargs['ranks']; j = ranks.index(rank)
                if slot in aa_slots:
                    cell.opname = 'AllToAllPrim'; cell.node = cell.node._replace(irname=cell.opname)
                    cell.kwargs = dict(ranks=ranks,idim=1,odim=2)
                    y.indmap = (y.indmap[0],y.indmap[1],(j*3,(j+1)*3)); y.shape = (1,seqlen,3)
                    w = IR(wtid,f'projection.weight.{slot}',(3*tp,3*tp),((0,3*tp),(j*3,(j+1)*3)),param=True)
                    old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace(
                        f'all_gather(sequence_alias_0_{slot}, dim=1, ranks={ranks})',
                        f'all_to_all(sequence_alias_0_{slot}, ranks={ranks}, idim=1, odim=2)')
                row = dict(ref=dict(world=world,runtime_rank=rank,microbatch=0,source_cid=cell.node.cid,
                    call_instance=0,op=cell.opname,origin='fixture'),source_irname=cell.node.irname,
                    inputs=[tref(r) for r in cell.inputs],outputs=[tref(r) for r in cell.outputs],
                    parameter_grad_tids=[],adapter_kwargs=copy.deepcopy(cell.kwargs))
                rows.append(row); adapter = copy.deepcopy(row)
                adapter['inputs'] = [tref(r) for r in cell.inputs if r.rank == rank]
                adapter['primitive'] = dict(kind=cell.node.irname,forward=True,kwargs=copy.deepcopy(cell.kwargs),
                    signature='nnscaler.runtime.adapter.'+('all_to_all' if slot in aa_slots else 'all_gather'),
                    generated_inputs=[f'sequence_alias_0_{slot}'],generated_outputs=[f'downstream_0_{slot}'])
                adapters.append(adapter)
                graph.shapes[cell.outputs[0]] = y.shape
                # Genuine downstream linear is present but is NOT consumed.
                out = IR(alias_tid+6000+slot,f'projection.output.{slot}',(D,seqlen,3*tp),
                    (y.indmap[0],(0,seqlen),(0,3*tp)))
                linear = NS(node=N(world,rank,0,out.tid,'FW_linear'),rank=rank,opname='FW_linear',
                    inputs=[cell.outputs[0],T(world,rank,-1,wtid,0)],outputs=[T(world,rank,0,out.tid,1)],
                    kwargs=dict(bias=None,__consts=[]),_input_irs=[copy.deepcopy(y),w],_output_irs=[out])
                at = next((i for i,c in enumerate(graph.cells) if c.rank == rank and c.opname.startswith('BW_')),len(graph.cells))
                graph.cells.insert(at,linear)
                rows.append(dict(ref=dict(world=world,runtime_rank=rank,microbatch=0,source_cid=out.tid,
                    call_instance=0,op='FW_linear',origin='fixture'),source_irname='FW_linear',
                    inputs=[tref(r) for r in linear.inputs],outputs=[tref(r) for r in linear.outputs],parameter_grad_tids=[]))
                adapters.append(copy.deepcopy(rows[-1]))
                old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                    f'\n        projection_{slot} = torch.nn.functional.linear(downstream_0_{slot}, self.param_{wtid}, bias=None)\ndef _train_step')
            else:
                linear = cell; linear.opname = 'FW_linear'; linear.node = linear.node._replace(irname='FW_linear')
                linear.inputs = [cell.inputs[0],T(world,rank,-1,wtid,0)]
                linear._input_irs = [x,w]; linear.kwargs = dict(bias=None,__consts=[])
            for c in (cell,linear):
                c.ir = NS(signature=c.opname,inputs=lambda c=c:c._input_irs,outputs=lambda c=c:c._output_irs)
            graph.shapes.update({r:ir.shape for r,ir in zip(linear.inputs+linear.outputs,linear._input_irs+linear._output_irs,strict=True)})
    snapshot = build_snapshot([*old_writers,*rows])
    snapshot.update({k:old[k] for k in ('source','runtime_ndevs','rank_sources')})
    by_writer = {writer_export_id(w['ref']):w for w in [*old_adapters,*adapters]}
    snapshot['adapter_source'] = [by_writer[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm,pm,(copy.deepcopy(sm.cells),copy.deepcopy(pm.cells),snapshot,*authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous,'fixture',return_value=f):
        return previous.prepared(D=kwargs.get('D',2),tp=kwargs.get('tp',2),seqlen=kwargs.get('seqlen',2))


def test_public_real_q_k_v_tracer():
    subject = api()
    args = prepared(); observed = []; original = predecessor.render
    def fresh(*six):
        result = original(*six); observed.append(result); return result
    with patch.object(predecessor,'render',side_effect=fresh) as refresh:
        text,result = subject.render(*args)
    assert refresh.call_count == 1
    assert all(a is b for a,b in zip(refresh.call_args.args,args,strict=True))
    old_text,closed = observed[0]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [8,4,8,2,2]
    assert result['consumed_frontier_indices'] == [1,2,5,6]
    for i,(old,new) in enumerate(zip(closed['frontier_units'],result['frontier_units'],strict=True)):
        if i not in result['consumed_frontier_indices']:
            assert new is old
            continue
        assert new['source_step'] is old['source_step']
        for key in ('source_output_slot','sm_output_ref','sm_output_tid','global_shape','ranks','positions'):
            assert new[key] == old[key]
        assert new['predecessor_facts'] == old['facts_theorem']
        assert new['dimensions'] == dict(D=2,T=2,B=1,S=2,H=3)
        assert new['gather_axis'] == 2 and new['local_shape'] == [1,2,3]
        assert new['source_step']['op'] == 'FW_multiref'
        assert new['sm_consumers'] == old['sm_consumers']
        assert all(s['op'] == 'AllToAllPrim' for s in new['local_steps'])
    assert result['retained_units'] == closed['retained_units']
    assert all(r['source_output_slot'] == 0 and 'AllGather' in r['reason'] for r in result['deferred_units'])
    for row in result['reads']:
        assert row['world'] == 'pm' and row['input_metadata'] == 'local-only'
        assert row['input_parent_identity'] == 'local-only' and row['producer_metadata'] == 'all-peers'
        assert row['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][row['execution_index']:]
    assert text.count('SourceSequenceHiddenExchange.output_facts') == 4
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 8
    assert 'SourceLinearRead' not in text and 'SourceAllGatherRead' not in text
    decls = lambda s:set(re.findall(r'^theorem (\w+)',s,re.M))
    assert decls(text).isdisjoint(decls(old_text))
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    with pytest.raises(TypeError): subject.render(*args,closed)


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args,predecessor.render(*args)[1]


def transport(args,closed):
    """Only prior render is substituted; all transport/source guards stay real."""
    with patch.object(predecessor,'render',return_value=('',closed)) as fresh:
        result = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a,b in zip(fresh.call_args.args,args,strict=True))
    return result


def selected(args,slot=1,rank=1,tid=271003):
    return next(c for c in args[3]._inputs[1] if c.node.cid == tid+2000+slot and c.rank == rank)


@pytest.mark.parametrize('fault',['input-bool-bound','input-float-value','input-parent','input-missing',
    'output-bool-bound','output-float-value','output-parent','peer-parent','local-parent',
    'descriptor-input','descriptor-slot','all-slot-missing'])
def test_transport_metadata_and_complete_alias_slots(baseline,fault):
    args,closed = copy.deepcopy(baseline); cell = selected(args)
    if fault.startswith('input-'):
        if fault == 'input-missing': cell._input_irs = None
        elif fault == 'input-parent': cell._input_irs[0].parent.tid += 1
        elif fault == 'input-bool-bound': cell._input_irs[0].indmap = ((False,1),*cell._input_irs[0].indmap[1:])
        else: cell._input_irs[0].valmap = (0.0,1)
    elif fault.startswith('output-'):
        if fault == 'output-parent': cell._output_irs[0].parent.tid += 1
        elif fault == 'output-bool-bound': cell._output_irs[0].indmap = ((False,1),*cell._output_irs[0].indmap[1:])
        else: cell._output_irs[0].valmap = (0.0,1)
        # Make it terminal so successor edge validation cannot mask this guard.
        for c in list(args[3]._inputs[1]):
            if c.rank == cell.rank and c.node.cid == 277004:
                args[1]._node2inputs[c.node] = []
                c.inputs = []; c._input_irs = []
                writer = next(w for w in args[1]._collective_source['writers'] if w['ref']['source_cid'] == c.node.cid and w['ref']['runtime_rank'] == c.rank)
                writer['inputs'] = []
    elif fault in ('peer-parent','local-parent'):
        peer = next(c for c in args[3]._inputs[1] if c.node.cid == 271002 and c.rank == (0 if fault == 'peer-parent' else 1))
        peer._output_irs[1].parent.tid += 1
        # Producer parent tid is deliberately absent from the Port descriptor.
    elif fault == 'descriptor-input': closed['frontier_units'][0]['source_step']['inputs'][0]['endpoint']['tid'] += 1
    elif fault == 'descriptor-slot': closed['frontier_units'][1]['slot'] = 2
    else: closed['frontier_units'] = [r for r in closed['frontier_units'] if not (r['gather_axis'] == 1 and r['source_output_slot'] == 2)]
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('slot', [0,1,2])
@pytest.mark.parametrize('fault', ['scope-local','scope-bool','scope-order','scope-group','scope-params',
    'scope-output','scope-shape','scope-writer','raw-ref-order','raw-rank','raw-kwarg',
    'input-empty','input-partial','output-missing','writer-export','writer-call','writer-fullref',
    'peer-missing','peer-shape'])
def test_all_collective_branches_revalidate_original_metadata(baseline,slot,fault):
    from dataclasses import replace
    args,closed = copy.deepcopy(baseline); cell = selected(args,slot=slot); view = args[1]
    if fault.startswith('scope-'):
        scope = view.collective_scopes[cell.node]
        changes = {'scope-local':dict(local_index=0), 'scope-bool':dict(local_index=True),
            'scope-order':dict(input_tids=tuple(reversed(scope.input_tids))),
            'scope-group':dict(ranks=scope.ranks[:-1]), 'scope-params':dict(params=(2,) if slot == 0 else (2,1)),
            'scope-output':dict(output_tid=True), 'scope-shape':dict(input_shape=(1,9,6)),
            'scope-writer':dict(source_writer='wrong')}
        view.collective_scopes[cell.node] = replace(scope,**changes[fault])
    elif fault == 'raw-ref-order': cell.inputs.reverse()
    elif fault == 'raw-rank': cell.rank = True
    elif fault == 'raw-kwarg': cell.kwargs['dim' if slot == 0 else 'idim'] = True
    elif fault == 'input-empty': cell._input_irs = []
    elif fault == 'input-partial': cell._input_irs = cell._input_irs*3
    elif fault == 'output-missing': cell._output_irs = None
    elif fault.startswith('writer-'):
        w = next(w for w in view._collective_source['writers'] if w['ref']['source_cid'] == cell.node.cid and w['ref']['runtime_rank'] == cell.rank)
        if fault == 'writer-export': w['export_id'] = 'wrong'
        elif fault == 'writer-call': w['ref']['call_instance'] = True
        else: w['inputs'][0]['version'] += 1
    else:
        peer = next(c for c in args[3]._inputs[1] if c.node.cid == 271002 and c.rank == 0)
        if fault == 'peer-missing': peer._output_irs = None
        else: peer._output_irs[slot].shape = (True,*peer._output_irs[slot].shape[1:])
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('index',[0,1,2,3,4,5,6,7])
@pytest.mark.parametrize('fault',['shape','slot','missing'])
def test_every_frontier_row_validated_even_deferred_or_retained(baseline,index,fault):
    args,closed = copy.deepcopy(baseline); row = closed['frontier_units'][index]
    if fault == 'shape': row['local_shape'][0] = True
    elif fault == 'slot': row['source_output_slot'] = False
    else: closed['frontier_units'].pop(index)
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('fault',['duplicate','ranks','positions','local-order','pm-tids','sm-ref',
    'order-partial','order-reverse','order-bool'])
def test_complete_cover_and_schedule(baseline,fault):
    args,closed = copy.deepcopy(baseline); row = closed['frontier_units'][1]
    if fault == 'duplicate': closed['frontier_units'].append(copy.deepcopy(row))
    elif fault == 'ranks': row['ranks'].reverse()
    elif fault == 'positions': row['positions'][0] = False
    elif fault == 'local-order': row['local_steps'].reverse()
    elif fault == 'pm-tids': row['pm_output_tids'].reverse()
    elif fault == 'sm-ref': row['sm_output_ref'][3] += 1
    elif fault == 'order-partial': args[-1]['pm']['execution_to_source'].pop()
    elif fault == 'order-reverse': args[-1]['pm']['execution_to_source'].reverse()
    else: args[-1]['pm']['execution_to_source'][0] = False
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('slot',[1,2])
@pytest.mark.parametrize('operand',[0,1])
def test_full_bw_suffix_nonwrite(baseline,slot,operand):
    args,closed = copy.deepcopy(baseline); cell = selected(args,slot=slot); view = args[1]
    backward = next(n for n in reversed(view.nodes()) if view.node_opname(n).startswith('BW_'))
    view._node2outputs[backward] = [view.node_inputs(cell.node)[operand]]
    with pytest.raises(ValueError): transport(args,closed)


def test_coherent_peer_parent_reidentification_rejected(baseline):
    args,closed = copy.deepcopy(baseline)
    for cell in args[3]._inputs[1]:
        if cell.rank != 0: continue
        if cell.node.cid == 271002: cell._output_irs[1].parent.tid += 7
        elif cell.node.cid == 273004:
            cell._input_irs[0].parent.tid += 7
            cell._output_irs[0].parent.tid += 7
        elif cell.node.cid == 277004: cell._input_irs[0].parent.tid += 7
    with pytest.raises(ValueError): transport(args,closed)


@pytest.mark.parametrize('metadata,aa_slots', [('all-peers',(1,2)),('local-only',(0,2))])
def test_dynamic_source_selected_slots_and_all_ordered_peers(metadata,aa_slots):
    args = prepared(D=1,tp=3,seqlen=6,alias_tid=381003,metadata=metadata,aa_slots=aa_slots)
    text,result = api().render(*args)
    assert [len(result[k]) for k in ('reads','units','frontier_units','deferred_units','retained_units')] == [6,2,4,1,1]
    assert result['consumed_frontier_indices'] == list(aa_slots)
    assert {r['source_output_slot'] for r in result['units']} == set(aa_slots)
    for row in result['units']:
        assert row['dimensions'] == dict(D=1,T=3,B=1,S=6,H=3)
        assert row['global_shape'] == [1,6,9] and row['local_shape'] == [1,6,3]
        assert len(row['pm_consumers']) == 3
    for row in result['reads']:
        assert row['input_metadata'] == metadata and row['input_parent_identity'] == metadata
        assert row['producer_metadata'] == 'all-peers'
        assert len(row['input_refs']) == 3
    assert 'SourceLinearRead' not in text and 'SourceAllGatherRead' not in text
