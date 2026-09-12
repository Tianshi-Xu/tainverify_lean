"""Selective AA source tests, local B=1 only; no capture or kernel claim."""
import copy
import importlib
import importlib.util
import re
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_next_linear_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_next_linear_values as predecessor
from Verdict import runtime_output_projection_exchange_values as exchange


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_sequence_hidden_values'), 'selective exchange renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_sequence_hidden_values')


def fixture(D=2, tp=2, seqlen=2, reverse=False, O=10, exchange_tid=111003,
            skip_kind='FW_add', copies=1, omit_rank=None, terminal=False, **kwargs):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D=D, tp=tp, seqlen=seqlen, reverse=reverse,
                                         O=O, skip_kind=skip_kind, **kwargs)
    old = copy.deepcopy(authority[2]); rows, adapters = [], []

    def append(graph, world, rank, cid, kind, refs, irs, outs, kw):
        cell = NS(node=N(world,rank,0,cid,kind),rank=rank,opname=kind,inputs=refs,
                  outputs=[T(world,rank,0,ir.tid,1) for ir in outs], kwargs=kw,
                  _input_irs=copy.deepcopy(irs), _output_irs=outs)
        cell.ir = NS(signature=kind,inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
        at = next((i for i,c in enumerate(graph.cells) if c.rank == rank and c.opname.startswith('BW_')),len(graph.cells))
        graph.cells.insert(at,cell)
        graph.shapes.update({r: ir.shape for r,ir in zip(cell.outputs,outs,strict=True)})
        if world == 'p':
            row = dict(ref=dict(world=world,runtime_rank=rank,microbatch=0,source_cid=cid,
                call_instance=0,op=kind,origin='fixture'),source_irname=kind,
                inputs=[tref(r) for r in refs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[])
            rows.append(row); adapters.append(copy.deepcopy(row))
        return cell

    for world, graph in [('s',sm),('p',pm)]:
        producers = [c for c in graph.cells if c.opname == 'FW_linear' and c._output_irs[0].parent.name == 'next.direct.output']
        for producer in producers:
            if world == 'p' and producer.rank == omit_rank:
                continue
            x = producer._output_irs[0]; rank = producer.rank
            targets = [producer]
            if world == 'p':
                targets = []
                ranks = list(range(rank//tp*tp,(rank//tp+1)*tp)); j = ranks.index(rank)
                peers = [next(p for p in producers if p.rank == r) for r in ranks]
                width, rem = divmod(O,tp); assert rem == 0
                for k in range(copies):
                    y = IR(exchange_tid+k*10,x.parent.name,x.parent.shape,
                           (x.indmap[0],(0,seqlen),(j*width,(j+1)*width)))
                    y.parent.tid = x.parent.tid
                    kw = dict(ranks=ranks,idim=1,odim=2)
                    aa = append(graph,world,rank,exchange_tid+k*10,'AllToAllPrim',
                                [p.outputs[0] for p in peers],[x],[y],kw)
                    rows[-1]['adapter_kwargs'] = copy.deepcopy(kw)
                    adapter = adapters[-1]; adapter['inputs'] = [tref(producer.outputs[0])]
                    adapter['primitive'] = dict(kind='AllToAllPrim',forward=True,kwargs=copy.deepcopy(kw),
                        signature='nnscaler.runtime.adapter.all_to_all',generated_inputs=['projected'],
                        generated_outputs=[f'next_exchanged_{k}'])
                    params = ', '.join(f'{key}={v!r}' for key,v in kw.items())
                    old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                        f'\n        next_exchanged_{k} = nnscaler.runtime.adapter.all_to_all(projected, {params})\ndef _train_step')
                    targets.append(aa)
            # Genuine original downstream ADD; the frontier is not fake-closed.
            for k,target in enumerate([] if terminal else targets):
                ir = target._output_irs[0]
                y = IR(exchange_tid+100+k*10,'later.add',ir.parent.shape,ir.indmap)
                append(graph,world,rank,exchange_tid+100+k*10,'FW_add',
                       target.outputs*2,[ir,ir],[y],dict(__consts=[]))
                if world == 'p':
                    old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                        f'\n        later = next_exchanged_{k} + next_exchanged_{k}\ndef _train_step')
    snapshot = build_snapshot([*old['writers'],*rows])
    snapshot.update({k:old[k] for k in ('source','runtime_ndevs','rank_sources')})
    by_writer = {writer_export_id(w['ref']):w for w in [*old['adapter_source'],*adapters]}
    snapshot['adapter_source'] = [by_writer[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm,pm,(copy.deepcopy(sm.cells),copy.deepcopy(pm.cells),snapshot,*authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous,'fixture',return_value=f):
        return previous.prepared(D=kwargs.get('D',2),tp=kwargs.get('tp',2),seqlen=kwargs.get('seqlen',2))


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args,predecessor.render(*args)[1]


def test_public_fresh_full_cover_tracer(baseline):
    args,old = copy.deepcopy(baseline)
    with patch.object(predecessor,'render',wraps=predecessor.render) as fresh, \
         patch.object(exchange,'_render',wraps=exchange._render) as legacy:
        text,result = api().render(*args)
    assert fresh.call_count == 1 and legacy.call_count == 1  # ancestor only
    assert all(a is b for a,b in zip(fresh.call_args.args,args,strict=True))
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [4,2,4,2,0]
    assert result['consumed_frontier_indices'] == [0,2]
    assert result['retained_units'] == old['retained_units']
    assert result['frontier_units'][1::2] == old['frontier_units'][1::2]
    assert text.count('SourceSequenceHiddenExchange.output_facts') == 2
    assert text.count('SourcePrimitiveRead.allToAll_value_of_split') == 4
    for row in result['units']:
        prior = old['frontier_units'][row['frontier_index']]
        for key in ('source_step','source_output_slot','sm_output_ref','sm_output_tid','global_shape','ranks','positions'):
            assert row[key] == prior[key]
        assert row['predecessor_facts'] == row['predecessor'] == prior['facts_theorem']
        assert row['theorem'] == row['facts_theorem']
        assert row['dimensions'] == dict(D=2,T=2,B=1,S=2,H=5)
        assert row['local_shape'] == [1,2,5] and row['gather_axis'] == 2
        fragment = text.split('theorem '+row['theorem']+' ',1)[1].split('#print axioms')[0]
        assert '.shape = [2, 2, 10] ∧' in fragment and '∀ y ∈' in fragment
        assert '.shape = [1, 2, 5]' in fragment and 'allGatherPrimDimN 2 2 0' in fragment
    for row in result['reads']:
        assert row['world'] == 'pm' and row['input_metadata'] == 'local-only'
        assert row['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][row['execution_index']:]
    old_text = exchange.render(*args)[0]
    decls = lambda s:set(re.findall(r'^theorem (\w+)',s,re.M))
    assert decls(text).isdisjoint(decls(old_text))
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'):
        assert result[flag] is False
    with pytest.raises(TypeError): api().render(*args,old)



def test_terminal_raw_output_cannot_hide_bad_metadata():
    args = prepared(terminal=True)
    _,closed = predecessor.render(*args)
    accepted = []
    for fault in ('parent','bool-bounds','float-value'):
        bad = copy.deepcopy(args); cell,_ = selected(bad); ir = cell._output_irs[0]
        if fault == 'parent': ir.parent.tid += 999
        elif fault == 'bool-bounds': ir.indmap = ((False,1),*ir.indmap[1:])
        else: ir.valmap = (0.0,1)
        try:
            private(bad,closed)
        except ValueError:
            continue
        accepted.append(fault)
    assert not accepted, accepted


def private(args, closed):
    """Guard probe using a real fresh receipt, never public authority."""
    return api()._render(args[0],args[1],args[3],args[-1],closed)


def selected(args):
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 111003 and c.rank == 0)
    node = next(n for n in args[1].nodes() if tuple(n) == tuple(cell.node))
    return cell,node


@pytest.mark.parametrize('field,fault', [('_input_irs','missing'),('_input_irs','bool-bounds'),
    ('_input_irs','float-value'),('_input_irs','parent'),('_input_irs','shape'),
    ('_output_irs','parent'),('_output_irs','bool-bounds'),('_output_irs','float-value')])
def test_raw_exchange_metadata(baseline, field, fault):
    args,closed = copy.deepcopy(baseline); cell,_ = selected(args)
    if fault == 'missing': delattr(cell,field)
    else:
        ir = getattr(cell,field)[0]
        if fault == 'parent': ir.parent.tid += 999
        elif fault == 'bool-bounds': ir.indmap = ((False,1),*ir.indmap[1:])
        elif fault == 'float-value': ir.valmap = (0.0,1)
        else: ir.shape = (True,*ir.shape[1:])
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('fault', ['missing-unit','duplicate-unit','ranks','positions','dimensions',
    'slot','ref','retained-ref','retained-dimension','local-order','order-partial','order-bool','order-reverse'])
def test_complete_frontier_authority(baseline, fault):
    args,closed = copy.deepcopy(baseline); row = closed['frontier_units'][0]
    if fault == 'missing-unit': closed['frontier_units'].pop(2)
    elif fault == 'duplicate-unit': closed['frontier_units'].append(copy.deepcopy(row))
    elif fault == 'ranks': row['ranks'].reverse()
    elif fault == 'positions': row['positions'] = [99]
    elif fault == 'dimensions': row['dimensions']['H'] = True
    elif fault == 'slot': row['source_output_slot'] = False
    elif fault == 'ref': row['sm_output_ref'][3] += 1
    elif fault == 'retained-ref': closed['frontier_units'][1]['pm_output_refs'][0][3] += 1
    elif fault == 'retained-dimension': closed['frontier_units'][1]['dimensions']['S'] += 1
    elif fault == 'local-order': row['local_steps'].reverse()
    elif fault == 'order-partial': args[-1]['pm']['execution_to_source'].pop()
    elif fault == 'order-bool': args[-1]['pm']['execution_to_source'][0] = False
    else: args[-1]['pm']['execution_to_source'].reverse()
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('fault',['kwargs','ranks','extra','consts','writer-call','writer-export','writer-ref',
    'raw-ref','raw-rank','scope','wred','output-writer'])
def test_original_aa_authority(baseline,fault):
    from dataclasses import replace
    args,closed = copy.deepcopy(baseline); cell,node = selected(args); view = args[1]
    writer = next(w for w in view._collective_source['writers'] if
        w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    if fault == 'kwargs': cell.kwargs['idim'] = True
    elif fault == 'ranks': cell.kwargs['ranks'].reverse()
    elif fault == 'extra': cell.kwargs['extra'] = None
    elif fault == 'consts': cell.kwargs['__consts'] = False
    elif fault == 'writer-call': writer['ref']['call_instance'] = True
    elif fault == 'writer-export': writer['export_id'] = 'wrong'
    elif fault == 'writer-ref': writer['inputs'][0]['version'] += 1
    elif fault == 'raw-ref': cell.inputs.reverse()
    elif fault == 'raw-rank': cell.rank = False
    elif fault == 'scope': view.collective_scopes[node] = replace(view.collective_scopes[node],ranks=(1,0))
    elif fault == 'wred': view.wred_scopes = {node: next(iter(view.collective_scopes.values()))}
    else: view._node2outputs[node] = list(view.node_inputs(node))
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('operand',[0,1])
def test_every_bw_suffix_operand_nonwrite(baseline,operand):
    args,closed = copy.deepcopy(baseline); cell,node = selected(args); view = args[1]
    for target in [node,*[n for n in view.nodes() if view.node_opname(n).startswith('BW_')]]:
        copied = copy.deepcopy(args)
        copied[1]._node2outputs[target] = [view.node_inputs(node)[operand]]
        with pytest.raises(ValueError): private(copied,closed)


@pytest.mark.parametrize('D,tp,S,reverse,O,out',[(1,3,6,False,15,121003),(3,2,8,True,14,131003)])
def test_public_shapes_alias_reorder_and_identities(D,tp,S,reverse,O,out):
    args = prepared(D=D,tp=tp,seqlen=S,reverse=reverse,O=O,exchange_tid=out,
                    weight_tid=out+1000,output_tid=out+2000)
    _,closed = predecessor.render(*args); text,result = api().render(*args)
    assert len(result['reads']) == D*tp and len(result['units']) == D
    assert result['consumed_frontier_indices'] == list(range(int(reverse),2*D,2))
    for i,old in enumerate(closed['frontier_units']):
        if i not in result['consumed_frontier_indices']: assert result['frontier_units'][i] == old
    for row in result['units']:
        assert row['dimensions'] == dict(D=D,T=tp,B=1,S=S,H=O//tp)
        assert row['global_shape'] == [D,S,O] and row['local_shape'] == [1,S,O//tp]
    assert len(re.findall(r'^theorem ',text,re.M)) == D*tp+D


@pytest.mark.parametrize('options',[dict(copies=2),dict(omit_rank=0)])
def test_public_partial_and_fanout(options):
    with pytest.raises(ValueError,match='partial|fan-out|incomplete|scope|adapter|peer occurrence'):
        api().render(*prepared(**options))


def test_public_no_exchange_defers_sequence_and_keeps_hidden():
    args = previous.prepared()
    _,closed = predecessor.render(*args); _,result = api().render(*args)
    assert result['frontier_units'] == closed['frontier_units']
    assert len(result['retained_units']) == len(result['deferred_units']) == 2
    assert not result['units'] and not result['reads']


def test_hidden_other_branch_is_explicitly_deferred():
    args = prepared(skip_kind='FW_mul')
    _,closed = predecessor.render(*args); _,result = api().render(*args)
    assert len(result['deferred_units']) == 2 and not result['retained_units']
    assert result['frontier_units'][1::2] == closed['frontier_units'][1::2]
    assert all(r['observed_consumer_ops'] == [['FW_mul']]*3 for r in result['deferred_units'])
