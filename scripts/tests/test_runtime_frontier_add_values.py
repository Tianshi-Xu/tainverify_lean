"""Source-authenticated frontier pairing; portable fixtures use local B=1 only."""
import copy
import importlib
import importlib.util
import re
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_sequence_hidden_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_sequence_hidden_values as predecessor
from Verdict import runtime_attention_residual_values as residual


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_add_values'), 'frontier ADD pairing renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_add_values')


def fixture(D=2, tp=2, seqlen=2, reverse=False, swap=False, pm_swap=False,
            add_tid=141003, terminal=False, copies=1, omit_rank=None, extra_branch=False, **kwargs):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D=D,tp=tp,seqlen=seqlen,reverse=reverse,
        O=3*tp,terminal=True,skip_kind=None,**kwargs)
    old = copy.deepcopy(authority[2]); rows = []
    if extra_branch:
        for world,graph in [('s',sm),('p',pm)]:
            for alias in [c for c in graph.cells if c.node.cid == 27000]:
                x = alias._output_irs[0]
                extra = IR(27003,x.parent.name,x.parent.shape,x.indmap)
                extra.parent.tid = 28003
                alias._output_irs.append(extra); alias.outputs.append(T(world,alias.rank,0,extra.tid,1))
                alias.kwargs['times'] = 3; graph.shapes[alias.outputs[-1]] = extra.shape
                if world == 'p':
                    for collection in ('writers','adapter_source'):
                        writer = next(w for w in old[collection] if w['ref']['source_cid'] == 27000
                                      and w['ref']['runtime_rank'] == alias.rank)
                        writer['outputs'] = [tref(r) for r in alias.outputs]
    for world, graph in [('s',sm),('p',pm)]:
        mains = [c for c in graph.cells if (c.opname == 'FW_linear' if world == 's' else c.opname == 'AllToAllPrim')
                 and c._output_irs[0].parent.name == 'next.direct.output']
        for main in mains:
            if terminal or (world == 'p' and main.rank == omit_rank): continue
            alias = next(c for c in graph.cells if c.rank == main.rank and c.node.cid == 27000)
            slot = next(i for i,ir in enumerate(alias._output_irs) if ir.parent.tid == 28002)
            refs = [main.outputs[0],alias.outputs[slot]]
            irs = [main._output_irs[0],alias._output_irs[slot]]
            if swap ^ (pm_swap and world == 'p'): refs.reverse(); irs.reverse()
            for k in range(copies):
                out = IR(add_tid+k*10,'joined.output',irs[0].parent.shape,irs[0].indmap)
                cell = NS(node=N(world,main.rank,0,add_tid+k*10,'FW_add'),rank=main.rank,opname='FW_add',
                    inputs=list(refs),outputs=[T(world,main.rank,0,out.tid,1)],kwargs=dict(alpha=1,__consts=[]),
                    _input_irs=copy.deepcopy(irs),_output_irs=[out])
                cell.ir = NS(signature=cell.opname,inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
                at = next((i for i,c in enumerate(graph.cells) if c.rank == main.rank and c.opname.startswith('BW_')),len(graph.cells))
                graph.cells.insert(at,cell); graph.shapes[cell.outputs[0]] = out.shape
                if world == 'p':
                    rows.append(dict(ref=dict(world=world,runtime_rank=cell.rank,microbatch=0,source_cid=cell.node.cid,
                        call_instance=0,op=cell.opname,origin='fixture'),source_irname=cell.opname,
                        inputs=[tref(r) for r in refs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[]))
                    expression = 'frontier_1 + next_exchanged_0' if swap ^ pm_swap else 'next_exchanged_0 + frontier_1'
                    old['rank_sources'][str(cell.rank)] = old['rank_sources'][str(cell.rank)].replace('\ndef _train_step',
                        f'\n        joined_{k} = {expression}\ndef _train_step')
    snapshot = build_snapshot([*old['writers'],*rows])
    snapshot.update({k:old[k] for k in ('source','runtime_ndevs','rank_sources')})
    adapters = {writer_export_id(w['ref']):w for w in [*old['adapter_source'],*copy.deepcopy(rows)]}
    snapshot['adapter_source'] = [adapters[writer_export_id(w['ref'])] for w in snapshot['writers']]
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


def test_public_fresh_ordered_pair_tracer(baseline):
    args,closed = copy.deepcopy(baseline)
    with patch.object(predecessor,'render',wraps=predecessor.render) as fresh, \
         patch.object(residual,'_alias',wraps=residual._alias) as alias:
        text,result = api().render(*args)
    assert fresh.call_count == 1
    assert all(a is b for a,b in zip(fresh.call_args.args,args,strict=True))
    assert alias.call_count == 2  # old attention ancestor ONLY; no new alias restoration
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [5,2,2,0,0]
    assert result['consumed_frontier_indices'] == [0,1,2,3]
    assert text.count('source_add_unit_output_facts') == 2
    for row in result['units']:
        indices = row['input_frontier_indices']; assert len(indices) == 2
        records = [closed['frontier_units'][i] for i in indices]
        assert row['predecessors'] == [r['facts_theorem'] for r in records]
        assert row['source_output_slot'] == 0
        assert row['dimensions'] == dict(D=2,T=2,B=1,S=2,H=3)
        assert [list(p['endpoint']['ref']) for p in row['source_step']['inputs']] == [r['sm_output_ref'] for r in records]
        for j,step in enumerate(row['local_steps']):
            assert [list(p['endpoint']['ref']) for p in step['inputs']] == [r['pm_output_refs'][j] for r in records]
        fragment = text.split('theorem '+row['facts_theorem']+' ',1)[1].split('#print axioms')[0]
        assert '.shape = [2, 2, 6] ∧' in fragment and '∀ y ∈' in fragment
        assert '.shape = [1, 2, 3]' in fragment and 'chunkPrimDimN 0 2' in fragment
        assert 'allGatherPrimDimN 2 2 0' in fragment
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    oldtext = residual.render(*args)[0]
    decls = lambda s:set(re.findall(r'^theorem (\w+)',s,re.M))
    assert decls(text).isdisjoint(decls(oldtext))
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :'): assert bad not in text
    with pytest.raises(TypeError): api().render(*args,closed)


def private(args,closed):
    """Negative guard probes only; never public caller receipt authority."""
    return api()._render(args[0],args[1],args[3],args[-1],closed)


def selected(args,world=1):
    cell = next(c for c in args[3]._inputs[world] if c.node.cid == 141003 and c.rank == 0)
    node = next(n for n in args[world].nodes() if tuple(n) == tuple(cell.node))
    return cell,node


@pytest.mark.parametrize('fault',['parent','parent-shape','bounds','value','input-descriptor'])
def test_new_original_identity_guards(baseline,fault):
    args,closed = copy.deepcopy(baseline); cell,_ = selected(args)
    if fault == 'input-descriptor':
        closed['frontier_units'][0]['source_step']['inputs'][0]['endpoint']['ref'] = ('s',0,0,999999,1)
    else:
        ir = cell._output_irs[0]
        if fault == 'parent': ir.parent.tid += 999
        elif fault == 'parent-shape': ir.parent.shape = (2.0,*ir.parent.shape[1:])
        elif fault == 'bounds': ir.indmap = ((False,1),*ir.indmap[1:])
        else: ir.valmap = (0.0,1)
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('D,tp,S,reverse,swap,out',[(1,3,6,False,True,151003),(3,2,8,True,False,161003)])
def test_public_dynamic_dimensions_and_both_orders(D,tp,S,reverse,swap,out):
    args = prepared(D=D,tp=tp,seqlen=S,reverse=reverse,swap=swap,add_tid=out,
                    exchange_tid=out+1000,output_tid=out+2000,weight_tid=out+3000)
    _,closed = predecessor.render(*args); text,result = api().render(*args)
    assert len(result['reads']) == 1+D*tp and len(result['units']) == D
    assert result['consumed_frontier_indices'] == list(range(2*D))
    assert not result['retained_units'] and not result['deferred_units']
    for row in result['units']:
        assert row['dimensions'] == dict(D=D,T=tp,B=1,S=S,H=3)
        assert row['global_shape'] == [D,S,3*tp] and row['local_shape'] == [1,S,3]
        records = [closed['frontier_units'][i] for i in row['input_frontier_indices']]
        assert row['predecessors'] == [r['facts_theorem'] for r in records]
        assert [list(p['endpoint']['ref']) for p in row['source_step']['inputs']] == [r['sm_output_ref'] for r in records]
    assert text.count('source_add_unit_output_facts') == D


@pytest.mark.parametrize('fault',['bounds','value','parent-shape'])
def test_original_multiref_input_raw_types(baseline,fault):
    args,closed = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 27000 and c.rank == 0)
    ir = cell._input_irs[0]
    if fault == 'bounds': ir.indmap = ((False,1),*ir.indmap[1:])
    elif fault == 'value': ir.valmap = (0.0,1)
    else: ir.parent.shape = (2.0,*ir.parent.shape[1:])
    with pytest.raises(ValueError): private(args,closed)


def test_public_sm_pm_operand_role_mismatch_is_not_commutativity():
    with pytest.raises(ValueError,match='metadata|predecessor|parent|pair'):
        api().render(*prepared(pm_swap=True))


def test_public_terminal_retains_every_original_row():
    args = prepared(terminal=True); _,closed = predecessor.render(*args)
    _,result = api().render(*args)
    assert result['frontier_units'] == result['retained_units'] == closed['frontier_units']
    assert not result['reads'] and not result['units'] and not result['deferred_units']
    assert result['consumed_frontier_indices'] == []


def test_public_join_retains_unrelated_fullref_branch_in_order():
    args = prepared(extra_branch=True,reverse=True,swap=True)
    _,closed = predecessor.render(*args); _,result = api().render(*args)
    assert len(closed['frontier_units']) == 6
    assert len(result['units']) == 2 and len(result['reads']) == 5
    assert result['consumed_frontier_indices'] == [0,1,3,4]
    assert result['retained_units'] == closed['frontier_units'][2::3]
    assert result['frontier_units'][1::2] == result['retained_units']
    assert not result['deferred_units']


@pytest.mark.parametrize('options',[dict(copies=2),dict(omit_rank=0)])
def test_public_partial_fanout_never_drops_frontier(options):
    args = prepared(**options)
    try:
        _,closed = predecessor.render(*args)
        _,result = api().render(*args)
    except ValueError:
        return  # explicit fail-closed rejection is supported
    assert result['frontier_units'] == closed['frontier_units']
    assert not result['units'] and not result['consumed_frontier_indices']
    assert len(result['retained_units']) + len(result['deferred_units']) == len(closed['frontier_units'])


def test_public_missing_distinct_operand_rejects_duplicate_self_add():
    # The predecessor's genuine ADDs consume each branch twice, not a paired join.
    with pytest.raises(ValueError,match='duplicate'):
        api().render(*previous.prepared())


@pytest.mark.parametrize('fault',['missing-unit','duplicate-unit','ranks','positions','dimensions','slot',
    'ref','retained-ref','retained-dimension','local-order','order-partial','order-bool','order-reverse',
    'global-shape','local-shape','axis'])
def test_complete_frontier_authority(baseline,fault):
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
    elif fault == 'order-reverse': args[-1]['pm']['execution_to_source'].reverse()
    elif fault == 'global-shape': row['global_shape'][0] = True
    elif fault == 'local-shape': row['local_shape'][0] = True
    else: row['gather_axis'] = False
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('fault',['alpha','extra','consts','opcode','arity','raw-rank','writer-call',
    'writer-export','writer-ref','scope','output-writer','raw-ref','missing-metadata','input-parent'])
def test_original_add_authority(baseline,fault):
    args,closed = copy.deepcopy(baseline); cell,node = selected(args); view = args[1]
    writer = next(w for w in view._collective_source['writers'] if
        w['ref']['runtime_rank'] == cell.rank and w['ref']['source_cid'] == cell.node.cid)
    if fault == 'alpha': cell.kwargs['alpha'] = True
    elif fault == 'extra': cell.kwargs['extra'] = None
    elif fault == 'consts': cell.kwargs['__consts'] = False
    elif fault == 'opcode': cell.opname = 'FW_mul'
    elif fault == 'arity': cell.inputs.pop()
    elif fault == 'raw-rank': cell.rank = False
    elif fault == 'writer-call': writer['ref']['call_instance'] = True
    elif fault == 'writer-export': writer['export_id'] = 'wrong'
    elif fault == 'writer-ref': writer['inputs'][0]['version'] += 1
    elif fault == 'scope': view.wred_scopes = {node:object()}
    elif fault == 'output-writer': view._node2outputs[node] = list(view.node_inputs(node))
    elif fault == 'raw-ref': cell.inputs.reverse()
    elif fault == 'missing-metadata': del cell._input_irs
    else: cell._input_irs[1].parent.tid += 999
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('world',[0,1])
@pytest.mark.parametrize('operand',[0,1])
def test_selected_and_entire_bw_suffix_nonwrite(baseline,world,operand):
    args,closed = copy.deepcopy(baseline); _,node = selected(args,world); view = args[world]
    targets = [node,*[n for n in view.nodes() if view.node_opname(n).startswith('BW_')]]
    assert len(targets) > 1
    for target in targets:
        bad = copy.deepcopy(args)
        bad[world]._node2outputs[target] = [view.node_inputs(node)[operand]]
        with pytest.raises(ValueError): private(bad,closed)


@pytest.mark.parametrize('field',['_input_irs','_output_irs'])
@pytest.mark.parametrize('fault',['parent-bool','parent-shape','shape-bool','bounds','value'])
def test_typed_raw_before_port(baseline,field,fault):
    args,closed = copy.deepcopy(baseline); cell,_ = selected(args); ir = getattr(cell,field)[0]
    if fault == 'parent-bool': ir.parent.tid = True
    elif fault == 'parent-shape': ir.parent.shape = (2.0,*ir.parent.shape[1:])
    elif fault == 'shape-bool': ir.shape = (True,*ir.shape[1:])
    elif fault == 'bounds': ir.indmap = ((False,1),*ir.indmap[1:])
    else: ir.valmap = (0.0,1)
    with pytest.raises(ValueError): private(args,closed)
