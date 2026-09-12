"""Real ADD -> multiref/AA composition; portable local B=1, main terminal.

The other branch has a source-backed later ADD; no LN or kernel claim is made.
Inherited fixtures fix the hidden input shard width at 3; sequence output H
varies with TP. This does not claim independent hidden-width or local B>1 coverage.
"""
import copy
import importlib
import importlib.util
import re
import sys
from contextlib import ExitStack
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_add_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_add_values as predecessor
from Verdict import runtime_frontier_alias_exchange_values as adapter


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_next_alias_exchange_values'), 'next alias/exchange renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_next_alias_exchange_values')


def fixture(D=2, tp=2, seqlen=2, reverse=False, next_tid=171003,
            omit_rank=None, copies=1, mixed_fanout=False, **kwargs):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D=D,tp=tp,seqlen=seqlen,reverse=reverse,**kwargs)
    old = copy.deepcopy(authority[2]); rows, adapters = [], []

    def append(graph, world, rank, cid, kind, refs, irs, outs, kw):
        cell = NS(node=N(world,rank,0,cid,kind),rank=rank,opname=kind,inputs=list(refs),
            outputs=[T(world,rank,0,ir.tid,1) for ir in outs],kwargs=kw,
            _input_irs=copy.deepcopy(irs),_output_irs=outs)
        cell.ir = NS(signature=kind,inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
        at = next((i for i,c in enumerate(graph.cells) if c.rank == rank and c.opname.startswith('BW_')),len(graph.cells))
        graph.cells.insert(at,cell)
        graph.shapes.update({r:ir.shape for r,ir in zip(cell.outputs,outs,strict=True)})
        if world == 'p':
            row = dict(ref=dict(world=world,runtime_rank=rank,microbatch=0,source_cid=cid,
                call_instance=0,op=kind,origin='fixture'),source_irname=kind,
                inputs=[tref(r) for r in refs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[])
            rows.append(row); adapters.append(copy.deepcopy(row))
        return cell

    aliases = {}
    for world,graph in [('s',sm),('p',pm)]:
        for producer in [c for c in graph.cells if c.opname == 'FW_add' and c._output_irs[0].parent.name == 'joined.output']:
            x = producer._output_irs[0]
            outs = [IR(next_tid+k,x.parent.name,x.parent.shape,x.indmap) for k in range(2)]
            for k,ir in enumerate(outs): ir.parent.tid = next_tid+100+k
            if reverse: outs.reverse()
            a = append(graph,world,producer.rank,next_tid-1,'FW_multiref',producer.outputs,[x],outs,dict(times=2,__consts=[]))
            aliases[world,producer.rank] = a
            slot = next(k for k,ir in enumerate(outs) if ir.parent.tid == next_tid+101)
            skip = outs[slot]
            y = IR(next_tid+200,'later.skip.add',skip.parent.shape,skip.indmap)
            append(graph,world,producer.rank,next_tid+200,'FW_add',[a.outputs[slot]]*2,[skip]*2,[y],dict(alpha=1,__consts=[]))
            if mixed_fanout:
                main = outs[1-slot]
                extra = IR(next_tid+201,'mixed.main.add',main.parent.shape,main.indmap)
                append(graph,world,producer.rank,next_tid+201,'FW_add',
                       [a.outputs[1-slot]]*2,[main]*2,[extra],dict(alpha=1,__consts=[]))
            if world == 'p':
                old['rank_sources'][str(producer.rank)] = old['rank_sources'][str(producer.rank)].replace('\ndef _train_step',
                    '\n        next_alias_0, next_alias_1 = joined_0, joined_0\n        next_skip = next_alias_1 + next_alias_1\ndef _train_step')
                if mixed_fanout:
                    old['rank_sources'][str(producer.rank)] = old['rank_sources'][str(producer.rank)].replace(
                        '\ndef _train_step','\n        mixed_main = next_alias_0 + next_alias_0\ndef _train_step')
    for rank in range(D*tp):
        if rank == omit_rank: continue
        ranks = list(range(rank//tp*tp,(rank//tp+1)*tp)); j = ranks.index(rank)
        peers = [aliases['p',r] for r in ranks]
        slot = next(k for k,ir in enumerate(peers[j]._output_irs) if ir.parent.tid == next_tid+100)
        x = peers[j]._output_irs[slot]
        for k in range(copies):
            y = IR(next_tid+300+k,x.parent.name,x.parent.shape,
                   (x.indmap[0],(j*(seqlen//tp),(j+1)*(seqlen//tp)),(0,3*tp)))
            y.parent.tid = x.parent.tid
            kw = dict(ranks=ranks,idim=2,odim=1)
            append(pm,'p',rank,next_tid+300+k,'AllToAllPrim',[p.outputs[slot] for p in peers],[x],[y],kw)
            rows[-1]['adapter_kwargs'] = copy.deepcopy(kw)
            a = adapters[-1]; a['inputs'] = [tref(peers[j].outputs[slot])]
            a['primitive'] = dict(kind='AllToAllPrim',forward=True,kwargs=copy.deepcopy(kw),
                signature='nnscaler.runtime.adapter.all_to_all',generated_inputs=['next_alias_0'],
                generated_outputs=[f'next_sequence_{k}'])
            params = ', '.join(f'{key}={v!r}' for key,v in kw.items())
            old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                f'\n        next_sequence_{k} = nnscaler.runtime.adapter.all_to_all(next_alias_0, {params})\ndef _train_step')
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


def test_public_source_backed_two_branch_tracer(baseline):
    args,closed = copy.deepcopy(baseline)
    subject = api(); ancestors = []
    def record(fn):
        def wrapped(*a,**kw):
            result = fn(*a,**kw); ancestors.append(result[0]); return result
        return wrapped
    with ExitStack() as stack:
        # Record actual ancestor declarations during this single fresh chain.
        for name,module in list(sys.modules.items()):
            if name.startswith('Verdict.runtime_') and module is not subject and callable(getattr(module,'render',None)):
                stack.enter_context(patch.object(module,'render',side_effect=record(module.render)))
        fresh = predecessor.render; old_public = adapter.render
        text,result = subject.render(*args)
        assert fresh.call_count == 1 and old_public.call_count == 1  # ancestor only
        assert all(a is b for a,b in zip(fresh.call_args.args,args,strict=True))
    assert [len(result[k]) for k in ('reads','alias_units','exchange_units','frontier_units','retained_units','deferred_units')] == [9,4,2,4,2,0]
    assert result['consumed_frontier_indices'] == [0,1]
    assert [r['source_output_slot'] for r in result['frontier_units']] == [0,1,0,1]
    assert [r['gather_axis'] for r in result['frontier_units']] == [1,2,1,2]
    assert result['retained_units'] == result['frontier_units'][1::2]
    for row in result['alias_units']:
        assert row['predecessor_facts'] == closed['frontier_units'][row['frontier_index']]['facts_theorem']
        slot = row['source_output_slot']
        assert list(row['source_step']['outputs'][slot]['endpoint']['ref']) == row['sm_output_ref']
        assert [list(s['outputs'][slot]['endpoint']['ref']) for s in row['local_steps']] == row['pm_output_refs']
    for row in result['retained_units']:
        assert len(row['sm_consumers']) == 1 and len(row['pm_consumers']) == 2
    for row in result['exchange_units']:
        assert row['pm_consumers'] == row['sm_consumers'] == []  # explicitly terminal main
        assert row['dimensions'] == dict(D=2,T=2,B=1,S=1,H=6)
    for row in result['reads']:
        if row['op'] == 'AllToAllPrim':
            assert row['input_metadata'] == 'local-only'
            assert row['operand_nonwrite_source_indices'] == args[-1]['pm']['execution_to_source'][row['execution_index']:]
        else:
            assert len(row['source_step']['outputs']) == 2
    for row in result['frontier_units']:
        fragment = text.split('theorem '+row['facts_theorem']+' ',1)[1].split('#print axioms')[0]
        assert '.shape = [2, 2, 6] ∧' in fragment and '∀ y ∈' in fragment
        assert str(row['local_shape']) in fragment
        assert f'allGatherPrimDimN {row["gather_axis"]} 2 0' in fragment
    decls = lambda s:set(re.findall(r'^(?:theorem|def|abbrev) (\w+)',s,re.M))
    assert ancestors and all(decls(text).isdisjoint(decls(old)) for old in ancestors)
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :'): assert bad not in text
    with pytest.raises(TypeError): subject.render(*args,closed)


@pytest.mark.parametrize('D,tp,S,reverse,out',[(1,3,6,True,181003),(3,2,8,False,191003)])
def test_public_dynamic_source_order_and_complete_adapter_result(D,tp,S,reverse,out):
    args = prepared(D=D,tp=tp,seqlen=S,reverse=reverse,next_tid=out,
                    add_tid=out+1000,exchange_tid=out+2000,output_tid=out+3000,weight_tid=out+4000)
    observed = []
    original = adapter._render
    def capture(*a):
        result = original(*a); observed.append((a,result)); return result
    with patch.object(adapter,'_render',side_effect=capture):
        text,result = api().render(*args)
    assert len(observed) == 2  # original attention stage, then this next ADD stage
    assert (text,result) == observed[-1][1]
    assert len(observed[-1][0][-1]['frontier_units']) == D
    assert len(result['reads']) == 1+2*D*tp
    assert len(result['frontier_units']) == 2*D and len(result['retained_units']) == D
    assert [r['slot'] for r in result['frontier_units']] == [0,1]*D
    assert [r['gather_axis'] for r in result['frontier_units']] == ([2,1] if reverse else [1,2])*D
    assert result['consumed_frontier_indices'] == list(range(D))
    for row in result['frontier_units']:
        sequence = row['gather_axis'] == 1
        assert row['dimensions'] == dict(D=D,T=tp,B=1,S=S//tp if sequence else S,H=3*tp if sequence else 3)
        assert row['global_shape'] == [D,S,3*tp]
        assert row['local_shape'] == ([1,S//tp,3*tp] if sequence else [1,S,3])
        assert row['positions'] == [row['unit']]
        assert row['ranks'] == list(range(row['unit']*tp,(row['unit']+1)*tp))
        assert len(row['pm_output_refs']) == len(row['local_steps']) == tp
    decls = lambda s:set(re.findall(r'^(?:theorem|def|abbrev) (\w+)',s,re.M))
    assert decls(text).isdisjoint(decls(observed[0][1][0]))


def private(args,closed):
    """Composition private guard probes ONLY, not public receipt authority."""
    return api()._render(args[0],args[1],args[3],args[-1],closed)


@pytest.mark.parametrize('fault',['missing-unit','duplicate-unit','ranks','positions','dimension',
                                'global-shape','local-shape','ref','local-order','partial-order'])
def test_composed_complete_add_frontier_private_guards(baseline,fault):
    args,closed = copy.deepcopy(baseline); row = closed['frontier_units'][0]
    if fault == 'missing-unit': closed['frontier_units'].pop()
    elif fault == 'duplicate-unit': closed['frontier_units'].append(copy.deepcopy(row))
    elif fault == 'ranks': row['ranks'].reverse()
    elif fault == 'positions': row['positions'] = [99]
    elif fault == 'dimension': row['dimensions']['H'] = True
    elif fault == 'global-shape': row['global_shape'][0] = True
    elif fault == 'local-shape': row['local_shape'][0] = True
    elif fault == 'ref': row['pm_output_refs'][0][3] += 1
    elif fault == 'local-order': row['local_steps'].reverse()
    else: args[-1]['pm']['execution_to_source'].pop()
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('fault',['skip-parent','skip-value','alias-input','exchange-input',
    'exchange-output','writer-call','writer-export','scope-owner','scope-axes','kwargs'])
def test_composed_original_authority_private_guards(baseline,fault):
    from dataclasses import replace
    args,closed = copy.deepcopy(baseline); view = args[1]
    alias = next(c for c in args[3]._inputs[1] if c.node.cid == 171002 and c.rank == 0)
    aa = next(c for c in args[3]._inputs[1] if c.node.cid == 171303 and c.rank == 0)
    if fault == 'skip-parent': alias._output_irs[1].parent.tid += 1
    elif fault == 'skip-value': alias._output_irs[1].valmap = (False,1)
    elif fault == 'alias-input': alias._input_irs[0].parent.tid += 1
    elif fault == 'exchange-input': aa._input_irs[0].indmap = ((False,1),*aa._input_irs[0].indmap[1:])
    elif fault == 'exchange-output': aa._output_irs[0].parent.tid += 1
    elif fault.startswith('writer-'):
        writer = next(w for w in view._collective_source['writers'] if w['ref']['source_cid'] == aa.node.cid and w['ref']['runtime_rank'] == 0)
        if fault == 'writer-call': writer['ref']['call_instance'] = True
        else: writer['export_id'] = 'wrong'
    elif fault.startswith('scope-'):
        key,scope = next((k,s) for k,s in view.collective_scopes.items() if tuple(s.node) == tuple(aa.node))
        view.collective_scopes[key] = replace(scope,**(dict(local_index=False) if fault == 'scope-owner' else dict(params=(2,True))))
    else: aa.kwargs['idim'] = True
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('world',[0,1])
def test_composed_entire_bw_suffix_nonwrite_private(baseline,world):
    args,closed = baseline; view = args[world]
    nodes = [n for n in view.nodes() if n.cid in (171002,171303)]
    assert nodes
    suffix = [n for n in view.nodes() if view.node_opname(n).startswith('BW_')]
    assert suffix
    for node in nodes:
        for target in [node,*suffix]:
            bad = copy.deepcopy(args)
            bad[world]._node2outputs[target] = [view.node_inputs(node)[0]]
            with pytest.raises(ValueError): private(bad,copy.deepcopy(closed))


@pytest.mark.parametrize('options',[dict(omit_rank=0),dict(copies=2),dict(extra_branch=True),dict(mixed_fanout=True)])
def test_public_partial_fanout_or_unconsumed_predecessor_rejects(options):
    # No predecessor filtering or successful partial branch closure is permitted.
    with pytest.raises(ValueError): api().render(*prepared(**options))


def test_public_revalidates_predecessor_and_retained_source(baseline):
    for cid,field,slot in [(141003,'_input_irs',0),(171002,'_output_irs',1)]:
        args,_ = copy.deepcopy(baseline)
        cell = next(c for c in args[3]._inputs[1] if c.node.cid == cid and c.rank == 0)
        getattr(cell,field)[slot].parent.tid += 999
        with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('mutation',['old-entry','drop-unit','drop-skip','copy-six'])
def test_public_tracer_kills_composition_mutations(baseline,mutation):
    import inspect
    subject = api(); source = inspect.getsource(subject.render)
    if mutation == 'old-entry':
        source = source.replace('return _render(sm, pm, validation, execution_order, closed)',
                                'return adapter.render(sm, pm, lineages, validation, bound, execution_order)')
    elif mutation == 'drop-unit':
        source = source.replace('return _render', "closed['frontier_units'] = closed['frontier_units'][:1]\n        return adapter._render")
    elif mutation == 'drop-skip':
        source = source.replace('return _render(sm, pm, validation, execution_order, closed)',
            "text, result = adapter._render(sm, pm, validation, execution_order, closed)\n        result['frontier_units'] = result['exchange_units']\n        return text, result")
    else:
        source = source.replace('predecessor.render(sm, pm, lineages, validation, bound, execution_order)',
            'predecessor.render(*copy.deepcopy((sm, pm, lineages, validation, bound, execution_order)))')
    assert source != inspect.getsource(subject.render), 'mutation did not apply'
    namespace = dict(predecessor=predecessor,adapter=adapter,copy=copy,_render=subject._render)
    exec(compile(source,'<in-memory-composition-mutant>','exec'),namespace)
    with patch.object(subject,'render',namespace['render']):
        with pytest.raises((AssertionError,ValueError)):
            test_public_source_backed_two_branch_tracer(baseline)


def test_private_typed_contract_mutant_is_killed(baseline):
    # Only the private composition seam is mutated; no caller receipt is used
    # to assert a public positive or a kernel result.
    subject = api()
    with patch.object(subject,'_render',adapter._render):
        for fault in ('dimension','local-shape'):
            with pytest.raises(pytest.fail.Exception):
                test_composed_complete_add_frontier_private_guards(baseline,fault)
