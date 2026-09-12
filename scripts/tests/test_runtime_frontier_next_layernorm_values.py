"""Next real LN composition; portable local B=1, inherited hidden shard H=3.

D/TP/sequence and source identities vary; independent hidden width and local
B>1, actual capture, kernel compilation and whole-model/Torch are not claimed.
"""
import copy
import importlib
import importlib.util
import inspect
import re
import sys
from contextlib import ExitStack
from dataclasses import asdict
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_next_alias_exchange_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_next_alias_exchange_values as predecessor
from Verdict import runtime_frontier_layernorm_values as adapter
from Verdict.runtime_lineage import Role


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_next_layernorm_values'), 'next LayerNorm renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_next_layernorm_values')


def fixture(D=2, tp=2, seqlen=2, reverse=False, next_tid=171003,
            ln_tid=211003, parameter_tid=221001, names=('next.scale', 'next.offset'),
            swap=False, ln_omit_rank=None, ln_copies=1, skip_kind='FW_add', **kwargs):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(D=D, tp=tp, seqlen=seqlen, reverse=reverse, next_tid=next_tid, **kwargs)
    old = copy.deepcopy(authority[2]); rows = []
    for world, graph in [('s', sm), ('p', pm)]:
        for rank in range(graph.W.runtime_ndevs):
            producer = next(c for c in graph.cells if c.rank == rank and c.node.cid == (next_tid-1 if world == 's' else next_tid+300))
            slot = next(i for i, ir in enumerate(producer._output_irs) if ir.parent.tid == next_tid+100)
            x = producer._output_irs[slot]
            if not (world == 'p' and rank == ln_omit_rank):
                for k in range(ln_copies):
                    params = [IR(parameter_tid+i, name, (3*tp,), param=True) for i, name in enumerate(names)]
                    if swap: params.reverse()
                    refs = [producer.outputs[slot], *(T(world, rank, -1, p.tid, 0) for p in params)]
                    out = IR(ln_tid+k, 'next.normalized', x.parent.shape, x.indmap)
                    cell = NS(node=N(world, rank, 0, ln_tid+k, 'FW_layernorm'), rank=rank, opname='FW_layernorm',
                        inputs=refs, outputs=[T(world, rank, 0, out.tid, 1)],
                        kwargs=dict(normalized_shape=[3*tp], eps=1e-5, __consts=[]),
                        _input_irs=[copy.deepcopy(x), *params], _output_irs=[out])
                    cell.ir = NS(signature=cell.opname, inputs=lambda c=cell:c._input_irs, outputs=lambda c=cell:c._output_irs)
                    at = next((i for i,c in enumerate(graph.cells) if c.rank == rank and c.opname.startswith('BW_')), len(graph.cells))
                    graph.cells.insert(at, cell)
                    graph.shapes.update({r:ir.shape for r,ir in zip(cell.inputs+cell.outputs, cell._input_irs+cell._output_irs, strict=True)})
                    if world == 'p':
                        rows.append(dict(ref=dict(world=world, runtime_rank=rank, microbatch=0, source_cid=ln_tid+k,
                            call_instance=0, op=cell.opname, origin='fixture'), source_irname=cell.opname,
                            inputs=[tref(r) for r in refs], outputs=[tref(r) for r in cell.outputs], parameter_grad_tids=[]))
                        old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                            f'\n        next_normalized_{k} = torch.nn.functional.layer_norm(next_sequence_0, normalized_shape=[{3*tp}], '
                            f'weight=self.param_{params[0].tid}, bias=self.param_{params[1].tid}, eps=1e-5)\ndef _train_step')
            if skip_kind != 'FW_add':
                skip = next(c for c in graph.cells if c.rank == rank and c.node.cid == next_tid+200)
                skip.opname = skip_kind; skip.node = skip.node._replace(irname=skip_kind)
                skip.kwargs = {}; skip.ir.signature = skip_kind
                if world == 'p':
                    for collection in ('writers', 'adapter_source'):
                        writer = next(w for w in old[collection] if w['ref']['source_cid'] == next_tid+200 and w['ref']['runtime_rank'] == rank)
                        writer['ref']['op'] = skip_kind; writer['source_irname'] = skip_kind
                    old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('next_alias_1 + next_alias_1', 'next_alias_1 * next_alias_1')
    snapshot = build_snapshot([*old['writers'], *rows])
    snapshot.update({k:old[k] for k in ('source', 'runtime_ndevs', 'rank_sources')})
    adapters = {writer_export_id(w['ref']):w for w in [*old['adapter_source'], *copy.deepcopy(rows)]}
    snapshot['adapter_source'] = [adapters[writer_export_id(w['ref'])] for w in snapshot['writers']]
    bind_reducers(snapshot); bind_adapters(snapshot)
    return sm, pm, (copy.deepcopy(sm.cells), copy.deepcopy(pm.cells), snapshot, *authority[3:])


def prepared(**kwargs):
    f = fixture(**kwargs)
    with patch.object(previous, 'fixture', return_value=f):
        return previous.prepared(D=kwargs.get('D', 2), tp=kwargs.get('tp', 2), seqlen=kwargs.get('seqlen', 2))


@pytest.fixture(scope='module')
def baseline():
    args = prepared()
    return args, predecessor.render(*args)[1]


def test_public_real_next_ln_tracer(baseline):
    args, expected_closed = copy.deepcopy(baseline)
    subject = api(); ancestors = []; observed = []; fresh_results = []
    original = adapter._render
    def record(fn):
        def wrapped(*a, **kw):
            result = fn(*a, **kw); ancestors.append(result[0])
            if fn.__module__ == predecessor.__name__: fresh_results.append(result[1])
            return result
        return wrapped
    def consume(*a):
        result = original(*a); observed.append((a, result)); return result
    with ExitStack() as stack:
        for name, module in list(sys.modules.items()):
            if name.startswith('Verdict.runtime_') and module is not subject and callable(getattr(module, 'render', None)):
                stack.enter_context(patch.object(module, 'render', side_effect=record(module.render)))
        stack.enter_context(patch.object(adapter, '_render', side_effect=consume))
        fresh = predecessor.render; old_public = adapter.render
        text, result = subject.render(*args)
        assert fresh.call_count == 1
        assert old_public.call_count == 1  # earlier genuine LN ancestor, never a second public entry
        assert all(a is b for a,b in zip(fresh.call_args.args, args, strict=True))
    assert len(observed) == 2  # earlier LN plus this actual next LN
    assert all(a is b for a,b in zip(observed[-1][0][:-1], args, strict=True))
    assert observed[-1][0][-1] == expected_closed
    assert len(fresh_results) == 1 and observed[-1][0][-1] is fresh_results[0]
    assert (text, result) == observed[-1][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [5,2,4,2,0]
    assert result['consumed_frontier_indices'] == [0,2]
    assert result['frontier_units'][1::2] == expected_closed['frontier_units'][1::2]
    assert result['retained_units'] == expected_closed['retained_units']
    assert text.count('SourceLayernormRead.layernorm_value_of_split') == 5
    assert text.count('source_layernorm_unit_output_reconstruct') == 2
    assert 'initialParameterValues_final s p t q hs hp h' in text
    for row in result['units']:
        old = expected_closed['frontier_units'][row['frontier_index']]
        assert row['predecessor_facts'] == old['facts_theorem']
        assert row['source_step']['op'] == 'FW_layernorm'
        assert row['source_step']['inputs'][0]['endpoint']['ref'] == tuple(old['sm_output_ref'])
        assert [list(s['inputs'][0]['endpoint']['ref']) for s in row['local_steps']] == old['pm_output_refs']
        assert row['sm_output_ref'][3] == 211003
        assert row['dimensions'] == dict(D=2,T=2,B=1,S=1,H=6)
        assert row['global_shape'] == [2,2,6] and row['local_shape'] == [1,1,6]
        fragment = text.split('theorem '+row['facts_theorem']+' ',1)[1].split('#print axioms')[0]
        for required in ('.shape = [2, 2, 6] ∧', '∀ y ∈', '.shape = [1, 1, 6]', 'chunkPrimDimN 0 2', 'allGatherPrimDimN 1 2 0'):
            assert required in fragment
    for row in result['reads']:
        assert row['operand_nonwrite_source_indices'] == args[-1][row['world']]['execution_to_source'][row['execution_index']:]
    decls = lambda s:set(re.findall(r'^(?:theorem|def|abbrev) (\w+)',s,re.M))
    assert ancestors and decls(text) and all(decls(text).isdisjoint(decls(old)) for old in ancestors)
    assert 'frontierLayernormRead_' in text and 'frontierLayernormUnitFacts_' in text
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :'): assert bad not in text
    with pytest.raises(TypeError): subject.render(*args, expected_closed)


@pytest.mark.parametrize('D,tp,S,reverse,swap,out', [(1,3,6,True,True,231003), (3,2,8,False,False,251003)])
def test_public_dynamic_slots_shapes_and_canonical_parameter_indices(D,tp,S,reverse,swap,out):
    args = prepared(D=D,tp=tp,seqlen=S,reverse=reverse,swap=swap,ln_tid=out,
                    parameter_tid=out+1000,names=('arbitrary.weight.id','arbitrary.bias.id'),
                    next_tid=out+2000,add_tid=out+3000,exchange_tid=out+4000,
                    output_tid=out+5000,weight_tid=out+6000)
    observed = []; original = adapter._render
    def consume(*a):
        result = original(*a); observed.append((a,result)); return result
    with patch.object(adapter,'_render',side_effect=consume): text,result = api().render(*args)
    closed = observed[-1][0][-1]
    assert len(observed) == 2 and (text,result) == observed[-1][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units')] == [1+D*tp,D,2*D,D]
    assert result['consumed_frontier_indices'] == list(range(1 if reverse else 0,2*D,2))
    assert [r['gather_axis'] for r in result['frontier_units']] == ([2,1] if reverse else [1,2])*D
    parameters = [l for l in args[2] if l.role == Role.PARAMETER]
    assert [r['lineage'] for r in args[4]['relations']] == [asdict(p) for p in parameters]
    specs = [(r,u) for r in args[4]['relations'] for u in r['units']]
    for i,(old,row) in enumerate(zip(closed['frontier_units'],result['frontier_units'],strict=True)):
        if old['gather_axis'] == 2:
            assert row is old and row in result['retained_units']
            continue
        assert old['source_output_slot'] == (1 if reverse else 0)
        assert old['source_step']['outputs'][old['source_output_slot']]['endpoint']['ref'] == tuple(old['sm_output_ref'])
        assert row['frontier_index'] == i and row['predecessor_facts'] == old['facts_theorem']
        assert row['source_output_slot'] == 0 and row['sm_output_ref'][3] == out
        assert row['dimensions'] == dict(D=D,T=tp,B=1,S=S//tp,H=3*tp)
        assert row['global_shape'] == [D,S,3*tp] and row['local_shape'] == [1,S//tp,3*tp]
        assert [p['sm_ref'][3] for p in row['parameters']] == ([out+1001,out+1000] if swap else [out+1000,out+1001])
        for p in row['parameters']:
            spec,unit = specs[p['spec_index']]
            assert spec['sm_binding']['ref'] == p['sm_ref'] and unit['unit'] == row['unit']
            assert [b['ref'] for b in unit['bindings']] == p['pm_refs']
    for read in result['reads']:
        order = args[-1][read['world']]['execution_to_source']
        assert order[read['execution_index']] == read['source_index']
    assert result['deferred_units'] == []


def private(args,closed):
    """Negative composition seam probes, never public receipt positives."""
    return adapter._render(*args,closed)


@pytest.mark.parametrize('fault',['missing-unit','duplicate-unit','slot','skip-shape','partial-order'])
def test_complete_current_frontier_private_guards(baseline,fault):
    args,closed = copy.deepcopy(baseline)
    if fault == 'missing-unit': closed['frontier_units'].pop(2)
    elif fault == 'duplicate-unit': closed['frontier_units'].append(copy.deepcopy(closed['frontier_units'][0]))
    elif fault == 'slot': closed['frontier_units'][0]['source_output_slot'] = 1
    elif fault == 'skip-shape': closed['frontier_units'][1]['local_shape'][0] = True
    else: args[-1]['pm']['execution_to_source'].pop()
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('role',[221001,221002])
@pytest.mark.parametrize('fault',['parent','ref','source-shape','rawtype','binding-order','spec-order','unit-order'])
def test_current_parameter_and_bound_order_private_guards(baseline,role,fault):
    args,closed = copy.deepcopy(baseline)
    row = next(r for r in args[4]['relations'] if r['sm_binding']['ref'][3] == role)
    if fault == 'parent': row['units'][0]['bindings'][0]['parent_tid'] += 1
    elif fault == 'ref': row['units'][0]['bindings'][0]['ref'][3] += 1
    elif fault == 'binding-order': row['units'][0]['bindings'].reverse()
    elif fault == 'spec-order': args[4]['relations'].reverse()
    elif fault == 'unit-order': row['units'].reverse()
    else:
        cell = next(c for c in args[3]._inputs[1] if c.node.cid == 211003 and c.rank == 0)
        ir = next(ir for ir in cell._input_irs if ir.tid == role)
        if fault == 'source-shape': ir.parent.shape = (7,)
        else: ir.shape = (6.0,)
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('fault',['gamma-parent','beta-parent','output-parent','writer-export','writer-call','eps'])
def test_public_revalidates_current_original_authority(baseline,fault):
    args,_ = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 211003 and c.rank == 0)
    if fault in ('gamma-parent','beta-parent'):
        cell._input_irs[1 if fault == 'gamma-parent' else 2].parent.tid += 999
    elif fault == 'output-parent': cell._output_irs[0].parent.tid += 999
    elif fault == 'eps': cell.kwargs['eps'] = 1e-4
    else:
        writer = next(w for w in args[1]._collective_source['writers'] if w['ref']['source_cid'] == 211003 and w['ref']['runtime_rank'] == 0)
        if fault == 'writer-export': writer['export_id'] = 'wrong'
        else: writer['ref']['call_instance'] = True
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('cid,port,slot',[(141003,'_input_irs',0),(171002,'_output_irs',1)])
def test_public_revalidates_ancestor_and_retained_skip(baseline,cid,port,slot):
    args,_ = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == cid and c.rank == 0)
    getattr(cell,port)[slot].parent.tid += 999
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('options',[dict(ln_omit_rank=0),dict(ln_copies=2),dict(mixed_fanout=True)])
def test_public_partial_or_fanout_rejects(options):
    with pytest.raises(ValueError): api().render(*prepared(**options))


def test_public_unknown_hidden_consumer_explicitly_deferred():
    args = prepared(skip_kind='FW_mul')
    text,result = api().render(*args)
    assert len(result['units']) == 2 and len(result['frontier_units']) == 4
    assert result['retained_units'] == [] and len(result['deferred_units']) == 2
    assert result['consumed_frontier_indices'] == [0,2]
    for deferred,old in zip(result['deferred_units'],result['frontier_units'][1::2],strict=True):
        assert deferred['reason'] == 'unsupported hidden-frontier forward consumer'
        assert deferred['observed_consumer_ops'] == [['FW_mul'],['FW_mul'],['FW_mul']]
        assert {k:deferred[k] for k in old} == old
        assert 'theorem '+old['facts_theorem']+' ' not in text


@pytest.mark.parametrize('mutation',['old-entry','drop-unit','drop-skip','copy-six','copy-closed','twice'])
def test_public_tracer_kills_composition_mutations(baseline,mutation):
    subject = api(); original = inspect.getsource(subject.render)
    call = 'return adapter._render(sm, pm, lineages, validation, bound, execution_order, closed)'
    if mutation == 'old-entry': source = original.replace(call,'return adapter.render(sm, pm, lineages, validation, bound, execution_order)')
    elif mutation == 'drop-unit': source = original.replace(call,"closed['frontier_units'] = closed['frontier_units'][:2]\n        "+call)
    elif mutation == 'drop-skip': source = original.replace(call,
        "text, result = adapter._render(sm, pm, lineages, validation, bound, execution_order, closed)\n        result['frontier_units'] = result['units']\n        return text, result")
    elif mutation == 'copy-six': source = original.replace('predecessor.render(sm, pm, lineages, validation, bound, execution_order)',
        'predecessor.render(*copy.deepcopy((sm, pm, lineages, validation, bound, execution_order)))')
    elif mutation == 'copy-closed': source = original.replace(call,call.replace(', closed)',', copy.deepcopy(closed))'))
    else: source = original.replace(call,'predecessor.render(sm, pm, lineages, validation, bound, execution_order)\n        '+call)
    assert source != original, 'mutation did not apply'
    namespace = dict(predecessor=predecessor,adapter=adapter,copy=copy)
    exec(compile(source,'<in-memory-next-ln-mutant>','exec'),namespace)
    with patch.object(subject,'render',namespace['render']):
        with pytest.raises((AssertionError,ValueError)): test_public_real_next_ln_tracer(baseline)
