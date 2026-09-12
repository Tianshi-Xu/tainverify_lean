"""Real next-LN -> all multiref slots; local B=1 and inherited H=3*TP.

Dynamic D/TP/sequence/arity/identities, not independent B/H or kernel/Torch.
Downstream source-backed adds/AllGather mark boundaries; no projection is consumed.
"""
import copy
import importlib
import importlib.util
import inspect
import re
import sys
from contextlib import ExitStack
from types import SimpleNamespace as NS
from unittest.mock import patch

import pytest
from scripts.tests import test_runtime_frontier_next_layernorm_values as previous
from scripts.tests.test_graph_to_lean_runtime_lineage import IR, N, T
from scripts.tests.test_graph_to_lean_collective_scope import tref
from Verdict import runtime_frontier_next_layernorm_values as predecessor


def api():
    assert importlib.util.find_spec('Verdict.runtime_frontier_sequence_alias_values'), 'sequence alias renderer missing'
    return importlib.import_module('Verdict.runtime_frontier_sequence_alias_values')


def fixture(arity=3, alias_tid=271003, alias_reverse=False, omit_alias=None,
            mixed=False, copies=1, successor='FW_add', metadata='local-only', **kwargs):
    from trainverify.runtime_source_authority import build_snapshot, bind_reducers, bind_adapters, writer_export_id
    sm, pm, authority = previous.fixture(**kwargs)
    old = copy.deepcopy(authority[2]); rows = []
    ln_tid = kwargs.get('ln_tid', 211003)
    for world, graph in [('s', sm), ('p', pm)]:
        for producer in [c for c in graph.cells if c.node.cid == ln_tid]:
            rank = producer.rank
            tp = kwargs.get('tp',2); ranks = list(range(rank//tp*tp,(rank//tp+1)*tp))
            if world == 'p' and rank == omit_alias: continue
            x = producer._output_irs[0]
            def append(cid, kind, refs, irs, outs, kw):
                display = 'AllGatherReduceScatterPrim' if kind == 'AllGatherPrim' else kind
                cell = NS(node=N(world,rank,0,cid,display),rank=rank,opname=kind,inputs=list(refs),
                    outputs=[T(world,rank,0,ir.tid,1) for ir in outs],kwargs=kw,
                    _input_irs=copy.deepcopy(irs),_output_irs=outs)
                cell.ir = NS(signature=kind,inputs=lambda c=cell:c._input_irs,outputs=lambda c=cell:c._output_irs)
                at = next((i for i,c in enumerate(graph.cells) if c.rank == rank and c.opname.startswith('BW_')),len(graph.cells))
                graph.cells.insert(at,cell)
                graph.shapes.update({r:ir.shape for r,ir in zip(cell.outputs,outs,strict=True)})
                if world == 'p':
                    rows.append(dict(ref=dict(world=world,runtime_rank=rank,microbatch=0,source_cid=cid,
                        call_instance=0,op=kind,origin='fixture'),source_irname=display,
                        inputs=[tref(r) for r in refs],outputs=[tref(r) for r in cell.outputs],parameter_grad_tids=[]))
                return cell
            for k in range(copies):
                outs = [IR(alias_tid+k*100+j,x.parent.name,x.parent.shape,x.indmap) for j in range(arity)]
                for ir in outs: ir.parent.tid = ir.tid+1000
                if alias_reverse: outs.reverse()
                a = append(alias_tid-1+k*100,'FW_multiref',producer.outputs,[x],outs,dict(times=arity,__consts=[]))
                for j,out in enumerate(outs):
                    kind = 'FW_add' if successor == 'AllGatherPrim' and world == 's' else successor
                    if kind == 'AllGatherPrim':
                        y = IR(alias_tid+2000+k*100+j,out.parent.name,out.parent.shape,
                            (out.indmap[0],(0,out.parent.shape[1]),out.indmap[2]))
                        y.parent.tid = out.parent.tid
                        append(y.tid,kind,[a.outputs[j]._replace(rank=r) for r in ranks],
                            [out],[y],dict(ranks=ranks,dim=1))
                    else:
                        y = IR(alias_tid+2000+k*100+j,'downstream.boundary',out.parent.shape,out.indmap)
                        append(y.tid,kind,[a.outputs[j]]*2,[out]*2,[y],dict(alpha=1,__consts=[]) if kind == 'FW_add' else {})
                if world == 'p':
                    lhs = ', '.join(f'sequence_alias_{k}_{j}' for j in range(arity))
                    rhs = ', '.join('next_normalized_0' for _ in range(arity))
                    if arity == 1: lhs += ','; rhs += ','
                    code = f'\n        {lhs} = {rhs}'
                    for j in range(arity):
                        if successor == 'AllGatherPrim':
                            code += f'\n        downstream_{k}_{j} = nnscaler.runtime.adapter.all_gather(sequence_alias_{k}_{j}, dim=1, ranks={ranks})'
                        else:
                            operator = '+' if successor == 'FW_add' else '*'
                            code += f'\n        downstream_{k}_{j} = sequence_alias_{k}_{j} {operator} sequence_alias_{k}_{j}'
                    old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',code+'\ndef _train_step')
            if mixed:
                y = IR(alias_tid+4000,'mixed.frontier',x.parent.shape,x.indmap)
                append(y.tid,'FW_add',producer.outputs*2,[x]*2,[y],dict(alpha=1,__consts=[]))
                if world == 'p':
                    old['rank_sources'][str(rank)] = old['rank_sources'][str(rank)].replace('\ndef _train_step',
                        '\n        mixed_sequence = next_normalized_0 + next_normalized_0\ndef _train_step')
    collective_adapters = {}
    for row in rows:
        if row['ref']['op'] != 'AllGatherPrim': continue
        cell = next(c for c in pm.cells if c.node.cid == row['ref']['source_cid'] and c.rank == row['ref']['runtime_rank'])
        row['adapter_kwargs'] = copy.deepcopy(cell.kwargs)
        adapter = copy.deepcopy(row)
        adapter['inputs'] = [tref(r) for r in cell.inputs if r.rank == cell.rank]
        k, j = divmod(cell.outputs[0].tid-alias_tid-2000,100)
        adapter['primitive'] = dict(kind=cell.node.irname,forward=True,kwargs=copy.deepcopy(cell.kwargs),
            signature='nnscaler.runtime.adapter.all_gather',generated_inputs=[f'sequence_alias_{k}_{j}'],
            generated_outputs=[f'downstream_{k}_{j}'])
        collective_adapters[writer_export_id(row['ref'])] = adapter
        if metadata == 'all-peers':
            cell._input_irs = [copy.deepcopy(next(ir for p in pm.cells for ref,ir in zip(p.outputs,p._output_irs,strict=True)
                if ref == r)) for r in cell.inputs]
    snapshot = build_snapshot([*old['writers'],*rows])
    snapshot.update({k:old[k] for k in ('source','runtime_ndevs','rank_sources')})
    adapters = {writer_export_id(w['ref']):w for w in [*old['adapter_source'],*copy.deepcopy(rows)]}
    adapters.update(collective_adapters)
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


def test_public_real_all_slots_tracer(baseline):
    args,expected = copy.deepcopy(baseline)
    subject = api(); ancestors = []; fresh_results = []; observed = []
    original = subject._render
    def record(fn):
        def wrapped(*a,**kw):
            result = fn(*a,**kw); ancestors.append(result[0])
            if fn.__module__ == predecessor.__name__: fresh_results.append(result[1])
            return result
        return wrapped
    def consume(*a):
        result = original(*a); observed.append((a,result)); return result
    with ExitStack() as stack:
        for name,module in list(sys.modules.items()):
            if name.startswith('Verdict.runtime_') and module is not subject and callable(getattr(module,'render',None)):
                stack.enter_context(patch.object(module,'render',side_effect=record(module.render)))
        stack.enter_context(patch.object(subject,'_render',side_effect=consume))
        fresh = predecessor.render
        text,result = subject.render(*args)
        assert fresh.call_count == 1
        assert all(a is b for a,b in zip(fresh.call_args.args,args,strict=True))
    assert len(observed) == len(fresh_results) == 1
    assert all(a is b for a,b in zip(observed[0][0][:-1],args,strict=True))
    assert observed[0][0][-1] is fresh_results[0] and fresh_results[0] == expected
    assert (text,result) == observed[0][1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units','deferred_units')] == [5,6,8,2,0]
    assert result['units'] == result['alias_units'] and result['consumed_frontier_indices'] == [0,2]
    assert result['frontier_units'][3::4] == expected['frontier_units'][1::2]
    assert result['retained_units'] == expected['retained_units']
    for row in result['units']:
        old = expected['frontier_units'][row['frontier_index']]; slot = row['slot']
        assert row['predecessor_facts'] == old['facts_theorem']
        assert row['source_output_slot'] == slot
        assert list(row['source_step']['outputs'][slot]['endpoint']['ref']) == row['sm_output_ref']
        assert [list(s['outputs'][slot]['endpoint']['ref']) for s in row['local_steps']] == row['pm_output_refs']
        assert row['dimensions'] == old['dimensions'] and row['global_shape'] == old['global_shape']
        assert row['local_shape'] == old['local_shape'] and row['gather_axis'] == 1
        assert row['sm_consumers'] and len(row['pm_consumers']) == 2
        fragment = text.split('theorem '+row['facts_theorem']+' ',1)[1].split('#print axioms')[0]
        for required in ('.shape = [2, 2, 6] ∧','∀ y ∈','.shape = [1, 1, 6]','chunkPrimDimN 0 2','allGatherPrimDimN 1 2 0',
                         'exact '+old['facts_theorem']): assert required in fragment
    for read in result['reads']:
        assert read['op'] == 'FW_multiref' and read['params'] == [3]
        assert len(read['source_step']['outputs']) == 3
        assert read['source_kwargs'] == dict(times=3,__consts=[])
        assert read['operand_nonwrite_source_indices'] == args[-1][read['world']]['execution_to_source'][read['execution_index']:]
    decls = lambda s:set(re.findall(r'^(?:theorem|def|abbrev) (\w+)',s,re.M))
    assert ancestors and decls(text) and all(decls(text).isdisjoint(decls(old)) for old in ancestors)
    assert text.count('SourceMultirefRead.multiref_value_of_split') == 5
    assert result['lean_bytes'] == len(text.encode())
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False
    for bad in ('sorry','admit','native_decide','axiom ','(hshape :','(houtput :'): assert bad not in text
    with pytest.raises(TypeError): subject.render(*args,expected)


@pytest.mark.parametrize('metadata,D,tp,S,arity,tid',[
    ('local-only',2,2,2,3,271003), ('all-peers',1,3,6,2,381003)])
def test_public_real_allgather_boundary(metadata,D,tp,S,arity,tid):
    """Real source snapshot/export/adapter/scope; no supplied closed receipt."""
    args = prepared(successor='AllGatherPrim',metadata=metadata,D=D,tp=tp,seqlen=S,arity=arity,alias_tid=tid)
    subject = api(); observed = []; original = subject._render
    def capture(*a):
        result = original(*a); observed.append((a,result)); return result
    with patch.object(subject,'_render',side_effect=capture), patch.object(predecessor,'render',wraps=predecessor.render) as fresh:
        text,result = subject.render(*args)
        assert fresh.call_count == 1
        assert all(a is b for a,b in zip(fresh.call_args.args,args,strict=True))
    assert len(observed) == 1 and (text,result) == observed[0][1]
    assert all(a is b for a,b in zip(observed[0][0][:-1],args,strict=True))
    closed = observed[0][0][-1]
    assert len(result['alias_units']) == D*arity
    assert len(result['frontier_units']) == D*(arity+1)
    assert result['retained_units'] == closed['retained_units']
    assert result['deferred_units'] == []
    gathers = {tuple(c.node):c for c in args[3]._inputs[1] if c.node.cid >= tid+2000 and c.opname == 'AllGatherPrim'}
    assert len(gathers) == D*tp*arity
    for row in result['units']:
        assert len(row['pm_consumers']) == tp
        assert row['predecessor_facts'] == closed['frontier_units'][row['frontier_index']]['facts_theorem']
        for ref in row['pm_consumers']:
            c = gathers[tuple(ref)]; scope = args[1].collective_scopes[c.node]
            assert c.node.irname == 'AllGatherReduceScatterPrim' and scope.op == 'AllGatherPrim'
            assert scope.source_writer and len(c.inputs) == tp
            assert len(c._input_irs) == (1 if metadata == 'local-only' else tp)
            assert [list(r) for r in c.inputs] == row['pm_output_refs']
    assert {r['op'] for r in result['reads']} == {'FW_multiref'}
    assert 'SourceAllGatherRead' not in text and 'SourceLinearRead' not in text
    for flag in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement'): assert result[flag] is False


@pytest.fixture(scope='module')
def gather_baseline():
    return prepared(successor='AllGatherPrim',D=1,tp=3,seqlen=6,arity=2)


def gather_seam(args):
    """Private discovery scope only: no predecessor/value or public proof claim."""
    subject = api(); index = subject._Index(args[1],args[3]._inputs[1])
    cell = next(c for c in index.raw.values() if c.opname == 'AllGatherPrim' and c.node.cid == 273003 and c.rank == 1)
    producer = index.raw[tuple(index.writers[tuple(cell.inputs[0])])]
    port = next(p for p in subject.alias._ports(index,producer,'outputs') if p.endpoint.ref == tuple(cell.inputs[0]))
    return subject,index,cell,port


def corrupt_gather(args,fault):
    from dataclasses import replace
    subject,index,cell,port = gather_seam(args)
    if fault.startswith('scope-'):
        scope = args[1].collective_scopes[cell.node]
        change = {'scope-writer':dict(source_writer='wrong'), 'scope-local':dict(local_index=0),
            'scope-local-bool':dict(local_index=True), 'scope-order':dict(input_tids=tuple(reversed(scope.input_tids))),
            'scope-group':dict(ranks=scope.ranks[:-1]), 'scope-axis':dict(params=(2,)),
            'scope-shape':dict(input_shape=(1,99,9)), 'scope-output':dict(output_tid=True)}[fault]
        args[1].collective_scopes[cell.node] = replace(scope,**change)
    elif fault in ('input-absent','output-absent','input-empty','output-empty','partial','extra-output'):
        field = '_output_irs' if fault.startswith('output') or fault == 'extra-output' else '_input_irs'
        setattr(cell,field,None if fault.endswith('absent') else [] if fault.endswith('empty')
            else copy.deepcopy(getattr(cell,field))*2)
    elif fault in ('input-bool','output-bool'):
        ir = getattr(cell,'_input_irs' if fault.startswith('input') else '_output_irs')[0]
        ir.shape = (True,*ir.shape[1:])
    elif fault == 'input-parent': cell._input_irs[0].parent.tid += 1
    elif fault == 'output-parent': cell._output_irs[0].parent.tid += 1
    elif fault == 'wrong-local':
        other = next(c for c in index.raw.values() if c.node.cid == cell.node.cid and c.rank == 0)
        cell._input_irs = copy.deepcopy(other._input_irs)
    elif fault.startswith('peer-'):
        peer = index.raw[tuple(index.writers[tuple(cell.inputs[-1])])]
        ir = peer._output_irs[0]
        if fault == 'peer-parent': ir.parent.tid += 1
        elif fault == 'peer-bool': ir.indmap = ((False,1),*ir.indmap[1:])
        elif fault == 'peer-missing': peer._output_irs = None
        elif fault == 'peer-writer':
            writer = next(w for w in args[1]._collective_source['writers'] if w['ref']['source_cid'] == peer.node.cid and w['ref']['runtime_rank'] == peer.rank)
            writer['export_id'] = 'wrong'
    elif fault == 'raw-order': cell.inputs.reverse()
    elif fault == 'raw-target': cell.inputs[0] = cell.outputs[0]
    elif fault == 'rankgroup': cell.kwargs['ranks'].pop()
    elif fault == 'writer-export':
        writer = next(w for w in args[1]._collective_source['writers'] if w['ref']['source_cid'] == cell.node.cid and w['ref']['runtime_rank'] == cell.rank)
        writer['export_id'] = 'wrong'
    else: raise AssertionError(fault)
    return subject,index,cell,port


@pytest.mark.parametrize('fault',['input-absent','output-absent','input-empty','output-empty','partial','extra-output',
    'input-bool','output-bool','input-parent','output-parent','wrong-local','peer-parent','peer-bool','peer-missing',
    'peer-writer','scope-writer','scope-local','scope-local-bool','scope-order','scope-group','scope-axis','scope-shape',
    'scope-output','raw-order','raw-target','rankgroup','writer-export'])
def test_private_discovery_strict_allgather_guards(gather_baseline,fault):
    """Test the new discovery boundary, independently of ancestor rejection."""
    subject,index,cell,port = corrupt_gather(copy.deepcopy(gather_baseline),fault)
    with pytest.raises(ValueError): subject._consumers(index,[port])


@pytest.mark.parametrize('fault',['input-absent','output-bool','scope-local','adapter-call'])
def test_public_allgather_live_authority_revalidation(gather_baseline,fault):
    args = copy.deepcopy(gather_baseline)
    if fault == 'adapter-call':
        snapshot = args[3]._inputs[2]
        snapshot['rank_sources']['1'] = snapshot['rank_sources']['1'].replace(
            'all_gather(sequence_alias_0_0, dim=1','all_gather(sequence_alias_0_0, dim=2')
    else: corrupt_gather(args,fault)
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('fault,guard',[
    ('output-bool','alias._raw(outs[0])'),
    ('output-parent','if not _same_typed(outs[0].parent.tid, originals[j].parent.tid):'),
    ('peer-parent','if any(not _same_typed(ir.parent.tid, originals[0].parent.tid) for ir in originals):'),
    ('scope-writer',"scope.source_writer != writer['export_id']")])
def test_private_independent_allgather_guard_mutants(gather_baseline,fault,guard):
    """Narrow helper seam: original must reject, single-guard mutant must ACCEPT.

    This is not public completion; later consumer/ancestor guards cannot count
    as killing these isolated guards. No helpers or adapter checks are mocked.
    """
    subject,index,cell,_ = corrupt_gather(copy.deepcopy(gather_baseline),fault)
    refs = [tuple(r) for r in cell.inputs]
    subject.alias.residual._identity(index,cell)
    message = {'output-bool':'typed original rank-three','output-parent':'output parent identity',
        'peer-parent':'peer parent identity','scope-writer':'scope writer/output'}[fault]
    with pytest.raises(ValueError,match=message): subject._gather_consumer(index,cell,refs)
    source = inspect.getsource(subject._gather_consumer)
    replacement = 'pass' if fault == 'output-bool' else 'if False:' if guard.startswith('if ') else 'False'
    assert source.count(guard) == 1
    namespace = dict(subject.__dict__)
    exec(compile(source.replace(guard,replacement),'<sequence-allgather-guard-mutant>','exec'),namespace)
    assert namespace['_gather_consumer'](index,cell,refs) is None


def private(args,closed):
    """Only negative private receipt probes; positive authority is always fresh."""
    return api()._render(*args,closed)


@pytest.mark.parametrize('fault',['missing-unit','duplicate-unit','D','T','B','S','H','global-shape',
    'local-shape','slot','tid','local-tids','ranks','positions','local-order','partial-order','skip-shape','skip-slot'])
def test_complete_typed_predecessor_guards(baseline,fault):
    args,closed = copy.deepcopy(baseline); row = closed['frontier_units'][0]
    if fault == 'missing-unit': closed['frontier_units'].pop(2)
    elif fault == 'duplicate-unit': closed['frontier_units'].append(copy.deepcopy(row))
    elif fault in ('D','T','B','S','H'): row['dimensions'][fault] = True
    elif fault == 'global-shape': row['global_shape'][0] = float(row['global_shape'][0])
    elif fault == 'local-shape': row['local_shape'][0] = True
    elif fault == 'slot': row['source_output_slot'] = True
    elif fault == 'tid': row['sm_output_tid'] += 1
    elif fault == 'local-tids': row['pm_output_tids'].reverse()
    elif fault == 'ranks': row['ranks'][0] = False
    elif fault == 'positions': row['positions'][0] = False
    elif fault == 'local-order': row['local_steps'].reverse()
    elif fault == 'partial-order': args[-1]['pm']['execution_to_source'].pop()
    elif fault == 'skip-shape': closed['frontier_units'][1]['local_shape'][0] = True
    else: closed['frontier_units'][1]['source_output_slot'] = 0
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('D,tp,S,arity,reverse,out',[(1,3,6,1,True,331003),(3,2,8,4,False,351003)])
def test_public_dynamic_all_original_slots(D,tp,S,arity,reverse,out):
    args = prepared(D=D,tp=tp,seqlen=S,arity=arity,reverse=reverse,alias_reverse=True,
        alias_tid=out,ln_tid=out+5000,parameter_tid=out+6000,names=('odd.scale','odd.shift'),
        next_tid=out+7000,add_tid=out+8000,exchange_tid=out+9000,output_tid=out+10000,weight_tid=out+11000)
    subject = api(); observed = []; original = subject._render
    def capture(*a):
        result = original(*a); observed.append((a,result)); return result
    with patch.object(subject,'_render',side_effect=capture): text,result = subject.render(*args)
    assert len(observed) == 1
    closed = observed[0][0][-1]
    assert [len(result[k]) for k in ('reads','units','frontier_units','retained_units')] == [1+D*tp,D*arity,D*(arity+1),D]
    assert result['consumed_frontier_indices'] == list(range(1 if reverse else 0,2*D,2))
    cursor = 0
    for i,old in enumerate(closed['frontier_units']):
        if old['gather_axis'] == 2:
            assert result['frontier_units'][cursor] is old
            assert old in result['retained_units']; cursor += 1
            continue
        for slot in range(arity):
            row = result['frontier_units'][cursor]; cursor += 1
            assert row['slot'] == row['source_output_slot'] == slot and row['frontier_index'] == i
            assert row['source_step']['outputs'][slot]['parent_name'] == 'next.normalized'
            assert row['sm_output_ref'][3] == out+arity-1-slot
            assert row['dimensions'] == dict(D=D,T=tp,B=1,S=S//tp,H=3*tp)
            assert row['global_shape'] == [D,S,3*tp] and row['local_shape'] == [1,S//tp,3*tp]
            assert row['predecessor_facts'] == old['facts_theorem']
            assert len(row['source_step']['outputs']) == arity
            assert all(len(s['outputs']) == arity for s in row['local_steps'])
    assert cursor == len(result['frontier_units'])


@pytest.mark.parametrize('fault',['input-parent','output-parent','raw-shape','raw-parent','raw-bound','raw-value',
    'times','kwargs','metadata-inventory','alias-inventory','alias-order','output-fullref','input-fullref',
    'writer-export','writer-call','writer-ports','successor-edge'])
def test_original_alias_authority_guards(baseline,fault):
    args,closed = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == 271002 and c.rank == 0)
    if fault == 'input-parent': cell._input_irs[0].parent.tid += 1
    elif fault == 'output-parent': cell._output_irs[-1].parent.tid += 1
    elif fault == 'raw-shape': cell._output_irs[-1].shape = (1.0,*cell._output_irs[-1].shape[1:])
    elif fault == 'raw-parent': cell._output_irs[-1].parent.shape = (2.0,*cell._output_irs[-1].parent.shape[1:])
    elif fault == 'raw-bound': cell._output_irs[-1].indmap = ((False,1),*cell._output_irs[-1].indmap[1:])
    elif fault == 'raw-value': cell._output_irs[-1].valmap = (False,1)
    elif fault == 'times': cell.kwargs['times'] = 3.0
    elif fault == 'kwargs': cell.kwargs['axis'] = 1
    elif fault == 'metadata-inventory': cell._output_irs.pop()
    elif fault == 'alias-inventory': cell.outputs.pop(); cell._output_irs.pop(); cell.kwargs['times'] = 2
    elif fault == 'alias-order': cell.outputs.reverse(); cell._output_irs.reverse()
    elif fault == 'output-fullref': cell.outputs[-1] = cell.outputs[0]
    elif fault == 'input-fullref': cell.inputs[0] = cell.outputs[0]
    elif fault == 'successor-edge':
        c = next(c for c in args[3]._inputs[1] if c.node.cid == 273005 and c.rank == 0)
        c._input_irs[0].parent.tid += 1
    else:
        writer = next(w for w in args[1]._collective_source['writers'] if w['ref']['source_cid'] == 271002 and w['ref']['runtime_rank'] == 0)
        if fault == 'writer-export': writer['export_id'] = 'wrong'
        elif fault == 'writer-ports': writer['outputs'].reverse()
        else: writer['ref']['call_instance'] = True
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('options',[dict(omit_alias=0),dict(copies=2),dict(mixed=True)])
def test_public_partial_and_mixed_fanout_reject(options):
    with pytest.raises(ValueError): api().render(*prepared(**options))


def test_public_unknown_and_terminal_predecessors_are_explicitly_deferred():
    args = prepared(copies=0,skip_kind='FW_mul')
    observed = []; subject = api(); original = subject._render
    def capture(*a):
        result = original(*a); observed.append(a[-1]); return result
    with patch.object(subject,'_render',side_effect=capture): text,result = subject.render(*args)
    assert result['reads'] == result['units'] == result['retained_units'] == result['consumed_frontier_indices'] == []
    assert len(result['frontier_units']) == len(result['deferred_units']) == 4
    for old,new,deferred in zip(observed[0]['frontier_units'],result['frontier_units'],result['deferred_units'],strict=True):
        assert new is old and {k:deferred[k] for k in old} == old
        assert deferred['observed_consumer_ops'] == ([[],[],[]] if old['gather_axis'] == 1 else [['FW_mul']]*3)
        assert 'theorem '+old['facts_theorem']+' ' not in text


@pytest.mark.parametrize('world',[0,1])
def test_complete_bw_nonwrite_guard(baseline,world):
    args,closed = copy.deepcopy(baseline); view = args[world]
    node = next(n for n in view.nodes() if n.cid == 271002)
    backward = next(n for n in reversed(view.nodes()) if view.node_opname(n).startswith('BW_'))
    view._node2outputs[backward] = [view.node_inputs(node)[0]]
    with pytest.raises(ValueError): private(args,closed)


@pytest.mark.parametrize('cid,slot',[(211003,0),(171002,1)])
def test_public_revalidates_ln_and_hidden_skip(baseline,cid,slot):
    args,_ = copy.deepcopy(baseline)
    cell = next(c for c in args[3]._inputs[1] if c.node.cid == cid and c.rank == 0)
    cell._output_irs[slot].parent.tid += 999
    with pytest.raises(ValueError): api().render(*args)


@pytest.mark.parametrize('mutation',['old-entry','drop-unit','drop-skip','copy-six','copy-closed','twice'])
def test_public_tracer_kills_composition_mutants(baseline,mutation):
    subject = api(); original = inspect.getsource(subject.render)
    call = 'return _render(sm, pm, lineages, validation, bound, execution_order, closed)'
    if mutation == 'old-entry': source = original.replace(call,'return predecessor.render(sm, pm, lineages, validation, bound, execution_order)')
    elif mutation == 'drop-unit': source = original.replace(call,"closed['frontier_units'] = closed['frontier_units'][:2]\n        "+call)
    elif mutation == 'drop-skip': source = original.replace(call,
        "text, result = _render(sm, pm, lineages, validation, bound, execution_order, closed)\n        result['frontier_units'] = result['units']\n        return text, result")
    elif mutation == 'copy-six': source = original.replace('predecessor.render(sm, pm, lineages, validation, bound, execution_order)',
        'predecessor.render(*copy.deepcopy((sm, pm, lineages, validation, bound, execution_order)))')
    elif mutation == 'copy-closed': source = original.replace(call,call.replace(', closed)',', copy.deepcopy(closed))'))
    else: source = original.replace(call,'predecessor.render(sm, pm, lineages, validation, bound, execution_order)\n        '+call)
    assert source != original
    namespace = dict(predecessor=predecessor,copy=copy)
    # Resolve the live private seam so the tracer observes mutant composition too.
    namespace['_render'] = lambda *a: subject._render(*a)
    exec(compile(source,'<sequence-alias-composition-mutant>','exec'),namespace)
    with patch.object(subject,'render',namespace['render']):
        with pytest.raises((AssertionError,ValueError)): test_public_real_all_slots_tracer(baseline)
