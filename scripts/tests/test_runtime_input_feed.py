"""Real CPU observer/serialization; independent canonical authority, never validator mocks."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
import torch
from scripts import gpt_batch_runtime as runtime


def observed(root, units=2, tp=2):
    from scripts.tests.test_graph_to_lean_runtime_lineage import fixture
    from trainverify.runtime_source_authority import bind_adapters
    sm,pm,a=fixture(units,tp); s,record,r,ref=a[2:]
    world=units*tp
    (root/'run.json').write_text(json.dumps(dict(format='trainverify.input-handoff-run.v1',run_id='fresh-test',world=world)))
    torch.save({'inputs':{k:torch.tensor(v,dtype=torch.int64) for k,v in record['global_inputs'].items()}},root/'reference.pt')
    for rank in range(world):
        source=s['rank_sources'][str(rank)]
        source='import torch\nimport nnscaler\n'+source.replace('class GenModel:', 'class GenModel(torch.nn.Module):')
        source=source.replace('def __init__(self): pass','def __init__(self): super().__init__()')
        source=source.replace('def segment9(self, input_ids_10, position_ids_11): pass',
                              'def segment9(self, input_ids_10, position_ids_11): return input_ids_10')
        s['rank_sources'][str(rank)]=source
    import inspect, textwrap
    from nnscaler.runtime.executor import Executor, AsyncCommHandler
    runtime_sources={name:textwrap.dedent(inspect.getsource(fn)) for name,fn in
        [('fexecute',Executor.fexecute),('sync_tensors',Executor.sync_tensors),('wait',type(AsyncCommHandler()).wait)]}
    for row in s['adapter_source']:
        if 'generated_dataloader' in row: row['generated_dataloader']['runtime']=copy.deepcopy(runtime_sources)
    bind_adapters(s)
    for rank in range(world):
        path=root/f'model{rank}.py';path.write_text(s['rank_sources'][str(rank)])
        spec=importlib.util.spec_from_file_location(f'_input_feed_fixture_{rank}',path)
        module=importlib.util.module_from_spec(spec)
        import sys
        sys.modules[spec.name]=module;spec.loader.exec_module(module)
        model=module.GenModel()
        group,=[g for g in record['groups'] if rank in g['ranks']]
        values=tuple(torch.tensor(group['inputs'][k],dtype=torch.int64) for k in runtime.INPUT_NAMES)
        ob=runtime.InputHandoffObserver(model,module,s,record,rank,'fresh-test')
        with ob: ob.run([values])
        (root/f'rank{rank}.json').write_text(json.dumps(dict(rank=rank,inner_exit=0,handoff=ob.events)))
        torch.save(dict(rank=rank,handoff=ob.events,handoff_tensors=ob.payload),root/f'rank{rank}.pt')
    from nnscaler.runtime.executor import Executor
    Executor._detach.clear()
    return s,record,r,ref


class FeedTests(unittest.TestCase):
    def test_actual_observer_serialized_payload(self):
        self.assertIsNotNone(importlib.util.find_spec('Verdict.runtime_input_feed'), 'real input feed compiler missing')
        from Verdict.runtime_input_feed import load_handoff
        with tempfile.TemporaryDirectory() as d:
            root=Path(d); args=observed(root)
            sm, pm, run = load_handoff(root,*args)
            self.assertEqual(run,'fresh-test')
            self.assertEqual(set(pm),set(range(4)))
            self.assertTrue(torch.equal(sm['input_ids'],torch.tensor(args[1]['global_inputs']['input_ids'])))
            self.assertEqual(pm[0][0].tolist(),args[1]['groups'][0]['inputs']['input_ids'])

    def test_full_world_slots_and_legacy_bytes(self):
        from Verdict import graph_to_lean as c
        from Verdict.runtime_world import render, publish
        from Verdict.runtime_input_feed import bind
        from scripts.tests.test_graph_to_lean_runtime_lineage import fixture
        sm,pm,a=fixture()
        sv,pv=c._lower_runtime_graphs(sm,pm)
        legacy=render(sv,pv,a[0],a[1])
        with tempfile.TemporaryDirectory() as d:
            root=Path(d); source=observed(root)
            s,b,r,ref=source
            result=bind(legacy,sv,pv,a[0],a[1],s,b,r,ref,root)
            self.assertTrue(result.lean.startswith(legacy.lean))
            self.assertEqual(legacy,render(sv,pv,a[0],a[1]))
            self.assertEqual(result.lean.count(' : GraphDecl :='),2)
            for label,view in [('sm',sv),('pm',pv)]:
                schedule=result.lean.split(f'def {label}InputRequests : List InputRequest := [',1)[1].split(']',1)[0]
                import re
                self.assertEqual([int(x) for x in re.findall(label+r'Node_(\d+),',schedule)],list(range(len(view.nodes()))))
                self.assertEqual(schedule.count('some'),sum(str(view.node_opname(n)).endswith('DATALOADER') for n in view.nodes()))
            public=root/'Public.lean';public.write_bytes(b'preserve')
            out=root/'generated'/'World.lean';publish(result,out)
            with self.assertRaises(ValueError): publish(result,out)
            self.assertEqual(public.read_bytes(),b'preserve')
            self.assertEqual(out.read_text(),result.lean)

    def test_feed_rejects_detached_world_or_changed_view(self):
        from dataclasses import replace
        from Verdict import graph_to_lean as c
        from Verdict.runtime_world import render
        from Verdict.runtime_input_feed import bind
        from scripts.tests.test_graph_to_lean_runtime_lineage import fixture
        with tempfile.TemporaryDirectory() as d:
            root=Path(d); source=observed(root)
            for fault in ('world-order','world-receipt','view-order','view-omit'):
                with self.subTest(fault=fault):
                    sm,pm,a=fixture();sv,pv=c._lower_runtime_graphs(sm,pm)
                    world=render(sv,pv,a[0],a[1])
                    bind(world,sv,pv,a[0],a[1],*source,root)
                    if fault=='world-order':
                        changed=world.lean.replace('nodes := [smNode_0, smNode_1]', 'nodes := [smNode_1, smNode_0]')
                        self.assertNotEqual(changed,world.lean);world=replace(world,lean=changed)
                    elif fault=='world-receipt': world=replace(world,receipt=dict(world.receipt,sm_nodes=999))
                    elif fault=='view-order': pv.nodes().reverse()
                    else: pv.nodes().pop(0)
                    with self.assertRaises(ValueError): bind(world,sv,pv,a[0],a[1],*source,root)

    def test_raw_loader_writer_must_match_observed_source(self):
        from Verdict import graph_to_lean as c
        from Verdict.runtime_world import render
        from Verdict.runtime_input_feed import bind
        from scripts.tests.test_graph_to_lean_runtime_lineage import fixture
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);source=observed(root)
            sm,pm,a=fixture();sv,pv=c._lower_runtime_graphs(sm,pm)
            bind(render(sv,pv,a[0],a[1]),sv,pv,a[0],a[1],*source,root)
            pm.cells[0].node=pm.cells[0].node._replace(cid=105)
            a[1][0].node=a[1][0].node._replace(cid=105)
            sv,pv=c._lower_runtime_graphs(sm,pm)
            with self.assertRaises(ValueError):
                bind(render(sv,pv,a[0],a[1]),sv,pv,a[0],a[1],*source,root)

    def test_heldout_three_units_three_tp_real_entry(self):
        from types import SimpleNamespace
        from unittest.mock import patch
        from Verdict import graph_to_lean as c
        from scripts.tests.test_graph_to_lean_runtime_lineage import fixture
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);source=observed(root,3,3);sm,pm,a=fixture(3,3)
            verifier=SimpleNamespace(get_graph=lambda:(sm,pm),get_graph_compact=lambda:(sm,pm))
            with patch('sys.argv',['graph_to_lean','--out',str(root/'public'/'Never.lean'),'--module','Never',
                '--runtime-batch-authority','fixture','--runtime-input-handoff',str(root),
                '--runtime-world-definitions-out',str(root/'world'/'World.lean')]):args=c.parse_args()
            authority=(a[0],a[1],*source)
            with patch.object(c,'load_verifier',return_value=verifier),patch.object(c,'_load_runtime_lineage_inputs',return_value=authority):
                with self.assertRaises(ValueError) as caught:c._generate(args)
            result=caught.exception.receipt['world_definitions']['input_feed']
            self.assertEqual(result['slots'],{'sm':2,'pm':18})
            self.assertEqual(len(result['loaders']),10)
            self.assertEqual(sum(len(l['ports']) for l in result['loaders']),20)
            self.assertIn('denoteWithInputs',(root/'world'/'World.lean').read_text())
            self.assertFalse((root/'public').exists())

    def test_explicit_entry_flag_and_renderer_exist(self):
        from unittest.mock import patch
        from Verdict import graph_to_lean as c
        with patch('sys.argv', ['graph_to_lean','--out','never.lean','--module','Never','--runtime-input-handoff','fresh']):
            args = c.parse_args()
        self.assertEqual(args.runtime_input_handoff,'fresh')
        from Verdict.runtime_input_feed import bind
        self.assertTrue(callable(bind))

    def test_adversarial_serialized_authority(self):
        from Verdict.runtime_input_feed import load_handoff
        with tempfile.TemporaryDirectory() as d:
            root=Path(d); args=observed(root)
            original={p.name:p.read_bytes() for p in root.iterdir()}
            faults=['run','rank','ref','mb','version','port','order','count','shape','dtype','value','jsonpt','coherent','exit','extra','global']
            for fault in faults:
                with self.subTest(fault=fault):
                    for p in root.iterdir(): p.unlink()
                    for name,data in original.items(): (root/name).write_bytes(data)
                    row=json.loads((root/'rank0.json').read_text())
                    actual=torch.load(root/'rank0.pt',weights_only=True)
                    e=actual['handoff'][1]
                    actual['handoff_tensors']['post'][0]=list(actual['handoff_tensors']['post'][0])
                    if fault=='run': e['run_id']='old'
                    elif fault=='rank': e['rank']=1
                    elif fault=='ref': e['refs'][0]['source_tid']=999
                    elif fault=='mb': e['refs'][0]['microbatch']=1
                    elif fault=='version': e['refs'][0]['version']=2
                    elif fault=='port': e['parameter_indices'].reverse()
                    elif fault=='order': actual['handoff'].reverse()
                    elif fault=='count': actual['handoff_tensors']['post']=[]
                    elif fault=='shape': actual['handoff_tensors']['post'][0][0]=torch.zeros((2,1),dtype=torch.int64)
                    elif fault=='dtype': actual['handoff_tensors']['post'][0][0]=actual['handoff_tensors']['post'][0][0].float()
                    elif fault in ('value','coherent'): actual['handoff_tensors']['post'][0][0][0,0]=9
                    elif fault=='jsonpt': row['handoff'][1]['values'][0][0][0]=9
                    elif fault=='exit': row['inner_exit']=1
                    elif fault=='extra': (root/'rank4.json').write_text('{}')
                    elif fault=='global':
                        ref=torch.load(root/'reference.pt',weights_only=True); ref['inputs']['input_ids'][0,0]=9; torch.save(ref,root/'reference.pt')
                    if fault=='coherent': e['values']=[t.tolist() for t in actual['handoff_tensors']['post'][0]]
                    if fault!='jsonpt': row['handoff']=copy.deepcopy(actual['handoff'])
                    (root/'rank0.json').write_text(json.dumps(row)); torch.save(actual,root/'rank0.pt')
                    with self.assertRaises(ValueError): load_handoff(root,*args)

if __name__ == '__main__': unittest.main()
