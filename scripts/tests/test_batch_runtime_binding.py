"""Portable contracts: real observation, exact domains; no generated GPU mocks."""
import copy
import importlib
import importlib.util
import unittest
import torch
from scripts.tests.test_batch_source_authority import fixture
from trainverify.batch_source_authority import build_batch_record


class RuntimeBindingTests(unittest.TestCase):
    def test_next_observes_yield_not_constructor_claim(self):
        self.assertIsNotNone(importlib.util.find_spec('scripts.gpt_batch_runtime'))
        api = importlib.import_module('scripts.gpt_batch_runtime')
        s, r, ref, c, units, glob = fixture()
        record = build_batch_record(c, units, glob, s)
        payload = tuple(torch.tensor(units[0][k]) for k in api.INPUT_NAMES)
        observed = api.ObservedIterator(iter([payload]), record, 0)
        self.assertEqual(observed.observations, [])
        self.assertIs(next(observed), payload)
        api.validate_observations(observed.observations, record, 0)
        payload[0].fill_(9)
        self.assertEqual(observed.observations[0]['inputs']['input_ids'], [[3,4]])
        with self.assertRaises(StopIteration):
            next(observed)

    def test_closed_domains_and_observed_swaps(self):
        from scripts import gpt_batch_runtime as api
        s, r, ref, c, units, glob = fixture()
        record = build_batch_record(c, units, glob, s)
        good = api.expected_observation(record, 0)
        for key, value in [('rank', 1), ('unit', 1), ('positions', [1]),
                           ('refs', list(reversed(good['refs']))),
                           ('tuple_names', list(reversed(api.INPUT_NAMES))),
                           ('dtypes', ['torch.float32']*2)]:
            bad = copy.deepcopy(good)
            bad[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                api.validate_observations([bad], record, 0)
        for rows in ([], [good,good]):
            with self.assertRaises(ValueError):
                api.validate_observations(rows, record, 0)
        for rank in (-1, 4, True):
            with self.assertRaises(ValueError):
                api.expected_observation(record, rank)
        values = tuple(torch.tensor(units[0][k]) for k in api.INPUT_NAMES)
        for payload in (values[::-1], values[:1], values + values[:1]):
            with self.assertRaises(ValueError):
                next(api.ObservedIterator(iter([payload]), record, 0))
        self.assertTrue(hasattr(api, 'validate_rank_domain'), 'aggregate rank domain missing')
        api.validate_rank_domain([{'rank':i} for i in range(4)], 4)
        for ranks in ([0,1,2], [0,1,2,2], [0,1,2,3,4], [False,1,2,3]):
            with self.assertRaises(ValueError):
                api.validate_rank_domain([{'rank':i} for i in ranks], 4)

    def test_global_gradient_comparison_not_unit_sum_or_count_only(self):
        from scripts import gpt_batch_runtime as api
        self.assertTrue(hasattr(api, 'check_shards'), 'independent shard validator missing')
        state = {'weight':torch.tensor([[2.,4.]])}
        grads = {'weight':torch.tensor([[3.,8.]])}
        meta = {'local':dict(orig_name='weight', shape=[1,2],
                slicers=[[0,1,None],[0,2,None]], val_chunks=1)}
        actual = dict(initialized={'local':state['weight'].clone()},
                      grads={'local':grads['weight'].clone()}, metadata=meta)
        api.check_shards(actual, meta, state, grads)
        for field in ('initialized','grads'):
            bad = copy.deepcopy(actual)
            bad[field]['other'] = bad[field].pop('local')
            with self.assertRaises(ValueError):
                api.check_shards(bad, meta, state, grads)
        actual['grads']['local'] /= 2
        with self.assertRaises(AssertionError):
            api.check_shards(actual, meta, state, grads)

    def test_full_source_not_only_schedule_is_bound(self):
        from scripts import gpt_batch_runtime as api
        self.assertTrue(hasattr(api, 'validate_generated_source'))
        api.validate_generated_source('x = 1', 'x=1 # comment')
        with self.assertRaises(ValueError):
            api.validate_generated_source('x=2', 'x=1')

    def test_nonfinite_gradients_rejected_even_if_reference_agrees(self):
        from scripts import gpt_batch_runtime as api
        meta = {'p':dict(orig_name='w',shape=[1],slicers=[[0,1,None]],val_chunks=1)}
        actual = dict(metadata=meta, initialized={'p':torch.ones(1)},
                      grads={'p':torch.tensor([float('inf')])})
        with self.assertRaises(ValueError):
            api.check_shards(actual, meta, {'w':torch.ones(1)}, {'w':torch.tensor([float('inf')])})

    def test_output_comparison_rejects_nonfinite_on_either_side(self):
        from scripts import gpt_batch_runtime as api
        self.assertTrue(hasattr(api, 'check_output'), 'finite output gate missing')
        good = torch.tensor(2.)
        api.check_output(good, good.clone())
        for value in (float('inf'), float('-inf'), float('nan')):
            bad = torch.tensor(value)
            for a, b in ((bad, bad), (bad, good), (good, bad)):
                with self.subTest(value=value), self.assertRaises(ValueError):
                    api.check_output(a, b)
        with self.assertRaises(AssertionError):
            api.check_output(good, torch.tensor(3.))

    def test_global_reference_output_must_be_finite(self):
        from scripts import gpt_batch_runtime as api
        self.assertTrue(hasattr(api, 'require_finite_output'), 'reference output gate missing')
        api.require_finite_output(torch.tensor(2.))
        for value in (float('inf'), float('-inf'), float('nan')):
            with self.subTest(value=value), self.assertRaises(ValueError):
                api.require_finite_output(torch.tensor(value))

    def test_multirow_positions_and_variable_replication_units(self):
        from scripts import gpt_batch_runtime as api
        for plan, units_count in ((1,3),(3,2),(2,1)):
            groups, ranks = [], []
            for u in range(units_count):
                group = dict(unit=u, ranks=list(range(u*plan,(u+1)*plan)),
                    positions=[u*2,u*2+1], inputs=dict(input_ids=[[u+4,7],[u+5,8]],
                                                     position_ids=[[0,1],[1,0]]))
                groups.append(group)
                ranks.extend(dict(rank=r, unit=u, microbatch=0, refs=[{'rank':r,'tid':t} for t in (91,97)])
                             for r in group['ranks'])
            record = dict(groups=groups, rank_inputs=ranks)
            for rank in range(plan*units_count):
                expected = api.expected_observation(record, rank)
                values = tuple(torch.tensor(expected['inputs'][k]) for k in api.INPUT_NAMES)
                observed = api.ObservedIterator(iter([values]), record, rank)
                next(observed)
                bad = copy.deepcopy(observed.observations)
                bad[0]['positions'].reverse()
                with self.assertRaises(ValueError):
                    api.validate_observations(bad, record, rank)


class GenModel:
    rank = 0
    world_size = 4

    def __init__(self):
        pass

    def segment(self, input_ids_10, position_ids_11):
        self.calls += 1
        self.received = (input_ids_10, position_ids_11)
        if self.hook is not None:
            self.hook()
        if self.fail:
            raise RuntimeError('original failure')
        return input_ids_10


def _train_step(model, dataloader):
    input_ids_10, position_ids_11 = next(dataloader)
    result = nnscaler.runtime.executor.fexecute('segment', model.segment, input_ids_10, position_ids_11, requires_grad=True)
    return result


class HandoffTests(unittest.TestCase):
    def setup_case(self):
        import inspect
        import sys
        import nnscaler.runtime.executor
        globals()['nnscaler'] = nnscaler
        from trainverify.runtime_source_authority import build_snapshot
        s, r, ref, c, units, glob = fixture()
        source = inspect.getsource(GenModel) + '\n' + inspect.getsource(_train_step)
        s['rank_sources'] = {str(i): source.replace('rank = 0', f'rank = {i}') for i in range(4)}
        for w in s['writers']:
            w['parameter_grad_tids'] = []
        s['adapter_source'] = []
        from nnscaler.runtime.executor import Executor, AsyncCommHandler
        import textwrap
        runtime = {k: textwrap.dedent(inspect.getsource(v)) for k,v in
                   [('fexecute',Executor.fexecute),('sync_tensors',Executor.sync_tensors),
                    ('wait',type(AsyncCommHandler()).wait)]}
        for w in s['writers']:
            rank = w['ref']['runtime_rank']
            row = copy.deepcopy(w)
            row['generated_dataloader'] = dict(writer=w['ref'], output_refs=w['outputs'],
                loader='dataloader', outputs=['input_ids_10','position_ids_11'], ordinal=1,
                runtime=runtime, training_calls=[dict(method='segment', source_cid=2,
                runtime_rank=rank,microbatch=0,call_instance=0,ordinal=1,
                arguments=['input_ids_10','position_ids_11'],
                parameters=['input_ids_10','position_ids_11'],input_refs=w['outputs'])])
            s['adapter_source'].append(row)
        from trainverify.runtime_source_authority import bind_reducers, bind_adapters
        bind_reducers(s)
        bind_adapters(s)
        record = build_batch_record(c, units, glob, s)
        model = GenModel()
        model.calls, model.fail, model.hook = 0, False, None
        module = sys.modules[__name__]
        values = tuple(torch.tensor(units[0][k]) for k in ('input_ids','position_ids'))
        return s, r, ref, record, model, module, values

    def test_mechanism_matrix_and_immutable_pre(self):
        from scripts import gpt_batch_runtime as api
        from trainverify.batch_source_authority import validate_input_handoff
        from nnscaler.runtime.executor import AsyncCommHandler, Executor
        class Work:
            def __init__(self, completed):
                self.completed, self.waits = completed, 0
            def is_completed(self):
                return self.completed
            def wait(self):
                self.waits += 1
                self.completed = True
        for mode in ('completed','pending','clone','inplace','detach','nograd'):
            with self.subTest(mode=mode):
                s,r,ref,record,model,module,values = self.setup_case()
                if mode in ('detach','nograd'):
                    values=tuple(v.float().requires_grad_() for v in values)
                ob=api.InputHandoffObserver(model,module,s,record,0,'fresh-test')
                work=Work(mode=='completed')
                if mode in ('completed','pending'):
                    AsyncCommHandler().submit(values[0],[work],lambda t: torch.full_like(t,9))
                elif mode=='clone':
                    AsyncCommHandler().submit(values[0],[],lambda t: t.clone())
                elif mode=='inplace':
                    AsyncCommHandler().submit(values[0],[],lambda t: t.fill_(9))
                if mode=='nograd':
                    # Observer-level executor branch probe only, not admitted GPT IDs.
                    original_executor=Executor.fexecute
                    from unittest.mock import patch
                    def no_grad(name, subgraph, *args, **kw):
                        return original_executor(name,subgraph,*args,requires_grad=False)
                    with ob, patch.object(nnscaler.runtime.executor,'fexecute',side_effect=no_grad):
                        ob.run([values])
                else:
                    with ob:
                        ob.run([values])
                self.assertEqual(ob.payload['pre'][0][0].tolist(),[[3,4]])
                self.assertEqual(model.calls,1)
                if mode in ('completed','pending'):
                    self.assertEqual(work.waits,1)
                if mode=='detach':
                    self.assertIsNot(model.received[0],values[0])
                    self.assertEqual(model.received[0].data_ptr(),values[0].data_ptr())
                if mode=='nograd':
                    self.assertIs(model.received[0],values[0])
                if mode=='clone':
                    self.assertNotEqual(model.received[0].data_ptr(),values[0].data_ptr())
                    validate_input_handoff(ob.events,ob.payload,record,s,r,ref,'fresh-test',0)
                else:
                    with self.assertRaises(ValueError):
                        validate_input_handoff(ob.events,ob.payload,record,s,r,ref,'fresh-test',0)
                Executor._detach.clear()
                AsyncCommHandler().check_clear()

    def test_metadata_payload_source_and_cardinality_mutations(self):
        from scripts import gpt_batch_runtime as api
        from trainverify.batch_source_authority import validate_input_handoff
        from nnscaler.runtime.executor import Executor
        s,r,ref,record,model,module,values = self.setup_case()
        ob=api.InputHandoffObserver(model,module,s,record,0,'fresh-test')
        with ob:
            ob.run([values])
        def validate(events, payload=None, snapshot=None, run='fresh-test'):
            return validate_input_handoff(events,payload or ob.payload,record,snapshot or s,r,ref,run,0)
        validate(ob.events)
        mutations=[('run_id','old'),('rank',1),('unit',1),('positions',[1]),
                   ('next_ordinal',2),('train_step',2),('event_ordinal',7),
                   ('parameter_indices',[1,0]),('writer_export_id','wrong')]
        for key,value in mutations:
            for stage in (0,1):
                bad=copy.deepcopy(ob.events); bad[stage][key]=value
                with self.subTest(key=key,stage=stage), self.assertRaises(ValueError):
                    validate(bad)
        for field in ('world','runtime_rank','microbatch','source_cid','call_instance','op','origin'):
            bad=copy.deepcopy(ob.events); bad[1]['writer'][field]='wrong'
            with self.subTest(writer=field), self.assertRaises(ValueError):
                validate(bad)
        for field in ('world','runtime_rank','microbatch','source_tid','version'):
            bad=copy.deepcopy(ob.events); bad[1]['refs'][0][field]='wrong'
            with self.subTest(ref=field), self.assertRaises(ValueError):
                validate(bad)
        for field in ('method','source_cid','runtime_rank','microbatch','call_instance','ordinal'):
            bad=copy.deepcopy(ob.events); bad[1]['consumer'][field]='wrong'
            with self.subTest(consumer=field), self.assertRaises(ValueError):
                validate(bad)
        for mutate in (lambda e:e[1]['refs'].reverse(), lambda e:e[1]['consumer']['input_refs'].reverse(),
                       lambda e:e[1]['samples'][0].update(local_position=1),
                       lambda e:e[1].update(values=[[[]],[]]),
                       lambda e:e[1].update(dtypes=['torch.float32']*2),
                       lambda e:e[1].update(shapes=[[2],[2]])):
            bad=copy.deepcopy(ob.events); mutate(bad)
            with self.assertRaises(ValueError): validate(bad)
        for events in ([],ob.events[:1],ob.events*2,ob.events[::-1]):
            with self.assertRaises(ValueError): validate(events)
        for payload in ({'pre':ob.payload['pre']}, {'pre':ob.payload['pre'],'post':[]},
                        {'pre':ob.payload['pre'],'post':ob.payload['post']*2}):
            with self.assertRaises(ValueError): validate(ob.events,payload)
        with self.assertRaises(ValueError): validate(ob.events,run='different-run')
        for field in ('generated_dataloader',):
            bad=copy.deepcopy(s); del bad['adapter_source'][0][field]
            with self.assertRaises(ValueError): validate(ob.events,snapshot=bad)
        bad=copy.deepcopy(s); bad['rank_sources']['0']=bad['rank_sources']['0'].replace("'segment'", "'wrong'")
        with self.assertRaises(ValueError): validate(ob.events,snapshot=bad)
        for old,new in (("input_ids_10, position_ids_11 = next(dataloader)", 'pass'),
                        ("input_ids_10, position_ids_11 = next(dataloader)",
                         "input_ids_10, position_ids_11 = next(dataloader)\n    input_ids_10, position_ids_11 = next(dataloader)"),
                        ("result = nnscaler.runtime.executor.fexecute", "result = wrong_executor")):
            bad=copy.deepcopy(s)
            bad['rank_sources']['0']=bad['rank_sources']['0'].replace(old,new)
            with self.assertRaises(ValueError): validate(ob.events,snapshot=bad)
        model.segment=lambda *args: None
        with self.assertRaises(ValueError): api.InputHandoffObserver(model,module,s,record,0,'fresh-test')
        Executor._detach.clear()

    def test_handoff_metadata_rejects_equal_but_wrong_numeric_types(self):
        from scripts import gpt_batch_runtime as api
        from trainverify.batch_source_authority import validate_input_handoff
        from nnscaler.runtime.executor import Executor
        paths = [('rank',), ('train_step',), ('event_ordinal',), ('writer','runtime_rank'),
                 ('writer','call_instance'), ('refs',0,'version'), ('refs',0,'source_tid'),
                 ('parameter_indices',0), ('positions',0)]
        for path in paths:
            with self.subTest(path=path):
                s,r,ref,record,model,module,values=self.setup_case()
                ob=api.InputHandoffObserver(model,module,s,record,0,'fresh-test')
                try:
                    with ob:ob.run([values])
                    validate_input_handoff(ob.events,ob.payload,record,s,r,ref,'fresh-test',0)
                    bad=copy.deepcopy(ob.events); parent=bad[0]
                    for key in path[:-1]:parent=parent[key]
                    old=parent[path[-1]]; parent[path[-1]]=bool(old) if old in (0,1) else float(old)
                    with self.assertRaises(ValueError):
                        validate_input_handoff(bad,ob.payload,record,s,r,ref,'fresh-test',0)
                finally:Executor._detach.clear()

    def test_rank_json_and_tensor_event_types_are_independently_bound(self):
        from scripts import gpt_batch_runtime as api
        from nnscaler.runtime.executor import Executor
        for fault in ('row-only', 'tensor-shape', 'tensor-value'):
            with self.subTest(fault=fault):
                s,r,ref,record,model,module,values=self.setup_case()
                ob=api.InputHandoffObserver(model,module,s,record,0,'fresh-test')
                try:
                    with ob:ob.run([values])
                    actual=dict(rank=0,handoff=copy.deepcopy(ob.events),handoff_tensors=ob.payload)
                    row=dict(rank=0,handoff=copy.deepcopy(ob.events))
                    api.validate_rank_handoff(row,actual,record,s,r,ref,'fresh-test')
                    if fault=='row-only': row['handoff'][1]['refs'][0]['version']=True
                    else:
                        if fault=='tensor-shape': actual['handoff'][1]['shapes'][0][0]=True
                        else: actual['handoff'][1]['values'][0][0][0]=3.0
                        row['handoff']=copy.deepcopy(actual['handoff'])
                    with self.assertRaises(ValueError):
                        api.validate_rank_handoff(row,actual,record,s,r,ref,'fresh-test')
                finally:Executor._detach.clear()

    def test_exception_restoration_and_bounded_invocations(self):
        from scripts import gpt_batch_runtime as api
        from nnscaler.runtime.executor import Executor
        for mode in ('exception','missing-next','second-step','outside-consumer','double-consumer','nested-step'):
            s,r,ref,record,model,module,values = self.setup_case()
            original=model.segment
            prior=lambda loader: None
            model._train_step=prior
            ob=api.InputHandoffObserver(model,module,s,record,0,'fresh-test')
            if mode=='exception': model.fail=True
            if mode=='double-consumer': model.hook=lambda: model.segment(*values)
            if mode=='nested-step': model.hook=lambda: model._train_step([values])
            with self.subTest(mode=mode), self.assertRaises((ValueError,RuntimeError,StopIteration)):
                with ob:
                    if mode=='outside-consumer': model.segment(*values)
                    else:
                        ob.run([] if mode=='missing-next' else [values])
                        if mode=='second-step': ob.run([values])
            self.assertEqual(model.segment,original)
            self.assertIs(model._train_step,prior)
            self.assertEqual(model.calls,1 if mode in ('exception','second-step','double-consumer','nested-step') else 0)
            Executor._detach.clear()

    def test_swallowed_extra_consumer_still_rejects(self):
        from scripts import gpt_batch_runtime as api
        from nnscaler.runtime.executor import Executor
        s,r,ref,record,model,module,values = self.setup_case()
        def swallow():
            try:
                model.segment(*values)
            except ValueError:
                pass
        model.hook=swallow
        ob=api.InputHandoffObserver(model,module,s,record,0,'fresh-test')
        try:
            with self.assertRaises(ValueError), ob:
                ob.run([values])
            self.assertEqual(model.calls,1)
        finally:
            Executor._detach.clear()

    def test_worker_path_persists_failure_and_aggregate_rejects(self):
        from scripts import gpt_batch_runtime as api
        self.assertTrue(hasattr(api, 'execute_observed_training'), 'worker handoff path missing')
        import tempfile, types
        from pathlib import Path
        from unittest.mock import patch
        from nnscaler.runtime.executor import AsyncCommHandler, Executor
        s,r,ref,record,model,module,values = self.setup_case()
        model.train_step = lambda loader: [model._train_step(loader)]
        with tempfile.TemporaryDirectory() as directory:
            args=types.SimpleNamespace(out=Path(directory), batch_witness=Path(directory)/'witness.json')
            api.save_json(args.batch_witness,dict(reference_capture_receipt=ref))
            api.save_json(args.out/'run.json',dict(format='trainverify.input-handoff-run.v1',world=4,run_id='fresh'))
            AsyncCommHandler().submit(values[0],[],lambda t: torch.full_like(t,9))
            with self.assertRaisesRegex(ValueError,'post tensor'):
                api.execute_observed_training(args,model,module,s,record,0,values,r,ref)
            actual=torch.load(args.out/'rank0.pt',weights_only=True)
            self.assertEqual(actual['handoff_tensors']['post'][0][0].tolist(),[[9,9]])
            self.assertEqual(actual['handoff_tensors']['pre'][0][0].tolist(),[[3,4]])
            row=api.read(args.out/'rank0.json')
            self.assertEqual(row['inner_exit'],1)
            self.assertFalse(row['new_run_segment_input_association'])
            with self.assertRaises(ValueError):
                api.validate_rank_handoff(row,actual,record,s,r,ref,'fresh')
            # Public aggregate must reject old artifacts before touching canonical/GPU state.
            for rank in range(4):
                api.save_json(args.out/f'rank{rank}.json',dict(rank=rank,inner_exit=0))
                torch.save(dict(rank=rank),args.out/f'rank{rank}.pt')
            with patch.object(api,'load_inputs',return_value=(r,record,s,{})):
                with self.assertRaisesRegex(ValueError,'handoff'):
                    api.aggregate(args)
        self.assertEqual(model.calls,1)
        self.assertNotIn('_train_step',vars(model))
        Executor._detach.clear()
        AsyncCommHandler().check_clear()

    def test_real_executor_serialized_identity_and_callback(self):
        from scripts import gpt_batch_runtime as api
        self.assertTrue(hasattr(api, 'InputHandoffObserver'), 'postwait entry observer missing')
        from trainverify.batch_source_authority import validate_input_handoff
        from nnscaler.runtime.executor import AsyncCommHandler, Executor
        import io, json
        for changed in (False, True):
            s,r,ref,record,model,module,values = self.setup_case()
            original = model.segment
            ob = api.InputHandoffObserver(model,module,s,record,0,'fresh-test')
            if changed:
                AsyncCommHandler().submit(values[0], [], lambda t: torch.full_like(t,9))
            with ob:
                ob.run(iter([values]))
            self.assertEqual(model.segment, original)
            self.assertEqual(model.calls, 1)
            stream=io.BytesIO(); torch.save(ob.payload,stream); stream.seek(0)
            payload=torch.load(stream,weights_only=True)
            events=json.loads(json.dumps(ob.events))
            self.assertEqual(payload['post'][0][0].tolist(), [[9,9]] if changed else [[3,4]])
            if changed:
                with self.assertRaisesRegex(ValueError, 'post tensor'):
                    validate_input_handoff(events,payload,record,s,r,ref,'fresh-test',0)
            else:
                result=validate_input_handoff(events,payload,record,s,r,ref,'fresh-test',0)
                self.assertTrue(result['new_run_segment_input_association'])
                self.assertFalse(result['proof_admissible'])
            Executor._detach.clear()
            AsyncCommHandler().check_clear()


if __name__ == '__main__':
    unittest.main()
