"""Portable real CPU autograd tests; no capture paths, GPUs or skipped cases."""
import importlib
import importlib.util
import unittest
import torch


class Executor:
    _backward_pre_hook = None

    @staticmethod
    def backward(output, grad=None):
        torch.autograd.backward((output,), (grad,))


class Identity(torch.autograd.Function):
    @staticmethod
    def forward(ctx, value):
        return value.clone()

    @staticmethod
    def backward(ctx, grad):
        return grad


class SeedTests(unittest.TestCase):
    def api(self):
        spec = importlib.util.find_spec('trainverify.runtime_seed_authority')
        self.assertIsNotNone(spec, 'missing external seed observer')
        return importlib.import_module('trainverify.runtime_seed_authority')

    def test_real_none_scalar_identity_is_observed_not_proved(self):
        api = self.api()
        x = torch.arange(6., requires_grad=True)
        summed = x.sum()
        output = Identity.apply(summed)
        original = torch.autograd._make_grads
        calls = []
        def backward():
            calls.append(1)
            Executor.backward(output)
        observer = api.ScalarSeedObserver(Executor, output, summed, 'fresh-cpu-run')
        observer.run(backward)
        self.assertEqual(calls, [1])
        self.assertIs(torch.autograd._make_grads, original)
        self.assertTrue(torch.equal(x.grad, torch.ones_like(x)))
        receipt = observer.receipt()
        self.assertEqual(receipt['observed_seed'], {'torch_shape': [], 'value': 1.0})
        self.assertEqual(receipt['denote_intent'], {'shape': [1], 'valAt0': 1})
        self.assertTrue(receipt['unit_seed_observed'])
        self.assertFalse(receipt['runtime_accepted'])
        self.assertFalse(receipt['proof_admissible'])
        self.assertFalse(receipt['kernel_value_proved'])


    def test_rejects_live_hook_explicit_gradient_and_wrong_identity(self):
        api = self.api()
        for fault in ('prehook', 'explicit', 'wrong', 'nonscalar', 'complex', 'detached', 'tensorhook', 'latehook'):
            with self.subTest(fault=fault):
                x = torch.arange(6., requires_grad=True)
                summed = x.sum()
                output = Identity.apply(summed)
                if fault == 'nonscalar': output = output.reshape(1)
                if fault == 'complex': output = output.to(torch.complex64)
                if fault == 'detached': output = output.detach()
                handle = output.register_hook(lambda g: g) if fault == 'tensorhook' else None
                if fault == 'prehook': Executor._backward_pre_hook = lambda *a: a
                observer = api.ScalarSeedObserver(Executor, output, summed, 'new')
                original = torch.autograd._make_grads
                def call():
                    if fault == 'latehook': Executor._backward_pre_hook = lambda *a: a
                    Executor.backward(output + 0 if fault == 'wrong' else output,
                                      torch.ones_like(output) if fault == 'explicit' else None)
                try:
                    with self.assertRaises(ValueError): observer.run(call)
                    with self.assertRaises(ValueError): observer.receipt()
                    self.assertIs(torch.autograd._make_grads, original)
                finally:
                    Executor._backward_pre_hook = None
                    if handle: handle.remove()

    def test_exception_duplicate_missing_and_stale_revoke(self):
        api = self.api()
        for fault in ('exception', 'missing', 'duplicate', 'stale'):
            with self.subTest(fault=fault):
                x = torch.ones(2, requires_grad=True)
                summed = x.sum()
                observer = api.ScalarSeedObserver(Executor, summed, summed, 'new')
                original = torch.autograd._make_grads
                def call():
                    if fault == 'exception': raise RuntimeError('original failure')
                    if fault == 'missing': return
                    torch.autograd.backward((summed,), (None,), retain_graph=True)
                    if fault == 'duplicate': torch.autograd.backward((summed,), (None,))
                if fault == 'stale': observer.run(call)
                with self.assertRaises((ValueError, RuntimeError)): observer.run(call)
                with self.assertRaises(ValueError): observer.receipt()
                self.assertIs(torch.autograd._make_grads, original)

    def test_source_inventory_recomputed_not_seed_metadata(self):
        api = self.api()
        self.assertTrue(hasattr(api, 'bind_seed_inventory'), 'missing raw writer absence gate')
        ref = lambda tid, version=1: dict(world='p', runtime_rank=3, microbatch=0, source_tid=tid, version=version)
        bw = dict(ref=dict(world='p', runtime_rank=3, microbatch=0, source_cid=9,
                          call_instance=0, op='BW_sum', origin='nnscaler'),
                  inputs=[ref(20, 0), ref(21)], outputs=[ref(22)])
        path = dict(seed=ref(20, 0), bw_writer=bw['ref'], x=ref(21))
        self.assertEqual(api.bind_seed_inventory([bw], [path]), [path])
        from copy import deepcopy
        for fault in ('writer', 'duplicate', 'missing', 'version', 'rank', 'x', 'x-bool', 'order'):
            writers, paths = deepcopy([bw]), deepcopy([path])
            if fault == 'writer':
                writer = deepcopy(bw); writer['ref']['source_cid'] = 10
                writer['ref']['op'] = 'FW_sum'; writer['outputs'] = [ref(20, 0)]
                writers.append(writer)
            if fault == 'duplicate': paths.append(deepcopy(path))
            if fault == 'missing': paths.clear()
            if fault == 'version': paths[0]['seed']['version'] = 1
            if fault == 'rank': paths[0]['seed']['runtime_rank'] = 0
            if fault == 'x': paths[0]['x']['source_tid'] = 23
            if fault == 'x-bool': paths[0]['x']['version'] = True
            if fault == 'order': writers[0]['inputs'].reverse()
            with self.subTest(fault=fault), self.assertRaises(ValueError):
                api.bind_seed_inventory(writers, paths)

    def test_actual_executor_none_backward_cpu(self):
        from nnscaler.runtime.executor import Executor as ActualExecutor
        api = self.api()
        x = torch.arange(6., requires_grad=True)
        summed = ActualExecutor.fexecute('portable_seed', lambda: x.sum(), requires_grad=True)
        observer = api.ScalarSeedObserver(ActualExecutor, summed, summed, 'actual-executor-cpu')
        observer.run(lambda: ActualExecutor.backward('portable_seed', (), (summed,), (None,)))
        self.assertTrue(torch.equal(x.grad, torch.ones_like(x)))
        self.assertTrue(observer.receipt()['unit_seed_observed'])
        self.assertFalse(observer.receipt()['runtime_accepted'])

    def test_generated_schedule_live_binding_and_baseline(self):
        import types
        import nnscaler.runtime.executor as executor
        api = self.api()
        source = """import torch
import nnscaler.runtime.executor
class GenModel:
    def segment9(self, x):
        summed = torch.sum(x)
        return summed
def _train_step(model, x):
    output = nnscaler.runtime.executor.fexecute('segment9', model.segment9, x, requires_grad=True)
    nnscaler.runtime.executor.backward('segment9', (), (output,), (None,))
    return output
"""
        module = types.ModuleType('seed_fixture')
        exec(compile(source, '<seed-fixture>', 'exec'), module.__dict__)
        request = dict(segment='segment9', sum_name='summed', output_name='summed',
                       seed=dict(runtime_rank=0), identity_backward=False)
        model = module.GenModel()
        observer = api.GeneratedSeedObserver(model, module, source, request, 'fresh')
        x = torch.arange(6., requires_grad=True)
        fw, bw = executor.fexecute, executor.backward
        output = observer.run(lambda: module._train_step(model, x))
        self.assertEqual(output.item(), 15.)
        event, payload = observer.evidence()
        self.assertEqual(event['request'], request)
        self.assertEqual(event['observation']['effective_seed']['value'], 1.)
        self.assertEqual(payload['effective'].item(), 1.)
        self.assertIs(executor.fexecute, fw)
        self.assertIs(executor.backward, bw)
        with self.assertRaises(ValueError): observer.run(lambda: None)
        with self.assertRaises(ValueError): observer.evidence()

    def test_generated_code_change_after_construction(self):
        import types
        api = self.api()
        source = """import torch
class GenModel:
    def segment9(self, x):
        summed = torch.sum(x)
        return summed
def _train_step(model, x):
    return model.segment9(x)
"""
        module = types.ModuleType('changing_seed_fixture')
        exec(compile(source, '<changing-fixture>', 'exec'), module.__dict__)
        model = module.GenModel()
        observer = api.GeneratedSeedObserver(model, module, source,
            dict(segment='segment9', sum_name='summed', identity_backward=False), 'fresh')
        def replacement(self, x): return x.sum() * 7
        module.GenModel.segment9.__code__ = replacement.__code__
        calls = []
        with self.assertRaisesRegex(ValueError, 'loaded code changed'):
            observer.run(lambda: calls.append(1))
        self.assertEqual(calls, [])

    def test_k2_k3_effective_observer_preserves_parameter_gradients(self):
        api = self.api()
        for k in (2, 3):
            weight = torch.arange(1., 7., requires_grad=True)
            inputs = torch.arange(6.)
            baseline = torch.sum(weight * inputs * k)
            baseline.backward()
            expected = weight.grad.clone()
            weight.grad = None
            output = torch.sum(weight * inputs * k)
            observer = api.ScalarSeedObserver(Executor, output, output, f'k{k}')
            observer.run(lambda: Executor.backward(output))
            self.assertTrue(torch.equal(weight.grad, expected))

    def test_swallowed_duplicate_seed_revokes_receipt(self):
        api = self.api()
        x = torch.arange(6., requires_grad=True); output = x.sum()
        observer = api.ScalarSeedObserver(Executor, output, output, 'duplicate')
        def backward():
            torch.autograd.backward((output,), (None,), retain_graph=True)
            try: torch.autograd.backward((output,), (None,))
            except ValueError: pass
        with self.assertRaises(ValueError): observer.run(backward)
        with self.assertRaises(ValueError): observer.receipt()

    def test_k2_k3_full_raw_inventory_and_real_cpu_event_binding(self):
        api = self.api()
        for k in (2, 3):
            writers, requests, observations = [], [], []
            for rank in range(k):
                ref = lambda tid, v: dict(world='p', runtime_rank=rank, microbatch=0, source_tid=tid, version=v)
                bw = dict(ref=dict(world='p', runtime_rank=rank, microbatch=0, source_cid=9,
                                  call_instance=0, op='BW_sum', origin='nnscaler'),
                          inputs=[ref(20, 0), ref(21, 1)], outputs=[ref(22, 1)])
                request = dict(seed=ref(20, 0), bw_writer=bw['ref'], x=ref(21, 1))
                writers.append(bw); requests.append(request)
                x = torch.arange(6., requires_grad=True); y = x.sum()
                observer = api.ScalarSeedObserver(Executor, y, y, f'world-{k}')
                observer.run(lambda: Executor.backward(y))
                event = dict(run_id=f'world-{k}', event_ordinal=1, request=request, observation=observer.receipt())
                observations.append((event, dict(seed_event=event,
                    seed_tensors=dict(requested=observer._observed_tensor, effective=observer._effective_tensor))))
            authority = dict(requests=api.bind_seed_inventory(writers, requests))
            manifest = dict(run_id=f'world-{k}', world=k, format='trainverify.input-handoff-run.v1')
            for rank, (event, actual) in enumerate(observations):
                api.validate_seed_event(authority, event, actual, manifest, rank)
            with self.assertRaises(ValueError): api.bind_seed_inventory(writers, requests[::-1])

    def test_independent_event_pt_run_binding(self):
        from copy import deepcopy
        api = self.api()
        x = torch.arange(6., requires_grad=True); y = x.sum()
        obs = api.ScalarSeedObserver(Executor, y, y, 'run')
        obs.run(lambda: Executor.backward(y))
        request = dict(seed=dict(world='p', runtime_rank=0, microbatch=0, source_tid=279, version=0))
        authority = dict(requests=[request])
        event = dict(run_id='run', event_ordinal=1, request=request, observation=obs.receipt())
        actual = dict(seed_event=deepcopy(event), seed_tensors=dict(requested=obs._observed_tensor, effective=obs._effective_tensor))
        manifest = dict(run_id='run', world=1, format='trainverify.input-handoff-run.v1')
        api.validate_seed_event(authority, event, actual, manifest, 0)
        for fault in ('run', 'bool-rank', 'float-ref', 'request', 'pt', 'unit', 'shape', 'dtype', 'ordinal'):
            ev, pt, run = deepcopy(event), deepcopy(actual), deepcopy(manifest)
            if fault == 'run': ev['run_id'] = 'stale'; pt['seed_event']['run_id'] = 'stale'
            if fault == 'bool-rank': ev['request']['seed']['runtime_rank'] = False; pt['seed_event'] = deepcopy(ev)
            if fault == 'float-ref': ev['request']['seed']['source_tid'] = 279.; pt['seed_event'] = deepcopy(ev)
            if fault == 'request': ev['request']['seed']['version'] = 1; pt['seed_event'] = deepcopy(ev)
            if fault == 'pt': pt['seed_event']['run_id'] = 'other'
            if fault == 'unit': pt['seed_tensors']['effective'] *= 7
            if fault == 'shape': pt['seed_tensors']['effective'] = pt['seed_tensors']['effective'].reshape(1)
            if fault == 'dtype': pt['seed_tensors']['effective'] = pt['seed_tensors']['effective'].to(torch.int64)
            if fault == 'ordinal': ev['event_ordinal'] = True; pt['seed_event'] = deepcopy(ev)
            with self.subTest(fault=fault), self.assertRaises(ValueError):
                api.validate_seed_event(authority, ev, pt, run, 0)

    def test_gpu_cli_seed_opt_in(self):
        import subprocess, sys
        help_text = subprocess.check_output([sys.executable, '-B', '-m', 'scripts.gpt_batch_runtime', '--help'], text=True)
        self.assertIn('--seed-capture', help_text)

    def test_later_node_prehook_effective_consumer(self):
        api = self.api()
        x = torch.arange(6., requires_grad=True)
        summed = x.sum()
        observer = api.ScalarSeedObserver(Executor, summed, summed, 'late-node')
        handles = []
        original = torch.autograd._make_grads
        def backward():
            handles.append(summed.grad_fn.register_prehook(lambda gs: (gs[0] * 7,)))
            Executor.backward(summed)
        try:
            with self.assertRaisesRegex(ValueError, 'exact scalar unit'):
                observer.run(backward)
            self.assertTrue(torch.equal(x.grad, torch.full_like(x, 7)))
            self.assertIs(torch.autograd._make_grads, original)
            with self.assertRaises(ValueError): observer.receipt()
        finally:
            for handle in handles: handle.remove()

    def test_nonstandard_node_hook_never_admitted(self):
        api = self.api()
        for factor in (1, 2):
            x = torch.ones(2, requires_grad=True)
            summed = x.sum()
            handle = summed.grad_fn.register_prehook(lambda gs: (gs[0] * factor,))
            observer = api.ScalarSeedObserver(Executor, summed, summed, 'node-hook')
            try:
                if factor == 2:
                    with self.assertRaises(ValueError): observer.run(lambda: Executor.backward(summed))
                else:
                    observer.run(lambda: Executor.backward(summed))
                    self.assertFalse(observer.receipt()['runtime_accepted'])
                    self.assertEqual(observer.receipt()['effective_seed']['value'], 1.0)
            finally:
                handle.remove()

if __name__ == '__main__':
    unittest.main()
