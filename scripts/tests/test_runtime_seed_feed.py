"""Portable seed-map controls. These fixtures are not capture authentication."""
import importlib
import importlib.util
import unittest
from copy import deepcopy
from types import SimpleNamespace as NS
from collections import namedtuple

Ref = namedtuple('Ref', 'world rank mb tid ver')
Node = namedtuple('Node', 'world rank mb cid irname')
FIELDS = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')


def fixture(k):
    cells = []; originals = {}; shapes = {}; paths = []
    for rank in range(k):
        x, seed, out = (Ref('p', rank, 0, t, v) for t, v in ((37, 1), (91, 0), (53, 1)))
        node = Node('p', rank, 0, 19, 'BW_sum')
        ir = lambda grad: NS(is_grad=lambda: grad, is_param=lambda: False)
        cells.append(NS(node=node, opname='BW_sum', inputs=[seed, x], outputs=[out],
                        kwargs={"__consts": []}, _input_irs=[ir(True), ir(False)]))
        for ref in (x, seed, out):
            lowered = Ref('p', rank, 0, 1000 + len(originals)*7, ref.ver)
            originals[lowered] = ref
            shapes[lowered] = [1] if ref == seed else [2, 3]
        paths.append(dict(seed=dict(zip(FIELDS, seed)), x=dict(zip(FIELDS, x)),
            bw_writer=dict(world='p', runtime_rank=rank, microbatch=0, source_cid=19,
                           call_instance=0, op='BW_sum', origin='nnscaler')))
    reverse = {v:k for k,v in originals.items()}
    view = NS(tensors=lambda:list(originals), source_tensor=lambda t:originals[t],
        nodes=lambda:[c.node for c in cells],
        node_opname=lambda n:next(c.opname for c in cells if c.node==n),
        node_inputs=lambda n:[reverse[t] for c in cells if c.node==n for t in c.inputs],
        node_outputs=lambda n:[reverse[t] for c in cells if c.node==n for t in c.outputs],
        node_kwargs=lambda n:next(c.kwargs for c in cells if c.node==n),
        tensor_shape=lambda t:shapes[t])
    return view, cells, paths, originals


class SeedFeedTests(unittest.TestCase):
    def api(self):
        self.assertIsNotNone(importlib.util.find_spec('Verdict.runtime_seed_feed'),
                             'missing authenticated seed Store adapter')
        return importlib.import_module('Verdict.runtime_seed_feed')

    def test_loader_and_mathematical_adapter_are_explicit(self):
        api = self.api()
        self.assertTrue(hasattr(api, 'load_bundle'), 'missing fresh capture/event/PT loader')
        self.assertTrue(hasattr(api, 'render_adapter'), 'missing computed Store adapter')
        with self.assertRaises(ValueError):
            api.load_bundle({}, None, None, None, None, '.')
        rows = api.map_requests(*fixture(2)[:3])
        text = api.render_adapter({'sm': rows[:1], 'pm': rows})
        self.assertIn('def applySeeds', text)
        self.assertIn('storeSet_feed_value', text)
        self.assertIn('pmInitialWithSeeds', text)
        self.assertIn('pmSeededDenoteWithInputs', text)
        self.assertNotIn('hseed', text)
        self.assertIn('applySeeds_parameters', text)
        self.assertIn('unitSeed_bw_sum', text)

    def test_cpu_seed_events_join_typed_k2_k3(self):
        import torch
        from trainverify.runtime_seed_authority import ScalarSeedObserver, validate_seed_event
        from scripts.tests.test_runtime_seed_authority import Executor
        api = self.api()
        for k in (2, 3):
            view, raw, requests, _ = fixture(k)
            authority = {'requests': requests}
            manifest = dict(format='trainverify.input-handoff-run.v1', world=k, run_id=f'cpu-{k}')
            for rank, request in enumerate(requests):
                x = torch.arange(6., requires_grad=True)
                output = x.sum()
                observer = ScalarSeedObserver(Executor, output, output, manifest['run_id'])
                observer.run(lambda: Executor.backward(output))
                event = dict(run_id=manifest['run_id'], event_ordinal=1, request=request,
                             observation=observer.receipt())
                actual = dict(seed_event=deepcopy(event), seed_tensors=dict(
                    requested=observer._observed_tensor, effective=observer._effective_tensor))
                validate_seed_event(authority,event,actual,manifest,rank)
                self.assertTrue(torch.equal(x.grad, torch.ones_like(x)))
                for fault in ('rank', 'value', 'run', 'version'):
                    ev, pt = deepcopy(event), deepcopy(actual)
                    if fault == 'rank': ev['request']['seed']['runtime_rank'] = (rank+1)%k
                    if fault == 'value': pt['seed_tensors']['effective'] *= 2
                    if fault == 'run': ev['run_id'] = 'stale'
                    if fault == 'version': ev['request']['seed']['version'] = False
                    pt['seed_event'] = deepcopy(ev)
                    with self.subTest(k=k,rank=rank,fault=fault), self.assertRaises(ValueError):
                        validate_seed_event(authority,ev,pt,manifest,rank)
            self.assertEqual(len(api.map_requests(view,raw,requests)), k)

    def test_typed_complete_seed_mapping_k2_k3(self):
        api = self.api()
        for k in (2, 3):
            view, raw, requests, original = fixture(k)
            rows = api.map_requests(view, raw, requests)
            self.assertEqual(len(rows), k)
            self.assertEqual([row['ref'] for row in rows], [p['seed'] for p in requests])
            self.assertEqual([row['tid'] for row in rows],
                [t.tid for t, ref in original.items() if ref.ver == 0])
            for fault in ('missing', 'extra', 'bool', 'rank', 'version', 'order', 'future-writer', 'nongrad', 'map-permutation', 'lowered-alias'):
                v, cells, paths, refs = fixture(k)
                if fault == 'missing': paths.pop()
                if fault == 'extra': paths.append(deepcopy(paths[0]))
                if fault == 'bool': paths[0]['seed']['version'] = False
                if fault == 'rank': paths[0]['seed']['runtime_rank'] = k
                if fault == 'version': paths[0]['seed']['version'] = 1
                if fault == 'order': cells[0].inputs.reverse()
                if fault == 'future-writer': cells[-1].outputs.append(cells[0].inputs[0])
                if fault == 'nongrad': cells[0]._input_irs[0].is_grad = lambda:False
                if fault == 'map-permutation':
                    keys = list(refs); refs[keys[0]],refs[keys[1]]=refs[keys[1]],refs[keys[0]]
                if fault == 'lowered-alias':
                    keys=list(refs); old=keys[1]; ref=refs.pop(old)
                    refs[old._replace(tid=keys[0].tid)] = ref
                with self.subTest(k=k,fault=fault), self.assertRaises(ValueError):
                    api.map_requests(v,cells,paths)


if __name__ == '__main__':
    unittest.main()
