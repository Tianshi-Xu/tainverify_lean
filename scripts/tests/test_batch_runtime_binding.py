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


if __name__ == '__main__':
    unittest.main()
