"""CPU-only source mapping contracts; sample identity is not token equality."""
import copy
import importlib
import importlib.util
import unittest
from trainverify.runtime_source_authority import build_snapshot


def fixture():
    writers = []
    for rank in range(4):
        refs = [dict(world='p', runtime_rank=rank, microbatch=0,
                     source_tid=tid, version=1) for tid in (10, 11)]
        writers.append(dict(ref=dict(world='p', runtime_rank=rank, microbatch=0,
            source_cid=1, call_instance=0, op='DATALOADER', origin='fixture'),
            inputs=[], outputs=refs))
    snapshot = build_snapshot(writers)
    snapshot['source'] = dict(plan_ndevs=2, runtime_ndevs=4)
    snapshot['runtime_ndevs'] = 4
    model = dict(seqlen=2, num_embeddings=32)
    receipt = dict(model=model, batch_size=1, compute=dict(plan_ngpus=2, runtime_ngpus=4))
    reference_receipt = dict(model=model, batch_size=2)
    config = dict(num_pp=1, num_mb=1, gbs=2, normalizer=1, objective='sum',
                  units=[dict(unit=0, ranks=[0,1], positions=[0]),
                         dict(unit=1, ranks=[2,3], positions=[1])])
    observed = [dict(input_ids=[[3,4]], position_ids=[[0,1]]),
                dict(input_ids=[[3,4]], position_ids=[[0,1]])]
    global_input = dict(input_ids=[[3,4],[3,4]], position_ids=[[0,1],[0,1]])
    return snapshot, receipt, reference_receipt, config, observed, global_input


class BatchAuthorityTests(unittest.TestCase):
    def test_observed_duplicate_values_remain_distinct_sample_positions(self):
        self.assertIsNotNone(importlib.util.find_spec('trainverify.batch_source_authority'),
                             'batch source authority implementation missing')
        api = importlib.import_module('trainverify.batch_source_authority')
        snapshot, receipt, reference, config, units, global_input = fixture()
        record = api.build_batch_record(config, units, global_input, snapshot)
        result = api.validate_batch_record(record, snapshot, receipt, reference)
        self.assertTrue(result['batch_input_mapping_verified'])
        self.assertFalse(result['proof_admissible'])
        self.assertFalse(result['kernel_value_proved'])
        self.assertFalse(result['capture_sample_association_verified'])
        self.assertEqual(record['samples'], [dict(global_position=0, unit=0, local_position=0,
            microbatch=0), dict(global_position=1, unit=1, local_position=0, microbatch=0)])

    def test_rejects_changes_to_assignment_domain_refs_and_reference(self):
        api = importlib.import_module('trainverify.batch_source_authority')
        snapshot, receipt, reference, config, units, global_input = fixture()
        units[1]['input_ids'] = [[20,21]]
        global_input['input_ids'][1] = [20,21]
        good = api.build_batch_record(config, units, global_input, snapshot)
        api.validate_batch_record(good, snapshot, receipt, reference)
        mutations = {
            'gbs-only': lambda r: r['config'].update(gbs=4),
            'pp': lambda r: r['config'].update(num_pp=2),
            'mb': lambda r: r['config'].update(num_mb=2),
            'normalizer': lambda r: r['config'].update(normalizer=0.5),
            'boolean-normalizer': lambda r: r['config'].update(normalizer=True),
            'mean': lambda r: r['config'].update(objective='mean'),
            'duplicate-position': lambda r: r['groups'][1].update(positions=[0]),
            'missing-sample': lambda r: r['samples'].pop(),
            'local-order': lambda r: r['samples'][0].update(local_position=1),
            'wrong-unit': lambda r: r['rank_inputs'][0].update(unit=1),
            'wrong-ranks': lambda r: r['groups'][0].update(ranks=[0,2]),
            'rank-order': lambda r: r['groups'][0]['ranks'].reverse(),
            'wrong-ref-version': lambda r: r['rank_inputs'][0]['refs'][0].update(version=0),
            'ref-order': lambda r: r['rank_inputs'][0]['refs'].reverse(),
            'global-coordinate': lambda r: r['global_inputs']['input_ids'][0].reverse(),
            'global-position-coordinate': lambda r: r['global_inputs']['position_ids'][0].reverse(),
            'unit-order': lambda r: r['groups'].reverse(),
            'admission': lambda r: r.update(proof_admissible=True),
            'missing-input': lambda r: r['groups'][0]['inputs'].pop('position_ids'),
        }
        for name, mutate in mutations.items():
            with self.subTest(name=name):
                bad = copy.deepcopy(good)
                mutate(bad)
                with self.assertRaises(ValueError):
                    api.validate_batch_record(bad, snapshot, receipt, reference)
        for bad_ref in (dict(reference, batch_size=1), dict(reference, model={'seqlen':3})):
            with self.assertRaises(ValueError):
                api.validate_batch_record(good, snapshot, receipt, bad_ref)

    def test_actual_cpu_gpt_all_parameter_gradients(self):
        self.assertIsNotNone(importlib.util.find_spec('scripts.gpt_batch_authority'),
                             'actual CPU witness entry missing')
        from scripts.gpt_batch_authority import run_witness
        snapshot, receipt, reference, config, _, _ = fixture()
        receipt.update(seed=7)
        receipt['model'].update(hidden=8, layers=1, heads=2, ffn_hidden_dim=16)
        reference['model'] = copy.deepcopy(receipt['model'])
        result, tensors = run_witness(receipt, reference, snapshot, config)
        self.assertTrue(result['numeric']['all_parameter_grads_close'])
        self.assertGreater(result['numeric']['parameter_count'], 10)
        self.assertTrue(result['numeric']['objective_close'])
        self.assertFalse(result['validation']['proof_admissible'])
        self.assertEqual(set(tensors['global_grads']), set(tensors['unit_grad_sum']))
        self.assertNotEqual(result['batch']['groups'][0]['inputs']['input_ids'],
                            result['batch']['groups'][1]['inputs']['input_ids'])
        self.assertIn('torch.sum(logits)', result['loss_source']['forward_source'])
        with self.assertRaises(ValueError):
            run_witness(receipt, dict(reference, batch_size=1), snapshot, config)


if __name__ == '__main__':
    unittest.main()
