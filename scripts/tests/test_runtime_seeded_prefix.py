"""Portable production option/seeded emitter contracts."""
import inspect
import unittest
from Verdict import runtime_input_feed as feed, runtime_seed_feed as seed
from Verdict import runtime_prefix as prefix
from scripts.tests.test_runtime_seed_feed import fixture

class ProductionSeedTests(unittest.TestCase):
    def test_explicit_production_attachment(self):
        self.assertIn('seed_bundle', inspect.signature(feed.bind).parameters)
        self.assertIsNone(inspect.signature(feed.bind).parameters['seed_bundle'].default)
        rows = seed.map_requests(*fixture(2)[:3])
        groups = seed.render_adapter({'sm': rows[:1], 'pm': rows}, structured=True)
        self.assertTrue(all(isinstance(g, prefix.ProofGroup) for g in groups))
        text, chunks = prefix.pack_proofs([groups])
        self.assertEqual(text.count('namespace TrainVerify.Denote.RuntimeWorld'), 1)
        self.assertIn('pmInitialWithSeeds_seed_1', text)
        self.assertIn('seed_inventories', inspect.signature(prefix.render).parameters)

    def test_cli_requires_handoff_before_loading(self):
        from unittest.mock import patch
        from Verdict import graph_to_lean as c
        with patch('sys.argv', ['graph_to_lean', '--out', 'never.lean', '--module', 'Never', '--runtime-seed-bundle', 'missing.json']):
            args = c.parse_args()
        with patch.object(c, 'load_verifier', side_effect=AssertionError('must not load')):
            with self.assertRaisesRegex(ValueError, 'seed bundle requires runtime input handoff'):
                c._generate(args)

    def test_seeded_cpu_source_k2_k3_and_failed_fresh_bind(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from types import SimpleNamespace as NS
        from unittest.mock import patch
        from Verdict import graph_to_lean as c
        from scripts.tests.test_runtime_scoped_prefix import collective_world, proof_text
        from scripts.tests.test_graph_to_lean_runtime_lineage import T, N, IR
        fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
        lower, bind = c._lower_runtime_graphs, feed.bind
        for k in (2, 3):
            for fault in (None, 'uncomputed-x'):
                captured = []
                def lowered(sm, pm):
                    for label, graph in [('s', sm), ('p', pm)]:
                        sources = [cell for cell in graph.cells if cell.opname == ('FW_embedding' if label == 's' else 'AllToAllPrim')]
                        for src in sources:
                            rank = src.rank; x = src.outputs[0]
                            g = T(label, rank, 0, 900, 0); y = T(label, rank, 0, 901, 1)
                            gir = IR(900, 'seed', (1,)); gir.is_grad = lambda: True
                            graph.shapes[g] = (1,); graph.shapes[y] = graph.shapes[x]
                            inp = g if fault == 'uncomputed-x' and label == 'p' else x
                            graph.cells.append(NS(node=N(label, rank, 0, 900, 'BW_sum'), rank=rank, opname='BW_sum', kwargs={},
                                inputs=[g, inp], outputs=[y], _input_irs=[gir, IR(inp.tid, 'x', graph.shapes[inp])],
                                _output_irs=[IR(901, 'gradient', graph.shapes[y])]))
                    return None
                def inventory(config, sm, pm, raw_sm, raw_pm, root):
                    if config == 'bad': raise ValueError('fresh authority rejected')
                    inventories = {}
                    for label, view, cells in [('sm', sm, raw_sm), ('pm', pm, raw_pm)]:
                        reqs = [dict(seed=dict(zip(fields, cell.inputs[0])), x=dict(zip(fields, cell.inputs[1])),
                            bw_writer=dict(world=cell.node[0], runtime_rank=cell.rank, microbatch=0, source_cid=cell.node.cid,
                                           call_instance=0, op='BW_sum', origin='nnscaler')) for cell in cells if cell.opname=='BW_sum']
                        inventories[label] = seed.map_requests(view, cells, reqs)
                    return dict(inventories=inventories, pins={}, runs={})
                def attached(*args, **kw):
                    captured.append(args)
                    return bind(*args, seed_bundle='fixture')
                # Only capture/event/PT authentication is mocked. Raw fullref mapping,
                # source world/feed checks, shape inference and atomic packing are real.
                with TemporaryDirectory() as d, patch.object(feed, 'bind', attached), patch.object(seed, 'load_bundle', side_effect=inventory):
                    fed = collective_world(Path(d), k, seeded_transform=lowered)
                    p = fed.receipt['scoped_prefix']['pm']; text = proof_text(fed)
                    if fault:
                        self.assertEqual(p['frontier']['reason'], 'unsupported-seed-sum-contract')
                    else:
                        self.assertIsNone(p['frontier'])
                        self.assertEqual(len(p['initial_premises']), k)
                        self.assertIn(':= bw_sum unitSeed', text)
                        self.assertIn('pmSeededPrefixState_0 (init : Store) : Store := (pmInitialWithSeeds init)', text)
                        self.assertIn('exact pmInitialWithSeeds_seed_', text)
                        self.assertIn('pmSeededDenoteWithInputs init = runUsing', text)
                        self.assertIn('pmInitialWithSeeds_frame init', text)
                        self.assertIn('= (pmInitialWithSeeds init) tid', text)
                        self.assertNotIn('def pmPrefixState_', text)
                    with self.assertRaisesRegex(ValueError, 'fresh authority rejected'):
                        bind(*captured[0], seed_bundle='bad')
                    plain = bind(*captured[0])
                    self.assertEqual(plain.receipt['scoped_prefix']['pm']['frontier']['reason'], 'unsupported-producer')
                    self.assertNotIn('seed_input', plain.receipt)
                    self.assertNotIn('pmInitialWithSeeds', proof_text(plain))
