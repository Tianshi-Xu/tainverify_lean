"""Atomic source-only world bundles, using independent CPU-observed feeds."""
import json
import re
import tempfile
import unittest
from pathlib import Path
from scripts.tests.test_runtime_scoped_prefix import collective_world

BASE = 'TrainVerifyRuntimeWorldData.lean'


class BundleTests(unittest.TestCase):
    def test_published_entry_imports_complete_base(self):
        from Verdict.runtime_world import publish
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            fed = collective_world(root, 2, normalize=True, project=True, gather=True)
            self.assertIn(BASE, fed.supporting_sources)
            chunks = sorted(set(fed.supporting_sources) - {BASE})
            self.assertTrue(chunks)
            base = fed.supporting_sources[BASE]
            self.assertTrue(fed.lean.startswith('import TrainVerifyRuntimeWorldData\nimport denote.SourceScopedPrefix\n'))
            self.assertEqual(base.count(' : GraphDecl :='), 2)
            self.assertNotIn(' : GraphDecl :=', fed.lean)
            self.assertNotIn('theorem pmPrefix', base)
            for label in ('sm', 'pm'):
                self.assertIn(f'def {label}InputRequests', base)
                self.assertIn(f'theorem {label}InputSchedule_valid', base)
            out = root/'published'/'World.lean'
            publish(fed, out)
            self.assertEqual({p.name for p in out.parent.iterdir()}, {BASE, *chunks, 'World.lean', 'world-receipt.json'})
            self.assertEqual(out.read_text(), fed.lean)
            self.assertEqual((out.parent/BASE).read_text(), base)
            receipt = json.loads((out.parent/'world-receipt.json').read_text())
            bundle = receipt['proof_bundle']
            self.assertEqual(bundle['dependency_order'], [BASE, *chunks, 'World.lean'])
            self.assertFalse(bundle['kernel_checked'])
            self.assertEqual([m['file'] for m in bundle['modules']], [BASE, *chunks, 'World.lean'])
            for member in bundle['modules']:
                text = (out.parent/member['file']).read_text()
                self.assertEqual(member['imports'], re.findall(r'^import (\S+)$', text, re.M))
                self.assertEqual(member['theorems'], re.findall(r'^theorem (\S+)', text, re.M))
                self.assertFalse(member['kernel_checked'])

    def test_rejects_tampered_members_and_preserves_previous_destination(self):
        from dataclasses import replace
        from Verdict.runtime_world import publish
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); fed = collective_world(root, 2)
            public = root/'Public.lean'; public.write_bytes(b'public sentinel')
            out = root/'bundle'/'World.lean'
            for support in ({}, {BASE: fed.supporting_sources[BASE]+'-- changed\n'},
                            {'../escape.lean': 'bad'}, {BASE: fed.supporting_sources[BASE], 'extra.lean': 'bad'}):
                with self.assertRaises(ValueError): publish(replace(fed, supporting_sources=support), out)
                self.assertFalse(out.parent.exists())
            detached = replace(fed, supporting_sources={}, receipt={k:v for k,v in fed.receipt.items() if k != 'proof_bundle'})
            with self.assertRaises(ValueError): publish(detached, out)
            with self.assertRaises(ValueError): publish(fed, root/'collision'/BASE)
            publish(fed, out)
            previous = {p.name:p.read_bytes() for p in out.parent.iterdir()}
            with self.assertRaises(ValueError): publish(fed, out)
            self.assertEqual(previous, {p.name:p.read_bytes() for p in out.parent.iterdir()})
            self.assertEqual(public.read_bytes(), b'public sentinel')
            self.assertFalse(list(root.glob('trainverify-world-*')))

    def test_staged_membership_and_write_failure_are_atomic(self):
        from unittest.mock import patch
        from Verdict.runtime_world import publish
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); fed = collective_world(root, 2)
            public = root/'Public.lean'; public.write_bytes(b'public sentinel')
            original = Path.write_text
            for fault in ('exception', 'omit', 'extra', 'tamper'):
                def write(path, text, *args, **kwargs):
                    if path.name == BASE:
                        if fault == 'exception': raise OSError('injected staging failure')
                        if fault == 'omit': return 0
                        if fault == 'extra': original(path.parent/'Unexpected.lean', '-- unexpected\n')
                        if fault == 'tamper': text += '-- changed\n'
                    return original(path, text, *args, **kwargs)
                out = root/fault/'World.lean'
                with patch.object(Path, 'write_text', write):
                    with self.assertRaises((ValueError, OSError)): publish(fed, out)
                self.assertFalse(out.parent.exists())
                self.assertFalse(list(root.glob('trainverify-world-*')))
                self.assertEqual(public.read_bytes(), b'public sentinel')


    def test_canonical_scanner_checks_both_bundle_members(self):
        from dataclasses import replace
        from Verdict.runtime_world import publish, _proof_bundle
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); fed = collective_world(root, 2)
            for role in ('data', 'entry'):
                entry = fed.lean
                support = dict(fed.supporting_sources)
                if role == 'data': support[BASE] += '\naxiom forged : True\n'
                else: entry += '\naxiom forged : True\n'
                receipt = dict(fed.receipt, proof_bundle=_proof_bundle(entry, support))
                out = root/role/'World.lean'
                with self.assertRaises(ValueError): publish(replace(fed, lean=entry, supporting_sources=support, receipt=receipt), out)
                self.assertFalse(out.parent.exists())
                self.assertFalse(list(root.glob('trainverify-world-*')))

    def test_bind_authenticates_additive_field(self):
        from dataclasses import replace
        from Verdict import graph_to_lean as c
        from Verdict.runtime_world import render
        from Verdict.runtime_input_feed import bind
        from scripts.tests.test_runtime_input_feed import observed
        from scripts.tests.test_graph_to_lean_runtime_lineage import fixture
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); source = observed(root)
            sm, pm, args = fixture(); sv, pv = c._lower_runtime_graphs(sm, pm)
            world = render(sv, pv, args[0], args[1])
            self.assertEqual(world.supporting_sources, {})
            with self.assertRaises(ValueError):
                bind(replace(world, supporting_sources={BASE:'forged'}), sv, pv, args[0], args[1], *source, root)
