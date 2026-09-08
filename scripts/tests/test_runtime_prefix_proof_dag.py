"""Canonical bounded proof DAG publication, with one shared computation."""
import json
import re
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch
from scripts.tests.test_runtime_scoped_prefix import collective_world
from Verdict import runtime_prefix as prefix
from Verdict.runtime_world import publish, _proof_bundle, WORLD_DATA_FILE


class PrefixProofDAGTests(unittest.TestCase):
    def test_forced_budget_complete_chain_and_atomic_publication(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            with patch.object(prefix, 'PROOF_DECLARATION_BUDGET', 24, create=True):
                fed = collective_world(root, 2, chain=True)
            chunks = sorted(n for n in fed.supporting_sources if n != WORLD_DATA_FILE)
            self.assertGreater(len(chunks), 1)
            sources = [*fed.supporting_sources.values(), fed.lean]
            text = '\n'.join(sources)
            n = fed.receipt['scoped_prefix']['pm']['prefix_length']
            self.assertEqual(text.count(' : GraphDecl :='), 2)
            for j in range(n):
                self.assertEqual(len(re.findall(rf'^def pmPrefixState_{j+1} ', text, re.M)), 1)
                self.assertEqual(len(re.findall(rf'^theorem pmPrefixStep_{j} ', text, re.M)), 1)
            self.assertIn('theorem pmPrefixSuccess', fed.lean)
            imported_opaque = [name for names in re.findall(
                r'^attribute \[local irreducible\] (.+)$', fed.lean, re.M)
                for name in names.split()]
            self.assertIn('pmPrefixState_1', imported_opaque)
            bundle = fed.receipt['proof_bundle']
            self.assertEqual(bundle['dependency_order'], [WORLD_DATA_FILE, *chunks, '$entry'])
            checks = [t for m in bundle['modules'] for t in m['theorems'] if t.startswith('pmPrefix')]
            self.assertCountEqual(checks, fed.receipt['scoped_prefix']['pm']['kernel_checks'])
            out = root/'bundle'/'World.lean'
            publish(fed, out)
            self.assertEqual(set(p.name for p in out.parent.iterdir()), {WORLD_DATA_FILE, *chunks, 'World.lean', 'world-receipt.json'})
            original = {p.name:p.read_bytes() for p in out.parent.iterdir()}
            for kind in ('missing', 'tamper', 'orphan', 'cycle'):
                support = dict(fed.supporting_sources)
                if kind == 'missing': del support[chunks[0]]
                elif kind == 'tamper': support[chunks[0]] += '-- changed\n'
                elif kind == 'orphan': support['TrainVerifyRuntimePrefix9999.lean'] = support[chunks[0]]
                else: support[chunks[0]] = support[chunks[0]].replace('import denote.SourceScopedPrefix', 'import '+Path(chunks[-1]).stem)
                with self.assertRaises(ValueError): publish(replace(fed, supporting_sources=support), root/kind/'World.lean')
                self.assertFalse((root/kind).exists())
            with self.assertRaises(ValueError): publish(fed, root/'collision'/chunks[0])
            with self.assertRaises(ValueError): publish(fed, out)
            self.assertEqual(original, {p.name:p.read_bytes() for p in out.parent.iterdir()})
            self.assertFalse(list(root.glob('trainverify-world-*')))

    def test_imported_irreducibility_is_one_ordered_command_per_boundary(self):
        groups = [prefix.ProofGroup(
            f'def state{i} := {i}\ndef value{i} := {i}\n'
            f'attribute [local irreducible] state{i}\n',
            2, (f'state{i}', f'value{i}')) for i in range(7)]
        final = prefix.ProofGroup('theorem done : True := trivial\n', 1, (), True)
        with patch.object(prefix, 'PROOF_DECLARATION_BUDGET', 4):
            entry, support = prefix.pack_proofs([groups + [final]])
        opaque = []
        for index, source in enumerate([*support.values(), entry]):
            chunk = groups[index * 2:index * 2 + 2] if index < 4 else [final]
            edge = f'import TrainVerifyRuntimePrefix{index-1:04d}\n' if index else ''
            attrs = ('attribute [local irreducible] ' + ' '.join(opaque) + '\n'
                     if opaque else '')
            expected = ('import TrainVerifyRuntimeWorldData\nimport denote.SourceScopedPrefix\n'
                        + edge + prefix._HEADER + attrs
                        + '\n'.join(g.text for g in chunk) + prefix._FOOTER)
            self.assertEqual(source, expected)
            opaque.extend(n for g in chunk for n in g.opaque)
        self.assertEqual(list(support), [f'TrainVerifyRuntimePrefix{i:04d}.lean' for i in range(4)])
        with patch.object(prefix, 'PROOF_DECLARATION_BUDGET', 80):
            single, support = prefix.pack_proofs([groups + [final]])
        self.assertFalse(support)
        self.assertEqual(single, 'import TrainVerifyRuntimeWorldData\nimport denote.SourceScopedPrefix\n'
                         + prefix._HEADER + '\n'.join(g.text for g in groups + [final]) + prefix._FOOTER)

    def test_read_certificates_reuse_latest_full_tid_version(self):
        from types import SimpleNamespace as NS
        # Equal source identities with distinct full tids must never alias.
        a, b = NS(tid=17, source_tid=9), NS(tid=18, source_tid=9)
        rows = []
        for j in range(32):
            outs = [a, b] if j in (15, 23) else [NS(tid=100+j)]
            rows.append(dict(index=j, op='FW_multiref', ins=[a, b], outs=outs,
                             scope=None, input_shapes=[[1], [1]],
                             output_shapes=[[1]] * len(outs), params=[]))
        rows[0].update(op='AllToAllPrim', scope=NS(ranks=(0, 1), local_index=0,
                                                params=(0, 0)))
        rows[27]['ins'] = [a, a]
        for seeds in (None, [{'tid': 18}]):
            initial = {17: dict(tid=17, shape=[1])}
            if seeds is None: initial[18] = dict(tid=18, shape=[1])
            groups, _ = prefix._render('p', rows, {}, initial, None,
                                       structured=True, seeds=seeds)
            text = '\n'.join(g.text for g in groups)
            stem = 'pPrefix' if seeds is None else 'pSeededPrefix'
            def body(j, port):
                return text.split(f'theorem {stem}Read_{j}_{port} ', 1)[1].split('#print', 1)[0]
            for port in (0, 1):
                self.assertIn(f'exact {stem}Read_14_{port} init', body(15, port))
                self.assertIn(f'exact {stem}Written_15_{port} init', body(16, port))
                self.assertNotIn(f'Read_15_{port}', body(16, port))
                self.assertIn(f'exact {stem}Written_23_{port} init', body(24, port))
                self.assertNotIn(f'Read_23_{port}', body(24, port))
                self.assertIn(f'exact {stem}Read_30_{port} init', body(31, port))
                self.assertEqual(body(31, port).count('Skip_'), 1)
            self.assertIn(f'exact {stem}Read_27_0 init', body(27, 1))
            self.assertNotIn('Skip_', body(27, 1))

    def test_sparse_reads_use_shared_aligned_no_write_certificates(self):
        from types import SimpleNamespace as NS
        rows = [dict(index=j, op='FW_multiref', ins=[NS(tid=7)],
                     outs=[NS(tid=100+j)], scope=None, input_shapes=[[1]],
                     output_shapes=[[1]], params=[]) for j in range(64)]
        rows[0].update(op='AllToAllPrim', scope=NS(ranks=(0,), local_index=0, params=(0, 0)))
        rows[-1]['ins'] = [NS(tid=8)]
        groups, receipt = prefix._render('p', rows, {},
            {t: dict(tid=t, shape=[1]) for t in (7, 8)}, None, structured=True)
        text = '\n'.join(g.text for g in groups)
        body = text.split('theorem pPrefixRead_63_0 ', 1)[1].split('#print', 1)[0]
        self.assertLessEqual(body.count('  rw ['), 7)
        self.assertIn('pPrefixNoWrite_0_32', body)
        for g in groups:
            self.assertLessEqual(len(g.text.encode()), prefix.PROOF_BYTE_BUDGET)
            self.assertLessEqual(g.declarations, prefix.PROOF_DECLARATION_BUDGET)
        self.assertEqual(receipt['prefix_length'], 64)

    def test_packing_is_generic_greedy_and_bounded(self):
        gs = [prefix.ProofGroup(f'def x{i} := {i}\n', 1, ()) for i in range(7)]
        final = prefix.ProofGroup('theorem done : True := trivial\n', 1, (), True)
        with patch.object(prefix, 'PROOF_DECLARATION_BUDGET', 3):
            entry, support = prefix.pack_proofs([gs + [final]])
            self.assertEqual(len(support), 3)
            self.assertIn('def x2', support['TrainVerifyRuntimePrefix0000.lean'])
            self.assertNotIn('def x3', support['TrainVerifyRuntimePrefix0000.lean'])
            _, extended = prefix.pack_proofs([gs + [prefix.ProofGroup('def x7 := 7\n', 1, ()), final]])
            self.assertEqual(support['TrainVerifyRuntimePrefix0000.lean'], extended['TrainVerifyRuntimePrefix0000.lean'])
        with patch.object(prefix, 'PROOF_BYTE_BUDGET', 15):
            with self.assertRaisesRegex(ValueError, 'budget'):
                prefix.pack_proofs([[final]])

    def test_import_closure_rejects_forged_reinventory(self):
        with tempfile.TemporaryDirectory() as d:
            with patch.object(prefix, 'PROOF_DECLARATION_BUDGET', 24):
                fed = collective_world(Path(d), 2, chain=True)
            chunks = sorted(set(fed.supporting_sources) - {WORLD_DATA_FILE})
            last = Path(chunks[-1]).stem
            with self.assertRaisesRegex(ValueError, 'import'):
                _proof_bundle(fed.lean.replace(f'import {last}\n', ''), fed.supporting_sources)
            support = dict(fed.supporting_sources)
            support[chunks[0]] = support[chunks[0]].replace('import denote.SourceScopedPrefix', f'import denote.SourceScopedPrefix {last}')
            with self.assertRaisesRegex(ValueError, 'import'):
                _proof_bundle(fed.lean, support)

    def test_chunk_staging_failures_and_scanner_are_atomic(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            with patch.object(prefix, 'PROOF_DECLARATION_BUDGET', 24):
                fed = collective_world(root, 2, chain=True)
            chunk = sorted(set(fed.supporting_sources) - {WORLD_DATA_FILE})[0]
            public = root/'Public.lean'; public.write_text('sentinel')
            original = Path.write_text
            for fault in ('exception', 'omit', 'tamper', 'extra'):
                def write(path, text, *args, **kwargs):
                    if path.name == chunk:
                        if fault == 'exception': raise OSError('injected')
                        if fault == 'omit': return 0
                        if fault == 'tamper': text += '-- tamper\n'
                        if fault == 'extra': original(path.parent/'Extra.lean', '-- extra\n')
                    return original(path, text, *args, **kwargs)
                with patch.object(Path, 'write_text', write):
                    with self.assertRaises((ValueError, OSError)):
                        publish(fed, root/fault/'World.lean')
                self.assertFalse((root/fault).exists())
            support = dict(fed.supporting_sources)
            support[chunk] += '\naxiom forged : True\n'
            receipt = dict(fed.receipt, proof_bundle=_proof_bundle(fed.lean, support))
            with self.assertRaises(ValueError):
                publish(replace(fed, supporting_sources=support, receipt=receipt), root/'axiom'/'World.lean')
            self.assertEqual(public.read_text(), 'sentinel')
            self.assertFalse(list(root.glob('trainverify-world-*')))

    def test_oversized_atomic_group_fails_closed(self):
        with tempfile.TemporaryDirectory() as d:
            with patch.object(prefix, 'PROOF_DECLARATION_BUDGET', 1, create=True):
                with self.assertRaisesRegex(ValueError, 'budget'):
                    collective_world(Path(d), 2)


if __name__ == '__main__': unittest.main()
