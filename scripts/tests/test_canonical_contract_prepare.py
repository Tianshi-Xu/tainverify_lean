"""Preparation is source-only; these fixtures never invoke Lean."""
import hashlib
import importlib
import json
from pathlib import Path
import tempfile
import unittest
from trainverify.artifact_tools import Configuration


def api():
    try:
        return importlib.import_module('trainverify.canonical_contract_prepare')
    except ModuleNotFoundError:
        return None


class PinnedReadTests(unittest.TestCase):
    def test_original_digest_is_checked_after_explicit_relocation(self):
        module = api()
        self.assertIsNotNone(module, 'manifest-driven preparer is missing')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / 'relocated.json'
            target.write_text('{"value": 3}')
            pin = dict(path='/retired/input.json', sha256=hashlib.sha256(target.read_bytes()).hexdigest())
            config = Configuration(dict(version=1, relocations=[dict(kind='file', source=pin['path'], target=str(target))],
                binding_sets=[dict(path=str(target), sha256=pin['sha256'], field=[], base=None)], lean=None))
            reader = module.PinnedInputs(config)
            self.assertEqual(reader.json(pin), {'value': 3})
            self.assertEqual(reader.bound[pin['path']]['resolved'], str(target))
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                reader.json(dict(pin, sha256='0' * 64))


class JointTests(unittest.TestCase):
    def fixture(self):
        from trainverify.artifact_tools import render_joint
        row = dict(theorem='freshUnit', facts_theorem='freshUnit', dimensions={'D': 1, 'T': 2},
                   unit=0, ranks=[0, 1], sm_output_tid=8, pm_output_tids=[9, 10],
                   global_shape=[1, 4], local_shape=[1, 4], layout='replicated_within_dp', gather_axis=None)
        generated = render_joint([row], 'Accepted')
        header = generated.split('theorem projectionFrontierJoint ', 1)[1].split(' := by', 1)[0]
        binders, prop = header.split(') :\n', 1)
        binders += ')'
        seed = dict(anchor='oldAll', instance='oldAll_inhabited', prelude='  have hs := seedLeft\n  have hp := seedRight\n',
                    arguments=dict(s='startLeft', p='startRight', t='finalLeft', q='finalRight', hs='hs', hp='hp', hvalues='seedValues'),
                    read_worlds=dict(sm=dict(initial='s', final='t', hypothesis='hs', run='smDenoteWithInputs'),
                                     pm=dict(initial='p', final='q', hypothesis='hp', run='pmDenoteWithInputs')))
        old = 'import RuntimeWorld\nnamespace Example.World\n'
        old += 'theorem oldAll '+binders+' :\n    True := by\n  trivial\n#print axioms oldAll\n'
        old += 'theorem oldAll_inhabited :\n    True := by\n'+seed['prelude']+'  exact oldAll startLeft startRight finalLeft finalRight hs hp seedValues\n#print axioms oldAll_inhabited\n'
        old += 'end Example.World\nrun_cmd do\n  pure ()\n'
        source = 'import Accepted\nnamespace Example.World\n'
        source += 'theorem freshRead (s t : Store) (h : smDenoteWithInputs s = some t) :\n    t 8 = t 7 := by\n  rfl\n#print axioms freshRead\n'
        source += 'theorem freshUnit '+header+' := by\n  exact independent\n#print axioms freshUnit\nend Example.World\n'
        detail = dict(reads=[dict(theorem='freshRead', world='sm')], units=[row], frontier_units=[row], retained_units=[], deferred_units=[])
        stage = dict(pair='newPair', cumulative='newAll')
        return old, source, detail, seed, stage

    def test_reopened_old_namespace_is_byte_preserved(self):
        old, source, detail, seed, stage = self.fixture()
        old = old.replace('namespace Example.World\n', 'namespace Example.World\nend Example.World\nnamespace Example.World\n', 1)
        result = api().extend_joint(old, source, detail, 'Example.World', seed, stage, 'oldAll')
        self.assertTrue(result.startswith(old.rsplit('end Example.World\n', 1)[0]))

    def test_local_shape_bound_variable_alpha_equivalence(self):
        old, source, detail, seed, stage = self.fixture()
        source = source.replace('(∀ y ∈ [q 9, q 10], y.shape', '(∀ z ∈ [q 9, q 10], z.shape')
        self.assertIn('z.shape', api().extend_joint(old, source, detail, 'Example.World', seed, stage, 'oldAll'))

    def test_indented_published_declarations_are_counted(self):
        self.assertEqual(api().names(' theorem compact : True := by trivial\n'), ['compact'])

    def test_legacy_term_proofs_without_adjacent_observer(self):
        source = 'theorem first : True :=\n  trivial\ntheorem second : True := by\n  trivial\n#print axioms first\n#print axioms second\n'
        self.assertEqual(api().declarations(source)['first'][0], ': True')
        self.assertIn('trivial', api().declarations(source)['second'][1])

    def test_preparation_transaction_and_coordinated_deletion(self):
        module = api()
        self.assertTrue(hasattr(module, 'prepare'), 'manifest preparation is missing')
        import copy
        from trainverify.artifact_tools import render_joint
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def pin(name, value):
                p = root / name
                raw = value.encode() if isinstance(value, str) else json.dumps(value).encode()
                p.write_bytes(raw)
                return dict(path=str(p), sha256=hashlib.sha256(raw).hexdigest())
            old, source, detail, seed, stage = self.fixture()
            ns = 'Example.World.'
            entry = 'import Support\nnamespace Example.World\ntheorem baseline : True := by\n  trivial\n#print axioms baseline\nend Example.World\n'
            ep = pin('RuntimeWorld.lean', entry)
            full = pin('full.json', {ns+'baseline': '[]|Expr.baseline', '_private.RuntimeWorld.0.hidden': '[]|Expr.private'})
            joint = pin('joint.json', {ns+n: '[]|Expr.'+n for n in ['oldAll', 'oldAll_inhabited']})
            jp = pin('Joint.lean', old)
            receipt = dict(fullrefs={'sm': [1], 'pm': [2]}, execution_order={'sm': [0], 'pm': [0]},
                           proof_bundle={'modules': [dict(module='RuntimeWorld', file='RuntimeWorld.lean', source_sha256=ep['sha256'], theorems=['baseline'])]})
            prep = pin('preparation.json', dict(public_targets=[ns+'baseline'], private_targets=['_private.RuntimeWorld.0.hidden'], joint_targets=list(json.loads((root/'joint.json').read_text())), outputs={jp['path']: jp['sha256']}))
            completion = pin('complete.json', dict(verified=True, full_contracts=2, joint_theorems=2, files={full['path']: full['sha256'], joint['path']: joint['sha256']}))
            world = pin('world.json', dict(world_fullrefs=receipt['fullrefs'], execution_order=receipt['execution_order'], bound={'initial': 1}))
            sp = pin('Fragment.lean', source)
            local = pin('LocalJoint.lean', render_joint(detail['frontier_units'], 'Fragment').replace('TrainVerify.Denote.RuntimeWorld', 'Example.World'))
            obj = pin('Fragment.olean', 'synthetic object, not a Lean result')
            dep = pin('Support.olean', 'synthetic dependency')
            def kernel(name, src, axioms):
                return pin(name, dict(inner_exit=0, source=src['path'], source_sha256=src['sha256'], object=obj['path'], object_sha256=obj['sha256'], dependency_objects={dep['path']: dep['sha256']}, axioms={n: [] for n in axioms}))
            recipe = dict(version=1, namespace='Example.World', base_module='RuntimeWorld',
                base=dict(receipt=pin('receipt.json', receipt), preparation=prep, complete=completion, full_records=full, joint_records=joint, joint_source=jp, world=world),
                seed=seed, previous='oldAll', stages=[dict(source=sp, detail=pin('detail.json', detail), world=world,
                    kernel=kernel('kernel.json', sp, [ns+'freshRead', ns+'freshUnit']), joint_source=local,
                    joint_kernel=kernel('joint-kernel.json', local, [ns+'projectionFrontierJoint']),
                    first_import='Accepted', module='ReferenceA', pair=stage['pair'], cumulative=stage['cumulative'])])
            config = Configuration(dict(version=1, relocations=[], binding_sets=[dict(path=full['path'], sha256=full['sha256'], field=[], base=None)], lean=None))
            rp = pin('recipe.json', recipe)
            out = root / 'output'
            report = module.prepare(config, rp, str(out))
            self.assertEqual(report['old_full_preserved'], 2)
            self.assertEqual(report['old_joint_preserved'], 2)
            self.assertEqual(report['counts'], dict(public=3, full=4, joint=8))
            self.assertFalse(report['kernel_verified'])
            self.assertEqual((out/'baseline/full-types.json').read_bytes(), (root/'full.json').read_bytes())
            self.assertEqual((out/'reference/ReferenceA.lean').read_text(), source.replace('import Accepted\n', 'import RuntimeWorld\n', 1))
            with self.assertRaises(FileExistsError): module.prepare(config, rp, str(out))
            # Even with a rehashed detail and fragment, the independent kernel census closes deletion.
            bad = copy.deepcopy(recipe)
            bad['stages'][0]['detail'] = pin('bad-detail.json', dict(detail, reads=[]))
            block = source.split('theorem freshRead ', 1)[1].split('#print axioms freshRead\n', 1)[0]
            badsource = source.replace('theorem freshRead '+block+'#print axioms freshRead\n', '')
            bad['stages'][0]['source'] = pin('bad-source.lean', badsource)
            with self.assertRaises(ValueError): module.prepare(config, pin('bad-recipe.json', bad), str(root/'rejected'))
            self.assertFalse((root/'rejected').exists())

    def test_append_preserves_body_and_full_replica_contract(self):
        module = api()
        self.assertTrue(hasattr(module, 'extend_joint'), 'joint extension is missing')
        old, source, detail, seed, stage = self.fixture()
        result = module.extend_joint(old, source, detail, 'Example.World', seed, stage, 'oldAll')
        self.assertTrue(result.startswith(old.split('end Example.World')[0]))
        self.assertIn('∀ y ∈ [finalRight 9, finalRight 10], y = chunkPrimDimN', result)
        self.assertIn('y.shape = [1, 4]', result)
        self.assertIn('audit_freshRead', result)
        self.assertIn('newPair_inhabited', result)
        self.assertIn('newAll_inhabited', result)
        self.assertNotIn('run_cmd', result)
        for mutation in ('mapping', 'missing', 'duplicate', 'premise', 'replica_axis'):
            import copy
            o, s, d, se, st = copy.deepcopy((old, source, detail, seed, stage))
            if mutation == 'mapping': se['arguments']['unused'] = 'x'
            if mutation == 'missing': d['reads'] = []
            if mutation == 'duplicate': d['reads'] *= 2
            if mutation == 'premise': s = s.replace('(hvalues : InitialParameterValues s p)', '(hvalues : InitialParameterValues s p) (extra : True)')
            if mutation == 'replica_axis': d['frontier_units'][0]['gather_axis'] = 0
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                module.extend_joint(o, s, d, 'Example.World', se, st, 'oldAll')


if __name__ == '__main__':
    unittest.main()
