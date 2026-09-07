"""Generated read points must consume independently retained prepared producers."""
from copy import deepcopy
import json
import unittest
from test_runtime_source_adapters import adapter_fixture


def baseline():
    from nnscaler_backend.runtime_source_authority import capture_adapter_source, export_expanded_cells
    from nnscaler_backend.build_graph import _fuse_collective_inputs
    world, cells, sources = adapter_fixture()
    evidence = capture_adapter_source(cells)
    _fuse_collective_inputs(cells)
    return export_expanded_cells(world, cells, rank_sources=sources, adapter_source=evidence)


class GeneratedReadpointTests(unittest.TestCase):
    def test_preparation_constants_are_positional_not_generated_keywords(self):
        from nnscaler_backend.build_graph import _set_node_kwargs, _fuse_collective_inputs
        from nnscaler_backend.runtime_source_authority import capture_adapter_source, export_expanded_cells
        from trainverify.runtime_source_authority import validate_snapshot
        world, cells, sources = adapter_fixture()
        # Exercise the real pass which adds the reserved __consts metadata.
        for c in cells:
            if c.ir is not None:
                c._input_consts = list(c.ir.inputs()) if c.node.irname == 'producer' else []
        _set_node_kwargs(cells)
        evidence = capture_adapter_source(cells)
        _fuse_collective_inputs(cells)
        snapshot = export_expanded_cells(world, cells, rank_sources=sources, adapter_source=evidence)
        validate_snapshot(snapshot)
        self.assertEqual(snapshot['adapter_generated_read_binding'], 'complete')
        for row in evidence:
            if 'generated_producer' in row:
                self.assertNotIn('__consts', row['generated_producer']['kwargs'])
                self.assertEqual(row['generated_producer']['inputs'], ['(4, 8)'])

    def test_unsupported_direct_writes_cannot_retain_complete(self):
        from trainverify.runtime_source_authority import bind_adapters, validate_snapshot
        for form in ('nested_target', 'named_expression', 'nested_named_expression', 'chained_unpacking', 'tuple_delete'):
            s = baseline()
            row = s['adapter_source'][1]
            name = row['primitive']['generated_inputs'][0]
            rank = str(row['ref']['runtime_rank'])
            insertion = {
                'nested_target': f'({name},), ignored = (({name} + 1,), 0)',
                'chained_unpacking': f'{name}, ignored = alias = ({name} + 1, 0)',
                'tuple_delete': f'del ({name},)',
                'named_expression': f'ignored = ({name} := {name} + 1)',
                'nested_named_expression': f'ignored = (({name} := {name} + 1), 0)',
            }[form]
            line = f'        {name} = torch.empty((4, 8))\n'
            self.assertIn(line, s['rank_sources'][rank])
            s['rank_sources'][rank] = s['rank_sources'][rank].replace(
                line, line + '        ' + insertion + '\n')
            bind_adapters(s, allow_translation_mismatch=True)
            validate_snapshot(s)
            with self.subTest(form=form):
                self.assertNotEqual(s['adapter_generated_read_binding'], 'complete')
                self.assertIn('generated-adapter-reaching-definitions', s['completeness']['missing'])

    def test_mutations_recompute_current_definition(self):
        from trainverify.runtime_source_authority import bind_adapters
        for mutation in ('replace', 'wrong_producer', 'future', 'other_method'):
            s = baseline()
            row = s['adapter_source'][1]
            name = row['primitive']['generated_inputs'][0]
            rank = str(row['ref']['runtime_rank'])
            text = s['rank_sources'][rank]
            line = f'        {name} = torch.empty((4, 8))\n'
            if mutation == 'replace': text = text.replace(line, f'        {name} = {name} + 1\n')
            elif mutation == 'wrong_producer': text = text.replace('torch.empty', 'torch.ones')
            elif mutation == 'future': text = text.replace(line, '') + line
            else: text = text.replace(line, '') + f'    def unrelated(self):\n{line}'
            s['rank_sources'][rank] = text
            with self.subTest(mutation=mutation), self.assertRaisesRegex(ValueError, 'reaching definition'):
                bind_adapters(s)

    def test_duplicate_producer_in_another_method_is_ambiguous(self):
        from trainverify.runtime_source_authority import bind_adapters
        s = baseline()
        row = s['adapter_source'][1]
        rank = str(row['ref']['runtime_rank'])
        name = row['primitive']['generated_inputs'][0]
        s['rank_sources'][rank] += f'    def unrelated(self):\n        {name} = torch.empty((4, 8))\n'
        bind_adapters(s)
        self.assertEqual(s['adapter_generated_read_binding'], 'missing')

    def test_unreachable_read_is_not_bound(self):
        from trainverify.runtime_source_authority import bind_adapters
        s = baseline()
        rank = str(s['adapter_source'][1]['ref']['runtime_rank'])
        s['rank_sources'][rank] = s['rank_sources'][rank].replace('def forward(self):', 'def forward(self):\n        return')
        bind_adapters(s)
        self.assertEqual(s['adapter_generated_read_binding'], 'missing')

    def test_retained_rejection_is_not_complete_value_authority(self):
        from trainverify.runtime_source_authority import bind_adapters, validate_snapshot
        s = baseline()
        rank = str(s['adapter_source'][1]['ref']['runtime_rank'])
        s['rank_sources'][rank] = s['rank_sources'][rank].replace('torch.empty', 'torch.ones')
        bind_adapters(s, allow_translation_mismatch=True)
        self.assertEqual(s['adapter_generated_binding'], 'complete')
        self.assertEqual(s['adapter_generated_read_binding'], 'rejected')
        self.assertIn('generated-adapter-reaching-definitions', s['completeness']['missing'])
        validate_snapshot(json.loads(json.dumps(s)))

    def test_supported_reuse_selects_second_source_version(self):
        from trainverify.runtime_source_authority import bind_adapters, build_snapshot, writer_export_id
        s = baseline()
        for index in reversed(range(0, len(s['adapter_source']), 2)):
            prior = s['adapter_source'][index]
            producer = deepcopy(prior)
            producer['ref']['source_cid'] += 1
            producer['outputs'][0]['version'] += 1
            s['adapter_source'][index + 1]['inputs'] = deepcopy(producer['outputs'])
            s['adapter_source'].insert(index + 1, producer)
            w = deepcopy(s['writers'][index]); w['ref'] = deepcopy(producer['ref']); w['outputs'] = deepcopy(producer['outputs'])
            s['writers'].insert(index + 1, w)
            rank = str(producer['ref']['runtime_rank'])
            name = producer['generated_producer']['outputs'][0]
            line = f'        {name} = torch.empty((4, 8))\n'
            s['rank_sources'][rank] = s['rank_sources'][rank].replace(line, line + line)
        for w in s['writers']:
            if 'adapter' in w:
                for ref in w['inputs']: ref['version'] = 2
        s['tensors'] = build_snapshot(s['writers'])['tensors']
        bind_adapters(s)
        for w in s['writers']:
            if 'adapter' in w:
                p, = w['adapter']['generated_read_points']
                self.assertEqual(p['definition_ordinal'], 2)
                self.assertEqual(p['ref']['version'], 2)
                self.assertIn(',11,', p['writer'])

    def test_arithmetic_redefinition_is_not_the_prepared_writer(self):
        from trainverify.runtime_source_authority import bind_adapters, validate_snapshot
        s = baseline()
        validate_snapshot(json.loads(json.dumps(s)))
        self.assertEqual(s['adapter_generated_binding'], 'complete')
        row = s['adapter_source'][1]
        name = row['primitive']['generated_inputs'][0]
        rank = str(row['ref']['runtime_rank'])
        s['rank_sources'][rank] = s['rank_sources'][rank].replace(
            f'{name} = torch.empty((4, 8))', f'{name} = torch.empty((4, 8))\n        {name} = {name} + 1')
        with self.assertRaisesRegex(ValueError, 'reaching definition'):
            bind_adapters(s)
