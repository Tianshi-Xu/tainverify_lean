"""Portable real IR data/segment fixture: no generated runtime execution mock."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT), str(ROOT / 'Verdict'), str(Path(__file__).parent)]


def baseline():
    from test_runtime_source_chunk_scope import fixture
    from nnscaler.ir.operator import IRDataOperation
    from nnscaler.ir.cten import IRObject
    from nnscaler.graph.segment import IRSegment
    from nnscaler.codegen.emit import CodeEmission
    from nnscaler_backend.runtime_source_authority import capture_adapter_source, export_expanded_cells
    from verdict.operators import OpName
    world, cells, sources = fixture()
    p, c = cells
    x = p._output_irs[0]
    loader = IRObject('loader')
    import torch
    from nnscaler.ir.tensor import IRFullTensor
    from nnscaler_backend.dfg import Tensor
    z = IRFullTensor((4, 8), name='second', dtype=torch.float32).tosub()
    p.outputs.append(Tensor('p', 2, 0, z.tid, 1))
    p._output_irs.append(z)
    p.ir = IRDataOperation(loader, (x, z))
    p.opname = OpName.DATALOADER
    from nnscaler.ir.adapter.adapter import IRAdapter
    adapter = IRAdapter([x], list(c.ir.outputs()))
    adapter.prims = [c.ir]
    segment = IRSegment([adapter], [x, z], list(c.ir.outputs()), name='portable_segment')
    emit = CodeEmission()
    method = emit.node_name(segment)
    name = emit.tensor_name(x)
    second = emit.tensor_name(z)
    sources[2] = sources[2].replace('def forward(self):', f'def {method}(self, {name}, {second}):').replace(f'        {name} = torch.empty((4, 8))\n', '')
    sources[2] += f'''\ndef _train_step(model, {emit.tensor_name(loader)}):
    _ = None
    model.zero_grad()
    {name}, {second} = next(*({emit.tensor_name(loader)},))
    result = nnscaler.runtime.executor.fexecute('{method}', model.{method}, *({name}, {second},), requires_grad=True)
    return result

def _infer_step(model, loader):
    return nnscaler.runtime.executor.fexecute('{method}', model.{method}, *(other,), requires_grad=False)
'''
    # Source sequence consists of actual IR nodes, independently of Python AST.
    source = capture_adapter_source(cells, training_sequences={2: [p.ir, segment]})
    return export_expanded_cells(world, cells, rank_sources=sources, adapter_source=source)


class DataloaderReadTests(unittest.TestCase):
    def test_real_ir_training_chain(self):
        from trainverify.runtime_source_authority import validate_snapshot
        s = baseline()
        c = s['writers'][1]['chunk_scope']
        self.assertEqual(c.get('training_call_binding'), 'bound', c.get('generated_read_missing'))
        point = c['training_call_points'][0]
        self.assertEqual(point['training_scope'], '_train_step only; inference unclaimed')
        self.assertEqual(point['ref'], s['writers'][0]['outputs'][0])
        # Actual fexecute synchronizes through a handler that may substitute
        # tensors; static call alignment must not silently seed value authority.
        self.assertEqual(c['generated_read_binding'], 'missing')
        self.assertIn('AsyncCommHandler.wait', c['generated_read_missing'])
        self.assertEqual(s['chunk_scope_generated_read_binding'], 'missing')
        self.assertFalse(s['proof_admissible'])
        validate_snapshot(s)

    def test_training_mutations_fail_closed(self):
        from trainverify.runtime_source_authority import bind_adapters
        for mutation in ('wrongloader', 'wrongmethod', 'before_call', 'before_chunk', 'repeat', 'hidden_next', 'hidden_fexecute', 'controlflow', 'arguments', 'tuple', 'parameters', 'alias_inplace', 'call_instance', 'unit', 'mb', 'version', 'ordinal', 'delete_parameter', 'overwrite_delete_parameter'):
            with self.subTest(mutation=mutation):
                s = baseline()
                text = s['rank_sources']['2']
                train = text.index('def _train_step')
                prefix, schedule = text[:train], text[train:]
                name = s['adapter_source'][1]['primitive']['generated_inputs'][0]
                evidence = s['adapter_source'][0]['generated_dataloader']
                second = evidence['outputs'][1]
                if mutation == 'wrongloader': schedule = schedule.replace('next(*(' + evidence['loader'], 'next(*(wrong_loader')
                elif mutation in ('call_instance', 'unit', 'mb', 'ordinal'):
                    key = {'unit': 'runtime_rank', 'mb': 'microbatch'}.get(mutation, mutation)
                    evidence['training_calls'][0][key] += 1
                elif mutation == 'version': evidence['training_calls'][0]['input_refs'][0]['version'] += 1
                elif mutation == 'arguments': schedule = schedule.replace(f'*({name}, {second},)', f'*({second}, {name},)', 1)
                elif mutation == 'tuple': schedule = schedule.replace(f'{name}, {second} = next', f'{second}, {name} = next')
                elif mutation == 'parameters': prefix = prefix.replace(f'self, {name}, {second}', f'self, {second}, {name}')
                elif mutation == 'alias_inplace': prefix = prefix.replace('        y_', f'        ignored = {name}.add_(1)\n        y_')
                elif mutation in ('delete_parameter', 'overwrite_delete_parameter'):
                    before = f'        del {name}\n'
                    if mutation == 'overwrite_delete_parameter':
                        before = f'        {name} = other\n' + before
                    prefix = prefix.replace('        y_', before + '        y_')
                elif mutation == 'wrongmethod': schedule = schedule.replace('model.portable_segment', 'model.wrong_segment')
                elif mutation == 'before_call': schedule = schedule.replace('    result = ', f'    {name} = other\n    result = ', 1)
                elif mutation == 'before_chunk': prefix = prefix.replace('        y_', f'        {name} = other\n        y_')
                elif mutation == 'repeat':
                    line = next(x for x in schedule.splitlines() if 'result = ' in x)
                    schedule = schedule.replace(line, line + '\n' + line)
                elif mutation == 'hidden_next': schedule = schedule.replace('next(*(', 'next(*(side_effect(), ')
                elif mutation == 'hidden_fexecute': schedule = schedule.replace('requires_grad=True', 'requires_grad=side_effect()')
                elif mutation == 'controlflow': schedule = schedule.replace('    result = ', '    if True:\n        result = ', 1)
                s['rank_sources']['2'] = prefix + schedule
                try:
                    bind_adapters(s, allow_translation_mismatch=True)
                except (ValueError, SyntaxError):
                    continue
                self.assertNotEqual(s['chunk_scope_generated_read_binding'], 'complete')
                self.assertNotEqual(s['writers'][1]['chunk_scope'].get('training_call_binding'), 'bound')


if __name__ == '__main__':
    unittest.main()
