"""Portable ctx-source checks; no capture file or distributed execution."""
import ast
from copy import deepcopy
import inspect
from pathlib import Path
import sys
import textwrap
import unittest
ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT), str(ROOT / 'Verdict')]


def actual_runtime(name):
    from nnscaler.runtime.adapter import nn
    wrapper = getattr(nn, name)
    source = textwrap.dedent(inspect.getsource(wrapper))
    dispatch = ast.parse(source).body[0].body[0].value
    cls = wrapper.__globals__[dispatch.func.value.id]
    return dict(wrapper_source=source, class_source=textwrap.dedent(inspect.getsource(cls)),
                class_name=cls.__name__, source_file=inspect.getsourcefile(cls),
                backward_global_functions={n: dict(module=f.__module__, name=f.__name__,
                    source_file=inspect.getsourcefile(f)) for n in cls.backward.__code__.co_names
                    if inspect.isfunction(f := cls.backward.__globals__.get(n))})


class BackwardContextTests(unittest.TestCase):
    def test_actual_dispatch_context_and_dimension_order(self):
        from trainverify.runtime_source_authority import _runtime_autograd_context
        for name, fw, bw, kwargs in (
            ('alltoall_alltoall', 'AllToAllPrim', 'AllToAllPrim', dict(idim=1, odim=2, ranks=[3, 2])),
            ('allgather_reducescatter', 'AllGatherPrim', 'ReduceScatterPrim', dict(dim=1, ranks=[3, 2])),
        ):
            with self.subTest(name=name):
                runtime = actual_runtime(name)
                out = _runtime_autograd_context(runtime, dict(signature='nnscaler.runtime.adapter.nn.'+name, kwargs=kwargs))
                self.assertEqual(out['forward']['op'], fw)
                self.assertEqual(out['backward']['op'], bw)
                self.assertEqual(out['ctx_slots']['_ranks'], [3, 2])
                self.assertEqual(out['forward']['kwargs'], kwargs)
                expected = dict(kwargs)
                if name == 'alltoall_alltoall':
                    expected.update(idim=2, odim=1)
                    self.assertEqual(out['class_name'], 'AllToAllAllToAllSingle')
                    self.assertEqual(out['backward']['function'], 'all_to_all_single')
                self.assertEqual(out['backward']['kwargs'], expected)
                self.assertEqual(out['backward']['tensor'], 'output-gradient')

    def test_dispatch_argument_effect_cannot_be_hidden_by_forward_assignment(self):
        from trainverify.runtime_source_authority import _runtime_autograd_context
        runtime = actual_runtime('alltoall_alltoall')
        call = dict(signature='nnscaler.runtime.adapter.nn.alltoall_alltoall',
                    kwargs=dict(idim=1, odim=2, ranks=[3, 2]))
        _runtime_autograd_context(runtime, call)
        runtime['wrapper_source'] = runtime['wrapper_source'].replace(
            '.apply(itensor, idim, odim, ranks)',
            '.apply(itensor, all_to_all_single(itensor, idim, odim, [999]), odim, ranks)')
        runtime['class_source'] = runtime['class_source'].replace(
            'ctx._ranks = ranks', 'idim = 1\n        ctx._ranks = ranks', 1)
        with self.assertRaises(ValueError):
            _runtime_autograd_context(runtime, call)

    def test_unused_collective_effect_is_not_discarded(self):
        from trainverify.runtime_source_authority import _runtime_autograd_context
        runtime = actual_runtime('alltoall_alltoall')
        call = dict(signature='nnscaler.runtime.adapter.nn.alltoall_alltoall',
                    kwargs=dict(idim=1, odim=2, ranks=[3, 2]))
        _runtime_autograd_context(runtime, call)
        for phase in ('forward', 'backward'):
            bad = deepcopy(runtime)
            if phase == 'backward':
                old = 'grad = all_to_all_single(grad, odim, idim, ranks)'
                new = 'unused = all_to_all_single(grad, idim, odim, [999])\n        ' + old
            else:
                old = 'return all_to_all_single(itensor, idim, odim, ranks)'
                new = 'unused = all_to_all_single(itensor, idim, odim, [999])\n        ' + old
            self.assertIn(old, bad['class_source'])
            bad['class_source'] = bad['class_source'].replace(old, new)
            with self.subTest(phase=phase), self.assertRaises(ValueError):
                _runtime_autograd_context(bad, call)

    def test_changed_dispatch_or_collective_source_cannot_match(self):
        from trainverify.runtime_source_authority import _runtime_autograd_context
        runtime = actual_runtime('alltoall_alltoall')
        call = dict(signature='nnscaler.runtime.adapter.nn.alltoall_alltoall', kwargs=dict(idim=1, odim=2, ranks=[3, 2]))
        for change in ('dispatch', 'function', 'control_flow'):
            bad = deepcopy(runtime)
            if change == 'dispatch':
                bad['wrapper_source'] = bad['wrapper_source'].replace('AllToAllAllToAllSingle.apply', 'Other.apply')
            elif change == 'function':
                bad['class_source'] = bad['class_source'].replace('grad = all_to_all_single(', 'grad = all_reduce(')
            else:
                bad['class_source'] = bad['class_source'].replace('ranks = ctx._ranks', 'if True: pass\n        ranks = ctx._ranks')
            self.assertNotEqual(bad, runtime)
            with self.subTest(change=change), self.assertRaises(ValueError):
                _runtime_autograd_context(bad, call)


if __name__ == '__main__':
    unittest.main()
