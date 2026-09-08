"""Whole-world checked input entry, with actual CPU-observed mixed requests."""
import tempfile
from pathlib import Path
import unittest
from Verdict.runtime_world import render
from Verdict.runtime_input_feed import bind
from scripts.tests.test_runtime_input_feed import observed
from scripts.tests.test_runtime_schedule import cross_rank


def mixed_world(root, k):
    authority = observed(root, 1, k)
    sv, pv, rs, rp = cross_rank(k)
    legacy = render(sv, pv, rs, rp)
    return legacy, bind(legacy, sv, pv, rs, rp, *authority, root)



def negative_schedule_witnesses():
    """Nonvacuous bad schedules over the same held-out world, checked by Lean."""
    lines = ['namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
             'open SourceScopedEval', 'set_option maxHeartbeats 500000',
             'set_option maxRecDepth 4096']
    for label in ('sm', 'pm'):
        lines += [f'def {label}DuplicateGraph : GraphDecl := {{ {label}Graph with nodes := {label}Graph.nodes ++ [{label}Node_0] }}']
        for fault, graph, requests in (
            ('reordered', label+'Graph', label+'InputRequests.reverse'),
            ('omitted', label+'Graph', label+'InputRequests.tail'),
            ('duplicate', label+'DuplicateGraph', f'({label}InputRequests ++ [({label}Node_0, none)])')):
            name = label+'_'+fault
            lines += [f'theorem {name}_invalid : ¬ InputSchedule {graph}.nodes {requests} := by decide +kernel',
                      f'#print axioms {name}_invalid',
                      f'theorem {name}_checked_none (s : Store) : runWithInputs {graph} {label}Scope {label}Peers {graph}.nodes (some {requests}) (some s) = none := by',
                      '  unfold runWithInputs', f'  exact if_neg {name}_invalid',
                      f'#print axioms {name}_checked_none']
    return '\n'.join(lines + ['end', 'end TrainVerify.Denote.RuntimeWorld', ''])

class InputScheduleKernelTests(unittest.TestCase):
    def test_complete_schedule_and_checked_entry_are_emitted(self):
        for k in (2, 3):
            with self.subTest(k=k), tempfile.TemporaryDirectory() as d:
                legacy, fed = mixed_world(Path(d), k)
                self.assertTrue(fed.lean.startswith(legacy.lean))
                for label in ('sm', 'pm'):
                    name = label + 'InputSchedule_valid'
                    self.assertIn(f'theorem {name} : SourceScopedEval.InputSchedule {label}Graph.nodes {label}InputRequests', fed.lean)
                    self.assertIn(f'theorem {label}DenoteWithInputs_entry (s : Store)', fed.lean)
                    self.assertIn(name, fed.receipt['input_feed']['kernel_checks'])
                    self.assertIn(f'#print axioms {label}DenoteWithInputs_entry', fed.lean)
                self.assertFalse(fed.receipt['input_feed']['whole_world_option_success'])
                self.assertFalse(fed.receipt['input_feed']['kernel_value_proved'])


if __name__ == '__main__': unittest.main()
