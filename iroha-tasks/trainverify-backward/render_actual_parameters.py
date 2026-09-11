"""Select backward parameter projections from the accepted canonical contract.

The inventory chooses conjunction positions only. Importing the exact accepted
RuntimeWorld and kernel checking are mandatory: the metadata proves no relation.
The shared original-run parameter frame is reused, never reimplemented.
"""
import json
from pathlib import Path
from reuse_forward_entry import main as reuse
ROOT = Path(__file__).resolve().parents[2]
BASE = Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/dp-prefix-cost-closure/output-projection/actual-output-projection1')


def render(goals, requested_tids, weight_tid):
    def select(i):
        return 'h' + '.2' * i + ('.1' if i < len(goals) - 1 else '')
    proofs = ['theorem backwardParameterValuesFinal (s p t q : Store)',
              '    (hs : smSeededDenoteWithInputs s = some t)',
              '    (hp : pmSeededDenoteWithInputs p = some q)',
              '    (h : InitialParameterValues (smInitialWithSeeds s) (pmInitialWithSeeds p)) :',
              '    InitialParameterValues t q :=',
              '  initialParameterValues_final (smInitialWithSeeds s) (pmInitialWithSeeds p) t q hs hp h',
              '#print axioms backwardParameterValuesFinal']
    for tid in requested_tids:
        i = next(i for i, g in enumerate(goals) if g['sm_tid'] == tid)
        proofs += [f'theorem backwardParameterShape_{tid} (t q : Store) (h : InitialParameterValues t q) :',
                   f"    (t {tid}).shape = {goals[i]['sm_shape']} := {select(i)}.1",
                   f'#print axioms backwardParameterShape_{tid}']
    for i, g in enumerate(goals):
        if g['sm_tid'] != weight_tid:
            continue
        if g['kind'] != 'sharded' or g['dim'] != 0:
            raise ValueError('backward dX requires output-row weight sharding')
        tids = g['pm_tids']
        xs = '[' + ', '.join(f'q {tid}' for tid in tids) + ']'
        name = f'backwardWeightUnit_{tids[0]}'
        proofs += [f'theorem {name} (t q : Store) (h : InitialParameterValues t q) :',
                   f"    RelationCompiler.ShardedRel (t {weight_tid}) {xs} 0 {g['sm_shape']} {g['pm_shape']} := by",
                   '  have h := initialParameterRelations_of_values t q h',
                   f'  exact {select(i)}', f'#print axioms {name}']
    return '\n'.join(proofs) + '\n'


def main():
    reuse()
    receipt = json.loads((BASE / 'world-receipt.json').read_text())
    goals = [unit['initial_goal'] for row in receipt['initial_relations']['relations'] for unit in row['units']]
    # This exact-capture projection is a replay caller, not a model dispatch rule.
    needed = [1212, 1213, 1219, 1222, 1223, 1229, 1232, 1233, 1236]
    text = render(goals, needed, 1236)
    out = ROOT / '.hermes/backward-kernel/ActualBWParameters.lean'
    out.write_text('import RuntimeWorld\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\n' + text + 'end\nend TrainVerify.Denote.RuntimeWorld\n')
    print(out)

if __name__ == '__main__':
    main()
