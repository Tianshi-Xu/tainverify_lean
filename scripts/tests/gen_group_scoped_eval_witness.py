#!/usr/bin/env python3
"""Deterministic CPU torch.chunk values; supported positive divisible dim=1 only.
No claim about ragged chunks, runtime process-group ordering, or source authority.
Run with the capture venv's Python; --check compares exact generated UTF-8 bytes.
"""
import argparse
import re
from pathlib import Path
import torch


def generate():
    torch.set_num_threads(1)
    x = torch.tensor([[i*i+3*i+7 for i in range(r*12,(r+1)*12)] for r in range(2)], dtype=torch.int64)
    text = ['import denote.GroupScopedEval', 'namespace TrainVerify.Denote.GroupScopedEval.Witness',
            'set_option maxHeartbeats 500000', 'noncomputable section',
            'def x : Tensor := Tensor.mkShape [2, 12] (fun i => ((i.val*i.val+3*i.val+7 : Nat) : Scalar))',
            'def s : Store := fun _ => x', 'def g : GraphDecl := {numRanks := 4, nodes := []}',
            'def node (rank : Nat) : NodeDecl := {rank := rank, op := "OpName.ChunkPrim", ins := [10], outs := [20], params := [1]}']
    cases = [('rank2', [2,3],2),('rank3',[2,3],3),('noncontiguous',[0,2],2),('k1',[3],3),('k3',[0,1,3],3)]
    for name,rs,rank in cases:
        k=len(rs); idx=rs.index(rank)
        assert x.shape[1] % k == 0
        ys=torch.chunk(x,k,dim=1); values=ys[idx].flatten().tolist()
        text += [f'theorem {name}_resolved : resolve 4 {rank} (some {rs}) = some ({rs}, {idx}) := by decide',
                 f'theorem {name}_input : ChunkInput {rs} 1 x := by change 1 < 2 ∧ 0 < 12 ∧ {k} ∣ 12; decide',
                 f'theorem {name}_step : step g (.group (some {rs})) s (node {rank}) = some (localStep {rs} s (node {rank})) :=',
                 f'  step_scoped g s (node {rank}) {rs} (by decide) (by rfl)',
                 f'theorem {name}_shape : (localStep {rs} s (node {rank}) 20).shape = [2, {12//k}] := by rfl']
        for i,v in enumerate(values):
            text += [f'theorem {name}_value_{i} : valAt (localStep {rs} s (node {rank}) 20) {i} = {v} := by',
                     f'  change (({v} : Nat) : Scalar) = {v}; norm_num',
                     f'#print axioms {name}_value_{i}']
        text += [f'#print axioms {name}_step']
    old=torch.chunk(x,4,dim=1)[2].flatten()[0].item()
    assert old != torch.chunk(x,2,dim=1)[0].flatten()[0].item()
    text += [f'theorem old_world_value : valAt (applyNode g s (node 2) 20) 0 = {old} := by',
             f'  change (({old} : Nat) : Scalar) = {old}; norm_num',
             'theorem old_world_differs : localStep [2,3] s (node 2) 20 ≠ applyNode g s (node 2) 20 := by',
             '  intro h', '  have he := congrArg (fun t => valAt t 0) h',
             '  rw [rank2_value_0, old_world_value] at he', '  norm_num at he', '#print axioms old_world_differs']
    for name,rs,rank in [('empty',[],2),('duplicate',[2,2],2),('nonmember',[0,1],2),('out_of_world',[2,4],2)]:
        text += [f'theorem reject_{name} : resolve 4 {rank} (some {rs}) = none := by decide', f'#print axioms reject_{name}']
    text += ['theorem reject_missing : resolve 4 2 none = none := rfl',
             'theorem membership_no_alias : resolve 4 2 (some [2,3]) ≠ resolve 4 2 (some [0,1]) := by decide',
             'theorem ordered_membership_no_alias : resolve 4 2 (some [2,3]) ≠ resolve 4 2 (some [0,2]) := by decide',
             '#print axioms membership_no_alias', '#print axioms ordered_membership_no_alias',
             'end', 'end TrainVerify.Denote.GroupScopedEval.Witness', '']
    # Audit every exported witness, including scope/input and shape certificates.
    missing = [m.group(1) for line in text if (m := re.match(r'theorem (\w+)', line))
               and f'#print axioms {m.group(1)}' not in text]
    text[-3:-3] = [f'#print axioms {name}' for name in missing]
    return '\n'.join(text)

if __name__ == '__main__':
    p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
    out=Path(__file__).resolve().parents[2]/'trainverify/denote/GroupScopedEvalWitness.lean'
    data=generate().encode()
    assert data == generate().encode()
    if a.check:
        assert out.exists() and out.read_bytes()==data, 'generated witness missing or stale'
    else: out.write_bytes(data)
    print(f'{"CHECK" if a.check else "GENERATE"} {len(data)} bytes; torch={torch.__version__}; dim=1; K=1,2,3; CPU')
