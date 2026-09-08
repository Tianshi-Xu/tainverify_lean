"""Deterministic CPU derived-source-flow replay, NOT a distributed collective call.
Authority: nnscaler/runtime/adapter/collectives.py all_to_all and all_to_all_single.
"""
import argparse
from pathlib import Path
import torch


def cases():
    for k, ranks in [(1, [2]), (2, [1, 3]), (3, [0, 2, 5])]:
        for idim, odim in [(0, 0), (1, 1), (0, 1), (1, 0)]:
            shape = (k, 2 * k)
            xs = [torch.arange(shape[0] * shape[1], dtype=torch.int64).reshape(shape) + 100 * r for r in ranks]
            for dest in range(k):
                source = torch.cat([x.chunk(k, dim=odim)[dest] for x in xs], dim=idim)
                # Replay packed all_to_all_single: transpose, exchange equal dim-0
                # chunks in source order, transpose back, then chunk/cat callback.
                packed = [x.transpose(0, odim).contiguous() for x in xs]
                exchanged = torch.cat([x.chunk(k, dim=0)[dest] for x in packed], dim=0)
                back = exchanged.transpose(0, odim)
                single = torch.cat(back.chunk(k, dim=odim), dim=idim)
                assert torch.equal(source, single)
                if idim != odim:
                    assert torch.equal(source, torch.cat(xs, dim=idim).chunk(k, dim=odim)[dest])
                yield k, ranks, idim, odim, dest, xs, source


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--red', choices=['sameaxis', 'wrongworld'])
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    rows = list(cases())
    if args.red:
        k, ranks, i, o, d, xs, expected = next(c for c in rows if c[0] == 2 and c[2:5] == (1, 1, 0))
        if args.red == 'sameaxis':
            actual = torch.cat(xs, dim=i).chunk(k, dim=o)[d]
        else:
            actual = torch.cat([x.chunk(4, dim=o)[ranks[d]] for x in xs], dim=i)
        assert torch.equal(actual, expected), (args.red, actual.tolist(), expected.tolist())
        return
    lines = ['import denote.AllToAllSourceFaithful',
             'namespace TrainVerify.Denote.AllToAllSourceFaithful.Witness',
             'set_option maxHeartbeats 500000', 'noncomputable section',
             '-- Generated CPU derived-source-flow replay; no GPU/collective invocation.',
             'def sample (sh : Shape) (base : Nat) : Tensor :=',
             '  Tensor.mkShape sh (fun j => ((base + j.val : Nat) : Scalar))']
    names = []
    def theorem(name, statement, proof):
        names.append(name)
        lines.append(f'theorem {name} : {statement} := by\n  {proof}')
    for k, ranks, i, o, d, xs, expected in rows:
        tag = f'k{k}_i{i}_o{o}_d{d}'
        sh = list(xs[0].shape)
        ls = '[' + ', '.join(f'sample {sh} {100*r}' for r in ranks) + ']'
        lines.append(f'def xs_{tag} : List Tensor := {ls}')
        expr = f'tensor {k} {d} {i} {o} xs_{tag}'
        simp = f'tensor, allGatherPrimDimN, chunkPrimDimN, valAt, Tensor.mkShape, prodShape, sample, xs_{tag}'
        theorem(f'shape_{tag}', f'({expr}).shape = {list(expected.shape)}', 'rfl')
        for j, value in enumerate(expected.flatten().tolist()):
            theorem(f'value_{tag}_{j}', f'valAt ({expr}) {j} = ({value} : Scalar)', (f'change (({value} : Nat) : Scalar) = {value}\n  norm_num' if value < 2 else 'rfl'))
        # Original TIDs are the noncontiguous process IDs for this fixture only.
        lines.append(f'def store_{tag} : Store := fun tid => sample {sh} (100 * tid)')
        lines.append(f'def node_{tag} : NodeDecl := {{rank := {ranks[d]}, op := "OpName.AllToAllPrim", ins := {ranks}, outs := [99], params := [{i}, {o}]}}')
        contract = f'NodeContract {ranks} id store_{tag} node_{tag} {i} {o} 99'
        cases_proof = ' | '.join(['rfl'] * k)
        proof = (f'refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, {sh}, ?_, by decide, by decide, by decide, by decide⟩\n'
                 f'  intro x hx\n  change x ∈ {ls} at hx\n'
                 f'  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx\n'
                 f'  rcases hx with {cases_proof}\n  all_goals rfl')
        theorem(f'contract_{tag}', contract, proof)
        theorem(f'step_{tag}', f'step {{numRanks := 6, nodes := []}} (some {ranks}) id store_{tag} node_{tag} = .ok (localStep {ranks} store_{tag} node_{tag} {i} {o})',
                f'exact step_valid _ _ _ _ _ {i} {o} 99 (by decide) contract_{tag}')
    tag = 'k2_i1_o1_d0'
    simp = f'allToAllPrimWithDims, tensor, allGatherPrimDimN, chunkPrimDimN, valAt, Tensor.mkShape, prodShape, sample, xs_{tag}'
    theorem('legacy_sameaxis_counterexample', f'valAt (allToAllPrimWithDims 2 0 xs_{tag} 1 1) 2 ≠ valAt (tensor 2 0 1 1 xs_{tag}) 2', 'change (102 : Scalar) ≠ 300\n  norm_num')
    theorem('missing_scope', 'step {numRanks := 6, nodes := []} none id store_k2_i1_o1_d0 node_k2_i1_o1_d0 = .error .missingScope', 'rfl')
    theorem('wrong_world_rejected', 'step {numRanks := 2, nodes := []} (some [1, 3]) id store_k2_i1_o1_d0 node_k2_i1_o1_d0 = .error .rejectedScope', 'exact step_rejected _ _ _ _ _ (by decide)')
    theorem('legacy_distinct_axis_control', 'valAt (allToAllPrimWithDims 2 0 xs_k2_i0_o1_d0 0 1) 4 = (300 : Scalar)', 'rfl')
    theorem('duplicate_group_rejected', 'step {numRanks := 6, nodes := []} (some [1, 1]) id store_k2_i1_o1_d0 node_k2_i1_o1_d0 = .error .rejectedScope', 'exact step_rejected _ _ _ _ _ (by decide)')
    for label, update, projection in [('op', 'op := "bad"', '.1'), ('order', 'ins := [3, 1]', '.2.2.1'), ('arity', 'ins := [1]', '.2.2.1')]:
        theorem(f'invalid_{label}', f'step {{numRanks := 6, nodes := []}} (some [1, 3]) id store_k2_i1_o1_d0 {{node_k2_i1_o1_d0 with {update}}} = .error .invalidNode',
                f'apply step_invalid _ _ _ _ _ 1 1 99 (by decide) rfl rfl\n  intro hc\n  have h := hc{projection}\n  contradiction')
    lines += [f'#print axioms {name}' for name in names]
    lines += ['end', 'end TrainVerify.Denote.AllToAllSourceFaithful.Witness', '']
    target = args.output or Path(__file__).resolve().parents[2] / 'trainverify/denote/AllToAllSourceFaithfulWitness.lean'
    target.write_text('\n'.join(lines))
    print({'cpu_source_flow_cases': len(rows), 'kernel_theorems_generated': len(names), 'output': str(target)})


if __name__ == '__main__':
    main()
