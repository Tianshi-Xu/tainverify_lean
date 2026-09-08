"""Generate tiny synthetic SAME-world input/add/source-scoped SUM witnesses.

Uses the existing independent source fixture and compiler scope validator to obtain
ordered noncontiguous group membership, world size, parameters and tensor shapes.
Values are explicit mathematical real tensors; no Torch capture association is made.
Run from the repository root with PYTHONPATH=.:Verdict; no accelerator is used.
"""
import argparse
from pathlib import Path


def generate(ranks=(0, 2)):
    from scripts.tests.test_graph_to_lean_collective_scope import fixture
    from Verdict import graph_to_lean as compiler
    ranks = tuple(ranks)
    if not ranks or len(set(ranks)) != len(ranks) or min(ranks) < 0:
        raise ValueError("nonempty unique nonnegative ranks required")
    raw, source = fixture("AllReducePrim", ranks)
    view, = compiler._lower_runtime_graphs(raw)
    compiler.attach_collective_scopes(view, source)
    certs = [view.collective_scopes[n] for n in raw.ns[1::2]]
    assert all(tuple(c.ranks) == ranks and not c.params for c in certs)
    shape = list(raw.shapes[raw.ins[raw.ns[1]][0]])
    k = len(ranks)
    lines = ["import denote.SourceScopedEval", "namespace TrainVerify.Denote.InputWitness",
             "set_option maxHeartbeats 500000", "noncomputable section", "open SourceScopedEval",
             "-- Synthetic values; source-validated SUM request and shape convention.",
             f"def tensor (v : Scalar) : Tensor := ⟨{shape}, fun _ => v⟩",
             "def initial : Store := fun _ => tensor 999"]
    names, payloads, states, advances = [], [], ["initial"], []
    for i, rank in enumerate(ranks):
        a, b, y = 10*i+1, 10*i+2, 10*i+3
        lines += [f'def loader{i} : NodeDecl := {{rank := {rank}, op := "OpName.DATALOADER", ins := [], outs := [{a}, {b}]}}',
                  f'def add{i} : NodeDecl := {{rank := {rank}, op := "OpName.FW_add", ins := [{a}, {b}], outs := [{y}]}}',
                  f"def ports{i} : PortFeed := [({a}, tensor {i+1}), ({b}, tensor {10*(i+1)})]"]
        names += [f"loader{i}", f"add{i}"]
        payloads += [f"some ports{i}", "none"]
    ins = [10*i+3 for i in range(k)]
    for i, rank in enumerate(ranks):
        lines += [f'def collective{i} : NodeDecl := {{rank := {rank}, op := "OpName.AllReducePrim", ins := {ins}, outs := [{100+i}], params := []}}']
        names.append(f"collective{i}"); payloads.append("none")
    lines += [f"def world : GraphDecl := {{numRanks := {raw.W.runtime_ndevs}, nodes := [{', '.join(names)}]}}",
              f'def scope (n : NodeDecl) : GroupScopedEval.Request := if n.op = "OpName.FW_add" then .global else if n.op = "OpName.AllReducePrim" then .group (some {list(ranks)}) else .group none',
              'def peers (_n : NodeDecl) (_r : Nat) : Tid := 0',
              f"def requests : List InputRequest := [{', '.join(f'({n}, {p})' for n,p in zip(names,payloads))}]"]
    for j, (n, p) in enumerate(zip(names, payloads)):
        prev = states[-1]; cur = f"state{j+1}"; states.append(cur)
        if n.startswith("loader"):
            i = int(n[6:]); expr = f"storeSet {prev} ports{i}"
            proof = f"  change checkedInputStep {prev} {n} ports{i} = _\n  exact checkedInputStep_valid _ _ _ (by decide)"
        elif n.startswith("add"):
            expr = f"applyNode world {prev} {n}"
            proof = "  rfl"
        else:
            expr = f"GroupScopedEval.localStep {list(ranks)} {prev} {n}"
            proof = f"  rw [stepWithInputs_ordinary _ _ _ _ _ (by decide)]\n  change step world (.group (some {list(ranks)})) _ {prev} {n} = _\n  rw [step_group _ _ _ _ _ (by decide) (by decide)]\n  exact GroupScopedEval.step_scoped _ _ _ _ (by decide) (by rfl)"
        lines += [f"def {cur} : Store := {expr}",
                  f"theorem advance{j} : stepWithInputs world (scope {n}) (peers {n}) {prev} {n} ({p}) = some {cur} := by", proof]
        advances.append(f"advance{j}")
    lines += ["theorem schedule_valid : InputSchedule world.nodes requests := by decide",
              f"theorem mixed_run : denoteWithInputs world scope peers (some requests) initial = some {states[-1]} := by",
              "  simp only [denoteWithInputs, runWithInputs]",
              "  rw [if_pos schedule_valid]",
              "  simp only [requests, runUsing, List.foldl, Option.bind_some, " + ", ".join(advances) + "]"]
    # Typed reduction avoids expanding the whole operator dispatcher under simplification.
    lines += [f"theorem mixed_read : valAt ({states[-1]} 100) 0 = {11*sum(range(1,k+1))} := by",
              "  change (0 + " + " + ".join(f"({i+1} + {10*(i+1)})" for i in range(k)) + f" : Scalar) = {11*sum(range(1,k+1))}",
              "  norm_num",
              f"theorem mixed_shape : ({states[-1]} 100).shape = {shape} := by rfl",
              f"theorem mixed_frame (tid : Tid) (ht : ∀ n ∈ world.nodes, tid ∉ n.outs) : {states[-1]} tid = initial tid := by",
              "  exact runWithInputs_skip world scope peers world.nodes (some requests) initial _ tid ht mixed_run",
              "theorem old_loader_blocked : step world (.group none) (peers loader0) initial loader0 = none := rfl",
              "theorem nofeed_compatibility : denoteWithInputs world scope peers none initial = denote world scope peers initial := rfl"]
    lines += [f"theorem mixed_success : ∃ s, denoteWithInputs world scope peers (some requests) initial = some s ∧ valAt (s 100) 0 = {11*sum(range(1,k+1))} ∧ (∀ tid, (∀ n ∈ world.nodes, tid ∉ n.outs) → s tid = initial tid) := by",
              f"  exact ⟨{states[-1]}, mixed_run, mixed_read, mixed_frame⟩"]
    # Full-schedule errors, including exact full NodeDecl identity rather than a cid.
    for name, expr in [
        ("missing_reject", "[]"),
        ("duplicate_reject", "requests ++ requests"),
        ("reordered_reject", "requests.reverse"),
        ("extra_reject", "requests ++ [(loader0, some ports0)]"),
        ("identity_reject", "({loader0 with rank := 999}, some ports0) :: requests.tail")]:
        lines += [f"theorem {name} : denoteWithInputs world scope peers (some ({expr})) initial = none := by",
                  "  simp only [denoteWithInputs, runWithInputs]", "  exact if_neg (by decide)"]
    for name, node, feed in [
        ("badports_reject", "loader0", "[(999, tensor 1)]"),
        ("duplicateports_reject", "loader0", "[(1, tensor 1), (1, tensor 2)]"),
        ("reorderedports_reject", "loader0", "ports0.reverse"),
        ("extraports_reject", "loader0", "ports0 ++ [(999, tensor 1)]"),
        ("emptyports_reject", "{loader0 with outs := []}", "[]"),
        ("duplicateouts_reject", "{loader0 with outs := [1, 1]}", "[(1, tensor 1), (1, tensor 2)]"),
        ("badins_reject", "{loader0 with ins := [999]}", "ports0"),
        ("badparams_reject", "{loader0 with params := [1]}", "ports0"),
        ("nonloader_reject", "add0", "ports0")]:
        lines += [f"theorem {name} : checkedInputStep initial ({node}) ({feed}) = none := by",
                  "  exact checkedInputStep_invalid _ _ _ (by decide)"]
    lines += ["theorem missingpayload_reject : stepWithInputs world (.group none) (peers loader0) initial loader0 none = none := rfl",
              "theorem extraordinary_reject : stepWithInputs world .global (peers add0) initial add0 (some ports0) = none := by decide",
              "theorem loader_value (s : Store) : storeSet s ports0 2 = tensor 10 := by",
              "  exact checkedInputStep_value s _ loader0 ports0 2 (tensor 10) (List.mem_cons_of_mem _ List.mem_cons_self) (checkedInputStep_valid _ _ _ (by decide))"]
    for name, payload in [("mixed_missingpayload_reject", "none"),
                          ("mixed_badports_reject", "some [(999, tensor 1)]"),
                          ("mixed_reorderedports_reject", "some ports0.reverse")]:
        expr = f"(loader0, {payload}) :: requests.tail"
        lines += [f"theorem {name} : denoteWithInputs world scope peers (some ({expr})) initial = none := by",
                  "  simp only [denoteWithInputs, runWithInputs]",
                  f"  rw [if_pos (show InputSchedule world.nodes ({expr}) from by decide)]",
                  "  apply runUsing_failed",
                  "  change stepWithInputs world (.group none) (peers loader0) initial loader0 _ = none"]
        if payload == "none":
            lines += ["  rfl"]
        else:
            lines += ["  simp only [stepWithInputs, ↓reduceIte]",
                      "  exact checkedInputStep_invalid _ _ _ (by decide)"]
    theorem_names = [line.split()[1] for line in lines if line.startswith("theorem ")]
    lines += [f"#print axioms {name}" for name in theorem_names]
    lines += ["end", "end TrainVerify.Denote.InputWitness", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ranks", default="0,2")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    text = generate(tuple(int(r) for r in args.ranks.split(",")))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(text)


if __name__ == "__main__":
    main()
