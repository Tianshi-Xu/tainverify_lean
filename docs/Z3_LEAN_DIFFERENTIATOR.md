# TrainVerify Z3 vs. kernel-checked TrainVerify: a concrete differentiator

## Compared source

Microsoft `microsoft/TrainVerify` commit:

```text
fbe49bc2f5619ac86dc9fd5101aae34c810d2ea1
```

Primary sources:

- `Verdict/z3_backend/core.py`
- `Verdict/verdict/graph/lineage.py`
- `Verdict/verdict/operators/registered_ops.py`
- `Verdict/verdict/operators/names.py`
- TrainVerify paper, arXiv:2506.15961

The local `Verdict/z3_backend/core.py` is byte-identical to that Microsoft commit:

```text
sha256 06a833980bff498f8f59a29dcc7470ebd3f091b1cd2ab9ffd36e4818be768837
```

## Concrete false-positive class: inconsistent stage premises

Microsoft TrainVerify proves a group by asking whether:

```text
given ∧ ¬claim
```

is unsatisfiable. `check_always_hold` and `_solver_check_unsat` do not first require `given` itself to be satisfiable. Consequently, inconsistent lineage/stage premises prove every output claim vacuously.

Executed with the repository's exact `core.py` and its pinned `z3-solver==4.15.1.0`:

```text
z3_version: 4.15.1
given_only: unsat
false_claim_under_inconsistent_given: True
false_claim_under_consistent_given: False
```

The false claim was `x == 42`; the inconsistent premises were `x == 0` and `x == 1`.

This is not a limitation of Z3. Z3 correctly reports the premises `unsat`; it is a missing non-vacuity check in the current TrainVerify verifier protocol.

## A corresponding fail-closed boundary in this project

This project's closed relation pipeline does not allow an arbitrary graph-written relation to be declared as an external stage premise. External facts must be complete immutable `init:` authority; every other pre-fact needs a unique graph transition producer.

A mutation of the real YOCO Goal 3 transition plan attempted to externalize:

```text
('sm:999:0', 'pm:999:0', 'pm:1000:0')
```

and was rejected before proof emission:

```text
RelationCompositionError: external pre-fact is not pure init authority
```

The distinction is scoped: Lean's kernel does not automatically prove arbitrary hypotheses satisfiable. The advantage comes from this project's authority validation, exact producer DAG, explicit caller contracts/non-vacuity witnesses where required, and axiom receipts—not from “Lean beats Z3” in theorem-proving power.

## Second practical gap: non-contiguous zigzag ownership

Microsoft's current lineage type maps one logical rectangular `SliceMap` (one `(start,end)` interval per dimension) to sorted parallel tensors. Its released operator registry has no `maybe_shuffle`, `maybe_unshuffle`, sliding-window ring attention, or zigzag attention operator. Therefore the released verifier cannot faithfully express a shard whose logical positions are a non-contiguous permutation.

For CP=2 and logical positions `0..3`, a zigzag owner map can be:

```text
rank 0: [0, 3]
rank 1: [1, 2]
rank-order gather: [0, 3, 1, 2]
```

A permutation-sensitive causal-attention scalar oracle produced:

```text
canonical: [1.0, 1.7310585786300048, 2.940292211914573, 5.02707902303914]
naive:     [1.0, 4.5,                3.6666666666666665, 5.02707902303914]
max_abs_error: 2.768941421369995
```

Restoring logical position order before attention matched the canonical result exactly.

This project represents that distinction explicitly with `ZigzagRel`, ordered buddy authority, `zigzagPos`, and value-faithful shuffle/unshuffle collectives. It can reject an ordinary rank-order gather where zigzag authority is required.

Again, Z3 could verify a faithful permutation encoding if one were added. The practical differentiation is that Microsoft TrainVerify's released lineage/operator language does not currently contain it, while this project does.

## Honest product verdict

Microsoft TrainVerify is broader and more automated today, including forward/backward/optimizer/metric symbolic checking and counterexamples. This project is differentiated by:

- independently replayable kernel-checked artifacts;
- graph-scoped and publication-scoped authority;
- exact theorem/axiom receipts;
- typed ownership states, including zigzag/permuted layouts;
- fail-closed certificate and producer-DAG validation.

The strongest architecture is hybrid: use Z3 for search and counterexamples, emit a small certificate, and replay it through the Lean checker.
