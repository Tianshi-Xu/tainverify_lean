# Content-addressed YOCO proof registry

Production YOCO snapshots must not publish the generic `Pattern_N.lean` files emitted
by `Verdict/graph_to_lean.py`: those files are proof-obligation skeletons and may
contain `sorry`.

The production emitter shall instead consume a closed registry committed in the same
private TrainVerify revision.  A registry entry is accepted only when all of these
match the freshly generated stage:

- SHA-256 of `GeneratedYOCOMoE.lean`;
- SHA-256 of every `Goal_N.lean` statement consumed by the proof;
- SHA-256 of every static contract/helper/proof module copied from the Git tree;
- exact expected module/path set;
- proof target name and its allowed `#print axioms` baseline.

A missing entry, unknown field, duplicate path, digest mismatch, missing proof module,
or any `sorry`/`axiom`/`unsafe` token fails closed before Lean validation and before
publication.  Registry proof paths are materialized from the declared TrainVerify Git
blob, never from a mutable worktree pathname.

Goal statement selection is semantic:

- slices containing `FW_maybe_shuffle`, `FW_maybe_unshuffle`, or `FW_attn_zigzag`
  use `denoteGraphDistributedFaithful`;
- Goal 1 additionally requires the labels-in-vocabulary caller contract;
- Goals 1, 3, and 4 require explicit packed-cu-seqlens well-formedness contracts;
- Goals 2 and 5 use the ordinary evaluator because their operators are already
  represented faithfully there.

The registry binds proofs to statements; it must never select a proof by Pattern hash
alone because the old Pattern key omitted shapes, init goals, replica groups, and
statement semantics.
