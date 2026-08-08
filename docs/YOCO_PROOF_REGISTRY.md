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
- exactly five fully qualified proof target names.  The allowed `#print axioms`
  baseline is hard-coded in the emitter, not registry-controlled, so a proof commit
  cannot widen its own trust base.

A missing entry, unknown field, duplicate path, digest mismatch, missing proof module,
or any `sorry`/`sorryAx`/`axiom`/`unsafe` token fails closed before Lean validation and before
publication.  Registry proof paths are materialized from the declared TrainVerify Git
blob, never from a mutable worktree pathname.  Proof dependencies outside
`yoco_goals/` are also explicit closed-list entries: for example,
`EmbeddingHiddenShard.lean` is materialized at the snapshot root and included in the
same exact SHA-256 ledger.  Depending on a helper merely because it exists in the
validation checkout is forbidden; missing or extra top-level modules fail closed.

After the complete target build, the emitter creates a private validation-only Lean
module containing `#print axioms` for all five registered targets.  It rejects missing
audit output and every dependency outside `propext`, `Classical.choice`, `Quot.sound`,
and the generated `native_decide` baseline.  This audit module is not published.

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
