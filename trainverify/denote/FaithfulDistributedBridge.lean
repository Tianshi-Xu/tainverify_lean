/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.DenoteDistributedFaithful

/-!
# Lifting `denoteGraphDistributed` results onto the faithful track

The faithful evaluator differs from `applyNodeDistributed` on exactly three
operators — `FW_maybe_shuffle`, `FW_maybe_unshuffle`, `FW_attn_zigzag`
(`applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective`). In the
YOCO-MoE graphs those appear only inside the zigzag region (SM ≥ 472, PM ≥ 1003),
so every tid whose final writer precedes that region has the *same* denotation
under both evaluators.

That makes the several hundred existing `_distributed` results in the
self-decoder region reusable as-is: rather than replaying each proof against the
faithful evaluator, transport it through `denote_faithful_eq_distributed_of_prefix`
below.

The hypotheses are exactly what the graph can decide:

* `hnil` / `hwrite` — after index `k`, no node writes `tid` (the usual
  not-written obligation, dischargeable by `native_decide`);
* `hops` — the first `k` nodes contain none of the three divergent operators,
  likewise decidable.

Nothing here is specific to a graph or a tid, so one instance serves the whole
region.
-/

namespace TrainVerify.Denote

/-- On a prefix free of the three faithful-divergent collectives, the faithful and
plain distributed denotations agree at any tid the suffix does not write. -/
theorem denote_faithful_eq_distributed_of_prefix
    (g : GraphDecl) (init : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hwrite : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs)
    (hops : ∀ n ∈ g.nodes.take k,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧
      n.op ≠ "OpName.FW_attn_zigzag") :
    denoteGraphDistributedFaithful g init tid = denoteGraphDistributed g init tid := by
  rw [denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hwrite]
  rw [foldl_take_applyNodeDistributedFaithful_eq_applyNodeDistributed g g.nodes init k hops]
  exact (denoteGraphDistributed_eq_prefix g init tid k hnil hwrite).symm

end TrainVerify.Denote
