/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.FaithfulDistributedBridge
import denote.GraphSlicing
import denote.yoco_goals.Layer0DistributedMigration

/-!
# Reaching `denoteGraph` results from the faithful track

The evaluators form a chain, each one intercepting a few more operators:

```
applyNodeDistributedFaithful  -- + maybe_shuffle / maybe_unshuffle / attn_zigzag
applyNodeDistributed          -- + all2all_moe_gmm
applyNodeRingAttn             -- + attn_zigzag / attn_sliding_window
applyNode                     -- the base evaluator
```

`Layer0DistributedMigration` already bridges the middle step
(`foldl_distributed_eq_ring_of_no_moe`). This file adds the last one, so a tid
whose prefix contains none of those operators has the *same* value under the
faithful evaluator and under plain `denoteGraph`.

That is what the head of the self-decoder needs: `4680` is produced by an
embedding and an `AllReducePrim`, neither of which any evaluator intercepts, and
its existing proof (`goal_5_intermediate`) is stated over `denoteGraph`.
-/

namespace TrainVerify.Denote

/-- On an attention-free list the ring evaluator is the base evaluator. -/
theorem foldl_ring_eq_plain_of_no_attn (g : GraphDecl) (pre : List NodeDecl) (s : Store)
    (h : ∀ n ∈ pre, n.op ≠ "OpName.FW_attn_zigzag" ∧
                    n.op ≠ "OpName.FW_attn_sliding_window") :
    pre.foldl (applyNodeRingAttn g) s = pre.foldl (applyNode g) s := by
  induction pre generalizing s with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl]
    have ha := h a List.mem_cons_self
    have : applyNodeRingAttn g s a = applyNode g s a := by
      unfold applyNodeRingAttn
      rw [if_neg ha.1, if_neg ha.2]
    rw [this]
    exact ih _ (fun n hn => h n (List.mem_cons_of_mem _ hn))

/-- Plain-evaluator counterpart of `denoteGraphDistributedFaithful_eq_prefix`. -/
theorem denoteGraph_eq_prefix_of_not_written
    (g : GraphDecl) (init : Store) (tid : Tid) (k : Nat)
    (hno : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    denoteGraph g init tid = ((g.nodes.take k).foldl (applyNode g) init) tid := by
  unfold denoteGraph
  conv_lhs => rw [← List.take_append_drop k g.nodes]
  rw [List.foldl_append]
  exact foldl_applyNode_at_not_written g _ _ tid hno

/-- A tid whose prefix contains none of the intercepted operators has the same
value under the faithful evaluator and under `denoteGraph`. -/
theorem denote_faithful_eq_plain_of_prefix
    (g : GraphDecl) (init : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hwrite : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs)
    (hops : ∀ n ∈ g.nodes.take k,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧
      n.op ≠ "OpName.FW_attn_zigzag")
    (hmoe : ∀ n ∈ g.nodes.take k, n.op ≠ "OpName.FW_all2all_moe_gmm")
    (hattn : ∀ n ∈ g.nodes.take k, n.op ≠ "OpName.FW_attn_zigzag" ∧
                                   n.op ≠ "OpName.FW_attn_sliding_window") :
    denoteGraphDistributedFaithful g init tid = denoteGraph g init tid := by
  rw [denote_faithful_eq_distributed_of_prefix g init tid k hnil hwrite hops]
  rw [denoteGraphDistributed_eq_prefix g init tid k hnil hwrite]
  rw [GeneratedPatterns.foldl_distributed_eq_ring_of_no_moe g (g.nodes.take k) init hmoe]
  rw [foldl_ring_eq_plain_of_no_attn g (g.nodes.take k) init hattn]
  exact (denoteGraph_eq_prefix_of_not_written g init tid k hwrite).symm

end TrainVerify.Denote
