/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.FaithfulDistributedBridge
import denote.GraphSlicing

/-!
# Reaching `denoteGraph` results from the faithful track

The evaluators form a chain, each one intercepting a few more operators:

```
applyNodeDistributedFaithful  -- + maybe_shuffle / maybe_unshuffle / attn_zigzag
applyNodeDistributed          -- + all2all_moe_gmm
applyNodeRingAttn             -- + attn_zigzag / attn_sliding_window
applyNode                     -- the base evaluator
```

The bridge is model-neutral: a prefix containing none of the intercepted
operators has the same value under the faithful evaluator and under plain
`denoteGraph`.

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

/-- On a list containing none of the five graph-aware interceptors, the faithful
distributed fold is exactly the base fold. -/
theorem foldl_faithful_eq_plain_of_no_special
    (g : GraphDecl) (pre : List NodeDecl) (s : Store)
    (hfaithful : ∀ n ∈ pre,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧
      n.op ≠ "OpName.FW_maybe_unshuffle" ∧
      n.op ≠ "OpName.FW_attn_zigzag")
    (hmoe : ∀ n ∈ pre,
      n.op ≠ "OpName.FW_all2all_moe_gmm" ∧
      n.op ≠ "OpName.BW_maybe_shuffle" ∧
      n.op ≠ "OpName.BW_maybe_unshuffle" ∧
      n.op ≠ "OpName.BW_attn_zigzag" ∧
      n.op ≠ "OpName.BW_attn_sliding_window")
    (hattn : ∀ n ∈ pre,
      n.op ≠ "OpName.FW_attn_zigzag" ∧
      n.op ≠ "OpName.FW_attn_sliding_window") :
    pre.foldl (applyNodeDistributedFaithful g) s =
      pre.foldl (applyNode g) s := by
  induction pre generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl]
    have hf := hfaithful a List.mem_cons_self
    have hm := hmoe a List.mem_cons_self
    have ha := hattn a List.mem_cons_self
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
      g s a hf.1 hf.2.1 hf.2.2]
    unfold applyNodeDistributed
    rw [if_neg hm.1, if_neg hm.2.1, if_neg hm.2.2.1,
      if_neg hm.2.2.2.1, if_neg hm.2.2.2.2]
    unfold applyNodeRingAttn
    rw [if_neg ha.1, if_neg ha.2]
    exact ih _
      (fun n hn => hfaithful n (List.mem_cons_of_mem _ hn))
      (fun n hn => hmoe n (List.mem_cons_of_mem _ hn))
      (fun n hn => hattn n (List.mem_cons_of_mem _ hn))

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
    (hmoe : ∀ n ∈ g.nodes.take k,
      n.op ≠ "OpName.FW_all2all_moe_gmm" ∧
      n.op ≠ "OpName.BW_maybe_shuffle" ∧
      n.op ≠ "OpName.BW_maybe_unshuffle" ∧
      n.op ≠ "OpName.BW_attn_zigzag" ∧
      n.op ≠ "OpName.BW_attn_sliding_window")
    (hattn : ∀ n ∈ g.nodes.take k, n.op ≠ "OpName.FW_attn_zigzag" ∧
                                   n.op ≠ "OpName.FW_attn_sliding_window") :
    denoteGraphDistributedFaithful g init tid = denoteGraph g init tid := by
  rw [denoteGraphDistributedFaithful_eq_prefix g init tid k hnil hwrite]
  rw [foldl_faithful_eq_plain_of_no_special g (g.nodes.take k) init hops hmoe hattn]
  exact (denoteGraph_eq_prefix_of_not_written g init tid k hwrite).symm

end TrainVerify.Denote
