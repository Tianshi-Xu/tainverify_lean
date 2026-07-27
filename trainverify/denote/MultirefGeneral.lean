/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.Denote

/-!
# A general `FW_multiref` output lemma

`Denote.lean` carries roughly thirty ad-hoc multiref lemmas, each pinned to one
arity, one output position, and often one generated goal
(`applyNode_fw_multiref3_second_out_g291`, …). The self-decoder fan-out goals
need arities 2, 3, 5 and 12 across twelve positions, which would mean another
four dozen special cases.

None of that is necessary. A multiref writes `List.replicate n x` across its
outputs, so **every** output position holds the same value `x`. Whichever pair
`storeSet`'s `find?` selects, the answer is `x` — the pairwise-distinctness side
conditions carried by the existing lemmas (`h13 : t1 ≠ t3`, …) are redundant.

One lemma therefore covers every arity and position, needing only that the
requested tid is among the outputs.
-/

namespace TrainVerify.Denote

/-- Looking up any tid present in `outs` inside a store updated with a constant
list yields that constant. -/
theorem storeSet_replicate_mem (s : Store) (v : Tensor) :
    ∀ (outs : List Tid) (t : Tid), t ∈ outs →
      storeSet s (outs.zip (List.replicate outs.length v)) t = v := by
  intro outs
  induction outs with
  | nil => intro t ht; cases ht
  | cons a rest ih =>
    intro t ht
    unfold storeSet
    simp only [List.length_cons, List.replicate, List.zip_cons_cons, List.find?_cons]
    by_cases hat : a = t
    · simp [hat]
    · simp only [hat, decide_false, Bool.false_eq_true, if_false]
      have ht' : t ∈ rest := by
        rcases List.mem_cons.mp ht with h | h
        · exact absurd h.symm hat
        · exact h
      have := ih t ht'
      unfold storeSet at this
      exact this

/-- The value at any output of a `FW_multiref` node is its input. No constraint
on arity, position, or distinctness of the output tids. -/
theorem applyNode_fw_multiref_at
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid : Tid) (outs : List Tid)
    (n : Nat) (hn : outs.length = n) (t : Tid) (hmem : t ∈ outs) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := outs, params := [n] } t = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  subst hn
  exact storeSet_replicate_mem s (s xTid) outs t hmem

end TrainVerify.Denote
