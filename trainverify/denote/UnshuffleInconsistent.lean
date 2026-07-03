import denote.yoco_goals.Pattern_1

/-!
  # Proof that `fw_maybe_unshuffle_cp2_commute` is inconsistent

  This file formally proves `False` from the axiom `fw_maybe_unshuffle_cp2_commute` in
  `denote.yoco_goals.Pattern_1`. Since Pattern_1's proof of `prove_pattern_1` depends
  on this axiom (see `#print axioms prove_pattern_1`), the entire Pattern_1 proof is
  **vacuous** — technically valid inside an inconsistent theory, but proving nothing about
  the actual mathematics.

  ## The witness
  - LHS: `fw_maybe_unshuffle (allGather [a, b]) 1 0 [cu]` has shape `cu.shape = [2]` under
    Denote's literal semantics (see `Denote.fw_maybe_unshuffle`: output shape is
    `xs.head?.shape` where `xs = [cu]`).
  - RHS: `allGather [fw_maybe_unshuffle a 2 0 [cu], fw_maybe_unshuffle b 2 1 [cu]]` has shape
    `[4]` (allGather on dim 0 of two `[2]` tensors).
  - `[2] ≠ [4]` by `decide`, contradicting the axiom's equality.

  ## Fix required
  Either:
  1. Change `Denote.fw_maybe_unshuffle`'s definition to use the data tensor's shape as
     `firstShape` (matching the graph's intended semantics), and update the axiom to
     match the corrected definition; OR
  2. Remove `fw_maybe_unshuffle_cp2_commute` and re-prove Pattern_1 without this step
     (which likely requires a completely different approach).
-/

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedPatterns

namespace UnshuffleInconsistency

noncomputable def cu : Tensor := { shape := [2], val := fun _ => 0 }
noncomputable def a : Tensor := { shape := [2048, 1024], val := fun _ => 0 }
noncomputable def b : Tensor := { shape := [2048, 1024], val := fun _ => 0 }

/-- The LHS has shape `[2]`, matching `cu.shape`. -/
theorem lhs_shape : (fw_maybe_unshuffle (allGatherPrimDimN 0 2 0 [a, b]) 1 0 [cu]).shape = [2] := by
  unfold fw_maybe_unshuffle
  show (match cu.shape with
        | [] => zeroTensor []
        | _ :: _ => Tensor.mkShape cu.shape _).shape = [2]
  simp [Tensor.mkShape]
  rfl

/-- The RHS has shape `[4]`. -/
theorem rhs_shape : (allGatherPrimDimN 0 2 0
              [fw_maybe_unshuffle a 2 0 [cu],
               fw_maybe_unshuffle b 2 1 [cu]]).shape = [4] := by
  have h1 : (fw_maybe_unshuffle a 2 0 [cu]).shape = [2] := by
    unfold fw_maybe_unshuffle; simp [Tensor.mkShape]; rfl
  have hhead : (([fw_maybe_unshuffle a 2 0 [cu], fw_maybe_unshuffle b 2 1 [cu]] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [2] := by simp [h1]
  rw [allGatherPrimDimN_shape 0 2 _ [2] hhead]
  simp [List.set, List.getD]

/-- The axiom equates two tensors of different shapes, so it forces `[2] = [4]`. -/
theorem two_eq_four : ([2] : List Nat) = [4] := by
  have hax := fw_maybe_unshuffle_cp2_commute a b cu
  have hshape := congrArg Tensor.shape hax
  rw [lhs_shape, rhs_shape] at hshape
  exact hshape

/-- `[2] ≠ [4]` by decidable equality on `List Nat`. -/
theorem two_neq_four : ¬(([2] : List Nat) = [4]) := by decide

/-- Contradiction: the axiom is inconsistent. -/
theorem contradiction : False := two_neq_four two_eq_four

-- Print the axioms `contradiction` depends on. Expected output:
--   'contradiction' depends on axioms: [propext, Classical.choice, Quot.sound,
--    fw_maybe_unshuffle_cp2_commute]
-- The four kernel/user axioms are all that's needed to derive False, confirming
-- the user axiom is inconsistent.
#print axioms contradiction

end UnshuffleInconsistency
