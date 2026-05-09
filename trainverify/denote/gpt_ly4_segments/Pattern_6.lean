/- Auto-generated pattern proof file.
   Pattern: 6
   Hash: 50d559b40c026d8e
   Goals: 6, 7, 32, 58, 83
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_6_goalIds : List Nat := [6, 7, 32, 58, 83]
inductive pattern_6_target : Prop → Prop
  | goal_6 : pattern_6_target goal_6_stmt
  | goal_7 : pattern_6_target goal_7_stmt
  | goal_32 : pattern_6_target goal_32_stmt
  | goal_58 : pattern_6_target goal_58_stmt
  | goal_83 : pattern_6_target goal_83_stmt

def pattern_6_stmt : Prop :=
  ∀ {target : Prop}, pattern_6_target target → target

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-! ## Helper lemmas

Pointwise valAt characterizations of `chunkPrimDimN` along dim 1 for the
shape used in this pattern (`x : [1, 8, 32]` sharded into 4 pieces
`[1, 2, 32]`). These are the building blocks for the `fw_linear`
distribution helper used by `prove_pattern_6`. -/

private lemma chunk1_x_1_8_32_shape (x : Tensor) (r : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4) :
    (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] := by
  rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
  simp [List.set, List.getD]

private lemma chunk1_x_1_8_32_valAt (x : Tensor) (r : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4)
    (jLocal : Nat) (k : Nat) (hjLocal : jLocal < 2) (hk : k < 32) :
    valAt (chunkPrimDimN 1 4 r x) (jLocal * 32 + k) =
      valAt x ((r * 2 + jLocal) * 32 + k) := by
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] :=
    chunk1_x_1_8_32_shape x r hx hr
  have hflat_lt : jLocal * 32 + k < prodShape (chunkPrimDimN 1 4 r x).shape := by
    rw [hchunk_shape]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hflat_lt]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.getD,
    show (4 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
    show (32 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega, ite_false]
  have hr' : r % 4 = r := Nat.mod_eq_of_lt hr
  have h_lt : jLocal * 32 + k < 64 := by omega
  have h_div : (jLocal * 32 + k) / 64 = 0 := Nat.div_eq_of_lt h_lt
  have h_mod : (jLocal * 32 + k) % 64 = jLocal * 32 + k := Nat.mod_eq_of_lt h_lt
  have h_div32 : (jLocal * 32 + k) / 32 = jLocal := by
    have heq : jLocal * 32 + k = k + 32 * jLocal := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by norm_num : (0:Nat) < 32),
        Nat.div_eq_of_lt hk, Nat.zero_add]
  have h_mod32 : (jLocal * 32 + k) % 32 = k := by
    have heq : jLocal * 32 + k = k + 32 * jLocal := by ring
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  have hjm : jLocal % 2 = jLocal := Nat.mod_eq_of_lt hjLocal
  have hidx : (jLocal * 32 + k) / (8 / 4 * (1 * 32)) * (8 * (1 * 32)) +
      (r % 4 * (8 / 4) +
        (jLocal * 32 + k) % (8 / 4 * (1 * 32)) / (1 * 32)) * (1 * 32) +
        (jLocal * 32 + k) % (8 / 4 * (1 * 32)) % (1 * 32) =
      (r * 2 + jLocal) * 32 + k := by
    simp only [show (8 / 4 * (1 * 32) : Nat) = 64 by norm_num,
      show (8 * (1 * 32) : Nat) = 256 by norm_num,
      show (1 * 32 : Nat) = 32 by norm_num,
      show (8 / 4 : Nat) = 2 by norm_num,
      h_div, h_mod, h_div32, h_mod32, hr', hjm]
    ring
  rw [show (8 / 4 * (1 * 32) : Nat) = 64 by norm_num] at *
  simp only [show (64 : Nat) ≠ 0 by omega, ite_false]
  rw [hidx]

theorem prove_pattern_6 : pattern_6_stmt := by
  intro target h
  cases h <;> sorry

end TrainVerify.Denote.GeneratedPatterns
