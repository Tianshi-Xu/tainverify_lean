/- Auto-generated pattern proof file.
   Pattern: 53
   Hash: d36f1761f4e16e1d
   Goals: 107
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_53_goalIds : List Nat := [107]
inductive pattern_53_target : Prop → Prop
  | goal_107 : pattern_53_target goal_107_stmt

def pattern_53_stmt : Prop :=
  ∀ {target : Prop}, pattern_53_target target → target
theorem prove_pattern_53 : pattern_53_stmt := by
  -- WIP: goal_107 asserts that the SM `bw_embedding` with weight shape [128,32]
  -- equals the dim-0 concatenation of the 4 PM `bw_embedding`s with weight shape
  -- [32,32].  In `denote/Denote.lean`, `bw_embedding g ids weight` only consults
  -- `weight.shape` (no offset parameter):
  --     out[row, h] = ∑_k [scalarToNat (ids[k]) == row] · g[k, h]
  -- The PM ops are
  --     { op := "OpName.BW_embedding", ins := [719, 714, 1065+r], outs := [1081+r] }
  -- with no `params` (no offset).  Since all four PM ranks share `g = 719` and
  -- `ids = 714` and only the (identical) shape of weight matters, all four shards
  -- produce the *same* [32,32] tensor.  Concatenating gives a [128,32] tensor that
  -- is periodic with period 32 along dim 0.  The SM side, in contrast, produces
  -- `bw_embedding g ids 563_[128,32]`, which is *not* periodic in general.
  -- So `goal_107_stmt` as stated is not provable from the hypotheses for arbitrary
  -- `initSM 719`, `initSM 714`, `initPM 719`, `initPM 714`.  Proving it would
  -- require either (a) extending `BW_embedding` semantics to take an offset
  -- parameter, (b) adding hypotheses constraining `ids` values to `[0, 32)`, or
  -- (c) revising the lineage goal to match the actual sharding semantics.
  -- Leaving as `sorry` per workflow instructions until the upstream semantics or
  -- goal generator is updated.
  sorry

end TrainVerify.Denote.GeneratedPatterns

