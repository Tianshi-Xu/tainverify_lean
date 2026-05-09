/- Auto-generated pattern proof file.
   Pattern: 5
   Hash: de5f5f99bf861ead
   Goals: 5, 30, 55, 75, 80, 100

   Structural pattern: every goal lifts a single-rank `FW_layernorm` over input
   shape `[1, 8, 32]` with weight/bias of shape `[32]` to four parallel
   `FW_layernorm`s over chunks of shape `[1, 2, 32]`, gathered along dim=1.

   The structural argument is identical for every goal; only the concrete tensor
   ids and the corresponding input-lineage prerequisite differ.  We factor the
   structural part into a single private lemma `layernorm_dim1_4_lift`
   parameterised over the relevant tids, and instantiate it once per goal with
   the right per-goal `*_eval` lemmas plus the input lineage (which is supplied
   by the prerequisite pattern proof).
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_127
import denote.gpt_ly4_segments.Pattern_128

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_5_goalIds : List Nat := [5, 30, 55, 75, 80, 100]
inductive pattern_5_target : Prop → Prop
  | goal_5   : pattern_5_target goal_5_stmt
  | goal_30  : pattern_5_target goal_30_stmt
  | goal_55  : pattern_5_target goal_55_stmt
  | goal_75  : pattern_5_target goal_75_stmt
  | goal_80  : pattern_5_target goal_80_stmt
  | goal_100 : pattern_5_target goal_100_stmt

def pattern_5_stmt : Prop :=
  ∀ {target : Prop}, pattern_5_target target → target

set_option maxRecDepth 32768

/-! ## Generic structural lemma -/

private theorem layernorm_dim1_4_lift
    (initSM initPM : Store)
    (smOutTid smInTid wTid bTid : Tid)
    (pmOut0 pmOut1 pmOut2 pmOut3 : Tid)
    (pmIn0 pmIn1 pmIn2 pmIn3 : Tid)
    (hsm_eval : denoteGraph sm initSM smOutTid =
      fw_layernorm (denoteGraph sm initSM smInTid)
                   (denoteGraph sm initSM wTid)
                   (denoteGraph sm initSM bTid))
    (hpm0_eval : denoteGraph pm initPM pmOut0 =
      fw_layernorm (denoteGraph pm initPM pmIn0)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (hpm1_eval : denoteGraph pm initPM pmOut1 =
      fw_layernorm (denoteGraph pm initPM pmIn1)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (hpm2_eval : denoteGraph pm initPM pmOut2 =
      fw_layernorm (denoteGraph pm initPM pmIn2)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (hpm3_eval : denoteGraph pm initPM pmOut3 =
      fw_layernorm (denoteGraph pm initPM pmIn3)
                   (denoteGraph pm initPM wTid)
                   (denoteGraph pm initPM bTid))
    (hw_sm_pm : denoteGraph sm initSM wTid = denoteGraph pm initPM wTid)
    (hb_sm_pm : denoteGraph sm initSM bTid = denoteGraph pm initPM bTid)
    (hxshape : (denoteGraph sm initSM smInTid).shape = [1, 8, 32])
    (hxshape_pm0 : (denoteGraph pm initPM pmIn0).shape = [1, 2, 32])
    (hxshape_pm1 : (denoteGraph pm initPM pmIn1).shape = [1, 2, 32])
    (hxshape_pm2 : (denoteGraph pm initPM pmIn2).shape = [1, 2, 32])
    (hxshape_pm3 : (denoteGraph pm initPM pmIn3).shape = [1, 2, 32])
    (hinput_chunk0 : denoteGraph pm initPM pmIn0 =
      chunkPrimDimN 1 4 0 (denoteGraph sm initSM smInTid))
    (hinput_chunk1 : denoteGraph pm initPM pmIn1 =
      chunkPrimDimN 1 4 1 (denoteGraph sm initSM smInTid))
    (hinput_chunk2 : denoteGraph pm initPM pmIn2 =
      chunkPrimDimN 1 4 2 (denoteGraph sm initSM smInTid))
    (hinput_chunk3 : denoteGraph pm initPM pmIn3 =
      chunkPrimDimN 1 4 3 (denoteGraph sm initSM smInTid)) :
    (denoteGraph sm initSM smOutTid).shape = [1, 8, 32] ∧
      ([(denoteGraph pm initPM pmOut0).shape,
        (denoteGraph pm initPM pmOut1).shape,
        (denoteGraph pm initPM pmOut2).shape,
        (denoteGraph pm initPM pmOut3).shape] =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]]) ∧
      denoteGraph sm initSM smOutTid =
        allGatherPrimDimN 1 4 0
          [denoteGraph pm initPM pmOut0, denoteGraph pm initPM pmOut1,
           denoteGraph pm initPM pmOut2, denoteGraph pm initPM pmOut3] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm_eval]
    exact fw_layernorm_shape_1_8_32 _ _ _ hxshape
  · rw [hpm0_eval, hpm1_eval, hpm2_eval, hpm3_eval]
    have h0 := fw_layernorm_shape_1_2_32 (denoteGraph pm initPM pmIn0)
        (denoteGraph pm initPM wTid) (denoteGraph pm initPM bTid) hxshape_pm0
    have h1 := fw_layernorm_shape_1_2_32 (denoteGraph pm initPM pmIn1)
        (denoteGraph pm initPM wTid) (denoteGraph pm initPM bTid) hxshape_pm1
    have h2 := fw_layernorm_shape_1_2_32 (denoteGraph pm initPM pmIn2)
        (denoteGraph pm initPM wTid) (denoteGraph pm initPM bTid) hxshape_pm2
    have h3 := fw_layernorm_shape_1_2_32 (denoteGraph pm initPM pmIn3)
        (denoteGraph pm initPM wTid) (denoteGraph pm initPM bTid) hxshape_pm3
    rw [h0, h1, h2, h3]
  · rw [hsm_eval, hpm0_eval, hpm1_eval, hpm2_eval, hpm3_eval]
    rw [hinput_chunk0, hinput_chunk1, hinput_chunk2, hinput_chunk3]
    rw [← hw_sm_pm, ← hb_sm_pm]
    exact fw_layernorm_split_dim1_4_1_8_32 _ _ _ hxshape

end TrainVerify.Denote.GeneratedPatterns
