/- Intermediate reconstruction lemmas for the YOCO-MoE cut→full bridges.

   Goal: discharge the ~1151-element `goal_N_prereqs` requirement by proving
   each `intermediateGoal_XXXX` holds on the COMPUTED stores
   `denoteGraph sm initSM` / `denoteGraph pm initPM`, packaged as per-op
   sub-lemmas joined by `InitGoalsHold_append`.

   See PROGRESS.md / HANDOFF.md at repo root for coverage status.
-/
import denote.yoco_goals.BridgeKit
import denote.yoco_goals.Goal_5_Intermediate

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- goal_5 value equality on computed stores: `sm 4680 = pm 4680`. -/
theorem recon_4680 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph sm initSM 4680 = denoteGraph pm initPM 4680 := by
  have h := goal_5_intermediate initSM initPM hSM hPM hInit
  unfold InitGoalHolds at h
  have hval := h.2.2
  simp only [goal_5, List.map, reconstructForGoal, reconstructWithDim_singleton] at hval
  exact hval

/-- Proof-of-concept: `intermediateGoal_4681` (FW_float, replicated prefix).
    FW_float is value-identity, so this reduces to `recon_4680`. -/
theorem recon_intermediateGoal_4681 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4681
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  -- SM: denoteGraph sm initSM 4681 = denoteGraph sm initSM 4680  (float = identity)
  have hsm : denoteGraph sm initSM 4681 = denoteGraph sm initSM 4680 := by
    rw [sm_val initSM 1 4681 (by native_decide) (by native_decide)]
    rw [show sm.nodes[1]'(by native_decide)
        = { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] }
        from by native_decide]
    rw [applyNode_fw_float_out]
    rw [sm_prefix_eq initSM 1 4680 (by native_decide)]
  -- PM: last writer of 4681 is node 28 (rank 1 float); input 4680.
  have hpm : denoteGraph pm initPM 4681 = denoteGraph pm initPM 4680 := by
    rw [pm_val initPM 28 4681 (by native_decide) (by native_decide)]
    rw [show pm.nodes[28]'(by native_decide)
        = { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] }
        from by native_decide]
    rw [applyNode_fw_float_out]
    rw [pm_prefix_eq initPM 28 4680 (by native_decide)]
  have h4680 := recon_4680 initSM initPM hSM hPM hInit
  -- Shape of 4680 from goal_5.
  have hshape : (denoteGraph sm initSM 4680).shape = [4096, 1024] := by
    have h := goal_5_intermediate initSM initPM hSM hPM hInit
    unfold InitGoalHolds at h
    have := h.1; simpa [goal_5] using this
  refine ⟨?_, ?_, ?_⟩
  · -- (sm 4681).shape = [4096,1024]
    simp only [intermediateGoal_4681]
    rw [hsm, hshape]
  · -- [(pm 4681).shape] = [[4096,1024]]
    simp only [intermediateGoal_4681, List.map]
    rw [hpm, ← h4680, hshape]
  · -- sm 4681 = reconstruct [pm 4681]
    simp only [intermediateGoal_4681, List.map, reconstructForGoal_of_not_replicated,
               reconstructWithDim_singleton]
    rw [hsm, hpm, h4680]

end TrainVerify.Denote.GeneratedPatterns
