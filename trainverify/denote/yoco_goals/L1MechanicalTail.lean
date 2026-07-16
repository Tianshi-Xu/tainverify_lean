/- Worker #21 — Layer-0/1 MoE residual tail over `denoteGraph_ringAttn`.

   Extends Worker #16's L1 gate-branch chain (`4731`/`4732`/`4733`) past the
   MoE all2all output `4714` (now discharged, given the well-formed-input
   contract `WellFormed_YOCOMoE_A04B`) into the residual add + float:

   - `recon_intermediateGoal_4734_ringAttn` — FW_add(4714, 4733)  (MoE residual)
   - `recon_intermediateGoal_4735_ringAttn` — FW_float(4734)       (dtype cast)

   Both are 1-tp replicated singletons whose inputs are same-tid on the SM and PM
   graphs, so they mirror the Worker #12/#16 replicated templates
   (`ringAttn_reduce2`/`ringAttn_reduce1` + `wrap_1tp_gen`).  They carry the `hWF`
   contract because they depend on `recon_intermediateGoal_4714_ringAttn`.
-/
import denote.yoco_goals.WellFormedInputs
import denote.yoco_goals.L1MechanicalReconstruction

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-! ### 4734 — MoE residual add FW_add(4714, 4733) (replicated) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4734_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4734
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- MoE all2all output 4714 (discharged given the well-formed-input contract)
  have h4714 := recon_intermediateGoal_4714_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4714 : denoteGraph_ringAttn sm initSM 4714 = denoteGraph_ringAttn pm initPM 4714 :=
    oneTp_valeq intermediateGoal_4714 _ _ 4714 rfl rfl rfl rfl h4714
  have hs4714 : (denoteGraph_ringAttn sm initSM 4714).shape = [4096, 1024] := by
    have := h4714.1; simpa [intermediateGoal_4714] using this
  -- gate-branch output 4733 (Worker #16)
  have h4733 := recon_intermediateGoal_4733_ringAttn initSM initPM hSM hPM hInit
  have hv4733 : denoteGraph_ringAttn sm initSM 4733 = denoteGraph_ringAttn pm initPM 4733 :=
    oneTp_valeq intermediateGoal_4733 _ _ 4733 rfl rfl rfl rfl h4733
  have hs4733 : (denoteGraph_ringAttn sm initSM 4733).shape = [4096, 1024] := by
    have := h4733.1; simpa [intermediateGoal_4733] using this
  have rSM : denoteGraph_ringAttn sm initSM 4734
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 4714) (denoteGraph_ringAttn sm initSM 4733) :=
    ringAttn_reduce2 sm initSM 38
      { rank := 0, op := "OpName.FW_add", ins := [4714, 4733], outs := [4734] }
      4714 4733 4734 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 4714 4733 4734)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4734
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 4714) (denoteGraph_ringAttn pm initPM 4733) :=
    ringAttn_reduce2 pm initPM 119
      { rank := 1, op := "OpName.FW_add", ins := [4714, 4733], outs := [4734] }
      4714 4733 4734 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 4714 4733 4734)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4734 = denoteGraph_ringAttn pm initPM 4734 := by
    rw [rSM, rPM, hv4714, hv4733]
  have hshape : (denoteGraph_ringAttn sm initSM 4734).shape = [4096, 1024] := by
    rw [rSM]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] hs4714 hs4733
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4734 4734 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4735 — dtype cast FW_float(4734) (identity, replicated) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4735_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4735
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4734 := recon_intermediateGoal_4734_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4734 : denoteGraph_ringAttn sm initSM 4734 = denoteGraph_ringAttn pm initPM 4734 :=
    oneTp_valeq intermediateGoal_4734 _ _ 4734 rfl rfl rfl rfl h4734
  have hs4734 : (denoteGraph_ringAttn sm initSM 4734).shape = [4096, 1024] := by
    have := h4734.1; simpa [intermediateGoal_4734] using this
  have rSM : denoteGraph_ringAttn sm initSM 4735 = id (denoteGraph_ringAttn sm initSM 4734) :=
    ringAttn_reduce1 sm initSM 39
      { rank := 0, op := "OpName.FW_float", ins := [4734], outs := [4735] }
      4734 4735 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4734 4735 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4735 = id (denoteGraph_ringAttn pm initPM 4734) :=
    ringAttn_reduce1 pm initPM 121
      { rank := 1, op := "OpName.FW_float", ins := [4734], outs := [4735] }
      4734 4735 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 4734 4735 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rPM
  have hval : denoteGraph_ringAttn sm initSM 4735 = denoteGraph_ringAttn pm initPM 4735 := by
    rw [rSM, rPM, hv4734]
  have hshape : (denoteGraph_ringAttn sm initSM 4735).shape = [4096, 1024] := by
    rw [rSM]; exact hs4734
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4735 4735 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

end TrainVerify.Denote.GeneratedPatterns
