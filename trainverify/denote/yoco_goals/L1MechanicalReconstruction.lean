/- Worker #16 — Layer-1 MoE gate-branch mechanical reconstruction over
   `denoteGraph_ringAttn`.

   Proves the replicated (1-tp) gate-branch intermediate goals that sit between
   Worker #14's MoE swiglu-allgather gear (`4729`) and the residual add (`4734`,
   which is gated by the upstream-blocked `4714` all2all_moe_gmm):

   - `recon_intermediateGoal_4731_ringAttn` — FW_mix_precision_linear(4729, 4730)
   - `recon_intermediateGoal_4732_ringAttn` — FW_view(4731)  (identity reshape)
   - `recon_intermediateGoal_4733_ringAttn` — FW_mul(4719, 4732) (gate * up, broadcast)

   Each mirrors the Worker #12 replicated 1-tp templates (4700/4701/4702) using
   `ringAttn_reduce1` / `ringAttn_reduce2` + `wrap_1tp_gen`. Inputs `4729` (W14),
   `4719` (W12 sigmoid gate) and weight leaf `4730` are already reconstructed.
-/
import denote.yoco_goals.MoEShardedReconstruction

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem elemwiseMul_shape_eq (x y : Tensor) :
    (elemwiseMul x y).shape = outShape2 x y := rfl

/-! ### 4731 — MoE up-projection linear (mix_precision_linear, replicated) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4731_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4731
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4729 := recon_intermediateGoal_4729_ringAttn initSM initPM hSM hPM hInit
  have hv4729 : denoteGraph_ringAttn sm initSM 4729 = denoteGraph_ringAttn pm initPM 4729 :=
    oneTp_valeq intermediateGoal_4729 _ _ 4729 rfl rfl rfl rfl h4729
  have hs4729 : (denoteGraph_ringAttn sm initSM 4729).shape = [4096, 512] := by
    have := h4729.1; simpa [intermediateGoal_4729] using this
  have hw4730 : denoteGraph_ringAttn sm initSM 4730 = denoteGraph_ringAttn pm initPM 4730 :=
    veq_weight_ring initSM initPM hInit initGoal_4730 (by native_decide) 4730
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4730 : (denoteGraph_ringAttn sm initSM 4730).shape = [1024, 512] :=
    shape_weight_ring initSM initPM hInit initGoal_4730 (by native_decide) 4730 [1024, 512]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4731
      = fw_linear (denoteGraph_ringAttn sm initSM 4729) (denoteGraph_ringAttn sm initSM 4730) :=
    ringAttn_reduce2 sm initSM 35
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731] }
      4729 4730 4731 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4729 4730 4731)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4731
      = fw_linear (denoteGraph_ringAttn pm initPM 4729) (denoteGraph_ringAttn pm initPM 4730) :=
    ringAttn_reduce2 pm initPM 113
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731] }
      4729 4730 4731 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 4729 4730 4731)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4731 = denoteGraph_ringAttn pm initPM 4731 := by
    rw [rSM, rPM, hv4729, hw4730]
  have hshape : (denoteGraph_ringAttn sm initSM 4731).shape = [4096, 1024] := by
    rw [rSM]; exact fw_linear_2d_shape 4096 512 1024 _ _ hs4729 hsw4730
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4731 4731 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4732 — view of the up-projection (identity reshape, replicated) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4732_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4732
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4731 := recon_intermediateGoal_4731_ringAttn initSM initPM hSM hPM hInit
  have hv4731 : denoteGraph_ringAttn sm initSM 4731 = denoteGraph_ringAttn pm initPM 4731 :=
    oneTp_valeq intermediateGoal_4731 _ _ 4731 rfl rfl rfl rfl h4731
  have rSM : denoteGraph_ringAttn sm initSM 4732
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4731) :=
    ringAttn_reduce1 sm initSM 36
      { rank := 0, op := "OpName.FW_view", ins := [4731], outs := [4732], params := [4096, 1024] }
      4731 4732 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4731 4732)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4732
      = fw_view [4096, 1024] (denoteGraph_ringAttn pm initPM 4731) :=
    ringAttn_reduce1 pm initPM 115
      { rank := 1, op := "OpName.FW_view", ins := [4731], outs := [4732], params := [4096, 1024] }
      4731 4732 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 4096 [1024] 4731 4732)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4732 = denoteGraph_ringAttn pm initPM 4732 := by
    rw [rSM, rPM, hv4731]
  have hshape : (denoteGraph_ringAttn sm initSM 4732).shape = [4096, 1024] := by
    rw [rSM]; rfl
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4732 4732 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4733 — gate * up-projection (elemwise mul, broadcast [4096,1]×[4096,1024]) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4733_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4733
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4719 := recon_intermediateGoal_4719_ringAttn initSM initPM hSM hPM hInit
  have hv4719 : denoteGraph_ringAttn sm initSM 4719 = denoteGraph_ringAttn pm initPM 4719 :=
    oneTp_valeq intermediateGoal_4719 _ _ 4719 rfl rfl rfl rfl h4719
  have hs4719 : (denoteGraph_ringAttn sm initSM 4719).shape = [4096, 1] := by
    have := h4719.1; simpa [intermediateGoal_4719] using this
  have h4732 := recon_intermediateGoal_4732_ringAttn initSM initPM hSM hPM hInit
  have hv4732 : denoteGraph_ringAttn sm initSM 4732 = denoteGraph_ringAttn pm initPM 4732 :=
    oneTp_valeq intermediateGoal_4732 _ _ 4732 rfl rfl rfl rfl h4732
  have hs4732 : (denoteGraph_ringAttn sm initSM 4732).shape = [4096, 1024] := by
    have := h4732.1; simpa [intermediateGoal_4732] using this
  have rSM : denoteGraph_ringAttn sm initSM 4733
      = elemwiseMul (denoteGraph_ringAttn sm initSM 4719) (denoteGraph_ringAttn sm initSM 4732) :=
    ringAttn_reduce2 sm initSM 37
      { rank := 0, op := "OpName.FW_mul", ins := [4719, 4732], outs := [4733] }
      4719 4732 4733 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out sm s 0 4719 4732 4733)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4733
      = elemwiseMul (denoteGraph_ringAttn pm initPM 4719) (denoteGraph_ringAttn pm initPM 4732) :=
    ringAttn_reduce2 pm initPM 117
      { rank := 1, op := "OpName.FW_mul", ins := [4719, 4732], outs := [4733] }
      4719 4732 4733 elemwiseMul (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mul_out pm s 1 4719 4732 4733)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4733 = denoteGraph_ringAttn pm initPM 4733 := by
    rw [rSM, rPM, hv4719, hv4732]
  have hshape : (denoteGraph_ringAttn sm initSM 4733).shape = [4096, 1024] := by
    rw [rSM, elemwiseMul_shape_eq]
    unfold outShape2
    rw [hs4719, hs4732]
    decide
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4733 4733 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

end TrainVerify.Denote.GeneratedPatterns
