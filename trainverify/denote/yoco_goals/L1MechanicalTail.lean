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

/-! ### 4736 — post-MoE residual add FW_add(7408, 4735) (replicated, multiref bridge) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4736_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4736
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- residual carry 4703 (L0 block output), already reconstructed
  have h4703 := recon_intermediateGoal_4703_ringAttn initSM initPM hSM hPM hInit
  have hv4703 : denoteGraph_ringAttn sm initSM 4703 = denoteGraph_ringAttn pm initPM 4703 :=
    oneTp_valeq intermediateGoal_4703 _ _ 4703 rfl rfl rfl rfl h4703
  have hs4703 : (denoteGraph_ringAttn sm initSM 4703).shape = [4096, 1024] := by
    have := h4703.1; simpa [intermediateGoal_4703] using this
  -- multiref copies: sm 7408 = pm 14656 = id 4703
  have s7408 : denoteGraph_ringAttn sm initSM 7408 = id (denoteGraph_ringAttn sm initSM 4703) :=
    ringAttn_reduce1 sm initSM 16
      { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] }
      4703 7408 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4703 7404 7408 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14656 : denoteGraph_ringAttn pm initPM 14656 = id (denoteGraph_ringAttn pm initPM 4703) :=
    ringAttn_reduce1 pm initPM 65
      { rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656], params := [2] }
      4703 14656 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 4703 14652 14656 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7408 p14656
  have hv7408 : denoteGraph_ringAttn sm initSM 7408 = denoteGraph_ringAttn pm initPM 14656 := by
    rw [s7408, p14656, hv4703]
  have hs7408 : (denoteGraph_ringAttn sm initSM 7408).shape = [4096, 1024] := by
    rw [s7408]; exact hs4703
  -- float 4735
  have h4735 := recon_intermediateGoal_4735_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4735 : denoteGraph_ringAttn sm initSM 4735 = denoteGraph_ringAttn pm initPM 4735 :=
    oneTp_valeq intermediateGoal_4735 _ _ 4735 rfl rfl rfl rfl h4735
  have hs4735 : (denoteGraph_ringAttn sm initSM 4735).shape = [4096, 1024] := by
    have := h4735.1; simpa [intermediateGoal_4735] using this
  have rSM : denoteGraph_ringAttn sm initSM 4736
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7408) (denoteGraph_ringAttn sm initSM 4735) :=
    ringAttn_reduce2 sm initSM 40
      { rank := 0, op := "OpName.FW_add", ins := [7408, 4735], outs := [4736] }
      7408 4735 4736 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7408 4735 4736)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4736
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14656) (denoteGraph_ringAttn pm initPM 4735) :=
    ringAttn_reduce2 pm initPM 123
      { rank := 1, op := "OpName.FW_add", ins := [14656, 4735], outs := [4736] }
      14656 4735 4736 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 14656 4735 4736)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4736 = denoteGraph_ringAttn pm initPM 4736 := by
    rw [rSM, rPM, hv7408, hv4735]
  have hshape : (denoteGraph_ringAttn sm initSM 4736).shape = [4096, 1024] := by
    rw [rSM]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] hs7408 hs4735
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4736 4736 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4738 — RMSNorm of 4736 (post-attn norm, L1) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4738_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4738
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4736 := recon_intermediateGoal_4736_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4736 : denoteGraph_ringAttn sm initSM 4736 = denoteGraph_ringAttn pm initPM 4736 :=
    oneTp_valeq intermediateGoal_4736 _ _ 4736 rfl rfl rfl rfl h4736
  have hs4736 : (denoteGraph_ringAttn sm initSM 4736).shape = [4096, 1024] := by
    have := h4736.1; simpa [intermediateGoal_4736] using this
  -- 7435 = multiref-first(4736) [SM node 41]; 14668 = multiref-first(4736) [PM node 125 rank1]
  have s7435 : denoteGraph_ringAttn sm initSM 7435 = id (denoteGraph_ringAttn sm initSM 4736) :=
    ringAttn_reduce1 sm initSM 41
      { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [7435, 7439], params := [2] }
      4736 7435 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4736 7435 7439)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14668 : denoteGraph_ringAttn pm initPM 14668 = id (denoteGraph_ringAttn pm initPM 4736) :=
    ringAttn_reduce1 pm initPM 125
      { rank := 1, op := "OpName.FW_multiref", ins := [4736], outs := [14668, 14672], params := [2] }
      4736 14668 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 4736 14668 14672)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7435 p14668
  -- weight 4737 : [1024]
  have hw4737 : denoteGraph_ringAttn sm initSM 4737 = denoteGraph_ringAttn pm initPM 4737 :=
    veq_weight_ring initSM initPM hInit initGoal_4737 (by native_decide) 4737
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  -- SM 4738 = fw_rms_norm(7435, 4737) [SM node 42]
  have rSM : denoteGraph_ringAttn sm initSM 4738
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7435) (denoteGraph_ringAttn sm initSM 4737) :=
    ringAttn_reduce2 sm initSM 42
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7435, 4737], outs := [4738] }
      7435 4737 4738 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7435 4737 4738)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- PM 4738 = fw_rms_norm(14668, 4737) [PM node 127 rank1]
  have rPM : denoteGraph_ringAttn pm initPM 4738
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14668) (denoteGraph_ringAttn pm initPM 4737) :=
    ringAttn_reduce2 pm initPM 127
      { rank := 1, op := "OpName.FW_rms_norm", ins := [14668, 4737], outs := [4738] }
      14668 4737 4738 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 14668 4737 4738)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4738 = denoteGraph_ringAttn pm initPM 4738 := by
    rw [rSM, rPM, s7435, p14668, hv4736, hw4737]
  have hshape : (denoteGraph_ringAttn sm initSM 4738).shape = [4096, 1024] := by
    rw [rSM]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s7435]; exact hs4736)
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4738 4738 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

end TrainVerify.Denote.GeneratedPatterns
