/- Worker #22 — Layer-1 per-head Q/K/V projection + rotary embedding tail.

   Extends Worker #21's L1 residual/RMSNorm tail (`4734…4738`) through the
   attention front-half of layer 1:

   - `recon_intermediateGoal_4740_ringAttn` — FW_per_head_mix_precision_linear Q  (4738·4739 → [4096,16,64])
   - `recon_intermediateGoal_4742_ringAttn` — FW_per_head_mix_precision_linear K  (4738·4741 → [4096,4,64])
   - `recon_intermediateGoal_4744_ringAttn` — FW_per_head_mix_precision_linear V  (4738·4743 → [4096,4,64])
   - `recon_intermediateGoal_4746_ringAttn` — FW_rotary_embedding.1 (Q')          ([4096,16,64])
   - `recon_intermediateGoal_4747_ringAttn` — FW_rotary_embedding.2 (K')          ([4096,4,64])

   These are 1-tp replicated singletons.  Their PM firings live at HIGH pm-graph
   node indices (rank-1 3-way `FW_multiref` at pm node 129, per-head linears at
   pm nodes 133-135, rotary at pm node 137), so they route the PM reductions
   through the whnf-safe `ringAttn_reduce{1,2}_pm_opaque` / `ringAttn_node_core_pm_opaque`
   gears (Worker #22, Part A) that dodge the `congr 1` fold blowup.

   No new well-formed-input field is needed: `FW_multiref` is the identity, and
   `fw_per_head_linear` / `fw_rotary_embedding` are pure functions, so equality of
   `4738` + replicated weights forces equality of the outputs structurally.
-/
import denote.yoco_goals.L1MechanicalTail
import denote.yoco_goals.RingAttnGearsPM

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-! ### 4740 — Q per-head linear FW_per_head(7444/14689, 4739) (replicated) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4740_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4740
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4738 := recon_intermediateGoal_4738_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4738 : denoteGraph_ringAttn sm initSM 4738 = denoteGraph_ringAttn pm initPM 4738 :=
    oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl h4738
  have hs4738 : (denoteGraph_ringAttn sm initSM 4738).shape = [4096, 1024] := by
    have := h4738.1; simpa [intermediateGoal_4738] using this
  -- SM: 7444 = multiref3-first(4738) [sm node 43]
  have s7444 : denoteGraph_ringAttn sm initSM 7444 = id (denoteGraph_ringAttn sm initSM 4738) :=
    ringAttn_reduce1 sm initSM 43
      { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452], params := [3] }
      4738 7444 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' sm s 0 4738 7444 7448 7452)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM: 14689 = multiref3-first(4738) [pm node 129] — whnf-safe variant
  have p14689 : denoteGraph_ringAttn pm initPM 14689 = id (denoteGraph_ringAttn pm initPM 4738) :=
    ringAttn_reduce1_pm_opaque pm initPM 129
      { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697], params := [3] }
      4738 14689 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_first_out' pm s 1 4738 14689 14693 14697)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7444 p14689
  -- weight 4739 : [16, 64, 1024]
  have hw4739 : denoteGraph_ringAttn sm initSM 4739 = denoteGraph_ringAttn pm initPM 4739 :=
    veq_weight_ring initSM initPM hInit initGoal_4739 (by native_decide) 4739
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4739 : (denoteGraph_ringAttn sm initSM 4739).shape = [16, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4739 (by native_decide) 4739 [16, 64, 1024]
      rfl rfl (by native_decide)
  -- SM 4740 = per_head(7444, 4739) [sm node 44]
  have rSM : denoteGraph_ringAttn sm initSM 4740
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7444) (denoteGraph_ringAttn sm initSM 4739) :=
    ringAttn_reduce2 sm initSM 44
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7444, 4739], outs := [4740] }
      7444 4739 4740 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7444 4739 4740 [])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- PM 4740 = per_head(14689, 4739) [pm node 133] — whnf-safe variant
  have rPM : denoteGraph_ringAttn pm initPM 4740
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14689) (denoteGraph_ringAttn pm initPM 4739) :=
    ringAttn_reduce2_pm_opaque pm initPM 133
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14689, 4739], outs := [4740] }
      14689 4739 4740 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14689 4739 4740 [])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4740 = denoteGraph_ringAttn pm initPM 4740 := by
    rw [rSM, rPM, s7444, p14689, hv4738, hw4739]
  have hshape : (denoteGraph_ringAttn sm initSM 4740).shape = [4096, 16, 64] := by
    rw [rSM]
    exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64 (by rw [s7444]; exact hs4738) hsw4739
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4740 4740 [4096, 16, 64] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4742 — K per-head linear FW_per_head(7448/14693, 4741) (replicated) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4742_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4742
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4738 := recon_intermediateGoal_4738_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4738 : denoteGraph_ringAttn sm initSM 4738 = denoteGraph_ringAttn pm initPM 4738 :=
    oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl h4738
  have hs4738 : (denoteGraph_ringAttn sm initSM 4738).shape = [4096, 1024] := by
    have := h4738.1; simpa [intermediateGoal_4738] using this
  -- SM: 7448 = multiref3-second(4738) [sm node 43]
  have s7448 : denoteGraph_ringAttn sm initSM 7448 = id (denoteGraph_ringAttn sm initSM 4738) :=
    ringAttn_reduce1 sm initSM 43
      { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452], params := [3] }
      4738 7448 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' sm s 0 4738 7444 7448 7452 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM: 14693 = multiref3-second(4738) [pm node 129] — whnf-safe variant
  have p14693 : denoteGraph_ringAttn pm initPM 14693 = id (denoteGraph_ringAttn pm initPM 4738) :=
    ringAttn_reduce1_pm_opaque pm initPM 129
      { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697], params := [3] }
      4738 14693 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_second_out' pm s 1 4738 14689 14693 14697 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7448 p14693
  have hw4741 : denoteGraph_ringAttn sm initSM 4741 = denoteGraph_ringAttn pm initPM 4741 :=
    veq_weight_ring initSM initPM hInit initGoal_4741 (by native_decide) 4741
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4741 : (denoteGraph_ringAttn sm initSM 4741).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4741 (by native_decide) 4741 [4, 64, 1024]
      rfl rfl (by native_decide)
  -- SM 4742 = per_head(7448, 4741) [sm node 45]
  have rSM : denoteGraph_ringAttn sm initSM 4742
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7448) (denoteGraph_ringAttn sm initSM 4741) :=
    ringAttn_reduce2 sm initSM 45
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7448, 4741], outs := [4742] }
      7448 4741 4742 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7448 4741 4742 [])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- PM 4742 = per_head(14693, 4741) [pm node 134] — whnf-safe variant
  have rPM : denoteGraph_ringAttn pm initPM 4742
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14693) (denoteGraph_ringAttn pm initPM 4741) :=
    ringAttn_reduce2_pm_opaque pm initPM 134
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14693, 4741], outs := [4742] }
      14693 4741 4742 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14693 4741 4742 [])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4742 = denoteGraph_ringAttn pm initPM 4742 := by
    rw [rSM, rPM, s7448, p14693, hv4738, hw4741]
  have hshape : (denoteGraph_ringAttn sm initSM 4742).shape = [4096, 4, 64] := by
    rw [rSM]
    exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s7448]; exact hs4738) hsw4741
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4742 4742 [4096, 4, 64] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4744 — V per-head linear FW_per_head(7452/14697, 4743) (replicated) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4744_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4744
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4738 := recon_intermediateGoal_4738_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4738 : denoteGraph_ringAttn sm initSM 4738 = denoteGraph_ringAttn pm initPM 4738 :=
    oneTp_valeq intermediateGoal_4738 _ _ 4738 rfl rfl rfl rfl h4738
  have hs4738 : (denoteGraph_ringAttn sm initSM 4738).shape = [4096, 1024] := by
    have := h4738.1; simpa [intermediateGoal_4738] using this
  -- SM: 7452 = multiref3-third(4738) [sm node 43]
  have s7452 : denoteGraph_ringAttn sm initSM 7452 = id (denoteGraph_ringAttn sm initSM 4738) :=
    ringAttn_reduce1 sm initSM 43
      { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452], params := [3] }
      4738 7452 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' sm s 0 4738 7444 7448 7452 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM: 14697 = multiref3-third(4738) [pm node 129] — whnf-safe variant
  have p14697 : denoteGraph_ringAttn pm initPM 14697 = id (denoteGraph_ringAttn pm initPM 4738) :=
    ringAttn_reduce1_pm_opaque pm initPM 129
      { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697], params := [3] }
      4738 14697 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref3_third_out' pm s 1 4738 14689 14693 14697 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7452 p14697
  have hw4743 : denoteGraph_ringAttn sm initSM 4743 = denoteGraph_ringAttn pm initPM 4743 :=
    veq_weight_ring initSM initPM hInit initGoal_4743 (by native_decide) 4743
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4743 : (denoteGraph_ringAttn sm initSM 4743).shape = [4, 64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4743 (by native_decide) 4743 [4, 64, 1024]
      rfl rfl (by native_decide)
  -- SM 4744 = per_head(7452, 4743) [sm node 46]
  have rSM : denoteGraph_ringAttn sm initSM 4744
      = fw_per_head_linear (denoteGraph_ringAttn sm initSM 7452) (denoteGraph_ringAttn sm initSM 4743) :=
    ringAttn_reduce2 sm initSM 46
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7452, 4743], outs := [4744] }
      7452 4743 4744 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out sm s 0 7452 4743 4744 [])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- PM 4744 = per_head(14697, 4743) [pm node 135] — whnf-safe variant
  have rPM : denoteGraph_ringAttn pm initPM 4744
      = fw_per_head_linear (denoteGraph_ringAttn pm initPM 14697) (denoteGraph_ringAttn pm initPM 4743) :=
    ringAttn_reduce2_pm_opaque pm initPM 135
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14697, 4743], outs := [4744] }
      14697 4743 4744 fw_per_head_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_per_head_mix_precision_linear_out pm s 1 14697 4743 4744 [])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4744 = denoteGraph_ringAttn pm initPM 4744 := by
    rw [rSM, rPM, s7452, p14697, hv4738, hw4743]
  have hshape : (denoteGraph_ringAttn sm initSM 4744).shape = [4096, 4, 64] := by
    rw [rSM]
    exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s7452]; exact hs4738) hsw4743
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4744 4744 [4096, 4, 64] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### rotary bridges shared by 4746/4747 -/

/-- Rotary cos-sin cache agreement (ring form): SM tid `4691` and the PM rank-1
    broadcast copy `11854` carry the same value. -/
theorem hcache_4691_11854 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4691 = denoteGraph_ringAttn pm initPM 11854 := by
  rw [sm_ring_eq initSM 4691 (by native_decide), pm_ring_eq initPM 11854 (by native_decide)]
  exact sm_pm_rotary_cache_agree initSM initPM hInit 11854 1 (by norm_num) rfl

/-! ### 4746 — rotary embedding first output (Q') -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4746_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4746
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4740 := recon_intermediateGoal_4740_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4740 : denoteGraph_ringAttn sm initSM 4740 = denoteGraph_ringAttn pm initPM 4740 :=
    oneTp_valeq intermediateGoal_4740 _ _ 4740 rfl rfl rfl rfl h4740
  have hs4740 : (denoteGraph_ringAttn sm initSM 4740).shape = [4096, 16, 64] := by
    have := h4740.1; simpa [intermediateGoal_4740] using this
  have h4742 := recon_intermediateGoal_4742_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4742 : denoteGraph_ringAttn sm initSM 4742 = denoteGraph_ringAttn pm initPM 4742 :=
    oneTp_valeq intermediateGoal_4742 _ _ 4742 rfl rfl rfl rfl h4742
  have hw4745 : denoteGraph_ringAttn sm initSM 4745 = denoteGraph_ringAttn pm initPM 4745 :=
    veq_weight_ring initSM initPM hInit initGoal_4745 (by native_decide) 4745
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcache := hcache_4691_11854 initSM initPM hInit
  -- SM 4746 = rotary(4691, 4745, 4740, 4742).1 [sm node 47]
  have rSM : denoteGraph_ringAttn sm initSM 4746
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 4745)
          (denoteGraph_ringAttn sm initSM 4740) (denoteGraph_ringAttn sm initSM 4742) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 47
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] }
          4746 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm sm initSM 47 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 47 4745 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 47 4740 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 47 4742 (by native_decide) (by native_decide)]
  -- PM 4746 = rotary(11854, 4745, 4740, 4742).1 [pm node 137, rank 1]
  have rPM : denoteGraph_ringAttn pm initPM 4746
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11854) (denoteGraph_ringAttn pm initPM 4745)
          (denoteGraph_ringAttn pm initPM 4740) (denoteGraph_ringAttn pm initPM 4742) 16 4).1 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 137
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11854, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] }
          4746 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_fst_out,
        ringAttn_prefix_read_pm pm initPM 137 11854 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 137 4745 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 137 4740 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 137 4742 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 4746 = denoteGraph_ringAttn pm initPM 4746 := by
    rw [rSM, rPM, hcache, hw4745, hv4740, hv4742]
  have hshape : (denoteGraph_ringAttn sm initSM 4746).shape = [4096, 16, 64] := by
    rw [rSM, fw_rotary_embedding_fst_shape]; exact hs4740
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4746 4746 [4096, 16, 64] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4747 — rotary embedding second output (K') -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4747_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4747
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4740 := recon_intermediateGoal_4740_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4740 : denoteGraph_ringAttn sm initSM 4740 = denoteGraph_ringAttn pm initPM 4740 :=
    oneTp_valeq intermediateGoal_4740 _ _ 4740 rfl rfl rfl rfl h4740
  have h4742 := recon_intermediateGoal_4742_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4742 : denoteGraph_ringAttn sm initSM 4742 = denoteGraph_ringAttn pm initPM 4742 :=
    oneTp_valeq intermediateGoal_4742 _ _ 4742 rfl rfl rfl rfl h4742
  have hs4742 : (denoteGraph_ringAttn sm initSM 4742).shape = [4096, 4, 64] := by
    have := h4742.1; simpa [intermediateGoal_4742] using this
  have hw4745 : denoteGraph_ringAttn sm initSM 4745 = denoteGraph_ringAttn pm initPM 4745 :=
    veq_weight_ring initSM initPM hInit initGoal_4745 (by native_decide) 4745
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hcache := hcache_4691_11854 initSM initPM hInit
  -- SM 4747 = rotary(4691, 4745, 4740, 4742).2 [sm node 47]
  have rSM : denoteGraph_ringAttn sm initSM 4747
      = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM 4691) (denoteGraph_ringAttn sm initSM 4745)
          (denoteGraph_ringAttn sm initSM 4740) (denoteGraph_ringAttn sm initSM 4742) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque sm initSM 47
          { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] }
          4747 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4745 4740 4742 4746 4747 (by decide),
        ringAttn_prefix_read_pm sm initSM 47 4691 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 47 4745 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 47 4740 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm sm initSM 47 4742 (by native_decide) (by native_decide)]
  -- PM 4747 = rotary(11854, 4745, 4740, 4742).2 [pm node 137, rank 1]
  have rPM : denoteGraph_ringAttn pm initPM 4747
      = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM 11854) (denoteGraph_ringAttn pm initPM 4745)
          (denoteGraph_ringAttn pm initPM 4740) (denoteGraph_ringAttn pm initPM 4742) 16 4).2 := by
    rw [ringAttn_node_core_pm_opaque pm initPM 137
          { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11854, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] }
          4747 (by native_decide) (by native_decide) (by decide) (by decide)
          (by native_decide) (by native_decide),
        applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11854 4745 4740 4742 4746 4747 (by decide),
        ringAttn_prefix_read_pm pm initPM 137 11854 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 137 4745 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 137 4740 (by native_decide) (by native_decide),
        ringAttn_prefix_read_pm pm initPM 137 4742 (by native_decide) (by native_decide)]
  have hval : denoteGraph_ringAttn sm initSM 4747 = denoteGraph_ringAttn pm initPM 4747 := by
    rw [rSM, rPM, hcache, hw4745, hv4740, hv4742]
  have hshape : (denoteGraph_ringAttn sm initSM 4747).shape = [4096, 4, 64] := by
    rw [rSM, fw_rotary_embedding_snd_shape]; exact hs4742
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4747 4747 [4096, 4, 64] rfl rfl rfl rfl rfl rfl hval hshape

end TrainVerify.Denote.GeneratedPatterns
