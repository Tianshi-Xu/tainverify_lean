/- Worker #23 — Layer-2 reconstruction cascade over `denoteGraph_ringAttn`.

   Chains forward from Worker #21's `recon_intermediateGoal_4750_ringAttn`
   (the layer-1 sliding-window attention output, unconditional-given-WF) through
   the layer-2 forward block:

     - Phase 1: `4751` (2-tp reshape of attention output), `4752` (sharded→
       replicated gather bridge).
     - Phase 2: `4754…4762` down-projection + residual + RMSNorm + router head
       (all 1-tp replicated, mirroring the L1 `4700…4708` template).
     - Router expert-input branches `4769…4781`.
     - Phase 3: the 2-tp MoE core (topk `4763/4764`, sigmoid `4773`, swiglu
       `4782`, `4783/4785/4786/4787`), the expert-parallel all2all `4768`, and the
       2-tp residual/RMSNorm/per-head/rotary tail `4788…4801`.

   Unlike the L1 block (fully 1-tp replicated because its MoE runs all 64 experts
   on each rank), the L2 block is a genuine 2-tp SHARDED cascade: the residual
   stream becomes sequence-parallel after the first attention/MoE block and the
   MoE is expert-parallel (rank 0 = experts 0-32, rank 1 = experts 32-64).

   Everything carries the `WellFormed_YOCOMoE_A04B` contract `hWF` because the
   block depends on `recon_intermediateGoal_4750_ringAttn` (attention) and the
   expert-parallel all2all `4768` (routing-locality). -/
import denote.yoco_goals.WellFormedInputs
import denote.yoco_goals.RingAttnGearsPM
import denote.yoco_goals.L1MechanicalTail

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- Whnf-safe `FW_reshape` node reduction over the ring denotation. Drop-in for
    `ringAttn_reshape_reduce_g12` that routes through `ringAttn_reduce1_pm_opaque`
    so it never triggers the high-node-index `congr 1` whnf blowup. -/
theorem ringAttn_reshape_reduce_pm (g : GraphDecl) (init : Store) (k : Nat)
    (rank inTid outTid : Tid) (hd : Nat) (tl : List Nat)
    (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk =
      { rank := rank, op := "OpName.FW_reshape", ins := [inTid], outs := [outTid], params := hd :: tl })
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraph_ringAttn g init outTid = fw_view (hd :: tl) (denoteGraph_ringAttn g init inTid) :=
  ringAttn_reduce1_pm_opaque g init k
    { rank := rank, op := "OpName.FW_reshape", ins := [inTid], outs := [outTid], params := hd :: tl }
    inTid outTid (fw_view (hd :: tl)) hk hnode
    (show ¬ (("OpName.FW_reshape" : String) = "OpName.FW_attn_zigzag") by decide)
    (show ¬ (("OpName.FW_reshape" : String) = "OpName.FW_attn_sliding_window") by decide)
    (fun s => applyNode_fw_reshape_out g s rank inTid outTid (hd :: tl))
    hdrop_nil hdrop hpre_nil hpre

/-! ## Phase 1 — attention-output reshape (2-tp) + gather bridge -/

/-- SM 4750 value reconstruction: `sm 4750 = allGather0 [pm 7623, pm 7624]`. -/
theorem hval_4750 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 4750
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7623, denoteGraph_ringAttn pm initPM 7624] := by
  have h := recon_intermediateGoal_4750_ringAttn initSM initPM hSM hPM hInit hWF
  have hshapes := h.2.1
  simp only [intermediateGoal_4750, List.map, List.cons.injEq, and_true] at hshapes
  obtain ⟨hs7623, _hs7624⟩ := hshapes
  have hv := h.2.2
  rw [reconstructForGoal_of_not_replicated intermediateGoal_4750 pm.numRanks _ rfl] at hv
  simp only [intermediateGoal_4750, List.map] at hv
  rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
        (by rw [hs7623]; decide)] at hv
  exact hv

theorem hs_7623 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    (denoteGraph_ringAttn pm initPM 7623).shape = [2048, 16, 64] := by
  have h := recon_intermediateGoal_4750_ringAttn initSM initPM hSM hPM hInit hWF
  have hshapes := h.2.1
  simp only [intermediateGoal_4750, List.map, List.cons.injEq, and_true] at hshapes
  exact hshapes.1

theorem hs_7624 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    (denoteGraph_ringAttn pm initPM 7624).shape = [2048, 16, 64] := by
  have h := recon_intermediateGoal_4750_ringAttn initSM initPM hSM hPM hInit hWF
  have hshapes := h.2.1
  simp only [intermediateGoal_4750, List.map, List.cons.injEq, and_true] at hshapes
  exact hshapes.2

/-- 4751 — 2-tp reshape of the attention output `[4096,16,64] → [4096,1024]`. -/
theorem recon_intermediateGoal_4751_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4751
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hval50 := hval_4750 initSM initPM hSM hPM hInit hWF
  have hs7623 := hs_7623 initSM initPM hSM hPM hInit hWF
  have hs7624 := hs_7624 initSM initPM hSM hPM hInit hWF
  -- reshape node reductions over the ring denotation
  have rSM : denoteGraph_ringAttn sm initSM 4751
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4750) :=
    ringAttn_reshape_reduce_pm sm initSM 49 0 4750 4751 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7625
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7623) :=
    ringAttn_reshape_reduce_pm pm initPM 146 0 7623 7625 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7626
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7624) :=
    ringAttn_reshape_reduce_pm pm initPM 147 1 7624 7626 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval51 : denoteGraph_ringAttn sm initSM 4751
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7625, denoteGraph_ringAttn pm initPM 7626] := by
    rw [rSM, hval50, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs7623 hs7624
  have hs7625 : (denoteGraph_ringAttn pm initPM 7625).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs7626 : (denoteGraph_ringAttn pm initPM 7626).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4751 : (denoteGraph_ringAttn sm initSM 4751).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4751 4751 7625 7626 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval51 hs4751 hs7625 hs7626

/-! ### helper extraction from 4751 for the gather bridge -/

theorem hval_4751 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 4751
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7625, denoteGraph_ringAttn pm initPM 7626] := by
  have h := recon_intermediateGoal_4751_ringAttn initSM initPM hSM hPM hInit hWF
  have hshapes := h.2.1
  simp only [intermediateGoal_4751, List.map, List.cons.injEq, and_true] at hshapes
  obtain ⟨hs7625, _hs7626⟩ := hshapes
  have hv := h.2.2
  rw [reconstructForGoal_of_not_replicated intermediateGoal_4751 pm.numRanks _ rfl] at hv
  simp only [intermediateGoal_4751, List.map] at hv
  rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
        (by rw [hs7625]; decide)] at hv
  exact hv

theorem hs_7625 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    (denoteGraph_ringAttn pm initPM 7625).shape = [2048, 1024] := by
  have h := recon_intermediateGoal_4751_ringAttn initSM initPM hSM hPM hInit hWF
  have hshapes := h.2.1
  simp only [intermediateGoal_4751, List.map, List.cons.injEq, and_true] at hshapes
  exact hshapes.1

theorem hs_7626 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    (denoteGraph_ringAttn pm initPM 7626).shape = [2048, 1024] := by
  have h := recon_intermediateGoal_4751_ringAttn initSM initPM hSM hPM hInit hWF
  have hshapes := h.2.1
  simp only [intermediateGoal_4751, List.map, List.cons.injEq, and_true] at hshapes
  exact hshapes.2

theorem hs_4751 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    (denoteGraph_ringAttn sm initSM 4751).shape = [4096, 1024] := by
  have h := recon_intermediateGoal_4751_ringAttn initSM initPM hSM hPM hInit hWF
  have := h.1; simpa [intermediateGoal_4751] using this

/-- 4752 — sharded→replicated gather bridge (identity reshapes + AllGatherPrim). -/
theorem recon_intermediateGoal_4752_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4752
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hval51 := hval_4751 initSM initPM hSM hPM hInit hWF
  have hs7625 := hs_7625 initSM initPM hSM hPM hInit hWF
  have hs7626 := hs_7626 initSM initPM hSM hPM hInit hWF
  have hs4751 := hs_4751 initSM initPM hSM hPM hInit hWF
  -- SM: 4752 = fw_view [4096,1024] (sm 4751) = sm 4751 (identity reshape)
  have rSM : denoteGraph_ringAttn sm initSM 4752
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4751) :=
    ringAttn_reshape_reduce_pm sm initSM 50 0 4751 4752 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hSMid : denoteGraph_ringAttn sm initSM 4752 = denoteGraph_ringAttn sm initSM 4751 := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4751]
  -- PM: 7631 = fw_view[2048,1024] 7625, 7632 = fw_view[2048,1024] 7626 (both identity)
  have r7631 : denoteGraph_ringAttn pm initPM 7631
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7625) :=
    ringAttn_reshape_reduce_pm pm initPM 148 0 7625 7631 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have r7632 : denoteGraph_ringAttn pm initPM 7632
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7626) :=
    ringAttn_reshape_reduce_pm pm initPM 149 1 7626 7632 2048 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h7631id : denoteGraph_ringAttn pm initPM 7631 = denoteGraph_ringAttn pm initPM 7625 := by
    rw [r7631, fw_view_id_shape [2048, 1024] _ hs7625]
  have h7632id : denoteGraph_ringAttn pm initPM 7632 = denoteGraph_ringAttn pm initPM 7626 := by
    rw [r7632, fw_view_id_shape [2048, 1024] _ hs7626]
  -- PM: 4752 = AllGatherPrim [7631, 7632]
  have rPM : denoteGraph_ringAttn pm initPM 4752
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7631, denoteGraph_ringAttn pm initPM 7632] :=
    ringAttn_reduce2_pm_opaque pm initPM 150
      { rank := 0, op := "OpName.AllGatherPrim", ins := [7631, 7632], outs := [4752], params := [0] }
      7631 7632 4752 (fun a b => allGatherPrimDimN 0 2 0 [a, b])
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_allGatherPrimDimN_out_thm pm s 0 [7631, 7632] 4752 0)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4752 = denoteGraph_ringAttn pm initPM 4752 := by
    rw [hSMid, hval51, rPM, h7631id, h7632id]
  have hshape : (denoteGraph_ringAttn sm initSM 4752).shape = [4096, 1024] := by
    rw [hSMid]; exact hs4751
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4752 4752 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-! ## Phase 2 — down-projection + residual + RMSNorm + router head (1-tp)

    These L2 intermediates are 1-tp REPLICATED (the MoE-router pre-processing runs
    identically on both ranks), mirroring the L1 `4700…4708` template but at the
    higher PM node indices `152…192`, so every reduction routes through the
    whnf-safe `ringAttn_reduce{1,2}_pm_opaque` gears. -/

/-- 4754 — down-projection `fw_linear(4752, 4753)`. -/
theorem recon_intermediateGoal_4754_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4754
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4752 := recon_intermediateGoal_4752_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4752 : denoteGraph_ringAttn sm initSM 4752 = denoteGraph_ringAttn pm initPM 4752 :=
    oneTp_valeq intermediateGoal_4752 _ _ 4752 rfl rfl rfl rfl h4752
  have hs4752 : (denoteGraph_ringAttn sm initSM 4752).shape = [4096, 1024] := by
    have := h4752.1; simpa [intermediateGoal_4752] using this
  have hw4753 : denoteGraph_ringAttn sm initSM 4753 = denoteGraph_ringAttn pm initPM 4753 :=
    veq_weight_ring initSM initPM hInit initGoal_4753 (by native_decide) 4753
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4753 : (denoteGraph_ringAttn sm initSM 4753).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4753 (by native_decide) 4753 [1024, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4754
      = fw_linear (denoteGraph_ringAttn sm initSM 4752) (denoteGraph_ringAttn sm initSM 4753) :=
    ringAttn_reduce2_pm_opaque sm initSM 51
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4752, 4753], outs := [4754] }
      4752 4753 4754 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4752 4753 4754)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4754
      = fw_linear (denoteGraph_ringAttn pm initPM 4752) (denoteGraph_ringAttn pm initPM 4753) :=
    ringAttn_reduce2_pm_opaque pm initPM 152
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4752, 4753], outs := [4754] }
      4752 4753 4754 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 4752 4753 4754)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4754 = denoteGraph_ringAttn pm initPM 4754 := by
    rw [rSM, rPM, hv4752, hw4753]
  have hshape : (denoteGraph_ringAttn sm initSM 4754).shape = [4096, 1024] := by
    rw [rSM]; exact fw_linear_2d_shape 4096 1024 1024 _ _ hs4752 hsw4753
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4754 4754 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4755 — `fw_view [4096,1024] 4754` (identity reshape). -/
theorem recon_intermediateGoal_4755_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4755
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4754 := recon_intermediateGoal_4754_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4754 : denoteGraph_ringAttn sm initSM 4754 = denoteGraph_ringAttn pm initPM 4754 :=
    oneTp_valeq intermediateGoal_4754 _ _ 4754 rfl rfl rfl rfl h4754
  have rSM : denoteGraph_ringAttn sm initSM 4755
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4754) :=
    ringAttn_reduce1_pm_opaque sm initSM 52
      { rank := 0, op := "OpName.FW_view", ins := [4754], outs := [4755], params := [4096, 1024] }
      4754 4755 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4754 4755)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4755
      = fw_view [4096, 1024] (denoteGraph_ringAttn pm initPM 4754) :=
    ringAttn_reduce1_pm_opaque pm initPM 154
      { rank := 1, op := "OpName.FW_view", ins := [4754], outs := [4755], params := [4096, 1024] }
      4754 4755 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 4096 [1024] 4754 4755)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4755 = denoteGraph_ringAttn pm initPM 4755 := by
    rw [rSM, rPM, hv4754]
  have hshape : (denoteGraph_ringAttn sm initSM 4755).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4755 4755 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4756 — `FW_float 4755` (identity). -/
theorem recon_intermediateGoal_4756_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4756
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4755 := recon_intermediateGoal_4755_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4755 : denoteGraph_ringAttn sm initSM 4755 = denoteGraph_ringAttn pm initPM 4755 :=
    oneTp_valeq intermediateGoal_4755 _ _ 4755 rfl rfl rfl rfl h4755
  have hs4755 : (denoteGraph_ringAttn sm initSM 4755).shape = [4096, 1024] := by
    have := h4755.1; simpa [intermediateGoal_4755] using this
  have rSM : denoteGraph_ringAttn sm initSM 4756 = id (denoteGraph_ringAttn sm initSM 4755) :=
    ringAttn_reduce1_pm_opaque sm initSM 53
      { rank := 0, op := "OpName.FW_float", ins := [4755], outs := [4756] }
      4755 4756 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4755 4756 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4756 = id (denoteGraph_ringAttn pm initPM 4755) :=
    ringAttn_reduce1_pm_opaque pm initPM 156
      { rank := 1, op := "OpName.FW_float", ins := [4755], outs := [4756] }
      4755 4756 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 4755 4756 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rPM
  have hval : denoteGraph_ringAttn sm initSM 4756 = denoteGraph_ringAttn pm initPM 4756 := by
    rw [rSM, rPM, hv4755]
  have hshape : (denoteGraph_ringAttn sm initSM 4756).shape = [4096, 1024] := by
    rw [rSM]; exact hs4755
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4756 4756 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4757 — second residual add: attention/MoE branch `4756` + sequence residual
    shortcut `7439` (SM) / `14672` (PM), both = `mref2-second(4736)`. -/
theorem recon_intermediateGoal_4757_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4757
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4756 := recon_intermediateGoal_4756_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4756 : denoteGraph_ringAttn sm initSM 4756 = denoteGraph_ringAttn pm initPM 4756 :=
    oneTp_valeq intermediateGoal_4756 _ _ 4756 rfl rfl rfl rfl h4756
  have hs4756 : (denoteGraph_ringAttn sm initSM 4756).shape = [4096, 1024] := by
    have := h4756.1; simpa [intermediateGoal_4756] using this
  -- residual shortcut via 4736
  have h4736 := recon_intermediateGoal_4736_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4736 : denoteGraph_ringAttn sm initSM 4736 = denoteGraph_ringAttn pm initPM 4736 :=
    oneTp_valeq intermediateGoal_4736 _ _ 4736 rfl rfl rfl rfl h4736
  have hs4736 : (denoteGraph_ringAttn sm initSM 4736).shape = [4096, 1024] := by
    have := h4736.1; simpa [intermediateGoal_4736] using this
  have s7439 : denoteGraph_ringAttn sm initSM 7439 = id (denoteGraph_ringAttn sm initSM 4736) :=
    ringAttn_reduce1_pm_opaque sm initSM 41
      { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [7435, 7439], params := [2] }
      4736 7439 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4736 7435 7439 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14672 : denoteGraph_ringAttn pm initPM 14672 = id (denoteGraph_ringAttn pm initPM 4736) :=
    ringAttn_reduce1_pm_opaque pm initPM 125
      { rank := 1, op := "OpName.FW_multiref", ins := [4736], outs := [14668, 14672], params := [2] }
      4736 14672 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 4736 14668 14672 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7439 p14672
  have hv7439 : denoteGraph_ringAttn sm initSM 7439 = denoteGraph_ringAttn pm initPM 14672 := by
    rw [s7439, p14672, hv4736]
  have hs7439 : (denoteGraph_ringAttn sm initSM 7439).shape = [4096, 1024] := by
    rw [s7439]; exact hs4736
  have rSM : denoteGraph_ringAttn sm initSM 4757
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7439) (denoteGraph_ringAttn sm initSM 4756) :=
    ringAttn_reduce2_pm_opaque sm initSM 54
      { rank := 0, op := "OpName.FW_add", ins := [7439, 4756], outs := [4757] }
      7439 4756 4757 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7439 4756 4757)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4757
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14672) (denoteGraph_ringAttn pm initPM 4756) :=
    ringAttn_reduce2_pm_opaque pm initPM 158
      { rank := 1, op := "OpName.FW_add", ins := [14672, 4756], outs := [4757] }
      14672 4756 4757 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 14672 4756 4757)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4757 = denoteGraph_ringAttn pm initPM 4757 := by
    rw [rSM, rPM, hv7439, hv4756]
  have hshape : (denoteGraph_ringAttn sm initSM 4757).shape = [4096, 1024] := by
    rw [rSM]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] hs7439 hs4756
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4757 4757 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4759 — RMSNorm of the second residual: `rms(mref2-first(4757), 4758)`. -/
theorem recon_intermediateGoal_4759_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4759
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4757 := recon_intermediateGoal_4757_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4757 : denoteGraph_ringAttn sm initSM 4757 = denoteGraph_ringAttn pm initPM 4757 :=
    oneTp_valeq intermediateGoal_4757 _ _ 4757 rfl rfl rfl rfl h4757
  have hs4757 : (denoteGraph_ringAttn sm initSM 4757).shape = [4096, 1024] := by
    have := h4757.1; simpa [intermediateGoal_4757] using this
  have s7456 : denoteGraph_ringAttn sm initSM 7456 = id (denoteGraph_ringAttn sm initSM 4757) :=
    ringAttn_reduce1_pm_opaque sm initSM 55
      { rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [7456, 7460], params := [2] }
      4757 7456 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4757 7456 7460)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p11889 : denoteGraph_ringAttn pm initPM 11889 = id (denoteGraph_ringAttn pm initPM 4757) :=
    ringAttn_reduce1_pm_opaque pm initPM 160
      { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }
      4757 11889 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 4757 11889 11890)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7456 p11889
  have hv7456 : denoteGraph_ringAttn sm initSM 7456 = denoteGraph_ringAttn pm initPM 11889 := by
    rw [s7456, p11889, hv4757]
  have hs7456 : (denoteGraph_ringAttn sm initSM 7456).shape = [4096, 1024] := by
    rw [s7456]; exact hs4757
  have hw4758 : denoteGraph_ringAttn sm initSM 4758 = denoteGraph_ringAttn pm initPM 4758 :=
    veq_weight_ring initSM initPM hInit initGoal_4758 (by native_decide) 4758
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4759
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7456) (denoteGraph_ringAttn sm initSM 4758) :=
    ringAttn_reduce2_pm_opaque sm initSM 56
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7456, 4758], outs := [4759] }
      7456 4758 4759 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7456 4758 4759)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4759
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 11889) (denoteGraph_ringAttn pm initPM 4758) :=
    ringAttn_reduce2_pm_opaque pm initPM 163
      { rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] }
      11889 4758 4759 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 11889 4758 4759)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4759 = denoteGraph_ringAttn pm initPM 4759 := by
    rw [rSM, rPM, hv7456, hw4758]
  have hshape : (denoteGraph_ringAttn sm initSM 4759).shape = [4096, 1024] := by
    rw [rSM]; exact fw_rms_norm_shape2 _ _ 4096 1024 hs7456
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4759 4759 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4760 — `FW_float(mref5-first(4759))` (identity, replicated). -/
theorem recon_intermediateGoal_4760_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4760
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4759 := recon_intermediateGoal_4759_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4759 : denoteGraph_ringAttn sm initSM 4759 = denoteGraph_ringAttn pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl h4759
  have hs4759 : (denoteGraph_ringAttn sm initSM 4759).shape = [4096, 1024] := by
    have := h4759.1; simpa [intermediateGoal_4759] using this
  have s7467 : denoteGraph_ringAttn sm initSM 7467 = id (denoteGraph_ringAttn sm initSM 4759) :=
    ringAttn_reduce1_pm_opaque sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7467 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 4759 7467 [7471, 7475, 7479, 7483])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p11903 : denoteGraph_ringAttn pm initPM 11903 = id (denoteGraph_ringAttn pm initPM 4759) :=
    ringAttn_reduce1_pm_opaque pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11903 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 4759 11903 [11904, 11905, 11906, 11907])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7467 p11903
  have rSM : denoteGraph_ringAttn sm initSM 4760 = id (denoteGraph_ringAttn sm initSM 7467) :=
    ringAttn_reduce1_pm_opaque sm initSM 58
      { rank := 0, op := "OpName.FW_float", ins := [7467], outs := [4760] }
      7467 4760 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7467 4760 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4760 = id (denoteGraph_ringAttn pm initPM 11903) :=
    ringAttn_reduce1_pm_opaque pm initPM 172
      { rank := 1, op := "OpName.FW_float", ins := [11903], outs := [4760] }
      11903 4760 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 11903 4760 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rPM
  have hval : denoteGraph_ringAttn sm initSM 4760 = denoteGraph_ringAttn pm initPM 4760 := by
    rw [rSM, rPM, s7467, p11903, hv4759]
  have hshape : (denoteGraph_ringAttn sm initSM 4760).shape = [4096, 1024] := by
    rw [rSM, s7467]; exact hs4759
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4760 4760 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4762 — router logits `fw_norm_linear(4760, 4761)` → `[4096, 64]`. -/
theorem recon_intermediateGoal_4762_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4762
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4760 := recon_intermediateGoal_4760_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4760 : denoteGraph_ringAttn sm initSM 4760 = denoteGraph_ringAttn pm initPM 4760 :=
    oneTp_valeq intermediateGoal_4760 _ _ 4760 rfl rfl rfl rfl h4760
  have hs4760 : (denoteGraph_ringAttn sm initSM 4760).shape = [4096, 1024] := by
    have := h4760.1; simpa [intermediateGoal_4760] using this
  have hw4761 : denoteGraph_ringAttn sm initSM 4761 = denoteGraph_ringAttn pm initPM 4761 :=
    veq_weight_ring initSM initPM hInit initGoal_4761 (by native_decide) 4761
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4761 : (denoteGraph_ringAttn sm initSM 4761).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4761 (by native_decide) 4761 [64, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4762
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 4760) (denoteGraph_ringAttn sm initSM 4761) :=
    ringAttn_reduce2_pm_opaque sm initSM 62
      { rank := 0, op := "OpName.FW_norm_linear", ins := [4760, 4761], outs := [4762] }
      4760 4761 4762 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 4760 4761 4762)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4762
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 4760) (denoteGraph_ringAttn pm initPM 4761) :=
    ringAttn_reduce2_pm_opaque pm initPM 178
      { rank := 1, op := "OpName.FW_norm_linear", ins := [4760, 4761], outs := [4762] }
      4760 4761 4762 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 4760 4761 4762)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4762 = denoteGraph_ringAttn pm initPM 4762 := by
    rw [rSM, rPM, hv4760, hw4761]
  have hshape : (denoteGraph_ringAttn sm initSM 4762).shape = [4096, 64] := by
    rw [rSM]; exact fw_norm_linear_2d_shape 4096 1024 64 _ _ (by decide) hs4760 hsw4761
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4762 4762 [4096, 64] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### Router expert-input branches (identity reshape → per-expert mixlin → view) -/

/-- 4769 — `FW_reshape[4096,1024](mref5-pos2(4759))` (identity). -/
theorem recon_intermediateGoal_4769_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4769
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4759 := recon_intermediateGoal_4759_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4759 : denoteGraph_ringAttn sm initSM 4759 = denoteGraph_ringAttn pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl h4759
  have hs4759 : (denoteGraph_ringAttn sm initSM 4759).shape = [4096, 1024] := by
    have := h4759.1; simpa [intermediateGoal_4759] using this
  have s7475 : denoteGraph_ringAttn sm initSM 7475 = id (denoteGraph_ringAttn sm initSM 4759) :=
    ringAttn_reduce1_pm_opaque sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7475 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4759 7467 7471 7475 7479 7483 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p11905 : denoteGraph_ringAttn pm initPM 11905 = id (denoteGraph_ringAttn pm initPM 4759) :=
    ringAttn_reduce1_pm_opaque pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11905 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7475 p11905
  have hs7475 : (denoteGraph_ringAttn sm initSM 7475).shape = [4096, 1024] := by
    rw [s7475]; exact hs4759
  have rSM : denoteGraph_ringAttn sm initSM 4769
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7475) :=
    ringAttn_reshape_reduce_pm sm initSM 59 0 7475 4769 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4769
      = fw_view [4096, 1024] (denoteGraph_ringAttn pm initPM 11905) :=
    ringAttn_reshape_reduce_pm pm initPM 174 1 11905 4769 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4769 = denoteGraph_ringAttn pm initPM 4769 := by
    rw [rSM, rPM, s7475, p11905, hv4759]
  have hshape : (denoteGraph_ringAttn sm initSM 4769).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7475]; exact hs7475
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4769 4769 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4771 — expert-0 mixlin `fw_linear(4769, 4770)` → `[4096, 1]`. -/
theorem recon_intermediateGoal_4771_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4771
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4769 := recon_intermediateGoal_4769_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4769 : denoteGraph_ringAttn sm initSM 4769 = denoteGraph_ringAttn pm initPM 4769 :=
    oneTp_valeq intermediateGoal_4769 _ _ 4769 rfl rfl rfl rfl h4769
  have hs4769 : (denoteGraph_ringAttn sm initSM 4769).shape = [4096, 1024] := by
    have := h4769.1; simpa [intermediateGoal_4769] using this
  have hw4770 : denoteGraph_ringAttn sm initSM 4770 = denoteGraph_ringAttn pm initPM 4770 :=
    veq_weight_ring initSM initPM hInit initGoal_4770 (by native_decide) 4770
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4770 : (denoteGraph_ringAttn sm initSM 4770).shape = [1, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4770 (by native_decide) 4770 [1, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4771
      = fw_linear (denoteGraph_ringAttn sm initSM 4769) (denoteGraph_ringAttn sm initSM 4770) :=
    ringAttn_reduce2_pm_opaque sm initSM 63
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] }
      4769 4770 4771 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4769 4770 4771)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4771
      = fw_linear (denoteGraph_ringAttn pm initPM 4769) (denoteGraph_ringAttn pm initPM 4770) :=
    ringAttn_reduce2_pm_opaque pm initPM 180
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] }
      4769 4770 4771 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 4769 4770 4771)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4771 = denoteGraph_ringAttn pm initPM 4771 := by
    rw [rSM, rPM, hv4769, hw4770]
  have hshape : (denoteGraph_ringAttn sm initSM 4771).shape = [4096, 1] := by
    rw [rSM]; exact fw_linear_2d_shape 4096 1024 1 _ _ hs4769 hsw4770
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4771 4771 [4096, 1] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4772 — `FW_view [4096,1] 4771` (identity). -/
theorem recon_intermediateGoal_4772_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4772
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4771 := recon_intermediateGoal_4771_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4771 : denoteGraph_ringAttn sm initSM 4771 = denoteGraph_ringAttn pm initPM 4771 :=
    oneTp_valeq intermediateGoal_4771 _ _ 4771 rfl rfl rfl rfl h4771
  have rSM : denoteGraph_ringAttn sm initSM 4772
      = fw_view [4096, 1] (denoteGraph_ringAttn sm initSM 4771) :=
    ringAttn_reduce1_pm_opaque sm initSM 67
      { rank := 0, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] }
      4771 4772 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 4771 4772)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4772
      = fw_view [4096, 1] (denoteGraph_ringAttn pm initPM 4771) :=
    ringAttn_reduce1_pm_opaque pm initPM 188
      { rank := 1, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] }
      4771 4772 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 4096 [1] 4771 4772)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4772 = denoteGraph_ringAttn pm initPM 4772 := by
    rw [rSM, rPM, hv4771]
  have hshape : (denoteGraph_ringAttn sm initSM 4772).shape = [4096, 1] := by rw [rSM]; rfl
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4772 4772 [4096, 1] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4774 — `FW_reshape[4096,1024](mref5-pos3(4759))` (identity). -/
theorem recon_intermediateGoal_4774_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4774
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4759 := recon_intermediateGoal_4759_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4759 : denoteGraph_ringAttn sm initSM 4759 = denoteGraph_ringAttn pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl h4759
  have hs4759 : (denoteGraph_ringAttn sm initSM 4759).shape = [4096, 1024] := by
    have := h4759.1; simpa [intermediateGoal_4759] using this
  have s7479 : denoteGraph_ringAttn sm initSM 7479 = id (denoteGraph_ringAttn sm initSM 4759) :=
    ringAttn_reduce1_pm_opaque sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7479 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4759 7467 7471 7475 7479 7483 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p11906 : denoteGraph_ringAttn pm initPM 11906 = id (denoteGraph_ringAttn pm initPM 4759) :=
    ringAttn_reduce1_pm_opaque pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11906 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7479 p11906
  have hs7479 : (denoteGraph_ringAttn sm initSM 7479).shape = [4096, 1024] := by
    rw [s7479]; exact hs4759
  have rSM : denoteGraph_ringAttn sm initSM 4774
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7479) :=
    ringAttn_reshape_reduce_pm sm initSM 60 0 7479 4774 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4774
      = fw_view [4096, 1024] (denoteGraph_ringAttn pm initPM 11906) :=
    ringAttn_reshape_reduce_pm pm initPM 175 1 11906 4774 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4774 = denoteGraph_ringAttn pm initPM 4774 := by
    rw [rSM, rPM, s7479, p11906, hv4759]
  have hshape : (denoteGraph_ringAttn sm initSM 4774).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7479]; exact hs7479
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4774 4774 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4776 — expert mixlin `fw_linear(4774, 4775)` → `[4096, 512]`. -/
theorem recon_intermediateGoal_4776_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4776
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4774 := recon_intermediateGoal_4774_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4774 : denoteGraph_ringAttn sm initSM 4774 = denoteGraph_ringAttn pm initPM 4774 :=
    oneTp_valeq intermediateGoal_4774 _ _ 4774 rfl rfl rfl rfl h4774
  have hs4774 : (denoteGraph_ringAttn sm initSM 4774).shape = [4096, 1024] := by
    have := h4774.1; simpa [intermediateGoal_4774] using this
  have hw4775 : denoteGraph_ringAttn sm initSM 4775 = denoteGraph_ringAttn pm initPM 4775 :=
    veq_weight_ring initSM initPM hInit initGoal_4775 (by native_decide) 4775
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4775 : (denoteGraph_ringAttn sm initSM 4775).shape = [512, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4775 (by native_decide) 4775 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4776
      = fw_linear (denoteGraph_ringAttn sm initSM 4774) (denoteGraph_ringAttn sm initSM 4775) :=
    ringAttn_reduce2_pm_opaque sm initSM 64
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] }
      4774 4775 4776 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4774 4775 4776)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4776
      = fw_linear (denoteGraph_ringAttn pm initPM 4774) (denoteGraph_ringAttn pm initPM 4775) :=
    ringAttn_reduce2_pm_opaque pm initPM 182
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] }
      4774 4775 4776 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 4774 4775 4776)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4776 = denoteGraph_ringAttn pm initPM 4776 := by
    rw [rSM, rPM, hv4774, hw4775]
  have hshape : (denoteGraph_ringAttn sm initSM 4776).shape = [4096, 512] := by
    rw [rSM]; exact fw_linear_2d_shape 4096 1024 512 _ _ hs4774 hsw4775
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4776 4776 [4096, 512] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4777 — `FW_view [4096,512] 4776` (identity). -/
theorem recon_intermediateGoal_4777_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4777
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4776 := recon_intermediateGoal_4776_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4776 : denoteGraph_ringAttn sm initSM 4776 = denoteGraph_ringAttn pm initPM 4776 :=
    oneTp_valeq intermediateGoal_4776 _ _ 4776 rfl rfl rfl rfl h4776
  have rSM : denoteGraph_ringAttn sm initSM 4777
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4776) :=
    ringAttn_reduce1_pm_opaque sm initSM 68
      { rank := 0, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] }
      4776 4777 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4776 4777)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4777
      = fw_view [4096, 512] (denoteGraph_ringAttn pm initPM 4776) :=
    ringAttn_reduce1_pm_opaque pm initPM 190
      { rank := 1, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] }
      4776 4777 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 4096 [512] 4776 4777)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4777 = denoteGraph_ringAttn pm initPM 4777 := by
    rw [rSM, rPM, hv4776]
  have hshape : (denoteGraph_ringAttn sm initSM 4777).shape = [4096, 512] := by rw [rSM]; rfl
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4777 4777 [4096, 512] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4778 — `FW_reshape[4096,1024](mref5-pos4(4759))` (identity). -/
theorem recon_intermediateGoal_4778_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4778
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4759 := recon_intermediateGoal_4759_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4759 : denoteGraph_ringAttn sm initSM 4759 = denoteGraph_ringAttn pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl h4759
  have hs4759 : (denoteGraph_ringAttn sm initSM 4759).shape = [4096, 1024] := by
    have := h4759.1; simpa [intermediateGoal_4759] using this
  have s7483 : denoteGraph_ringAttn sm initSM 7483 = id (denoteGraph_ringAttn sm initSM 4759) :=
    ringAttn_reduce1_pm_opaque sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7483 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4759 7467 7471 7475 7479 7483 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p11907 : denoteGraph_ringAttn pm initPM 11907 = id (denoteGraph_ringAttn pm initPM 4759) :=
    ringAttn_reduce1_pm_opaque pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11907 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7483 p11907
  have hs7483 : (denoteGraph_ringAttn sm initSM 7483).shape = [4096, 1024] := by
    rw [s7483]; exact hs4759
  have rSM : denoteGraph_ringAttn sm initSM 4778
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7483) :=
    ringAttn_reshape_reduce_pm sm initSM 61 0 7483 4778 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4778
      = fw_view [4096, 1024] (denoteGraph_ringAttn pm initPM 11907) :=
    ringAttn_reshape_reduce_pm pm initPM 176 1 11907 4778 4096 [1024] (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4778 = denoteGraph_ringAttn pm initPM 4778 := by
    rw [rSM, rPM, s7483, p11907, hv4759]
  have hshape : (denoteGraph_ringAttn sm initSM 4778).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7483]; exact hs7483
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4778 4778 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4780 — expert mixlin `fw_linear(4778, 4779)` → `[4096, 512]`. -/
theorem recon_intermediateGoal_4780_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4780
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4778 := recon_intermediateGoal_4778_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4778 : denoteGraph_ringAttn sm initSM 4778 = denoteGraph_ringAttn pm initPM 4778 :=
    oneTp_valeq intermediateGoal_4778 _ _ 4778 rfl rfl rfl rfl h4778
  have hs4778 : (denoteGraph_ringAttn sm initSM 4778).shape = [4096, 1024] := by
    have := h4778.1; simpa [intermediateGoal_4778] using this
  have hw4779 : denoteGraph_ringAttn sm initSM 4779 = denoteGraph_ringAttn pm initPM 4779 :=
    veq_weight_ring initSM initPM hInit initGoal_4779 (by native_decide) 4779
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4779 : (denoteGraph_ringAttn sm initSM 4779).shape = [512, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4779 (by native_decide) 4779 [512, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4780
      = fw_linear (denoteGraph_ringAttn sm initSM 4778) (denoteGraph_ringAttn sm initSM 4779) :=
    ringAttn_reduce2_pm_opaque sm initSM 65
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] }
      4778 4779 4780 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4778 4779 4780)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4780
      = fw_linear (denoteGraph_ringAttn pm initPM 4778) (denoteGraph_ringAttn pm initPM 4779) :=
    ringAttn_reduce2_pm_opaque pm initPM 184
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] }
      4778 4779 4780 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 4778 4779 4780)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4780 = denoteGraph_ringAttn pm initPM 4780 := by
    rw [rSM, rPM, hv4778, hw4779]
  have hshape : (denoteGraph_ringAttn sm initSM 4780).shape = [4096, 512] := by
    rw [rSM]; exact fw_linear_2d_shape 4096 1024 512 _ _ hs4778 hsw4779
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4780 4780 [4096, 512] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4781 — `FW_view [4096,512] 4780` (identity). -/
theorem recon_intermediateGoal_4781_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4781
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4780 := recon_intermediateGoal_4780_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4780 : denoteGraph_ringAttn sm initSM 4780 = denoteGraph_ringAttn pm initPM 4780 :=
    oneTp_valeq intermediateGoal_4780 _ _ 4780 rfl rfl rfl rfl h4780
  have rSM : denoteGraph_ringAttn sm initSM 4781
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4780) :=
    ringAttn_reduce1_pm_opaque sm initSM 69
      { rank := 0, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] }
      4780 4781 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [512] 4780 4781)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4781
      = fw_view [4096, 512] (denoteGraph_ringAttn pm initPM 4780) :=
    ringAttn_reduce1_pm_opaque pm initPM 192
      { rank := 1, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] }
      4780 4781 (fw_view [4096, 512]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 4096 [512] 4780 4781)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4781 = denoteGraph_ringAttn pm initPM 4781 := by
    rw [rSM, rPM, hv4780]
  have hshape : (denoteGraph_ringAttn sm initSM 4781).shape = [4096, 512] := by rw [rSM]; rfl
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4781 4781 [4096, 512] rfl rfl rfl rfl rfl rfl hval hshape

/-! ## Phase 3a — MoE core (2-tp expert/token-sharded)

    The router logits `4762` (1-tp replicated) are chunked per rank
    (`7665`/`7666`) and each rank runs `topk`; the full `topk(4762)` reconstructs
    as the dim-0 gather of the per-rank outputs.  Row-wise ops (topk fst/snd,
    sigmoid, swiglu, reshape, mixlin, view, broadcast-mul) commute with the token
    gather via the Pattern_1 `_allGather0_commute_2` lemmas. -/

/-- Whnf-safe shape-dependent single-input reduction: the `happly` is
    instantiated only at the specific prefix store (so a shape-conditioned
    `applyNode` lemma such as the topk gear applies), routing through
    `ringAttn_node_core_pm_opaque` to dodge the high-index `congr 1` blowup. -/
theorem ringAttn_reduce1_at_pm (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk = node)
    (hnr1 : node.op ≠ "OpName.FW_attn_zigzag")
    (hnr2 : node.op ≠ "OpName.FW_attn_sliding_window")
    (happly : applyNode g ((g.nodes.take k).foldl (applyNodeRingAttn g) init) node outTid
      = opfun ((g.nodes.take k).foldl (applyNodeRingAttn g) init inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraph_ringAttn g init outTid = opfun (denoteGraph_ringAttn g init inTid) := by
  rw [ringAttn_node_core_pm_opaque g init k node outTid hk hnode hnr1 hnr2 hdrop_nil hdrop,
      happly, ringAttn_prefix_read_pm g init k inTid hpre_nil hpre]

/-- Shared core: SM `4762` (full router logits) reconstructs as the dim-0 gather
    of the two PM per-rank chunks `7665`/`7666`, plus the shard/full shape facts
    and the per-store trailing-dim facts needed by the topk gears. -/
theorem moe_topk_common_L2 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    denoteGraph_ringAttn sm initSM 4762
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 7665, denoteGraph_ringAttn pm initPM 7666]
      ∧ (denoteGraph_ringAttn sm initSM 4762).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 7665).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 7666).shape = [2048, 64]
      ∧ ((sm.nodes.take 66).foldl (applyNodeRingAttn sm) initSM 4762).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 193).foldl (applyNodeRingAttn pm) initPM 7665).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 194).foldl (applyNodeRingAttn pm) initPM 7666).shape.reverse.head? = some 64 := by
  have h4762 := recon_intermediateGoal_4762_ringAttn initSM initPM hSM hPM hInit hWF
  have hv4762 : denoteGraph_ringAttn sm initSM 4762 = denoteGraph_ringAttn pm initPM 4762 :=
    oneTp_valeq intermediateGoal_4762 _ _ 4762 rfl rfl rfl rfl h4762
  have hs4762sm : (denoteGraph_ringAttn sm initSM 4762).shape = [4096, 64] := by
    have := h4762.1; simpa [intermediateGoal_4762] using this
  have hp4762 : (denoteGraph_ringAttn pm initPM 4762).shape = [4096, 64] := by
    rw [← hv4762]; exact hs4762sm
  have hnr : pm.numRanks = 2 := rfl
  have hc7665 : denoteGraph_ringAttn pm initPM 7665
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4762) :=
    ringAttn_reduce1_pm_opaque pm initPM 185
      { rank := 0, op := "OpName.ChunkPrim", ins := [4762], outs := [7665], params := [0] }
      4762 7665 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4762 7665 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7666 : denoteGraph_ringAttn pm initPM 7666
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4762) :=
    ringAttn_reduce1_pm_opaque pm initPM 186
      { rank := 1, op := "OpName.ChunkPrim", ins := [4762], outs := [7666], params := [0] }
      4762 7666 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4762 7666 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs7665 : (denoteGraph_ringAttn pm initPM 7665).shape = [2048, 64] := by
    rw [hc7665, chunkPrimDimN_shape 0 pm.numRanks 0 _ [4096, 64] hp4762 (by native_decide)]; rfl
  have hs7666 : (denoteGraph_ringAttn pm initPM 7666).shape = [2048, 64] := by
    rw [hc7666, chunkPrimDimN_shape 0 pm.numRanks 1 _ [4096, 64] hp4762 (by native_decide)]; rfl
  have hrec4762 : denoteGraph_ringAttn pm initPM 4762
      = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7665, denoteGraph_ringAttn pm initPM 7666] := by
    rw [hc7665, hc7666, hnr]
    exact (allGather0_reconstruct_chunks_2d 2048 64 (by omega) (by omega) _ hp4762).symm
  have hSMeq : denoteGraph_ringAttn sm initSM 4762
      = allGatherPrimDimN 0 pm.numRanks 0 [denoteGraph_ringAttn pm initPM 7665, denoteGraph_ringAttn pm initPM 7666] := by
    rw [hv4762, hrec4762, hnr]
  have hpre4762sm : denoteGraph_ringAttn sm initSM 4762
      = (sm.nodes.take 66).foldl (applyNodeRingAttn sm) initSM 4762 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 4762 66 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 66).foldl (applyNodeRingAttn sm) initSM 4762).shape.reverse.head? = some 64 := by
    rw [← hpre4762sm, hs4762sm]; rfl
  have hpre7665 : denoteGraph_ringAttn pm initPM 7665
      = (pm.nodes.take 193).foldl (applyNodeRingAttn pm) initPM 7665 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 7665 193 (by native_decide) (by native_decide)
  have hlast193 : ((pm.nodes.take 193).foldl (applyNodeRingAttn pm) initPM 7665).shape.reverse.head? = some 64 := by
    rw [← hpre7665, hs7665]; rfl
  have hpre7666 : denoteGraph_ringAttn pm initPM 7666
      = (pm.nodes.take 194).foldl (applyNodeRingAttn pm) initPM 7666 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 7666 194 (by native_decide) (by native_decide)
  have hlast194 : ((pm.nodes.take 194).foldl (applyNodeRingAttn pm) initPM 7666).shape.reverse.head? = some 64 := by
    rw [← hpre7666, hs7666]; rfl
  exact ⟨hSMeq, hs4762sm, hs7665, hs7666, hlastSM, hlast193, hlast194⟩

/-- 4763 — `FW_topk_routing` routing_probs (`.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_4763_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4763
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4762sm, hs7665, hs7666, hlastSM, hlast193, hlast194⟩ :=
    moe_topk_common_L2 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4763
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4762) 8 64).1 :=
    ringAttn_reduce1_at_pm sm initSM 66
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4762], outs := [4763, 4764, 4765], params := [8, 1] }
      4762 4763 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 66).foldl (applyNodeRingAttn sm) initSM) 0 4762 4763 4764 4765 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7667
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7665) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 193
      { rank := 0, op := "OpName.FW_topk_routing", ins := [7665], outs := [7667, 7669, 7671], params := [8, 1] }
      7665 7667 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 193).foldl (applyNodeRingAttn pm) initPM) 0 7665 7667 7669 7671 hlast193)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7668
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7666) 8 64).1 :=
    ringAttn_reduce1_at_pm pm initPM 194
      { rank := 1, op := "OpName.FW_topk_routing", ins := [7666], outs := [7668, 7670, 7672], params := [8, 1] }
      7666 7668 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 194).foldl (applyNodeRingAttn pm) initPM) 1 7666 7668 7670 7672 hlast194)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4763
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7667, denoteGraph_ringAttn pm initPM 7668] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs7665 hs7666,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4763).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs4762sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 7667).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs7665]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 7668).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs7666]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4763 4763 7667 7668 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-- 4764 — `FW_topk_routing` routing_map (`.snd.fst`), token-sharded 2-tp. -/
theorem recon_intermediateGoal_4764_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4764
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4762sm, hs7665, hs7666, hlastSM, hlast193, hlast194⟩ :=
    moe_topk_common_L2 initSM initPM hSM hPM hInit hWF
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4764
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4762) 8 64).2.1 :=
    ringAttn_reduce1_at_pm sm initSM 66
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4762], outs := [4763, 4764, 4765], params := [8, 1] }
      4762 4764 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 66).foldl (applyNodeRingAttn sm) initSM) 0 4762 4763 4764 4765 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7669
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7665) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 193
      { rank := 0, op := "OpName.FW_topk_routing", ins := [7665], outs := [7667, 7669, 7671], params := [8, 1] }
      7665 7669 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 193).foldl (applyNodeRingAttn pm) initPM) 0 7665 7667 7669 7671 (by decide) hlast193)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7670
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7666) 8 64).2.1 :=
    ringAttn_reduce1_at_pm pm initPM 194
      { rank := 1, op := "OpName.FW_topk_routing", ins := [7666], outs := [7668, 7670, 7672], params := [8, 1] }
      7666 7670 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 194).foldl (applyNodeRingAttn pm) initPM) 1 7666 7668 7670 7672 (by decide) hlast194)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4764
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7669, denoteGraph_ringAttn pm initPM 7670] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs7665 hs7666,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4764).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs4762sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 7669).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs7665]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 7670).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs7666]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4764 4764 7669 7670 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
