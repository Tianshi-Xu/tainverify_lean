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

end TrainVerify.Denote.GeneratedPatterns
