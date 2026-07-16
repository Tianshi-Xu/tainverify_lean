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

end TrainVerify.Denote.GeneratedPatterns
