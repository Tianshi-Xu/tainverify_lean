/- Worker #12 — residual / down-projection / MoE / layer-1 pre-attention
   reconstruction cascade over `denoteGraph_ringAttn`.

   Chains from Worker #11's `recon_intermediateGoal_4697_ringAttn` (the layer-0
   attention-output reshape) forward through the down-projection, the two
   residual adds, the RMSNorm+MoE block, and the layer-1 pre-attention
   projections, proving each `intermediateGoal_<tid>` UNCONDITIONALLY over the
   ring-attn denotation.

   All new theorems are named `recon_intermediateGoal_<tid>_ringAttn`, zero sorry,
   zero user axiom (kernel + native_decide baseline only). Imports the origin
   `IntermediateReconstruction` (for the sm/pm graphs, the goal defs, the proven
   4697 goal and the reusable wrappers) plus the shared `RingAttnGears`. -/
import denote.yoco_goals.IntermediateReconstruction
import denote.yoco_goals.RingAttnGears

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- Store-generic 1-tp (`ts = tp`, non-replicated, gatherDim 0) wrapper: package a
    value equality `smS T = pmS T` plus a shape into the `InitGoalHolds`
    obligation. Ring-store analog of `wrap_1tp`. -/
theorem wrap_1tp_gen (smS pmS : Store) (g : LineageGoal) (T : Tid) (sh : Shape)
    (htp : g.tps = [{rank := 0, tid := T}]) (hgd : g.gatherDim = 0)
    (hrep : g.replicated = false) (hts : g.ts = T) (htsShape : g.tsShape = sh)
    (htpShapes : g.tpShapes = [sh])
    (hval : smS T = pmS T)
    (hshape : (smS T).shape = sh) :
    InitGoalHolds pm.numRanks g smS pmS := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hts, htsShape]; exact hshape
  · rw [htp, htpShapes]; simp only [List.map, List.cons.injEq, and_true]
    rw [← hval]; exact hshape
  · rw [reconstructForGoal_of_not_replicated g pm.numRanks _ hrep, htp, hts, hgd]
    simp only [List.map, reconstructWithDim]
    exact hval

/-- Ring-store weight equality: for an init-weight tid `W` (never written by any
    node, hence ring/plain-agnostic and preserved across both graphs),
    `sm_ring W = pm_ring W`. -/
theorem veq_weight_ring (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W : Tid)
    (htp : gW.tps = [{rank := 0, tid := W}]) (hgd : gW.gatherDim = 0)
    (hrep : gW.replicated = false) (hts : gW.ts = W)
    (hsmSuf : ∀ n ∈ sm.nodes.drop 9, W ∉ n.outs)
    (hpmSuf : ∀ n ∈ pm.nodes.drop 49, W ∉ n.outs) :
    denoteGraph_ringAttn sm initSM W = denoteGraph_ringAttn pm initPM W := by
  rw [sm_ring_eq initSM W hsmSuf, pm_ring_eq initPM W hpmSuf]
  exact recon_weight initSM initPM hInit gW hgW W htp hgd hrep hts

/-! ### The 4697 value/shape extraction, reused by the whole cascade. -/

/-- Value reconstruction from the proven 4697 goal:
    `sm_ring 4697 = allGather 0 2 0 [pm_ring 7439, pm_ring 7440]`. -/
theorem hval_4697 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4697
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7439, denoteGraph_ringAttn pm initPM 7440] := by
  have h97 := recon_intermediateGoal_4697_ringAttn initSM initPM hSM hPM hInit
  have hshapes := h97.2.1
  simp only [intermediateGoal_4697, List.map, List.cons.injEq, and_true] at hshapes
  obtain ⟨hs7439, _hs7440⟩ := hshapes
  have hv := h97.2.2
  rw [reconstructForGoal_of_not_replicated intermediateGoal_4697 pm.numRanks _ rfl] at hv
  simp only [intermediateGoal_4697, List.map] at hv
  rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
        (by rw [hs7439]; decide)] at hv
  exact hv

/-- PM shard 7439 shape `[2048,1024]` (from 4697). -/
theorem hs_7439 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    (denoteGraph_ringAttn pm initPM 7439).shape = [2048, 1024] := by
  have h97 := recon_intermediateGoal_4697_ringAttn initSM initPM hSM hPM hInit
  have hshapes := h97.2.1
  simp only [intermediateGoal_4697, List.map, List.cons.injEq, and_true] at hshapes
  exact hshapes.1

/-- PM shard 7440 shape `[2048,1024]` (from 4697). -/
theorem hs_7440 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    (denoteGraph_ringAttn pm initPM 7440).shape = [2048, 1024] := by
  have h97 := recon_intermediateGoal_4697_ringAttn initSM initPM hSM hPM hInit
  have hshapes := h97.2.1
  simp only [intermediateGoal_4697, List.map, List.cons.injEq, and_true] at hshapes
  exact hshapes.2

/-- SM 4697 shape `[4096,1024]` (from 4697). -/
theorem hs_4697 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    (denoteGraph_ringAttn sm initSM 4697).shape = [4096, 1024] := by
  have h97 := recon_intermediateGoal_4697_ringAttn initSM initPM hSM hPM hInit
  have := h97.1; simpa [intermediateGoal_4697] using this

/-! ### 4698 — sharded→replicated gather bridge

    SM computes `4698 = reshape[4096,1024] 4697` (identity, `4697` is already
    `[4096,1024]`). PM computes `4698 = AllGatherPrim [7445, 7446]` where
    `7445 = reshape[2048,1024] 7439`, `7446 = reshape[2048,1024] 7440` (both
    identity). Hence both sides equal `allGather 0 2 0 [pm 7439, pm 7440]`. -/
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4698_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4698
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hval97 := hval_4697 initSM initPM hSM hPM hInit
  have hs7439 := hs_7439 initSM initPM hSM hPM hInit
  have hs7440 := hs_7440 initSM initPM hSM hPM hInit
  have hs4697 := hs_4697 initSM initPM hSM hPM hInit
  -- SM: 4698 = fw_view [4096,1024] (sm 4697) = sm 4697 (identity reshape)
  have rSM : denoteGraph_ringAttn sm initSM 4698
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4697) :=
    ringAttn_reshape_reduce_g12 sm initSM 11 0 4697 4698 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hSMid : denoteGraph_ringAttn sm initSM 4698 = denoteGraph_ringAttn sm initSM 4697 := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs4697]
  -- PM: 7445 = fw_view[2048,1024] 7439, 7446 = fw_view[2048,1024] 7440 (both identity)
  have r7445 : denoteGraph_ringAttn pm initPM 7445
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7439) :=
    ringAttn_reshape_reduce_g12 pm initPM 53 0 7439 7445 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have r7446 : denoteGraph_ringAttn pm initPM 7446
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7440) :=
    ringAttn_reshape_reduce_g12 pm initPM 54 1 7440 7446 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have h7445id : denoteGraph_ringAttn pm initPM 7445 = denoteGraph_ringAttn pm initPM 7439 := by
    rw [r7445, fw_view_id_shape [2048, 1024] _ hs7439]
  have h7446id : denoteGraph_ringAttn pm initPM 7446 = denoteGraph_ringAttn pm initPM 7440 := by
    rw [r7446, fw_view_id_shape [2048, 1024] _ hs7440]
  -- PM: 4698 = AllGatherPrim [7445, 7446]
  have rPM : denoteGraph_ringAttn pm initPM 4698
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7445, denoteGraph_ringAttn pm initPM 7446] :=
    ringAttn_reduce2 pm initPM 55
      { rank := 0, op := "OpName.AllGatherPrim", ins := [7445, 7446], outs := [4698], params := [0] }
      7445 7446 4698 (fun a b => allGatherPrimDimN 0 2 0 [a, b])
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_allGatherPrimDimN_out_thm pm s 0 [7445, 7446] 4698 0)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- assemble value equality
  have hval : denoteGraph_ringAttn sm initSM 4698 = denoteGraph_ringAttn pm initPM 4698 := by
    rw [hSMid, hval97, rPM, h7445id, h7446id]
  have hshape : (denoteGraph_ringAttn sm initSM 4698).shape = [4096, 1024] := by
    rw [hSMid]; exact hs4697
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4698 4698 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4700 / 4701 / 4702 — down-projection, view, float (replicated) -/

/-- Public 2-D `fw_linear` shape: `[b,i] × [o,i] → [b,o]`. -/
theorem fw_linear_2d_shape (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  rw [fw_linear_is_matmul b i o x w hx hw]; rfl

/-- Ring-store weight shape: for an init-weight tid `W`, `(sm_ring W).shape = sh`. -/
theorem shape_weight_ring (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W : Tid) (sh : Shape)
    (htsShape : gW.tsShape = sh) (hts : gW.ts = W)
    (hsmSuf : ∀ n ∈ sm.nodes.drop 9, W ∉ n.outs) :
    (denoteGraph_ringAttn sm initSM W).shape = sh := by
  rw [sm_ring_eq initSM W hsmSuf]
  exact shape_weight initSM initPM hInit gW hgW W sh htsShape hts

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4700_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4700
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4698 := recon_intermediateGoal_4698_ringAttn initSM initPM hSM hPM hInit
  have hv4698 : denoteGraph_ringAttn sm initSM 4698 = denoteGraph_ringAttn pm initPM 4698 :=
    oneTp_valeq intermediateGoal_4698 _ _ 4698 rfl rfl rfl rfl h4698
  have hs4698 : (denoteGraph_ringAttn sm initSM 4698).shape = [4096, 1024] := by
    have := h4698.1; simpa [intermediateGoal_4698] using this
  -- weight 4699
  have hw4699 : denoteGraph_ringAttn sm initSM 4699 = denoteGraph_ringAttn pm initPM 4699 :=
    veq_weight_ring initSM initPM hInit initGoal_4699 (by native_decide) 4699
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4699 : (denoteGraph_ringAttn sm initSM 4699).shape = [1024, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4699 (by native_decide) 4699 [1024, 1024]
      rfl rfl (by native_decide)
  -- SM: 4700 = fw_linear(4698, 4699)
  have rSM : denoteGraph_ringAttn sm initSM 4700
      = fw_linear (denoteGraph_ringAttn sm initSM 4698) (denoteGraph_ringAttn sm initSM 4699) :=
    ringAttn_reduce2 sm initSM 12
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] }
      4698 4699 4700 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4698 4699 4700)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- PM last writer of 4700 is node 57 (rank 1)
  have rPM : denoteGraph_ringAttn pm initPM 4700
      = fw_linear (denoteGraph_ringAttn pm initPM 4698) (denoteGraph_ringAttn pm initPM 4699) :=
    ringAttn_reduce2 pm initPM 57
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] }
      4698 4699 4700 fw_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 4698 4699 4700)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4700 = denoteGraph_ringAttn pm initPM 4700 := by
    rw [rSM, rPM, hv4698, hw4699]
  have hshape : (denoteGraph_ringAttn sm initSM 4700).shape = [4096, 1024] := by
    rw [rSM]; exact fw_linear_2d_shape 4096 1024 1024 _ _ hs4698 hsw4699
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4700 4700 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4701_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4701
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4700 := recon_intermediateGoal_4700_ringAttn initSM initPM hSM hPM hInit
  have hv4700 : denoteGraph_ringAttn sm initSM 4700 = denoteGraph_ringAttn pm initPM 4700 :=
    oneTp_valeq intermediateGoal_4700 _ _ 4700 rfl rfl rfl rfl h4700
  -- SM: 4701 = fw_view [4096,1024] 4700  (node 13)
  have rSM : denoteGraph_ringAttn sm initSM 4701
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4700) :=
    ringAttn_reduce1 sm initSM 13
      { rank := 0, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] }
      4700 4701 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1024] 4700 4701)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM last writer of 4701 is node 59 (rank 1)
  have rPM : denoteGraph_ringAttn pm initPM 4701
      = fw_view [4096, 1024] (denoteGraph_ringAttn pm initPM 4700) :=
    ringAttn_reduce1 pm initPM 59
      { rank := 1, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] }
      4700 4701 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 4096 [1024] 4700 4701)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4701 = denoteGraph_ringAttn pm initPM 4701 := by
    rw [rSM, rPM, hv4700]
  have hshape : (denoteGraph_ringAttn sm initSM 4701).shape = [4096, 1024] := by
    rw [rSM]; rfl
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4701 4701 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4702_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4702
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4701 := recon_intermediateGoal_4701_ringAttn initSM initPM hSM hPM hInit
  have hv4701 : denoteGraph_ringAttn sm initSM 4701 = denoteGraph_ringAttn pm initPM 4701 :=
    oneTp_valeq intermediateGoal_4701 _ _ 4701 rfl rfl rfl rfl h4701
  have hs4701 : (denoteGraph_ringAttn sm initSM 4701).shape = [4096, 1024] := by
    have := h4701.1; simpa [intermediateGoal_4701] using this
  -- SM: 4702 = float 4701 (node 14, identity)
  have rSM : denoteGraph_ringAttn sm initSM 4702 = id (denoteGraph_ringAttn sm initSM 4701) :=
    ringAttn_reduce1 sm initSM 14
      { rank := 0, op := "OpName.FW_float", ins := [4701], outs := [4702] }
      4701 4702 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 4701 4702 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM last writer of 4702 is node 61 (rank 1)
  have rPM : denoteGraph_ringAttn pm initPM 4702 = id (denoteGraph_ringAttn pm initPM 4701) :=
    ringAttn_reduce1 pm initPM 61
      { rank := 1, op := "OpName.FW_float", ins := [4701], outs := [4702] }
      4701 4702 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 4701 4702 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rPM
  have hval : denoteGraph_ringAttn sm initSM 4702 = denoteGraph_ringAttn pm initPM 4702 := by
    rw [rSM, rPM, hv4701]
  have hshape : (denoteGraph_ringAttn sm initSM 4702).shape = [4096, 1024] := by
    rw [rSM]; exact hs4701
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4702 4702 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

end TrainVerify.Denote.GeneratedPatterns
