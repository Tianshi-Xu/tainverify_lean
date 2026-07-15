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

/-- Transfer a plain-`denoteGraph` value equality on pre-attention tids to the
    ring denotation (both tids unwritten by the post-ring suffix). -/
theorem veq_ring_of_plain (initSM initPM : Store) (Tsm Tpm : Tid)
    (hsmSuf : ∀ n ∈ sm.nodes.drop 9, Tsm ∉ n.outs)
    (hpmSuf : ∀ n ∈ pm.nodes.drop 49, Tpm ∉ n.outs)
    (hplain : denoteGraph sm initSM Tsm = denoteGraph pm initPM Tpm) :
    denoteGraph_ringAttn sm initSM Tsm = denoteGraph_ringAttn pm initPM Tpm := by
  rw [sm_ring_eq initSM Tsm hsmSuf, pm_ring_eq initPM Tpm hpmSuf]; exact hplain

/-- Transfer a plain-`denoteGraph` SM shape on a pre-attention tid to the ring
    denotation. -/
theorem shape_ring_of_plain (initSM : Store) (Tsm : Tid) (sh : Shape)
    (hsmSuf : ∀ n ∈ sm.nodes.drop 9, Tsm ∉ n.outs)
    (hplain : (denoteGraph sm initSM Tsm).shape = sh) :
    (denoteGraph_ringAttn sm initSM Tsm).shape = sh := by
  rw [sm_ring_eq initSM Tsm hsmSuf]; exact hplain

/-! ### 4703 — first residual add (attention branch + embedding shortcut) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4703_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4703
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- attention branch input 4702
  have h4702 := recon_intermediateGoal_4702_ringAttn initSM initPM hSM hPM hInit
  have hv4702 : denoteGraph_ringAttn sm initSM 4702 = denoteGraph_ringAttn pm initPM 4702 :=
    oneTp_valeq intermediateGoal_4702 _ _ 4702 rfl rfl rfl rfl h4702
  have hs4702 : (denoteGraph_ringAttn sm initSM 4702).shape = [4096, 1024] := by
    have := h4702.1; simpa [intermediateGoal_4702] using this
  -- embedding shortcut: sm 7387 = pm 14615 (both replicated copies of 4681)
  have h4681 : denoteGraph_ringAttn sm initSM 4681 = denoteGraph_ringAttn pm initPM 4681 :=
    veq_ring_of_plain initSM initPM 4681 4681 (by native_decide) (by native_decide)
      (veq_4681 initSM initPM hSM hPM hInit)
  have hshape4681 : (denoteGraph_ringAttn sm initSM 4681).shape = [4096, 1024] :=
    shape_ring_of_plain initSM 4681 [4096, 1024] (by native_decide)
      (shape_4681 initSM initPM hSM hPM hInit)
  have s7387 : denoteGraph_ringAttn sm initSM 7387 = id (denoteGraph_ringAttn sm initSM 4681) :=
    ringAttn_reduce1 sm initSM 2
      { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }
      4681 7387 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' sm s 0 4681 7383 7387 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14615 : denoteGraph_ringAttn pm initPM 14615 = id (denoteGraph_ringAttn pm initPM 4681) :=
    ringAttn_reduce1 pm initPM 30
      { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }
      4681 14615 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_second_out' pm s 1 4681 14611 14615 (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7387 p14615
  have hv7387 : denoteGraph_ringAttn sm initSM 7387 = denoteGraph_ringAttn pm initPM 14615 := by
    rw [s7387, p14615, h4681]
  have hs7387 : (denoteGraph_ringAttn sm initSM 7387).shape = [4096, 1024] := by
    rw [s7387]; exact hshape4681
  -- SM: 4703 = elemwiseAdd(7387, 4702)  (node 15)
  have rSM : denoteGraph_ringAttn sm initSM 4703
      = elemwiseAdd (denoteGraph_ringAttn sm initSM 7387) (denoteGraph_ringAttn sm initSM 4702) :=
    ringAttn_reduce2 sm initSM 15
      { rank := 0, op := "OpName.FW_add", ins := [7387, 4702], outs := [4703] }
      7387 4702 4703 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out sm s 0 7387 4702 4703)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- PM last writer of 4703 is node 63 (rank 1): add(14615, 4702)
  have rPM : denoteGraph_ringAttn pm initPM 4703
      = elemwiseAdd (denoteGraph_ringAttn pm initPM 14615) (denoteGraph_ringAttn pm initPM 4702) :=
    ringAttn_reduce2 pm initPM 63
      { rank := 1, op := "OpName.FW_add", ins := [14615, 4702], outs := [4703] }
      14615 4702 4703 elemwiseAdd (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_add2_out pm s 1 14615 4702 4703)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4703 = denoteGraph_ringAttn pm initPM 4703 := by
    rw [rSM, rPM, hv7387, hv4702]
  have hshape : (denoteGraph_ringAttn sm initSM 4703).shape = [4096, 1024] := by
    rw [rSM]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] hs7387 hs4702
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4703 4703 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- Generic `FW_multiref` first-output reduction (any arity `n+1`). -/
theorem applyNode_fw_multiref_first_out' (g : GraphDecl) (s : Store) (rank n : Nat)
    (xTid t : Tid) (rest : List Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := t :: rest, params := [n + 1] } t = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ((t :: rest).zip (List.replicate (n + 1) (s xTid))) t = _
  unfold storeSet
  simp [List.replicate_succ, List.zip, List.zipWith, List.find?]

/-- `fw_rms_norm` preserves a 2-D shape `[a,b]`. -/
theorem fw_rms_norm_shape2 (x w : Tensor) (a b : Nat) (h : x.shape = [a, b]) :
    (fw_rms_norm x w).shape = [a, b] := by
  unfold fw_rms_norm; rw [h]; simp [Tensor.mkShape]

/-! ### 4705 — RMSNorm of first residual -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4705_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4705
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4703 := recon_intermediateGoal_4703_ringAttn initSM initPM hSM hPM hInit
  have hv4703 : denoteGraph_ringAttn sm initSM 4703 = denoteGraph_ringAttn pm initPM 4703 :=
    oneTp_valeq intermediateGoal_4703 _ _ 4703 rfl rfl rfl rfl h4703
  have hs4703 : (denoteGraph_ringAttn sm initSM 4703).shape = [4096, 1024] := by
    have := h4703.1; simpa [intermediateGoal_4703] using this
  -- 7404 = multiref-first(4703) [SM node 16]; 14652 = multiref-first(4703) [PM node 65 rank1]
  have s7404 : denoteGraph_ringAttn sm initSM 7404 = id (denoteGraph_ringAttn sm initSM 4703) :=
    ringAttn_reduce1 sm initSM 16
      { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] }
      4703 7404 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out sm s 0 4703 7404 7408)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p14652 : denoteGraph_ringAttn pm initPM 14652 = id (denoteGraph_ringAttn pm initPM 4703) :=
    ringAttn_reduce1 pm initPM 65
      { rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656], params := [2] }
      4703 14652 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref2_first_out pm s 1 4703 14652 14656)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7404 p14652
  -- weight 4704 : [1024]
  have hw4704 : denoteGraph_ringAttn sm initSM 4704 = denoteGraph_ringAttn pm initPM 4704 :=
    veq_weight_ring initSM initPM hInit initGoal_4704 (by native_decide) 4704
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  -- SM 4705 = fw_rms_norm(7404, 4704) [SM node 17]
  have rSM : denoteGraph_ringAttn sm initSM 4705
      = fw_rms_norm (denoteGraph_ringAttn sm initSM 7404) (denoteGraph_ringAttn sm initSM 4704) :=
    ringAttn_reduce2 sm initSM 17
      { rank := 0, op := "OpName.FW_rms_norm", ins := [7404, 4704], outs := [4705] }
      7404 4704 4705 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p sm s 0 7404 4704 4705)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- PM 4705 = fw_rms_norm(14652, 4704) [PM node 67 rank1]
  have rPM : denoteGraph_ringAttn pm initPM 4705
      = fw_rms_norm (denoteGraph_ringAttn pm initPM 14652) (denoteGraph_ringAttn pm initPM 4704) :=
    ringAttn_reduce2 pm initPM 67
      { rank := 1, op := "OpName.FW_rms_norm", ins := [14652, 4704], outs := [4705] }
      14652 4704 4705 fw_rms_norm (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_rms_norm_out_1p pm s 1 14652 4704 4705)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4705 = denoteGraph_ringAttn pm initPM 4705 := by
    rw [rSM, rPM, s7404, p14652, hv4703, hw4704]
  have hshape : (denoteGraph_ringAttn sm initSM 4705).shape = [4096, 1024] := by
    rw [rSM]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s7404]; exact hs4703)
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4705 4705 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4706 — float of RMSNorm (gate/router branch head) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4706_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4706
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4705 := recon_intermediateGoal_4705_ringAttn initSM initPM hSM hPM hInit
  have hv4705 : denoteGraph_ringAttn sm initSM 4705 = denoteGraph_ringAttn pm initPM 4705 :=
    oneTp_valeq intermediateGoal_4705 _ _ 4705 rfl rfl rfl rfl h4705
  have hs4705 : (denoteGraph_ringAttn sm initSM 4705).shape = [4096, 1024] := by
    have := h4705.1; simpa [intermediateGoal_4705] using this
  -- 7415 = multiref-first(4705) [SM node 18]; 11875 = multiref-first(4705) [PM node 69 rank1]
  have s7415 : denoteGraph_ringAttn sm initSM 7415 = id (denoteGraph_ringAttn sm initSM 4705) :=
    ringAttn_reduce1 sm initSM 18
      { rank := 0, op := "OpName.FW_multiref", ins := [4705],
        outs := [7415, 7419, 7423, 7427, 7431], params := [5] }
      4705 7415 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' sm s 0 4 4705 7415 [7419, 7423, 7427, 7431])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p11875 : denoteGraph_ringAttn pm initPM 11875 = id (denoteGraph_ringAttn pm initPM 4705) :=
    ringAttn_reduce1 pm initPM 69
      { rank := 1, op := "OpName.FW_multiref", ins := [4705],
        outs := [11875, 11876, 11877, 11878, 11879], params := [5] }
      4705 11875 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_first_out' pm s 1 4 4705 11875 [11876, 11877, 11878, 11879])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7415 p11875
  -- SM 4706 = float(7415) [SM node 19]; PM 4706 = float(11875) [PM node 75 rank1]
  have rSM : denoteGraph_ringAttn sm initSM 4706 = id (denoteGraph_ringAttn sm initSM 7415) :=
    ringAttn_reduce1 sm initSM 19
      { rank := 0, op := "OpName.FW_float", ins := [7415], outs := [4706] }
      7415 4706 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out sm s 0 7415 4706 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4706 = id (denoteGraph_ringAttn pm initPM 11875) :=
    ringAttn_reduce1 pm initPM 75
      { rank := 1, op := "OpName.FW_float", ins := [11875], outs := [4706] }
      11875 4706 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_float_out pm s 1 11875 4706 [])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rSM rPM
  have hval : denoteGraph_ringAttn sm initSM 4706 = denoteGraph_ringAttn pm initPM 4706 := by
    rw [rSM, rPM, s7415, p11875, hv4705]
  have hshape : (denoteGraph_ringAttn sm initSM 4706).shape = [4096, 1024] := by
    rw [rSM, s7415]; exact hs4705
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4706 4706 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4715 / 4720 / 4724 — identity reshapes of RMSNorm copies -/

/-- applyNode for `FW_norm_linear` with singleton output. -/
theorem applyNode_fw_norm_linear_out (g : GraphDecl) (s : Store) (rank : Nat)
    (xTid wTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_norm_linear", ins := [xTid, wTid],
                    outs := [outTid] } outTid = fw_norm_linear (s xTid) (s wTid) := by
  unfold applyNode
  rw [show ([xTid, wTid] : List Tid).map s = [s xTid, s wTid] from rfl]
  change storeSet s [(outTid, fw_norm_linear (s xTid) (s wTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- Public 2-D `fw_norm_linear` shape: `[b,k] × [n,k] → [b,n]`. -/
theorem fw_norm_linear_2d_shape (b k n : Nat) (x w : Tensor) (hn : 0 < n)
    (hx : x.shape = [b, k]) (hw : w.shape = [n, k]) :
    (fw_norm_linear x w).shape = [b, n] := by
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  unfold fw_norm_linear
  rw [hx, hw]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, if_neg hn']
  rfl

/-- `fw_sigmoid` preserves shape. -/
theorem fw_sigmoid_shape (x : Tensor) : (fw_sigmoid x).shape = x.shape := by
  unfold fw_sigmoid; rfl

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4715_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4715
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4705 := recon_intermediateGoal_4705_ringAttn initSM initPM hSM hPM hInit
  have hv4705 : denoteGraph_ringAttn sm initSM 4705 = denoteGraph_ringAttn pm initPM 4705 :=
    oneTp_valeq intermediateGoal_4705 _ _ 4705 rfl rfl rfl rfl h4705
  have hs4705 : (denoteGraph_ringAttn sm initSM 4705).shape = [4096, 1024] := by
    have := h4705.1; simpa [intermediateGoal_4705] using this
  have s7423 : denoteGraph_ringAttn sm initSM 7423 = id (denoteGraph_ringAttn sm initSM 4705) :=
    ringAttn_reduce1 sm initSM 18
      { rank := 0, op := "OpName.FW_multiref", ins := [4705],
        outs := [7415, 7419, 7423, 7427, 7431], params := [5] }
      4705 7423 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4705 7415 7419 7423 7427 7431
        (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p11877 : denoteGraph_ringAttn pm initPM 11877 = id (denoteGraph_ringAttn pm initPM 4705) :=
    ringAttn_reduce1 pm initPM 69
      { rank := 1, op := "OpName.FW_multiref", ins := [4705],
        outs := [11875, 11876, 11877, 11878, 11879], params := [5] }
      4705 11877 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 4705 11875 11876 11877 11878 11879
        (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7423 p11877
  have rSM : denoteGraph_ringAttn sm initSM 4715
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7423) :=
    ringAttn_reshape_reduce_g12 sm initSM 20 0 7423 4715 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4715
      = fw_view [4096, 1024] (denoteGraph_ringAttn pm initPM 11877) :=
    ringAttn_reshape_reduce_g12 pm initPM 77 1 11877 4715 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hSMid : denoteGraph_ringAttn sm initSM 4715 = denoteGraph_ringAttn sm initSM 7423 := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ (by rw [s7423]; exact hs4705)]
  have hPMid : denoteGraph_ringAttn pm initPM 4715 = denoteGraph_ringAttn pm initPM 11877 := by
    rw [rPM, fw_view_id_shape [4096, 1024] _ (by rw [p11877, ← hv4705]; exact hs4705)]
  have hval : denoteGraph_ringAttn sm initSM 4715 = denoteGraph_ringAttn pm initPM 4715 := by
    rw [hSMid, hPMid, s7423, p11877, hv4705]
  have hshape : (denoteGraph_ringAttn sm initSM 4715).shape = [4096, 1024] := by
    rw [hSMid, s7423]; exact hs4705
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4715 4715 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4720_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4720
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4705 := recon_intermediateGoal_4705_ringAttn initSM initPM hSM hPM hInit
  have hv4705 : denoteGraph_ringAttn sm initSM 4705 = denoteGraph_ringAttn pm initPM 4705 :=
    oneTp_valeq intermediateGoal_4705 _ _ 4705 rfl rfl rfl rfl h4705
  have hs4705 : (denoteGraph_ringAttn sm initSM 4705).shape = [4096, 1024] := by
    have := h4705.1; simpa [intermediateGoal_4705] using this
  have s7427 : denoteGraph_ringAttn sm initSM 7427 = id (denoteGraph_ringAttn sm initSM 4705) :=
    ringAttn_reduce1 sm initSM 18
      { rank := 0, op := "OpName.FW_multiref", ins := [4705],
        outs := [7415, 7419, 7423, 7427, 7431], params := [5] }
      4705 7427 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4705 7415 7419 7423 7427 7431
        (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p11878 : denoteGraph_ringAttn pm initPM 11878 = id (denoteGraph_ringAttn pm initPM 4705) :=
    ringAttn_reduce1 pm initPM 69
      { rank := 1, op := "OpName.FW_multiref", ins := [4705],
        outs := [11875, 11876, 11877, 11878, 11879], params := [5] }
      4705 11878 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 4705 11875 11876 11877 11878 11879
        (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7427 p11878
  have rSM : denoteGraph_ringAttn sm initSM 4720
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7427) :=
    ringAttn_reshape_reduce_g12 sm initSM 21 0 7427 4720 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4720
      = fw_view [4096, 1024] (denoteGraph_ringAttn pm initPM 11878) :=
    ringAttn_reshape_reduce_g12 pm initPM 78 1 11878 4720 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hSMid : denoteGraph_ringAttn sm initSM 4720 = denoteGraph_ringAttn sm initSM 7427 := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ (by rw [s7427]; exact hs4705)]
  have hPMid : denoteGraph_ringAttn pm initPM 4720 = denoteGraph_ringAttn pm initPM 11878 := by
    rw [rPM, fw_view_id_shape [4096, 1024] _ (by rw [p11878, ← hv4705]; exact hs4705)]
  have hval : denoteGraph_ringAttn sm initSM 4720 = denoteGraph_ringAttn pm initPM 4720 := by
    rw [hSMid, hPMid, s7427, p11878, hv4705]
  have hshape : (denoteGraph_ringAttn sm initSM 4720).shape = [4096, 1024] := by
    rw [hSMid, s7427]; exact hs4705
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4720 4720 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4724_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4724
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4705 := recon_intermediateGoal_4705_ringAttn initSM initPM hSM hPM hInit
  have hv4705 : denoteGraph_ringAttn sm initSM 4705 = denoteGraph_ringAttn pm initPM 4705 :=
    oneTp_valeq intermediateGoal_4705 _ _ 4705 rfl rfl rfl rfl h4705
  have hs4705 : (denoteGraph_ringAttn sm initSM 4705).shape = [4096, 1024] := by
    have := h4705.1; simpa [intermediateGoal_4705] using this
  have s7431 : denoteGraph_ringAttn sm initSM 7431 = id (denoteGraph_ringAttn sm initSM 4705) :=
    ringAttn_reduce1 sm initSM 18
      { rank := 0, op := "OpName.FW_multiref", ins := [4705],
        outs := [7415, 7419, 7423, 7427, 7431], params := [5] }
      4705 7431 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4705 7415 7419 7423 7427 7431
        (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p11879 : denoteGraph_ringAttn pm initPM 11879 = id (denoteGraph_ringAttn pm initPM 4705) :=
    ringAttn_reduce1 pm initPM 69
      { rank := 1, op := "OpName.FW_multiref", ins := [4705],
        outs := [11875, 11876, 11877, 11878, 11879], params := [5] }
      4705 11879 id (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 4705 11875 11876 11877 11878 11879
        (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7431 p11879
  have rSM : denoteGraph_ringAttn sm initSM 4724
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 7431) :=
    ringAttn_reshape_reduce_g12 sm initSM 22 0 7431 4724 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4724
      = fw_view [4096, 1024] (denoteGraph_ringAttn pm initPM 11879) :=
    ringAttn_reshape_reduce_g12 pm initPM 79 1 11879 4724 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hSMid : denoteGraph_ringAttn sm initSM 4724 = denoteGraph_ringAttn sm initSM 7431 := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ (by rw [s7431]; exact hs4705)]
  have hPMid : denoteGraph_ringAttn pm initPM 4724 = denoteGraph_ringAttn pm initPM 11879 := by
    rw [rPM, fw_view_id_shape [4096, 1024] _ (by rw [p11879, ← hv4705]; exact hs4705)]
  have hval : denoteGraph_ringAttn sm initSM 4724 = denoteGraph_ringAttn pm initPM 4724 := by
    rw [hSMid, hPMid, s7431, p11879, hv4705]
  have hshape : (denoteGraph_ringAttn sm initSM 4724).shape = [4096, 1024] := by
    rw [hSMid, s7431]; exact hs4705
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4724 4724 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4708 — router gate (norm_linear, replicated) -/

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4708_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4708
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4706 := recon_intermediateGoal_4706_ringAttn initSM initPM hSM hPM hInit
  have hv4706 : denoteGraph_ringAttn sm initSM 4706 = denoteGraph_ringAttn pm initPM 4706 :=
    oneTp_valeq intermediateGoal_4706 _ _ 4706 rfl rfl rfl rfl h4706
  have hs4706 : (denoteGraph_ringAttn sm initSM 4706).shape = [4096, 1024] := by
    have := h4706.1; simpa [intermediateGoal_4706] using this
  have hw4707 : denoteGraph_ringAttn sm initSM 4707 = denoteGraph_ringAttn pm initPM 4707 :=
    veq_weight_ring initSM initPM hInit initGoal_4707 (by native_decide) 4707
      rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsw4707 : (denoteGraph_ringAttn sm initSM 4707).shape = [64, 1024] :=
    shape_weight_ring initSM initPM hInit initGoal_4707 (by native_decide) 4707 [64, 1024]
      rfl rfl (by native_decide)
  have rSM : denoteGraph_ringAttn sm initSM 4708
      = fw_norm_linear (denoteGraph_ringAttn sm initSM 4706) (denoteGraph_ringAttn sm initSM 4707) :=
    ringAttn_reduce2 sm initSM 23
      { rank := 0, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] }
      4706 4707 4708 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out sm s 0 4706 4707 4708)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraph_ringAttn pm initPM 4708
      = fw_norm_linear (denoteGraph_ringAttn pm initPM 4706) (denoteGraph_ringAttn pm initPM 4707) :=
    ringAttn_reduce2 pm initPM 81
      { rank := 1, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] }
      4706 4707 4708 fw_norm_linear (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_norm_linear_out pm s 1 4706 4707 4708)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4708 = denoteGraph_ringAttn pm initPM 4708 := by
    rw [rSM, rPM, hv4706, hw4707]
  have hshape : (denoteGraph_ringAttn sm initSM 4708).shape = [4096, 64] := by
    rw [rSM]; exact fw_norm_linear_2d_shape 4096 1024 64 _ _ (by decide) hs4706 hsw4707
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4708 4708 [4096, 64] rfl rfl rfl rfl rfl rfl hval hshape

end TrainVerify.Denote.GeneratedPatterns
