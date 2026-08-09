/- Canonical Goal 1, layer 17: composition of the L17 boundary into Q. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagLinearRel
import denote.yoco_goals.ZigzagPointwiseRel
import denote.yoco_goals.ZigzagAttentionRel
import denote.yoco_goals.GatherOpGears
import denote.DenoteMoE

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private theorem cL17C_storeSet_zip_replicate (s : Store) (v : Tensor) :
    ∀ (l : List Tid) (m : Nat) (t : Tid), t ∈ l → l.length ≤ m →
      storeSet s (l.zip (List.replicate m v)) t = v := by
  intro l
  induction l with
  | nil => intro m t ht _; cases ht
  | cons a l ih =>
    intro m t ht hlen
    match m with
    | 0 => simp at hlen
    | m + 1 =>
      by_cases hat : a = t
      · subst t
        rw [List.replicate_succ]
        change storeSet s ((a, v) :: l.zip (List.replicate m v)) a = v
        unfold storeSet
        simp [List.find?]
      · have ht' : t ∈ l := by
          rcases List.mem_cons.mp ht with h | h
          · exact absurd h.symm hat
          · exact h
        rw [List.replicate_succ]
        change storeSet s ((a, v) :: l.zip (List.replicate m v)) t = v
        have hstep : storeSet s ((a, v) :: l.zip (List.replicate m v)) t =
            storeSet s (l.zip (List.replicate m v)) t := by
          unfold storeSet
          simp [List.find?, hat]
        rw [hstep]
        exact ih m t ht' (Nat.le_of_succ_le_succ hlen)

private def cL17C_multirefNode (rank n : Nat) (xTid : Tid)
    (outs : List Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
    outs := outs, params := [n] }

private theorem cL17C_apply_multiref (g : GraphDecl) (s : Store)
    (rank n xTid : Nat) (outs : List Tid) (t : Tid)
    (hmem : t ∈ outs) (hlen : outs.length ≤ n) :
    applyNode g s (cL17C_multirefNode rank n xTid outs) t = s xTid := by
  unfold cL17C_multirefNode
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  exact cL17C_storeSet_zip_replicate s (s xTid) outs n t hmem hlen

private theorem cL17C_multiref_reduce (g : GraphDecl) (init : Store)
    (idx rank n xTid t : Nat) (outs : List Tid)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL17C_multirefNode rank n xTid outs)
    (hmem : t ∈ outs) (hlen : outs.length ≤ n)
    (hafter : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (hwrite : ∀ nd ∈ g.nodes.drop (idx + 1), t ∉ nd.outs)
    (hpre : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hread : ∀ nd ∈ g.nodes.drop idx, xTid ∉ nd.outs) :
    denoteGraphDistributedFaithful g init t =
      denoteGraphDistributedFaithful g init xTid := by
  refine denoteGraphDistributedFaithful_reduce1 g init idx _ xTid t (fun x => x)
    hidx hnode ?_ hafter hwrite hpre hread
  intro s
  unfold cL17C_multirefNode
  have hs : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_multiref" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact cL17C_apply_multiref g s rank n xTid outs t hmem hlen

private def cL17C_rmsNode (rank : Nat) (xTid wTid outTid : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_rms_norm", ins := [xTid, wTid], outs := [outTid] }

private theorem cL17C_rms_reduce (g : GraphDecl) (init : Store)
    (idx rank xTid wTid outTid : Nat)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL17C_rmsNode rank xTid wTid outTid)
    (hafter : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (hwrite : ∀ nd ∈ g.nodes.drop (idx + 1), outTid ∉ nd.outs)
    (hpre : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hread0 : ∀ nd ∈ g.nodes.drop idx, xTid ∉ nd.outs)
    (hread1 : ∀ nd ∈ g.nodes.drop idx, wTid ∉ nd.outs) :
    denoteGraphDistributedFaithful g init outTid =
      fw_rms_norm (denoteGraphDistributedFaithful g init xTid)
        (denoteGraphDistributedFaithful g init wTid) := by
  refine denoteGraphDistributedFaithful_reduce2 g init idx _ xTid wTid outTid
    fw_rms_norm hidx hnode ?_ hafter hwrite hpre hread0 hread1
  intro s
  unfold cL17C_rmsNode
  have hs : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact applyNode_fw_rms_norm_out g s rank xTid wTid outTid []

private def cL17C_projNode (rank : Nat) (xTid wTid outTid : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_per_head_mix_precision_linear",
    ins := [xTid, wTid], outs := [outTid] }

private theorem cL17C_proj_reduce (g : GraphDecl) (init : Store)
    (idx rank xTid wTid outTid : Nat)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL17C_projNode rank xTid wTid outTid)
    (hafter : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (hwrite : ∀ nd ∈ g.nodes.drop (idx + 1), outTid ∉ nd.outs)
    (hpre : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hread0 : ∀ nd ∈ g.nodes.drop idx, xTid ∉ nd.outs)
    (hread1 : ∀ nd ∈ g.nodes.drop idx, wTid ∉ nd.outs) :
    denoteGraphDistributedFaithful g init outTid =
      fw_per_head_linear (denoteGraphDistributedFaithful g init xTid)
        (denoteGraphDistributedFaithful g init wTid) := by
  refine denoteGraphDistributedFaithful_reduce2 g init idx _ xTid wTid outTid
    fw_per_head_linear hidx hnode ?_ hafter hwrite hpre hread0 hread1
  intro s
  unfold cL17C_projNode
  have hs : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact applyNode_fw_per_head_mix_precision_linear_out g s rank xTid wTid outTid []

private def cL17C_gatherNode : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [10836, 10837],
    outs := [5983], params := [0] }
private def cL17C_pmProjNode : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear",
    ins := [5983, 5984], outs := [5985] }
private def cL17C_chunk0Node : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5985], outs := [10838], params := [0] }
private def cL17C_chunk1Node : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5985], outs := [10839], params := [0] }

private theorem cL17C_pm_gather_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5983 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 10836,
         denoteGraphDistributedFaithful pm_goal_1 initPM 10837] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1640 cL17C_gatherNode
    10836 10837 5983 (fun x0 x1 => allGatherPrimDimN 0 2 0 [x0, x1])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL17C_gatherNode
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [10836, 10837] 5983 0

private theorem cL17C_pm_proj_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5985 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5983)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5984) := by
  exact cL17C_proj_reduce pm_goal_1 initPM 1642 1 5983 5984 5985
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)

private theorem cL17C_pm_chunks_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10838 =
        chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5985) ∧
      denoteGraphDistributedFaithful pm_goal_1 initPM 10839 =
        chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5985) := by
  refine ⟨?_, ?_⟩
  · refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1643 cL17C_chunk0Node
      5985 10838 (fun x => chunkPrimDimN 0 2 0 x)
      (by native_decide) (by native_decide) ?_
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    intro s
    unfold cL17C_chunk0Node
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5985 10838 0
  · refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1644 cL17C_chunk1Node
      5985 10839 (fun x => chunkPrimDimN 0 2 1 x)
      (by native_decide) (by native_decide) ?_
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    intro s
    unfold cL17C_chunk1Node
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5985 10839 0

private theorem cL17C_init_singleton_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals) (tid : Tid)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid) :
    initSM tid = initPM tid := by
  have h := hInit g hg
  unfold InitGoalHolds at h
  have hv := h.2.2
  rw [reconstructForGoal_of_not_replicated g pm_goal_1.numRanks _ hrep,
    htp, hts, hgd] at hv
  simpa only [List.map, reconstructWithDim] using hv

/-- The canonical L17 Q path is derived from the L19 output and initialized
weights. No relation over a computed Q intermediate is a caller premise. -/
theorem canonical_l17_q_relation_from_incoming
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5977)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10829)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5985)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10838)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10839)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hsmBase := cL17C_multiref_reduce sm_goal_1 initSM 747 0 2 5977 8773
    [8773, 8777] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp0Base := cL17C_multiref_reduce pm_goal_1 initPM 1636 0 2 10828 16310
    [16310, 16314] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp1Base := cL17C_multiref_reduce pm_goal_1 initPM 1637 1 2 10829 16318
    [16318, 16322] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hsmRms := cL17C_rms_reduce sm_goal_1 initSM 748 0 8773 5982 5983
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hp0Rms := cL17C_rms_reduce pm_goal_1 initPM 1638 0 16310 5982 10836
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hp1Rms := cL17C_rms_reduce pm_goal_1 initPM 1639 1 16318 5982 10837
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h5766Init := cL17C_init_singleton_eq initSM initPM hInit initGoal_5982
    (by native_decide) 5982 rfl rfl rfl rfl
  have hsm5766 : denoteGraphDistributedFaithful sm_goal_1 initSM 5982 = initSM 5982 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM 5982 (by native_decide) (by native_decide)
  have hpm5766 : denoteGraphDistributedFaithful pm_goal_1 initPM 5982 = initPM 5982 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 5982 (by native_decide) (by native_decide)
  have hwRms : denoteGraphDistributedFaithful sm_goal_1 initSM 5982 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5982 := by
    rw [hsm5766, hpm5766, h5766Init]
  have hRms : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10837)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [hsmRms, hp0Rms, hp1Rms, hsmBase, hp0Base, hp1Base, hwRms]
    exact Zigzag2Rel.rms_norm 2048 1024 hIncoming (by decide) (by decide) rfl
  have h5768Init := cL17C_init_singleton_eq initSM initPM hInit initGoal_5984
    (by native_decide) 5984 rfl rfl rfl rfl
  have hsm5768 : denoteGraphDistributedFaithful sm_goal_1 initSM 5984 = initSM 5984 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM 5984 (by native_decide) (by native_decide)
  have hpm5768 : denoteGraphDistributedFaithful pm_goal_1 initPM 5984 = initPM 5984 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 5984 (by native_decide) (by native_decide)
  have hwEq : denoteGraphDistributedFaithful sm_goal_1 initSM 5984 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5984 := by
    rw [hsm5768, hpm5768, h5768Init]
  have hwShape : (denoteGraphDistributedFaithful pm_goal_1 initPM 5984).shape =
      [16, 64, 1024] := by
    rw [hpm5768]
    exact hPM 5984 [16, 64, 1024] (by native_decide)
  have hsmQ := cL17C_proj_reduce sm_goal_1 initSM 749 0 5983 5984 5985
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hExpr := Zigzag2Rel.per_head_linear 2048 1024 16 64 hRms hwShape
    (by decide) (by decide) (by decide) (by decide)
  have hPMRms : Gather2Rel
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10836)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10837)
      [4096, 1024] [2048, 1024] := by
    refine ⟨cL17C_pm_gather_reduce initPM, ?_, hRms.rank0_shape,
      hRms.rank1_shape, by decide⟩
    rw [cL17C_pm_gather_reduce initPM,
      allGatherPrimDimN_shape 0 2 _ [2048, 1024]]
    · rfl
    · simp only [List.head?_cons, Option.map_some, Option.getD_some,
        hRms.rank0_shape]
  have hPMProj := hPMRms.per_head_linear 2048 1024 16 64 hwShape
    (by decide) (by decide) (by decide) (by decide)
  have hChunks := cL17C_pm_chunks_reduce initPM
  have hChunk0 : denoteGraphDistributedFaithful pm_goal_1 initPM 10838 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10836)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5984) := by
    rw [hChunks.1, cL17C_pm_proj_reduce initPM, hPMProj.value]
    simpa only [List.getD_cons_zero] using
      (chunk_allGather_cp2_dim0_3d
      (x0 := fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10836)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5984))
      (x1 := fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10837)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5984))
      (lDim := 2048) (d1 := 16) (d2 := 64) (r := 0)
      hPMProj.shard0_shape hPMProj.shard1_shape (by decide) (by decide)
      (by decide) (by decide))
  have hChunk1 : denoteGraphDistributedFaithful pm_goal_1 initPM 10839 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10837)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5984) := by
    rw [hChunks.2, cL17C_pm_proj_reduce initPM, hPMProj.value]
    simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      (chunk_allGather_cp2_dim0_3d
        (x0 := fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10836)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5984))
        (x1 := fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10837)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5984))
        (lDim := 2048) (d1 := 16) (d2 := 64) (r := 1)
        hPMProj.shard0_shape hPMProj.shard1_shape (by decide) (by decide)
        (by decide) (by decide))
  rw [hsmQ, hwEq, hChunk0, hChunk1]
  exact hExpr

#print axioms canonical_l17_q_relation_from_incoming

end
end TrainVerify.Denote.GeneratedPatterns
