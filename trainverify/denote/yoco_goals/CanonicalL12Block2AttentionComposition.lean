/- Canonical Goal 1, layer 12 block 2: composition of the L19 boundary into Q. -/
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

private theorem cL12B2C_storeSet_zip_replicate (s : Store) (v : Tensor) :
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

private def cL12B2C_multirefNode (rank n : Nat) (xTid : Tid)
    (outs : List Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
    outs := outs, params := [n] }

private theorem cL12B2C_apply_multiref (g : GraphDecl) (s : Store)
    (rank n xTid : Nat) (outs : List Tid) (t : Tid)
    (hmem : t ∈ outs) (hlen : outs.length ≤ n) :
    applyNode g s (cL12B2C_multirefNode rank n xTid outs) t = s xTid := by
  unfold cL12B2C_multirefNode
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  exact cL12B2C_storeSet_zip_replicate s (s xTid) outs n t hmem hlen

private theorem cL12B2C_multiref_reduce (g : GraphDecl) (init : Store)
    (idx rank n xTid t : Nat) (outs : List Tid)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL12B2C_multirefNode rank n xTid outs)
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
  unfold cL12B2C_multirefNode
  have hs : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_multiref" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact cL12B2C_apply_multiref g s rank n xTid outs t hmem hlen

private def cL12B2C_rmsNode (rank : Nat) (xTid wTid outTid : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_rms_norm", ins := [xTid, wTid], outs := [outTid] }

private theorem cL12B2C_rms_reduce (g : GraphDecl) (init : Store)
    (idx rank xTid wTid outTid : Nat)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL12B2C_rmsNode rank xTid wTid outTid)
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
  unfold cL12B2C_rmsNode
  have hs : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact applyNode_fw_rms_norm_out g s rank xTid wTid outTid []

private def cL12B2C_projNode (rank : Nat) (xTid wTid outTid : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_per_head_mix_precision_linear",
    ins := [xTid, wTid], outs := [outTid] }

private theorem cL12B2C_proj_reduce (g : GraphDecl) (init : Store)
    (idx rank xTid wTid outTid : Nat)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL12B2C_projNode rank xTid wTid outTid)
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
  unfold cL12B2C_projNode
  have hs : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact applyNode_fw_per_head_mix_precision_linear_out g s rank xTid wTid outTid []

private def cL12B2C_gatherNode : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [9912, 9913],
    outs := [5659], params := [0] }
private def cL12B2C_pmProjNode : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear",
    ins := [5659, 5660], outs := [5661] }
private def cL12B2C_chunk0Node : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5661], outs := [9914], params := [0] }
private def cL12B2C_chunk1Node : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5661], outs := [9915], params := [0] }

private theorem cL12B2C_pm_gather_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5659 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 9912,
         denoteGraphDistributedFaithful pm_goal_1 initPM 9913] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1184 cL12B2C_gatherNode
    9912 9913 5659 (fun x0 x1 => allGatherPrimDimN 0 2 0 [x0, x1])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12B2C_gatherNode
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [9912, 9913] 5659 0

private theorem cL12B2C_pm_proj_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5661 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5659)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5660) := by
  exact cL12B2C_proj_reduce pm_goal_1 initPM 1186 1 5659 5660 5661
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)

private theorem cL12B2C_pm_chunks_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9914 =
        chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5661) ∧
      denoteGraphDistributedFaithful pm_goal_1 initPM 9915 =
        chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5661) := by
  refine ⟨?_, ?_⟩
  · refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1187 cL12B2C_chunk0Node
      5661 9914 (fun x => chunkPrimDimN 0 2 0 x)
      (by native_decide) (by native_decide) ?_
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    intro s
    unfold cL12B2C_chunk0Node
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5661 9914 0
  · refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1188 cL12B2C_chunk1Node
      5661 9915 (fun x => chunkPrimDimN 0 2 1 x)
      (by native_decide) (by native_decide) ?_
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    intro s
    unfold cL12B2C_chunk1Node
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5661 9915 0

private theorem cL12B2C_init_singleton_eq (initSM initPM : Store)
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

/-- The canonical L12 block 2 Q path is derived from the L19 output and initialized
weights. No relation over a computed Q intermediate is a caller premise. -/
theorem canonical_l12b2_q_relation_from_incoming
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hIncoming : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5653)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9905)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5661)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9914)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9915)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hsmBase := cL12B2C_multiref_reduce sm_goal_1 initSM 537 0 2 5653 8539
    [8539, 8543] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp0Base := cL12B2C_multiref_reduce pm_goal_1 initPM 1180 0 2 9904 16118
    [16118, 16122] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp1Base := cL12B2C_multiref_reduce pm_goal_1 initPM 1181 1 2 9905 16126
    [16126, 16130] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hsmRms := cL12B2C_rms_reduce sm_goal_1 initSM 538 0 8539 5658 5659
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hp0Rms := cL12B2C_rms_reduce pm_goal_1 initPM 1182 0 16118 5658 9912
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hp1Rms := cL12B2C_rms_reduce pm_goal_1 initPM 1183 1 16126 5658 9913
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h5658Init := cL12B2C_init_singleton_eq initSM initPM hInit initGoal_5658
    (by native_decide) 5658 rfl rfl rfl rfl
  have hsm5658 : denoteGraphDistributedFaithful sm_goal_1 initSM 5658 = initSM 5658 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM 5658 (by native_decide) (by native_decide)
  have hpm5658 : denoteGraphDistributedFaithful pm_goal_1 initPM 5658 = initPM 5658 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 5658 (by native_decide) (by native_decide)
  have hwRms : denoteGraphDistributedFaithful sm_goal_1 initSM 5658 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5658 := by
    rw [hsm5658, hpm5658, h5658Init]
  have hRms : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5659)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9912)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9913)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [hsmRms, hp0Rms, hp1Rms, hsmBase, hp0Base, hp1Base, hwRms]
    exact Zigzag2Rel.rms_norm 2048 1024 hIncoming (by decide) (by decide) rfl
  have h5660Init := cL12B2C_init_singleton_eq initSM initPM hInit initGoal_5660
    (by native_decide) 5660 rfl rfl rfl rfl
  have hsm5660 : denoteGraphDistributedFaithful sm_goal_1 initSM 5660 = initSM 5660 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM 5660 (by native_decide) (by native_decide)
  have hpm5660 : denoteGraphDistributedFaithful pm_goal_1 initPM 5660 = initPM 5660 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 5660 (by native_decide) (by native_decide)
  have hwEq : denoteGraphDistributedFaithful sm_goal_1 initSM 5660 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5660 := by
    rw [hsm5660, hpm5660, h5660Init]
  have hwShape : (denoteGraphDistributedFaithful pm_goal_1 initPM 5660).shape =
      [16, 64, 1024] := by
    rw [hpm5660]
    exact hPM 5660 [16, 64, 1024] (by native_decide)
  have hsmQ := cL12B2C_proj_reduce sm_goal_1 initSM 539 0 5659 5660 5661
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hExpr := Zigzag2Rel.per_head_linear 2048 1024 16 64 hRms hwShape
    (by decide) (by decide) (by decide) (by decide)
  have hPMRms : Gather2Rel
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5659)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9912)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9913)
      [4096, 1024] [2048, 1024] := by
    refine ⟨cL12B2C_pm_gather_reduce initPM, ?_, hRms.rank0_shape,
      hRms.rank1_shape, by decide⟩
    rw [cL12B2C_pm_gather_reduce initPM,
      allGatherPrimDimN_shape 0 2 _ [2048, 1024]]
    · rfl
    · simp only [List.head?_cons, Option.map_some, Option.getD_some,
        hRms.rank0_shape]
  have hPMProj := hPMRms.per_head_linear 2048 1024 16 64 hwShape
    (by decide) (by decide) (by decide) (by decide)
  have hChunks := cL12B2C_pm_chunks_reduce initPM
  have hChunk0 : denoteGraphDistributedFaithful pm_goal_1 initPM 9914 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9912)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5660) := by
    rw [hChunks.1, cL12B2C_pm_proj_reduce initPM, hPMProj.value]
    simpa only [List.getD_cons_zero] using
      (chunk_allGather_cp2_dim0_3d
      (x0 := fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9912)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5660))
      (x1 := fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9913)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5660))
      (lDim := 2048) (d1 := 16) (d2 := 64) (r := 0)
      hPMProj.shard0_shape hPMProj.shard1_shape (by decide) (by decide)
      (by decide) (by decide))
  have hChunk1 : denoteGraphDistributedFaithful pm_goal_1 initPM 9915 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9913)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5660) := by
    rw [hChunks.2, cL12B2C_pm_proj_reduce initPM, hPMProj.value]
    simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      (chunk_allGather_cp2_dim0_3d
        (x0 := fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9912)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5660))
        (x1 := fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9913)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5660))
        (lDim := 2048) (d1 := 16) (d2 := 64) (r := 1)
        hPMProj.shard0_shape hPMProj.shard1_shape (by decide) (by decide)
        (by decide) (by decide))
  rw [hsmQ, hwEq, hChunk0, hChunk1]
  exact hExpr

#print axioms canonical_l12b2_q_relation_from_incoming

end
end TrainVerify.Denote.GeneratedPatterns

