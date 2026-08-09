/- Canonical Goal 1, layer 22: composition of the L21 boundary into Q. -/
import denote.yoco_goals.CanonicalL21Output
import denote.yoco_goals.CanonicalL22Attention
import denote.yoco_goals.ZigzagAttentionRel

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private theorem cL22C_storeSet_zip_replicate (s : Store) (v : Tensor) :
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

private def cL22C_multirefNode (rank n : Nat) (xTid : Tid)
    (outs : List Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
    outs := outs, params := [n] }

private theorem cL22C_apply_multiref (g : GraphDecl) (s : Store)
    (rank n xTid : Nat) (outs : List Tid) (t : Tid)
    (hmem : t ∈ outs) (hlen : outs.length ≤ n) :
    applyNode g s (cL22C_multirefNode rank n xTid outs) t = s xTid := by
  unfold cL22C_multirefNode
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  exact cL22C_storeSet_zip_replicate s (s xTid) outs n t hmem hlen

private theorem cL22C_multiref_reduce (g : GraphDecl) (init : Store)
    (idx rank n xTid t : Nat) (outs : List Tid)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL22C_multirefNode rank n xTid outs)
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
  unfold cL22C_multirefNode
  have hs : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_multiref" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact cL22C_apply_multiref g s rank n xTid outs t hmem hlen

private def cL22C_rmsNode (rank : Nat) (xTid wTid outTid : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_rms_norm", ins := [xTid, wTid], outs := [outTid] }

private theorem cL22C_rms_reduce (g : GraphDecl) (init : Store)
    (idx rank xTid wTid outTid : Nat)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL22C_rmsNode rank xTid wTid outTid)
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
  unfold cL22C_rmsNode
  have hs : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact applyNode_fw_rms_norm_out g s rank xTid wTid outTid []

private theorem cL22C_init_singleton_eq (initSM initPM : Store)
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

private theorem cL22C_chunk0_of_gather (x0 x1 : Tensor)
    (hx0 : x0.shape = [2048, 16, 64])
    (hx1 : x1.shape = [2048, 16, 64]) :
    chunkPrimDimN 0 2 0 (allGatherPrimDimN 0 2 0 [x0, x1]) = x0 := by
  exact chunk_allGather_cp2_dim0_3d x0 x1 2048 16 64 0 hx0 hx1
    (by decide) (by decide) (by decide) (by decide)

private theorem cL22C_chunk1_of_gather (x0 x1 : Tensor)
    (hx0 : x0.shape = [2048, 16, 64])
    (hx1 : x1.shape = [2048, 16, 64]) :
    chunkPrimDimN 0 2 1 (allGatherPrimDimN 0 2 0 [x0, x1]) = x1 := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (chunk_allGather_cp2_dim0_3d x0 x1 2048 16 64 1 hx0 hx1
      (by decide) (by decide) (by decide) (by decide))

-- The canonical Q path is fully composed from the sole computed L21 boundary.
-- The conclusion exposes the genuine zigzag Q relation immediately before attention;
-- no Q computed relation is assumed.
set_option maxHeartbeats 4000000 in
theorem canonical_l22_q_relation_from_l21
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hL21 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11444)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11445)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11454)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11455)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hsmBase := cL22C_multiref_reduce sm_goal_1 initSM 887 0 2 6193 8929
    [8929, 8933] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp0Base := cL22C_multiref_reduce pm_goal_1 initPM 1940 0 2 11444 16438
    [16438, 16442] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp1Base := cL22C_multiref_reduce pm_goal_1 initPM 1941 1 2 11445 16446
    [16446, 16450] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hsmRms := cL22C_rms_reduce sm_goal_1 initSM 888 0 8929 6198 6199
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hp0Rms := cL22C_rms_reduce pm_goal_1 initPM 1942 0 16438 6198 11452
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hp1Rms := cL22C_rms_reduce pm_goal_1 initPM 1943 1 16446 6198 11453
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h6198Init := cL22C_init_singleton_eq initSM initPM hInit initGoal_6198
    (by native_decide) 6198 rfl rfl rfl rfl
  have hsmFinal : denoteGraphDistributedFaithful sm_goal_1 initSM 6198 = initSM 6198 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM 6198 (by native_decide) (by native_decide)
  have hpmFinal : denoteGraphDistributedFaithful pm_goal_1 initPM 6198 = initPM 6198 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6198 (by native_decide) (by native_decide)
  have hwRms : denoteGraphDistributedFaithful sm_goal_1 initSM 6198 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6198 := by
    rw [hsmFinal, hpmFinal, h6198Init]
  have hRms : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6199)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11452)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11453)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [hsmRms, hp0Rms, hp1Rms, hsmBase, hp0Base, hp1Base, hwRms]
    exact Zigzag2Rel.rms_norm 2048 1024 hL21 (by decide) (by decide) rfl
  have h6200Init := cL22C_init_singleton_eq initSM initPM hInit initGoal_6200
    (by native_decide) 6200 rfl rfl rfl rfl
  have hsmW : denoteGraphDistributedFaithful sm_goal_1 initSM 6200 = initSM 6200 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM 6200 (by native_decide) (by native_decide)
  have hpmW : denoteGraphDistributedFaithful pm_goal_1 initPM 6200 = initPM 6200 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6200 (by native_decide) (by native_decide)
  have hwEq : denoteGraphDistributedFaithful sm_goal_1 initSM 6200 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6200 := by
    rw [hsmW, hpmW, h6200Init]
  have hwShape : (denoteGraphDistributedFaithful pm_goal_1 initPM 6200).shape =
      [16, 64, 1024] := by
    rw [hpmW]
    exact hPM 6200 [16, 64, 1024] (by native_decide)
  have hProjected : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6201)
      (fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11452)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6200))
      (fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11453)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6200))
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
    rw [canonical_l22_q_sm_reduce initSM, hwEq]
    exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hRms hwShape
      (by decide) (by decide) (by decide) (by decide)
  have hCommute := fw_per_head_mix_precision_linear_allGather0_commute_2
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11452)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11453)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6200)
    2048 1024 16 64 (by decide) (by decide) (by decide) (by decide)
    hRms.rank0_shape hRms.rank1_shape hwShape
  have hFullPM : denoteGraphDistributedFaithful pm_goal_1 initPM 6201 =
      allGatherPrimDimN 0 2 0
        [fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11452)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 6200),
         fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11453)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 6200)] := by
    rw [canonical_l22_q_pm_full_reduce initPM,
      canonical_l22_q_pm_gather_reduce initPM, hCommute]
  have hChunks := canonical_l22_q_pm_chunks_reduce initPM
  have hChunk0 : denoteGraphDistributedFaithful pm_goal_1 initPM 11454 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11452)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6200) := by
    calc
      _ = chunkPrimDimN 0 2 0
          (denoteGraphDistributedFaithful pm_goal_1 initPM 6201) := hChunks.1
      _ = chunkPrimDimN 0 2 0 (allGatherPrimDimN 0 2 0
          [fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11452)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 6200),
           fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11453)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 6200)]) :=
        congrArg (chunkPrimDimN 0 2 0) hFullPM
      _ = _ := cL22C_chunk0_of_gather _ _
        hProjected.rank0_shape hProjected.rank1_shape
  have hChunk1 : denoteGraphDistributedFaithful pm_goal_1 initPM 11455 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11453)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6200) := by
    calc
      _ = chunkPrimDimN 0 2 1
          (denoteGraphDistributedFaithful pm_goal_1 initPM 6201) := hChunks.2
      _ = chunkPrimDimN 0 2 1 (allGatherPrimDimN 0 2 0
          [fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11452)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 6200),
           fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11453)
            (denoteGraphDistributedFaithful pm_goal_1 initPM 6200)]) :=
        congrArg (chunkPrimDimN 0 2 1) hFullPM
      _ = _ := cL22C_chunk1_of_gather _ _
        hProjected.rank0_shape hProjected.rank1_shape
  rw [hChunk0, hChunk1]
  exact hProjected

private theorem cL22C_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hnil : ∀ n ∈ g.nodes, n.outs ≠ [])
    (hwrite : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hnil hwrite

/-- The real L22 sharded-K/V attention nodes preserve the Q relation.  The
query cumulative-sequence alias is obtained from the generated external-value
class, while SM/PM metadata equality comes from the init lineage contract. -/
theorem canonical_l22_attention_from_qkv
    (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hPMValues : InputValueClassesHold pmInputValueClasses initPM)
    (hPacked : PackedCuSeqlensWF (initPM 6252) 4096 2)
    (hQ : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11454)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11455)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64])
    (hK : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6202)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11466)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11467)
      [4096, 4, 64] [2048, 4, 64])
    (hV : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6203)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11472)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11473)
      [4096, 4, 64] [2048, 4, 64]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11478)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11479)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hsm6204 := cL22C_leaf sm_goal_1 initSM 6204
    (by native_decide) (by native_decide)
  have hpm6204 := cL22C_leaf pm_goal_1 initPM 6204
    (by native_decide) (by native_decide)
  have hsm6205 := cL22C_leaf sm_goal_1 initSM 6205
    (by native_decide) (by native_decide)
  have hpm6205 := cL22C_leaf pm_goal_1 initPM 6205
    (by native_decide) (by native_decide)
  have hpm6252 := cL22C_leaf pm_goal_1 initPM 6252
    (by native_decide) (by native_decide)
  have h6204Init := cL22C_init_singleton_eq initSM initPM hInit initGoal_6204
    (by native_decide) 6204 rfl rfl rfl rfl
  have h6205Init := cL22C_init_singleton_eq initSM initPM hInit initGoal_6205
    (by native_decide) 6205 rfl rfl rfl rfl
  have hMetaQ : denoteGraphDistributedFaithful sm_goal_1 initSM 6204 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6204 := by
    rw [hsm6204, hpm6204, h6204Init]
  have hMetaKV : denoteGraphDistributedFaithful sm_goal_1 initSM 6205 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6205 := by
    rw [hsm6205, hpm6205, h6205Init]
  have hInitAlias : initPM 6204 = initPM 6252 :=
    InputValueClassesHold.eq_of_mem hPMValues (c := pmInputValueClasses[1])
      (by native_decide) (by native_decide) (by native_decide)
  have hMetaAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 6204 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hpm6204, hpm6252, hInitAlias]
  have hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 2 * 2048] := by
    rw [hpm6252]
    simpa only [Nat.reduceMul] using hPacked.decoded_single
  rw [canonical_l22_attention_sm_reduce initSM,
    canonical_l22_attention_pm0_reduce initPM,
    canonical_l22_attention_pm1_reduce initPM,
    hMetaQ, hMetaKV, hMetaAlias]
  exact Zigzag2Rel.attn_zigzag_sharded_kv
    (denoteGraphDistributedFaithful sm_goal_1 initSM 6201)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11454)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11455)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (denoteGraphDistributedFaithful sm_goal_1 initSM 6202)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11466)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11467)
    (denoteGraphDistributedFaithful sm_goal_1 initSM 6203)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11472)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11473)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6205)
    2048 16 4 64 64 true 0 hQ hK hV rfl hDecoded
    (by decide) (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
