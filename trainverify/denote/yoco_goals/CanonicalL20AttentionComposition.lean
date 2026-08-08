/- Canonical Goal 1, layer 20: composition of the L19 boundary into Q. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagLinearRel
import denote.yoco_goals.ZigzagPointwiseRel
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

private theorem cL20C_storeSet_zip_replicate (s : Store) (v : Tensor) :
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

private def cL20C_multirefNode (rank n : Nat) (xTid : Tid)
    (outs : List Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
    outs := outs, params := [n] }

private theorem cL20C_apply_multiref (g : GraphDecl) (s : Store)
    (rank n xTid : Nat) (outs : List Tid) (t : Tid)
    (hmem : t ∈ outs) (hlen : outs.length ≤ n) :
    applyNode g s (cL20C_multirefNode rank n xTid outs) t = s xTid := by
  unfold cL20C_multirefNode
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  exact cL20C_storeSet_zip_replicate s (s xTid) outs n t hmem hlen

private theorem cL20C_multiref_reduce (g : GraphDecl) (init : Store)
    (idx rank n xTid t : Nat) (outs : List Tid)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL20C_multirefNode rank n xTid outs)
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
  unfold cL20C_multirefNode
  have hs : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_multiref" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact cL20C_apply_multiref g s rank n xTid outs t hmem hlen

private def cL20C_rmsNode (rank : Nat) (xTid wTid outTid : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_rms_norm", ins := [xTid, wTid], outs := [outTid] }

private theorem cL20C_rms_reduce (g : GraphDecl) (init : Store)
    (idx rank xTid wTid outTid : Nat)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL20C_rmsNode rank xTid wTid outTid)
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
  unfold cL20C_rmsNode
  have hs : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact applyNode_fw_rms_norm_out g s rank xTid wTid outTid []

private def cL20C_projNode (rank : Nat) (xTid wTid outTid : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_per_head_mix_precision_linear",
    ins := [xTid, wTid], outs := [outTid] }

private theorem cL20C_proj_reduce (g : GraphDecl) (init : Store)
    (idx rank xTid wTid outTid : Nat)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL20C_projNode rank xTid wTid outTid)
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
  unfold cL20C_projNode
  have hs : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact applyNode_fw_per_head_mix_precision_linear_out g s rank xTid wTid outTid []

private theorem cL20C_init_singleton_eq (initSM initPM : Store)
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

/-- The canonical L20 Q path is derived from the L19 output and initialized
weights. No relation over a computed Q intermediate is a caller premise. -/
theorem canonical_l20_q_relation_from_l19
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hL19 : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6139)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11290)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11291)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6147)
      (fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11298)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6146))
      (fw_per_head_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11299)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6146))
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 16, 64] [2048, 16, 64] := by
  have hsmBase := cL20C_multiref_reduce sm_goal_1 initSM 852 0 2 6139 8890
    [8890, 8894] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp0Base := cL20C_multiref_reduce pm_goal_1 initPM 1864 0 2 11290 16406
    [16406, 16410] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp1Base := cL20C_multiref_reduce pm_goal_1 initPM 1865 1 2 11291 16414
    [16414, 16418] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hsmRms := cL20C_rms_reduce sm_goal_1 initSM 853 0 8890 6144 6145
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hp0Rms := cL20C_rms_reduce pm_goal_1 initPM 1866 0 16406 6144 11298
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hp1Rms := cL20C_rms_reduce pm_goal_1 initPM 1867 1 16414 6144 11299
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have h6144Init := cL20C_init_singleton_eq initSM initPM hInit initGoal_6144
    (by native_decide) 6144 rfl rfl rfl rfl
  have hsm6144 : denoteGraphDistributedFaithful sm_goal_1 initSM 6144 = initSM 6144 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM 6144 (by native_decide) (by native_decide)
  have hpm6144 : denoteGraphDistributedFaithful pm_goal_1 initPM 6144 = initPM 6144 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6144 (by native_decide) (by native_decide)
  have hwRms : denoteGraphDistributedFaithful sm_goal_1 initSM 6144 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6144 := by
    rw [hsm6144, hpm6144, h6144Init]
  have hRms : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6145)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11298)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11299)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [hsmRms, hp0Rms, hp1Rms, hsmBase, hp0Base, hp1Base, hwRms]
    exact Zigzag2Rel.rms_norm 2048 1024 hL19 (by decide) (by decide) rfl
  have h6146Init := cL20C_init_singleton_eq initSM initPM hInit initGoal_6146
    (by native_decide) 6146 rfl rfl rfl rfl
  have hsm6146 : denoteGraphDistributedFaithful sm_goal_1 initSM 6146 = initSM 6146 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
      initSM 6146 (by native_decide) (by native_decide)
  have hpm6146 : denoteGraphDistributedFaithful pm_goal_1 initPM 6146 = initPM 6146 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6146 (by native_decide) (by native_decide)
  have hwEq : denoteGraphDistributedFaithful sm_goal_1 initSM 6146 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6146 := by
    rw [hsm6146, hpm6146, h6146Init]
  have hwShape : (denoteGraphDistributedFaithful pm_goal_1 initPM 6146).shape =
      [16, 64, 1024] := by
    rw [hpm6146]
    exact hPM 6146 [16, 64, 1024] (by native_decide)
  have hsmQ := cL20C_proj_reduce sm_goal_1 initSM 854 0 6145 6146 6147
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  rw [hsmQ, hwEq]
  exact Zigzag2Rel.per_head_linear 2048 1024 16 64 hRms hwShape
    (by decide) (by decide) (by decide) (by decide)

#print axioms canonical_l20_q_relation_from_l19

end
end TrainVerify.Denote.GeneratedPatterns
