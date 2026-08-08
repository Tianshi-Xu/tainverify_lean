/- Canonical Goal 1, layer 20: faithful K/V cache graph reductions. -/
import denote.yoco_goals.Goal_1
import denote.DenoteMoE

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section

private theorem cL20KV_storeSet_zip_replicate (s : Store) (v : Tensor) :
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

private def cL20KV_multirefNode (rank n : Nat) (xTid : Tid) (outs : List Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs, params := [n] }

private theorem cL20KV_reduce_multiref (g : GraphDecl) (init : Store)
    (idx rank n xTid t : Nat) (outs : List Tid)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL20KV_multirefNode rank n xTid outs)
    (hmem : t ∈ outs) (hlen : outs.length ≤ n)
    (hafter : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (hwrite : ∀ nd ∈ g.nodes.drop (idx + 1), t ∉ nd.outs)
    (hpre : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hread : ∀ nd ∈ g.nodes.drop idx, xTid ∉ nd.outs) :
    denoteGraphDistributedFaithful g init t = denoteGraphDistributedFaithful g init xTid := by
  refine denoteGraphDistributedFaithful_reduce1 g init idx _ xTid t (fun x => x)
    hidx hnode ?_ hafter hwrite hpre hread
  intro s
  unfold cL20KV_multirefNode
  have hs : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_multiref" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ hs hu ha]
  unfold applyNodeDistributed
  have hmoe : ("OpName.FW_multiref" : String) ≠ "OpName.FW_all2all_moe_gmm" := by decide
  rw [if_neg hmoe]
  unfold applyNodeRingAttn
  have hz : ("OpName.FW_multiref" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  have hsw : ("OpName.FW_multiref" : String) ≠ "OpName.FW_attn_sliding_window" := by decide
  rw [if_neg hz, if_neg hsw]
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  exact cL20KV_storeSet_zip_replicate s (s xTid) outs n t hmem hlen

private def cL20KV_rmsNode (rank : Nat) (x w out : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_rms_norm", ins := [x, w], outs := [out] }
private def cL20KV_projNode (rank : Nat) (x w out : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_per_head_mix_precision_linear", ins := [x, w], outs := [out] }
private def cL20KV_toNode (rank : Nat) (x out : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_to", ins := [x], outs := [out] }

private theorem cL20KV_reduce_rms (g : GraphDecl) (init : Store)
    (idx rank x w out : Nat) (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL20KV_rmsNode rank x w out)
    (ha : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (ho : ∀ nd ∈ g.nodes.drop (idx + 1), out ∉ nd.outs)
    (hp : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hx : ∀ nd ∈ g.nodes.drop idx, x ∉ nd.outs)
    (hw : ∀ nd ∈ g.nodes.drop idx, w ∉ nd.outs) :
    denoteGraphDistributedFaithful g init out =
      fw_rms_norm (denoteGraphDistributedFaithful g init x)
        (denoteGraphDistributedFaithful g init w) := by
  refine denoteGraphDistributedFaithful_reduce2 g init idx _ x w out fw_rms_norm
    hidx hnode ?_ ha ho hp hx hw
  intro s
  unfold cL20KV_rmsNode
  have hs : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have hattn : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu hattn]
  exact applyNode_fw_rms_norm_out g s rank x w out []

private theorem cL20KV_reduce_proj (g : GraphDecl) (init : Store)
    (idx rank x w out : Nat) (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL20KV_projNode rank x w out)
    (ha : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (ho : ∀ nd ∈ g.nodes.drop (idx + 1), out ∉ nd.outs)
    (hp : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hx : ∀ nd ∈ g.nodes.drop idx, x ∉ nd.outs)
    (hw : ∀ nd ∈ g.nodes.drop idx, w ∉ nd.outs) :
    denoteGraphDistributedFaithful g init out =
      fw_per_head_linear (denoteGraphDistributedFaithful g init x)
        (denoteGraphDistributedFaithful g init w) := by
  refine denoteGraphDistributedFaithful_reduce2 g init idx _ x w out fw_per_head_linear
    hidx hnode ?_ ha ho hp hx hw
  intro s
  unfold cL20KV_projNode
  have hs : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_unshuffle" := by decide
  have hattn : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu hattn]
  exact applyNode_fw_per_head_mix_precision_linear_out g s rank x w out []

private theorem cL20KV_reduce_to (g : GraphDecl) (init : Store)
    (idx rank x out : Nat) (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL20KV_toNode rank x out)
    (ha : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (ho : ∀ nd ∈ g.nodes.drop (idx + 1), out ∉ nd.outs)
    (hp : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hx : ∀ nd ∈ g.nodes.drop idx, x ∉ nd.outs) :
    denoteGraphDistributedFaithful g init out = denoteGraphDistributedFaithful g init x := by
  refine denoteGraphDistributedFaithful_reduce1 g init idx _ x out (fun z => z)
    hidx hnode ?_ ha ho hp hx
  intro s
  unfold cL20KV_toNode
  have hs : ("OpName.FW_to" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_to" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have hattn : ("OpName.FW_to" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu hattn]
  exact applyNode_fw_to_out g s rank x out []

/-- Complete real SM L20 K graph relation: cache source through RMS, projection,
12-way fanout, and the L20 cast. -/
theorem canonical_l20_k_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6148 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
          (denoteGraphDistributedFaithful sm_goal_1 initSM 5596))
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5598) := by
  have hb := cL20KV_reduce_multiref sm_goal_1 initSM 470 0 2 5595 8368 [8368, 8372]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr := cL20KV_reduce_rms sm_goal_1 initSM 471 0 8368 5596 5597
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs := cL20KV_reduce_multiref sm_goal_1 initSM 473 0 2 5597 8376 [8376, 8380]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp := cL20KV_reduce_proj sm_goal_1 initSM 475 0 8376 5598 5599
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hf := cL20KV_reduce_multiref sm_goal_1 initSM 478 0 12 5599 8434
    [8394, 8398, 8402, 8406, 8410, 8414, 8418, 8422, 8426, 8430, 8434, 8438]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := cL20KV_reduce_to sm_goal_1 initSM 491 0 8434 6148
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hc, hf, hp, hs, hr, hb]

/-- Rank-0's complete real PM L20 K graph reduction. -/
theorem canonical_l20_k_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11312 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5598) := by
  have hb := cL20KV_reduce_multiref pm_goal_1 initPM 1040 0 2 9722 15822
    [15822, 15826] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr := cL20KV_reduce_rms pm_goal_1 initPM 1042 0 15822 5596 9726
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs := cL20KV_reduce_multiref pm_goal_1 initPM 1046 0 2 9726 15838
    [15838, 15842] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp := cL20KV_reduce_proj pm_goal_1 initPM 1050 0 15838 5598 9728
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hf := cL20KV_reduce_multiref pm_goal_1 initPM 1056 0 12 9728 15904
    [15864, 15868, 15872, 15876, 15880, 15884, 15888, 15892, 15896, 15900,
      15904, 15908]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := cL20KV_reduce_to pm_goal_1 initPM 1071 0 15904 11312
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hc, hf, hp, hs, hr, hb]

/-- Rank-1's complete real PM L20 K graph reduction. -/
theorem canonical_l20_k_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11313 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5598) := by
  have hb := cL20KV_reduce_multiref pm_goal_1 initPM 1041 1 2 9723 15830
    [15830, 15834] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr := cL20KV_reduce_rms pm_goal_1 initPM 1044 1 15830 5596 9727
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs := cL20KV_reduce_multiref pm_goal_1 initPM 1048 1 2 9727 15846
    [15846, 15850] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp := cL20KV_reduce_proj pm_goal_1 initPM 1053 1 15846 5598 9729
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hf := cL20KV_reduce_multiref pm_goal_1 initPM 1058 1 12 9729 15962
    [15922, 15926, 15930, 15934, 15938, 15942, 15946, 15950, 15954, 15958,
      15962, 15966]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := cL20KV_reduce_to pm_goal_1 initPM 1095 1 15962 11313
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hc, hf, hp, hs, hr, hb]

/-- Complete real SM L20 V graph relation. -/
theorem canonical_l20_v_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6149 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
          (denoteGraphDistributedFaithful sm_goal_1 initSM 5596))
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5600) := by
  have hb := cL20KV_reduce_multiref sm_goal_1 initSM 470 0 2 5595 8368 [8368, 8372]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr := cL20KV_reduce_rms sm_goal_1 initSM 471 0 8368 5596 5597
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs := cL20KV_reduce_multiref sm_goal_1 initSM 473 0 2 5597 8380 [8376, 8380]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp := cL20KV_reduce_proj sm_goal_1 initSM 476 0 8380 5600 5601
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hf := cL20KV_reduce_multiref sm_goal_1 initSM 479 0 12 5601 8492
    [8452, 8456, 8460, 8464, 8468, 8472, 8476, 8480, 8484, 8488, 8492, 8496]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := cL20KV_reduce_to sm_goal_1 initSM 503 0 8492 6149
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hc, hf, hp, hs, hr, hb]

#print axioms canonical_l20_k_sm_reduce
#print axioms canonical_l20_k_pm0_reduce
#print axioms canonical_l20_k_pm1_reduce
#print axioms canonical_l20_v_sm_reduce

end
end TrainVerify.Denote.GeneratedPatterns
