/- Canonical Goal 1, layer 19: faithful K/V cache graph reductions. -/
import denote.yoco_goals.Goal_1
import denote.DenoteMoE
import denote.yoco_goals.CanonicalL19KVSemantic

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section

private theorem cL19KV_storeSet_zip_replicate (s : Store) (v : Tensor) :
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

private def cL19KV_multirefNode (rank n : Nat) (xTid : Tid) (outs : List Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs, params := [n] }

private theorem cL19KV_reduce_multiref (g : GraphDecl) (init : Store)
    (idx rank n xTid t : Nat) (outs : List Tid)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL19KV_multirefNode rank n xTid outs)
    (hmem : t ∈ outs) (hlen : outs.length ≤ n)
    (hafter : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (hwrite : ∀ nd ∈ g.nodes.drop (idx + 1), t ∉ nd.outs)
    (hpre : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hread : ∀ nd ∈ g.nodes.drop idx, xTid ∉ nd.outs) :
    denoteGraphDistributedFaithful g init t = denoteGraphDistributedFaithful g init xTid := by
  refine denoteGraphDistributedFaithful_reduce1 g init idx _ xTid t (fun x => x)
    hidx hnode ?_ hafter hwrite hpre hread
  intro s
  unfold cL19KV_multirefNode
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
  exact cL19KV_storeSet_zip_replicate s (s xTid) outs n t hmem hlen

private def cL19KV_rmsNode (rank : Nat) (x w out : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_rms_norm", ins := [x, w], outs := [out] }
private def cL19KV_projNode (rank : Nat) (x w out : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_per_head_mix_precision_linear", ins := [x, w], outs := [out] }
private def cL19KV_toNode (rank : Nat) (x out : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_to", ins := [x], outs := [out] }

private theorem cL19KV_reduce_rms (g : GraphDecl) (init : Store)
    (idx rank x w out : Nat) (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL19KV_rmsNode rank x w out)
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
  unfold cL19KV_rmsNode
  have hs : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have hattn : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu hattn]
  exact applyNode_fw_rms_norm_out g s rank x w out []

private theorem cL19KV_reduce_proj (g : GraphDecl) (init : Store)
    (idx rank x w out : Nat) (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL19KV_projNode rank x w out)
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
  unfold cL19KV_projNode
  have hs : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_unshuffle" := by decide
  have hattn : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu hattn]
  exact applyNode_fw_per_head_mix_precision_linear_out g s rank x w out []

private theorem cL19KV_reduce_to (g : GraphDecl) (init : Store)
    (idx rank x out : Nat) (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL19KV_toNode rank x out)
    (ha : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (ho : ∀ nd ∈ g.nodes.drop (idx + 1), out ∉ nd.outs)
    (hp : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hx : ∀ nd ∈ g.nodes.drop idx, x ∉ nd.outs) :
    denoteGraphDistributedFaithful g init out = denoteGraphDistributedFaithful g init x := by
  refine denoteGraphDistributedFaithful_reduce1 g init idx _ x out (fun z => z)
    hidx hnode ?_ ha ho hp hx
  intro s
  unfold cL19KV_toNode
  have hs : ("OpName.FW_to" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_to" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have hattn : ("OpName.FW_to" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu hattn]
  exact applyNode_fw_to_out g s rank x out []

/-- Complete real SM L19 K graph relation: cache source through RMS, projection,
12-way fanout, and the L19 cast. -/
theorem canonical_l19_k_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6094 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
          (denoteGraphDistributedFaithful sm_goal_1 initSM 5596))
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5598) := by
  have hb := cL19KV_reduce_multiref sm_goal_1 initSM 470 0 2 5595 8368 [8368, 8372]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr := cL19KV_reduce_rms sm_goal_1 initSM 471 0 8368 5596 5597
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs := cL19KV_reduce_multiref sm_goal_1 initSM 473 0 2 5597 8376 [8376, 8380]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp := cL19KV_reduce_proj sm_goal_1 initSM 475 0 8376 5598 5599
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hf := cL19KV_reduce_multiref sm_goal_1 initSM 478 0 12 5599 8430
    [8394, 8398, 8402, 8406, 8410, 8414, 8418, 8422, 8426, 8430, 8434, 8438]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := cL19KV_reduce_to sm_goal_1 initSM 490 0 8430 6094
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hc, hf, hp, hs, hr, hb]

/-- Rank-0's complete real PM L19 K graph reduction. -/
theorem canonical_l19_k_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11158 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5598) := by
  have hb := cL19KV_reduce_multiref pm_goal_1 initPM 1040 0 2 9722 15822
    [15822, 15826] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr := cL19KV_reduce_rms pm_goal_1 initPM 1042 0 15822 5596 9726
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs := cL19KV_reduce_multiref pm_goal_1 initPM 1046 0 2 9726 15838
    [15838, 15842] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp := cL19KV_reduce_proj pm_goal_1 initPM 1050 0 15838 5598 9728
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hf := cL19KV_reduce_multiref pm_goal_1 initPM 1056 0 12 9728 15900
    [15864, 15868, 15872, 15876, 15880, 15884, 15888, 15892, 15896, 15900,
      15904, 15908]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := cL19KV_reduce_to pm_goal_1 initPM 1070 0 15900 11158
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hc, hf, hp, hs, hr, hb]

/-- Rank-1's complete real PM L19 K graph reduction. -/
theorem canonical_l19_k_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11159 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5598) := by
  have hb := cL19KV_reduce_multiref pm_goal_1 initPM 1041 1 2 9723 15830
    [15830, 15834] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr := cL19KV_reduce_rms pm_goal_1 initPM 1044 1 15830 5596 9727
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs := cL19KV_reduce_multiref pm_goal_1 initPM 1048 1 2 9727 15846
    [15846, 15850] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp := cL19KV_reduce_proj pm_goal_1 initPM 1053 1 15846 5598 9729
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hf := cL19KV_reduce_multiref pm_goal_1 initPM 1058 1 12 9729 15958
    [15922, 15926, 15930, 15934, 15938, 15942, 15946, 15950, 15954, 15958,
      15962, 15966]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := cL19KV_reduce_to pm_goal_1 initPM 1094 1 15958 11159
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hc, hf, hp, hs, hr, hb]

/-- Complete real SM L19 V graph relation. -/
theorem canonical_l19_v_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6095 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
          (denoteGraphDistributedFaithful sm_goal_1 initSM 5596))
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5600) := by
  have hb := cL19KV_reduce_multiref sm_goal_1 initSM 470 0 2 5595 8368 [8368, 8372]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr := cL19KV_reduce_rms sm_goal_1 initSM 471 0 8368 5596 5597
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs := cL19KV_reduce_multiref sm_goal_1 initSM 473 0 2 5597 8380 [8376, 8380]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp := cL19KV_reduce_proj sm_goal_1 initSM 476 0 8380 5600 5601
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hf := cL19KV_reduce_multiref sm_goal_1 initSM 479 0 12 5601 8488
    [8452, 8456, 8460, 8464, 8468, 8472, 8476, 8480, 8484, 8488, 8492, 8496]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc := cL19KV_reduce_to sm_goal_1 initSM 502 0 8488 6095
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hc, hf, hp, hs, hr, hb]

/-- Complete real PM L19 V graph relation on both ranks. -/
theorem canonical_l19_v_pm_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11164 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5600) ∧
    denoteGraphDistributedFaithful pm_goal_1 initPM 11165 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5600) := by
  have hb0 := cL19KV_reduce_multiref pm_goal_1 initPM 1040 0 2 9722 15822
    [15822, 15826] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hb1 := cL19KV_reduce_multiref pm_goal_1 initPM 1041 1 2 9723 15830
    [15830, 15834] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr0 := cL19KV_reduce_rms pm_goal_1 initPM 1042 0 15822 5596 9726
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hr1 := cL19KV_reduce_rms pm_goal_1 initPM 1044 1 15830 5596 9727
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 := cL19KV_reduce_multiref pm_goal_1 initPM 1046 0 2 9726 15842
    [15838, 15842] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs1 := cL19KV_reduce_multiref pm_goal_1 initPM 1048 1 2 9727 15850
    [15846, 15850] (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hp0 := cL19KV_reduce_proj pm_goal_1 initPM 1051 0 15842 5600 9740
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hp1 := cL19KV_reduce_proj pm_goal_1 initPM 1054 1 15850 5600 9741
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hf0 := cL19KV_reduce_multiref pm_goal_1 initPM 1057 0 12 9740 16016
    [15980, 15984, 15988, 15992, 15996, 16000, 16004, 16008, 16012, 16016,
      16020, 16024]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hf1 := cL19KV_reduce_multiref pm_goal_1 initPM 1059 1 12 9741 16074
    [16038, 16042, 16046, 16050, 16054, 16058, 16062, 16066, 16070, 16074,
      16078, 16082]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc0 := cL19KV_reduce_to pm_goal_1 initPM 1082 0 16016 11164
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have hc1 := cL19KV_reduce_to pm_goal_1 initPM 1106 1 16074 11165
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_⟩
  · rw [hc0, hf0, hp0, hs0, hr0, hb0]
  · rw [hc1, hf1, hp1, hs1, hr1, hb1]

private theorem cL19V_init_singleton_eq (initSM initPM : Store)
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

private theorem cL19V_weight_value (g : GraphDecl) (init : Store) (tid : Tid)
    (hne : ∀ n ∈ g.nodes, n.outs ≠ []) (hnw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hne hnw

private theorem cL19V_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (tid : Tid) (g : LineageGoal) (hg : g ∈ goal_1_full_initGoals)
    (htp : g.tps = [{ rank := 0, tid := tid }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hsnw : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs)
    (hpnw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM tid := by
  have hi := cL19V_init_singleton_eq initSM initPM hInit g hg tid htp hgd hrep hts
  rw [cL19V_weight_value sm_goal_1 initSM tid (by native_decide) hsnw,
    cL19V_weight_value pm_goal_1 initPM tid (by native_decide) hpnw, hi]

private theorem cL19V_proj_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5600).shape = [4, 64, 1024] := by
  rw [cL19V_weight_value pm_goal_1 initPM 5600 (by native_decide) (by native_decide)]
  exact hPM 5600 [4, 64, 1024] (by native_decide)

/-- Full ordinary canonical L19 V SM/PM graph relation. -/
theorem canonical_l19_v_ordinary_relation
    (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6095)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11164)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11165)
      [4096, 4, 64] [2048, 4, 64] := by
  have hRmsW := cL19V_weight_eq initSM initPM hInit 5596 initGoal_5596
    (by native_decide) rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hVW := cL19V_weight_eq initSM initPM hInit 5600 initGoal_5600
    (by native_decide) rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hVShape := cL19V_proj_weight_shape initPM hPM
  have hSemantic := canonical_l19_v_ordinary_semantic hCache hRmsW hVW hVShape
  have hPMr := canonical_l19_v_pm_reduce initPM
  have hSMr := canonical_l19_v_sm_reduce initSM
  rw [hSMr, hPMr.1, hPMr.2]
  exact hSemantic

#print axioms canonical_l19_k_sm_reduce
#print axioms canonical_l19_k_pm0_reduce
#print axioms canonical_l19_k_pm1_reduce
#print axioms canonical_l19_v_sm_reduce
#print axioms canonical_l19_v_pm_reduce
#print axioms canonical_l19_v_ordinary_relation

end
end TrainVerify.Denote.GeneratedPatterns
