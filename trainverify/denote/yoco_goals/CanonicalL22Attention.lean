/- Canonical Goal 1, layer 22: faithful reductions of the real attention nodes. -/
import denote.yoco_goals.Goal_1
import denote.yoco_goals.ZigzagLayoutRel
import denote.ZigzagCollective
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
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private theorem cL22A_reduce5
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 in2 in3 in4 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3) (s in4))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs)
    (hpre4 : ∀ n ∈ g.nodes.drop k, in4 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2)
        (denoteGraphDistributedFaithful g init in3)
        (denoteGraphDistributedFaithful g init in4) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpreNil hpre2,
    denoteGraphDistributedFaithful_prefix_read g init k in3 hpreNil hpre3,
    denoteGraphDistributedFaithful_prefix_read g init k in4 hpreNil hpre4]

private theorem cL22A_reduce6
    (g : GraphDecl) (init : Store) (k : Nat) (node : NodeDecl)
    (in0 in1 in2 in3 in4 in5 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3) (s in4) (s in5))
    (hafterNil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hafterWrite : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpreNil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs)
    (hpre4 : ∀ n ∈ g.nodes.drop k, in4 ∉ n.outs)
    (hpre5 : ∀ n ∈ g.nodes.drop k, in5 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0)
        (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2)
        (denoteGraphDistributedFaithful g init in3)
        (denoteGraphDistributedFaithful g init in4)
        (denoteGraphDistributedFaithful g init in5) := by
  rw [denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode
      hafterNil hafterWrite,
    happly,
    denoteGraphDistributedFaithful_prefix_read g init k in0 hpreNil hpre0,
    denoteGraphDistributedFaithful_prefix_read g init k in1 hpreNil hpre1,
    denoteGraphDistributedFaithful_prefix_read g init k in2 hpreNil hpre2,
    denoteGraphDistributedFaithful_prefix_read g init k in3 hpreNil hpre3,
    denoteGraphDistributedFaithful_prefix_read g init k in4 hpreNil hpre4,
    denoteGraphDistributedFaithful_prefix_read g init k in5 hpreNil hpre5]

private def cL22ASmQ : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear",
    ins := [6199, 6200], outs := [6201] }
private def cL22APmGatherQ : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [11452, 11453],
    outs := [6199], params := [0] }
private def cL22APmQ1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_per_head_mix_precision_linear",
    ins := [6199, 6200], outs := [6201] }
private def cL22APmQChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [6201], outs := [11454], params := [0] }
private def cL22APmQChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [6201], outs := [11455], params := [0] }

private def cL22ASmAttn : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [6201, 6202, 6203, 6204, 6205], outs := [6206, 6207],
    params := [16, 4, 64, 64, 1, 0] }
private def cL22APmAttn0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11454, 11466, 11472, 6204, 6205], outs := [11478, 6207],
    params := [16, 4, 64, 64, 1, 0] }
private def cL22APmAttn1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11455, 11467, 11473, 6204, 6205], outs := [11479, 6207],
    params := [16, 4, 64, 64, 1, 0] }

private theorem cL22A_q_nodes :
    sm_goal_1.nodes[889]'(by native_decide) = cL22ASmQ ∧
    pm_goal_1.nodes[1944]'(by native_decide) = cL22APmGatherQ ∧
    pm_goal_1.nodes[1946]'(by native_decide) = cL22APmQ1 ∧
    pm_goal_1.nodes[1947]'(by native_decide) = cL22APmQChunk0 ∧
    pm_goal_1.nodes[1948]'(by native_decide) = cL22APmQChunk1 := by native_decide

private theorem cL22A_sm_node :
    sm_goal_1.nodes[890]'(by native_decide) = cL22ASmAttn := by native_decide
private theorem cL22A_pm_node0 :
    pm_goal_1.nodes[1949]'(by native_decide) = cL22APmAttn0 := by native_decide
private theorem cL22A_pm_node1 :
    pm_goal_1.nodes[1950]'(by native_decide) = cL22APmAttn1 := by native_decide
private theorem cL22A_sm_buddies :
    sm_goal_1.replicaBuddies cL22ASmAttn = [cL22ASmAttn] := by native_decide
private theorem cL22A_pm_buddies0 :
    pm_goal_1.replicaBuddies cL22APmAttn0 = [cL22APmAttn0, cL22APmAttn1] := by
  native_decide
private theorem cL22A_pm_buddies1 :
    pm_goal_1.replicaBuddies cL22APmAttn1 = [cL22APmAttn0, cL22APmAttn1] := by
  native_decide

private theorem cL22A_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(891, 6206), (890, 6201), (890, 6202), (890, 6203),
      (890, 6204), (890, 6205)]) :
    ∀ n ∈ sm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem cL22A_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1950, 11478), (1951, 11479),
      (1949, 11454), (1949, 11455), (1949, 11466), (1949, 11467),
      (1949, 11472), (1949, 11473), (1949, 6204), (1949, 6205),
      (1950, 11454), (1950, 11455), (1950, 11466), (1950, 11467),
      (1950, 11472), (1950, 11473), (1950, 6204), (1950, 6205)]) :
    ∀ n ∈ pm_goal_1.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

/-- Exact canonical SM Q projection reduction. -/
theorem canonical_l22_q_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6201 =
      fw_per_head_linear
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6199)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6200) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 889 cL22ASmQ
    6199 6200 6201 fw_per_head_linear
    (by native_decide) cL22A_q_nodes.1 ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL22ASmQ
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out sm_goal_1 s 0 6199 6200 6201 []

/-- The canonical PM gathered Q input is the faithful dim-0 gather of both RMS shards. -/
theorem canonical_l22_q_pm_gather_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 6199 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11452,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11453] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1944 cL22APmGatherQ
    11452 11453 6199 (fun x0 x1 => allGatherPrimDimN 0 2 0 [x0, x1])
    (by native_decide) cL22A_q_nodes.2.1 ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL22APmGatherQ
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [11452, 11453] 6199 0

/-- The shared canonical PM Q projection reduces after the true gather node. -/
theorem canonical_l22_q_pm_full_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 6201 =
      fw_per_head_linear
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6199)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6200) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1946 cL22APmQ1
    6199 6200 6201 fw_per_head_linear
    (by native_decide) cL22A_q_nodes.2.2.1 ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL22APmQ1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_per_head_mix_precision_linear_out pm_goal_1 s 1 6199 6200 6201 []

/-- The two canonical PM Q shards are real dim-0 chunks of the shared projection. -/
theorem canonical_l22_q_pm_chunks_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11454 =
        chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 6201) ∧
      denoteGraphDistributedFaithful pm_goal_1 initPM 11455 =
        chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 6201) := by
  constructor
  · refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1947 cL22APmQChunk0
      6201 11454 (fun x => chunkPrimDimN 0 2 0 x)
      (by native_decide) cL22A_q_nodes.2.2.2.1 ?_
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
    intro s
    unfold cL22APmQChunk0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 6201 11454 0
  · refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1948 cL22APmQChunk1
      6201 11455 (fun x => chunkPrimDimN 0 2 1 x)
      (by native_decide) cL22A_q_nodes.2.2.2.2 ?_
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
    intro s
    unfold cL22APmQChunk1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 6201 11455 0

/-- The exact canonical SM L22 attention output reduces to faithful varlen attention. -/
theorem canonical_l22_attention_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6206 =
      fw_attn_varlen
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6201)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6202)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6203)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6204)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6205)
        16 4 64 64 true 0 := by
  refine cL22A_reduce5 sm_goal_1 initSM 890 cL22ASmAttn
    6201 6202 6203 6204 6205 6206
    (fun q k v cq ck => fw_attn_varlen q k v cq ck 16 4 64 64 true 0)
    (by native_decide) cL22A_sm_node ?_ (by native_decide)
    (cL22A_sm_not_written 891 6206 (by decide))
    (by native_decide)
    (cL22A_sm_not_written 890 6201 (by decide))
    (cL22A_sm_not_written 890 6202 (by decide))
    (cL22A_sm_not_written 890 6203 (by decide))
    (cL22A_sm_not_written 890 6204 (by decide))
    (cL22A_sm_not_written 890 6205 (by decide))
  intro s
  have hb := cL22A_sm_buddies
  unfold cL22ASmAttn at hb
  unfold cL22ASmAttn
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs
  simp [storeSet]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- The exact canonical rank-0 PM L22 attention output uses both Q shards and local K/V. -/
theorem canonical_l22_attention_pm0_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11478 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11454,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11455]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11466)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11472)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6204)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6205)
        16 4 64 64 true 0 2 0 := by
  refine cL22A_reduce6 pm_goal_1 initPM 1949 cL22APmAttn0
    11454 11455 11466 11472 6204 6205 11478
    (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
      [q0, q1] k v cq ck 16 4 64 64 true 0 2 0)
    (by native_decide) cL22A_pm_node0 ?_ (by native_decide)
    (cL22A_pm_not_written 1950 11478 (by decide))
    (by native_decide)
    (cL22A_pm_not_written 1949 11454 (by decide))
    (cL22A_pm_not_written 1949 11455 (by decide))
    (cL22A_pm_not_written 1949 11466 (by decide))
    (cL22A_pm_not_written 1949 11472 (by decide))
    (cL22A_pm_not_written 1949 6204 (by decide))
    (cL22A_pm_not_written 1949 6205 (by decide))
  intro s
  have hb := cL22A_pm_buddies0
  unfold cL22APmAttn0 cL22APmAttn1 at hb
  unfold cL22APmAttn0
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs
  simp [storeSet]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

/-- The exact canonical rank-1 PM L22 attention output uses both Q shards and local K/V. -/
theorem canonical_l22_attention_pm1_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11479 =
      fw_attn_zigzag_collective
        [denoteGraphDistributedFaithful pm_goal_1 initPM 11454,
         denoteGraphDistributedFaithful pm_goal_1 initPM 11455]
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11467)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 11473)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6204)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6205)
        16 4 64 64 true 0 2 1 := by
  refine cL22A_reduce6 pm_goal_1 initPM 1950 cL22APmAttn1
    11454 11455 11467 11473 6204 6205 11479
    (fun q0 q1 k v cq ck => fw_attn_zigzag_collective
      [q0, q1] k v cq ck 16 4 64 64 true 0 2 1)
    (by native_decide) cL22A_pm_node1 ?_ (by native_decide)
    (cL22A_pm_not_written 1951 11479 (by decide))
    (by native_decide)
    (cL22A_pm_not_written 1950 11454 (by decide))
    (cL22A_pm_not_written 1950 11455 (by decide))
    (cL22A_pm_not_written 1950 11467 (by decide))
    (cL22A_pm_not_written 1950 11473 (by decide))
    (cL22A_pm_not_written 1950 6204 (by decide))
    (cL22A_pm_not_written 1950 6205 (by decide))
  intro s
  have hb := cL22A_pm_buddies1
  unfold cL22APmAttn0 cL22APmAttn1 at hb
  unfold cL22APmAttn1
  unfold applyNodeDistributedFaithful
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  unfold storeCollectiveOutputs
  simp [storeSet]
  unfold applyNodeFaithfulZigzagAttnValue
  rw [hb]
  rfl

private theorem cL22A_storeSet_zip_replicate (s : Store) (v : Tensor) :
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

private def cL22A_multirefNode (rank n : Nat) (xTid : Tid)
    (outTids : List Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
    outs := outTids, params := [n] }

private theorem cL22A_applyNode_multiref_out (g : GraphDecl) (s : Store)
    (rank n : Nat) (xTid : Tid) (outs : List Tid) (t : Tid)
    (hmem : t ∈ outs) (hlen : outs.length ≤ n) :
    applyNode g s (cL22A_multirefNode rank n xTid outs) t = s xTid := by
  unfold cL22A_multirefNode
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  exact cL22A_storeSet_zip_replicate s (s xTid) outs n t hmem hlen

private theorem cL22A_reduce_multiref (g : GraphDecl) (init : Store)
    (idx rank n : Nat) (xTid t : Tid) (outs : List Tid)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL22A_multirefNode rank n xTid outs)
    (hmem : t ∈ outs) (hlen : outs.length ≤ n)
    (hafterNil : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (hafterWrite : ∀ nd ∈ g.nodes.drop (idx + 1), t ∉ nd.outs)
    (hpreNil : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hpre : ∀ nd ∈ g.nodes.drop idx, xTid ∉ nd.outs) :
    denoteGraphDistributedFaithful g init t =
      denoteGraphDistributedFaithful g init xTid := by
  refine denoteGraphDistributedFaithful_reduce1 g init idx
    (cL22A_multirefNode rank n xTid outs) xTid t (fun x => x)
    hidx hnode ?_ hafterNil hafterWrite hpreNil hpre
  intro s
  unfold cL22A_multirefNode
  have hs : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_multiref" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_multiref" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact cL22A_applyNode_multiref_out g s rank n xTid outs t hmem hlen

private def cL22A_toNode (rank : Nat) (xTid outTid : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_to", ins := [xTid], outs := [outTid] }

private theorem cL22A_reduce_to (g : GraphDecl) (init : Store)
    (idx rank : Nat) (xTid outTid : Tid)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL22A_toNode rank xTid outTid)
    (hafterNil : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (hafterWrite : ∀ nd ∈ g.nodes.drop (idx + 1), outTid ∉ nd.outs)
    (hpreNil : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hpre : ∀ nd ∈ g.nodes.drop idx, xTid ∉ nd.outs) :
    denoteGraphDistributedFaithful g init outTid =
      denoteGraphDistributedFaithful g init xTid := by
  refine denoteGraphDistributedFaithful_reduce1 g init idx
    (cL22A_toNode rank xTid outTid) xTid outTid (fun x => x)
    hidx hnode ?_ hafterNil hafterWrite hpreNil hpre
  intro s
  unfold cL22A_toNode
  have hs : ("OpName.FW_to" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_to" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_to" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact applyNode_fw_to_out g s rank xTid outTid []

private def cL22A_rmsNode (rank : Nat) (xTid wTid outTid : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_rms_norm", ins := [xTid, wTid], outs := [outTid] }

private theorem cL22A_reduce_rms (g : GraphDecl) (init : Store)
    (idx rank : Nat) (xTid wTid outTid : Tid)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL22A_rmsNode rank xTid wTid outTid)
    (hafterNil : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (hafterWrite : ∀ nd ∈ g.nodes.drop (idx + 1), outTid ∉ nd.outs)
    (hpreNil : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hpre0 : ∀ nd ∈ g.nodes.drop idx, xTid ∉ nd.outs)
    (hpre1 : ∀ nd ∈ g.nodes.drop idx, wTid ∉ nd.outs) :
    denoteGraphDistributedFaithful g init outTid =
      fw_rms_norm (denoteGraphDistributedFaithful g init xTid)
        (denoteGraphDistributedFaithful g init wTid) := by
  refine denoteGraphDistributedFaithful_reduce2 g init idx
    (cL22A_rmsNode rank xTid wTid outTid) xTid wTid outTid fw_rms_norm
    hidx hnode ?_ hafterNil hafterWrite hpreNil hpre0 hpre1
  intro s
  unfold cL22A_rmsNode
  have hs : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_rms_norm" : String) ≠ "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact applyNode_fw_rms_norm_out g s rank xTid wTid outTid []

private def cL22A_projNode (rank : Nat) (xTid wTid outTid : Tid) : NodeDecl :=
  { rank := rank, op := "OpName.FW_per_head_mix_precision_linear",
    ins := [xTid, wTid], outs := [outTid] }

private theorem cL22A_reduce_proj (g : GraphDecl) (init : Store)
    (idx rank : Nat) (xTid wTid outTid : Tid)
    (hidx : idx < g.nodes.length)
    (hnode : g.nodes[idx]'hidx = cL22A_projNode rank xTid wTid outTid)
    (hafterNil : ∀ nd ∈ g.nodes.drop (idx + 1), nd.outs ≠ [])
    (hafterWrite : ∀ nd ∈ g.nodes.drop (idx + 1), outTid ∉ nd.outs)
    (hpreNil : ∀ nd ∈ g.nodes.drop idx, nd.outs ≠ [])
    (hpre0 : ∀ nd ∈ g.nodes.drop idx, xTid ∉ nd.outs)
    (hpre1 : ∀ nd ∈ g.nodes.drop idx, wTid ∉ nd.outs) :
    denoteGraphDistributedFaithful g init outTid =
      fw_per_head_linear (denoteGraphDistributedFaithful g init xTid)
        (denoteGraphDistributedFaithful g init wTid) := by
  refine denoteGraphDistributedFaithful_reduce2 g init idx
    (cL22A_projNode rank xTid wTid outTid) xTid wTid outTid fw_per_head_linear
    hidx hnode ?_ hafterNil hafterWrite hpreNil hpre0 hpre1
  intro s
  unfold cL22A_projNode
  have hs : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_shuffle" := by decide
  have hu : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_maybe_unshuffle" := by decide
  have ha : ("OpName.FW_per_head_mix_precision_linear" : String) ≠
      "OpName.FW_attn_zigzag" := by decide
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    hs hu ha]
  exact applyNode_fw_per_head_mix_precision_linear_out g s rank xTid wTid outTid []

private def cL22ASmKBaseRms : NodeDecl :=
  { rank := 0, op := "OpName.FW_rms_norm", ins := [8368, 5596], outs := [5597] }
private def cL22ASmKProj : NodeDecl :=
  { rank := 0, op := "OpName.FW_per_head_mix_precision_linear",
    ins := [8376, 5598], outs := [5599] }
private def cL22ASmKCast : NodeDecl :=
  { rank := 0, op := "OpName.FW_to", ins := [8438], outs := [6202] }

/-- The canonical SM K cache follows the real multiref/RMSNorm/projection/fanout/cast chain. -/
theorem canonical_l22_k_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6202 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
          (denoteGraphDistributedFaithful sm_goal_1 initSM 5596))
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5598) := by
  have hbase : denoteGraphDistributedFaithful sm_goal_1 initSM 8368 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5595 := by
    exact cL22A_reduce_multiref sm_goal_1 initSM 470 0 2 5595 8368 [8368, 8372]
      (by native_decide) (by native_decide) (by decide) (by decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hrms : denoteGraphDistributedFaithful sm_goal_1 initSM 5597 =
      fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 8368)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5596) := by
    refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 471 cL22ASmKBaseRms
      8368 5596 5597 fw_rms_norm (by native_decide) (by native_decide) ?_
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
    intro s
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_rms_norm_out sm_goal_1 s 0 8368 5596 5597 []
  have hsplit : denoteGraphDistributedFaithful sm_goal_1 initSM 8376 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5597 := by
    exact cL22A_reduce_multiref sm_goal_1 initSM 473 0 2 5597 8376 [8376, 8380]
      (by native_decide) (by native_decide) (by decide) (by decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hproj : denoteGraphDistributedFaithful sm_goal_1 initSM 5599 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 8376)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5598) := by
    refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 475 cL22ASmKProj
      8376 5598 5599 fw_per_head_linear (by native_decide) (by native_decide) ?_
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
    intro s
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_per_head_mix_precision_linear_out sm_goal_1 s 0 8376 5598 5599 []
  have hfan : denoteGraphDistributedFaithful sm_goal_1 initSM 8438 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5599 := by
    exact cL22A_reduce_multiref sm_goal_1 initSM 478 0 12 5599 8438
      [8394, 8398, 8402, 8406, 8410, 8414, 8418, 8422, 8426, 8430, 8434, 8438]
      (by native_decide) (by native_decide) (by decide) (by decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hcast : denoteGraphDistributedFaithful sm_goal_1 initSM 6202 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8438 := by
    refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 492 cL22ASmKCast
      8438 6202 (fun x => x) (by native_decide) (by native_decide) ?_
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    intro s
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_to_out sm_goal_1 s 0 8438 6202 []
  rw [hcast, hfan, hproj, hsplit, hrms, hbase]

/-- The canonical SM V cache follows the real multiref/RMSNorm/projection/fanout/cast chain. -/
theorem canonical_l22_v_sm_reduce (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6203 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
          (denoteGraphDistributedFaithful sm_goal_1 initSM 5596))
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5600) := by
  have hbase := cL22A_reduce_multiref sm_goal_1 initSM 470 0 2 5595 8368 [8368, 8372]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hrms := cL22A_reduce_rms sm_goal_1 initSM 471 0 8368 5596 5597
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hsplit := cL22A_reduce_multiref sm_goal_1 initSM 473 0 2 5597 8380 [8376, 8380]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hproj := cL22A_reduce_proj sm_goal_1 initSM 476 0 8380 5600 5601
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hfan := cL22A_reduce_multiref sm_goal_1 initSM 479 0 12 5601 8496
    [8452, 8456, 8460, 8464, 8468, 8472, 8476, 8480, 8484, 8488, 8492, 8496]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hcast := cL22A_reduce_to sm_goal_1 initSM 504 0 8496 6203
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hcast, hfan, hproj, hsplit, hrms, hbase]

/-- Exact canonical PM K/V chains on both ranks.  These are genuine local shards,
not replicated aliases: each branch starts from its own rank's canonical cache input. -/
theorem canonical_l22_kv_pm_reduce (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11466 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5598) ∧
    denoteGraphDistributedFaithful pm_goal_1 initPM 11467 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5598) ∧
    denoteGraphDistributedFaithful pm_goal_1 initPM 11472 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5600) ∧
    denoteGraphDistributedFaithful pm_goal_1 initPM 11473 =
      fw_per_head_linear
        (fw_rms_norm (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 5596))
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5600) := by
  have hb0 := cL22A_reduce_multiref pm_goal_1 initPM 1040 0 2 9722 15822 [15822, 15826]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hb1 := cL22A_reduce_multiref pm_goal_1 initPM 1041 1 2 9723 15830 [15830, 15834]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hr0 := cL22A_reduce_rms pm_goal_1 initPM 1042 0 15822 5596 9726
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hr1 := cL22A_reduce_rms pm_goal_1 initPM 1044 1 15830 5596 9727
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hsK0 := cL22A_reduce_multiref pm_goal_1 initPM 1046 0 2 9726 15838 [15838, 15842]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hsV0 := cL22A_reduce_multiref pm_goal_1 initPM 1046 0 2 9726 15842 [15838, 15842]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hsK1 := cL22A_reduce_multiref pm_goal_1 initPM 1048 1 2 9727 15846 [15846, 15850]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hsV1 := cL22A_reduce_multiref pm_goal_1 initPM 1048 1 2 9727 15850 [15846, 15850]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hpK0 := cL22A_reduce_proj pm_goal_1 initPM 1050 0 15838 5598 9728
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpV0 := cL22A_reduce_proj pm_goal_1 initPM 1051 0 15842 5600 9740
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpK1 := cL22A_reduce_proj pm_goal_1 initPM 1053 1 15846 5598 9729
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpV1 := cL22A_reduce_proj pm_goal_1 initPM 1054 1 15850 5600 9741
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hfK0 := cL22A_reduce_multiref pm_goal_1 initPM 1056 0 12 9728 15908
    [15864, 15868, 15872, 15876, 15880, 15884, 15888, 15892, 15896, 15900, 15904, 15908]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hfV0 := cL22A_reduce_multiref pm_goal_1 initPM 1057 0 12 9740 16024
    [15980, 15984, 15988, 15992, 15996, 16000, 16004, 16008, 16012, 16016, 16020, 16024]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hfK1 := cL22A_reduce_multiref pm_goal_1 initPM 1058 1 12 9729 15966
    [15922, 15926, 15930, 15934, 15938, 15942, 15946, 15950, 15954, 15958, 15962, 15966]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hfV1 := cL22A_reduce_multiref pm_goal_1 initPM 1059 1 12 9741 16082
    [16038, 16042, 16046, 16050, 16054, 16058, 16062, 16066, 16070, 16074, 16078, 16082]
    (by native_decide) (by native_decide) (by decide) (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hcK0 := cL22A_reduce_to pm_goal_1 initPM 1072 0 15908 11466
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have hcV0 := cL22A_reduce_to pm_goal_1 initPM 1084 0 16024 11472
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have hcK1 := cL22A_reduce_to pm_goal_1 initPM 1096 1 15966 11467
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have hcV1 := cL22A_reduce_to pm_goal_1 initPM 1108 1 16082 11473
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcK0, hfK0, hpK0, hsK0, hr0, hb0]
  · rw [hcK1, hfK1, hpK1, hsK1, hr1, hb1]
  · rw [hcV0, hfV0, hpV0, hsV0, hr0, hb0]
  · rw [hcV1, hfV1, hpV1, hsV1, hr1, hb1]

end
end TrainVerify.Denote.GeneratedPatterns
