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

end
end TrainVerify.Denote.GeneratedPatterns
