/- Canonical Goal 1, layer 12: faithful router probabilities and map. -/
import denote.yoco_goals.L12ZigzagMoENormRouter
import denote.yoco_goals.ZigzagRouterRel
import denote.DenoteMoE
import denote.ChunkGatherDim0

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

private theorem l12ZMr_chunk_gather0 (x0 x1 : Tensor)
    (hx0 : x0.shape = [2048, 64]) (hx1 : x1.shape = [2048, 64]) :
    chunkPrimDimN 0 2 0 (allGatherPrimDimN 0 2 0 [x0, x1]) = x0 := by
  have hhead : (([x0, x1] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [2048, 64] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hx0]
  have hget : ∀ r (_ : r < 2),
      ([x0, x1].getD r (zeroTensor [2048, 64])).shape = [2048, 64] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hx0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hx1
  have hg : (allGatherPrimDimN 0 2 0 [x0, x1]).shape = [4096, 64] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 64] hhead]
    rfl
  have hc : (chunkPrimDimN 0 2 0 (allGatherPrimDimN 0 2 0 [x0, x1])).shape =
      [2048, 64] := by
    rw [chunkPrimDimN_shape 0 2 0 _ _ hg (by decide)]
    rfl
  apply Tensor.ext (by rw [hc, hx0])
  intro idx hidx
  rw [hc, prodShape_2d'] at hidx
  let i := idx / 64
  let j := idx % 64
  have hj : j < 64 := Nat.mod_lt _ (by decide)
  have hi : i < 2048 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hidx
  have hij : idx = i * 64 + j := (Nat.div_add_mod' idx 64).symm
  rw [hij]
  rw [chunkPrimDimN0_valAt 2 0 4096 64 _ hg (by decide) (by decide)
    (by decide) i hi j hj]
  rw [allGatherPrimDimN0_valAt 2 2048 64 [x0, x1] (by decide) (by decide)
    (by decide) hhead hget 0 (by decide) i hi j hj]
  simp only [List.getD_cons_zero]

private theorem l12ZMr_chunk_gather1 (x0 x1 : Tensor)
    (hx0 : x0.shape = [2048, 64]) (hx1 : x1.shape = [2048, 64]) :
    chunkPrimDimN 0 2 1 (allGatherPrimDimN 0 2 0 [x0, x1]) = x1 := by
  have hhead : (([x0, x1] : List Tensor).head?.map (fun t => t.shape)).getD [] =
      [2048, 64] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some, hx0]
  have hget : ∀ r (_ : r < 2),
      ([x0, x1].getD r (zeroTensor [2048, 64])).shape = [2048, 64] := by
    intro r hr
    interval_cases r
    · simpa only [List.getD_cons_zero] using hx0
    · simpa only [List.getD_cons_succ, List.getD_cons_zero] using hx1
  have hg : (allGatherPrimDimN 0 2 0 [x0, x1]).shape = [4096, 64] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 64] hhead]
    rfl
  have hc : (chunkPrimDimN 0 2 1 (allGatherPrimDimN 0 2 0 [x0, x1])).shape =
      [2048, 64] := by
    rw [chunkPrimDimN_shape 0 2 1 _ _ hg (by decide)]
    rfl
  apply Tensor.ext (by rw [hc, hx1])
  intro idx hidx
  rw [hc, prodShape_2d'] at hidx
  let i := idx / 64
  let j := idx % 64
  have hj : j < 64 := Nat.mod_lt _ (by decide)
  have hi : i < 2048 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hidx
  have hij : idx = i * 64 + j := (Nat.div_add_mod' idx 64).symm
  rw [hij]
  rw [chunkPrimDimN0_valAt 2 1 4096 64 _ hg (by decide) (by decide)
    (by decide) i hi j hj]
  rw [allGatherPrimDimN0_valAt 2 2048 64 [x0, x1] (by decide) (by decide)
    (by decide) hhead hget 1 (by decide) i hi j hj]
  simp only [List.getD_cons_succ, List.getD_cons_zero]

private def l12ZMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5622],
    outs := [8519, 8523, 8527, 8531, 8535], params := [5] }
private def l12ZMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9818],
    outs := [15388, 13932, 13942, 13956, 13968], params := [5] }
private def l12ZMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9819],
    outs := [15390, 13933, 13943, 13957, 13969], params := [5] }
private def l12ZMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8519], outs := [5623] }
private def l12ZMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15388, 15390],
    outs := [12114], params := [0] }
private def l12ZMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [12114], outs := [5623] }
private def l12ZMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5623, 5624], outs := [5625] }
private def l12ZMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5623, 5624], outs := [5625] }
private def l12ZMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5625], outs := [9826], params := [0] }
private def l12ZMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5625], outs := [9827], params := [0] }
private def l12ZMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5625],
    outs := [5626, 5627, 5628], params := [8, 1] }
private def l12ZMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9826],
    outs := [9828, 9830, 9832], params := [8, 1] }
private def l12ZMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9827],
    outs := [9829, 9831, 9833], params := [8, 1] }

private theorem l12ZMr_red_sm8519 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8519 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5622 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 514 l12ZMrSmRef
    5622 8519 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5622
    [8519, 8523, 8527, 8531, 8535] 5 rfl 8519 (by decide)

private theorem l12ZMr_red_pm15388 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15388 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9818 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1131 l12ZMrPmRef0
    9818 15388 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9818
    [15388, 13932, 13942, 13956, 13968] 5 rfl 15388 (by decide)

private theorem l12ZMr_red_pm15390 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15390 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9819 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1132 l12ZMrPmRef1
    9819 15390 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9819
    [15390, 13933, 13943, 13957, 13969] 5 rfl 15390 (by decide)

private theorem l12ZMr_red_sm5623 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5623 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8519 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 515 l12ZMrSmFloat
    8519 5623 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8519 5623 []

private theorem l12ZMr_red_pm12114 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12114 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15388,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15390] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1136 l12ZMrPmGather
    15388 15390 12114 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15388, 15390] 12114 0]
  rfl

private theorem l12ZMr_red_pm5623 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5623 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 12114 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1144 l12ZMrPmFloat1
    12114 5623 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 12114 5623 []

private theorem l12ZMr_red_sm5625 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5625 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5623)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5624) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 519 l12ZMrSmNormLinear
    5623 5624 5625 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5623 5624 5625 []

private theorem l12ZMr_red_pm5625 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5625 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5623)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5624) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1152 l12ZMrPmNormLinear1
    5623 5624 5625 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5623 5624 5625 []

private theorem l12ZMr_red_pm9826 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9826 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5625) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1158 l12ZMrPmChunk0
    5625 9826 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5625 9826 0

private theorem l12ZMr_red_pm9827 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9827 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5625) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1159 l12ZMrPmChunk1
    5625 9827 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12ZMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5625 9827 0

private def l12ZMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l12ZMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l12ZMrTopkNode rnk logits probs mapTid scores)
    (hsh : (denoteGraphDistributedFaithful g init logits).shape = [2048, 64] ∨
      (denoteGraphDistributedFaithful g init logits).shape = [4096, 64])
    (ha : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (haw : ∀ n ∈ g.nodes.drop (k + 1), probs ∉ n.outs)
    (hp : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, logits ∉ n.outs) :
    denoteGraphDistributedFaithful g init probs =
      (fw_topk_routing (denoteGraphDistributedFaithful g init logits) 8 64).1 := by
  have hr := denoteGraphDistributedFaithful_reduce1 g init k node logits probs
    (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).1)
    hk hn (by
      intro s
      rw [hnode]
      unfold l12ZMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l12ZMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l12ZMrTopkNode rnk logits probs mapTid scores)
    (hne : probs ≠ mapTid)
    (hsh : (denoteGraphDistributedFaithful g init logits).shape = [2048, 64] ∨
      (denoteGraphDistributedFaithful g init logits).shape = [4096, 64])
    (ha : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (haw : ∀ n ∈ g.nodes.drop (k + 1), mapTid ∉ n.outs)
    (hp : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, logits ∉ n.outs) :
    denoteGraphDistributedFaithful g init mapTid =
      (fw_topk_routing (denoteGraphDistributedFaithful g init logits) 8 64).2.1 := by
  have hr := denoteGraphDistributedFaithful_reduce1 g init k node logits mapTid
    (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.1)
    hk hn (by
      intro s
      rw [hnode]
      unfold l12ZMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l12ZMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5624 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5624 ∉ n.outs) := by
  native_decide

private theorem l12ZMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5624 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5624 := by
  have hi := (hInit initGoal_5624 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5624 pm_goal_1.numRanks _ rfl,
    show initGoal_5624.tps = [{rank := 0, tid := 5624}] from rfl,
    show initGoal_5624.ts = 5624 from rfl,
    show initGoal_5624.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5624 (by native_decide) l12ZMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5624 (by native_decide) l12ZMr_weight_not_written.2]
  exact hi

private theorem l12ZMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5624).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5624 (by native_decide) l12ZMr_weight_not_written.2]
  exact hPM 5624 [64, 1024] (by native_decide)

private theorem l12ZMr_hdec (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) =
      [0, 2 * 2048] := by
  have hcu : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      6252 (by native_decide) (by native_decide)
  have hshape : (denoteGraphDistributedFaithful pm_goal_1 initPM 6252).shape = [2] := by
    rw [hcu]
    exact hPM 6252 [2] (by native_decide)
  have hlen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hshape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hNorm
  apply list_eq_pair_of_length_head_last _ (2 * 2048) hlen hs.cu_wf.cu_starts_zero
  have ht := hs.cu_wf.local_tokens
  simp only [List.getD_cons_zero] at ht
  rw [hs.source0_shape] at ht
  norm_num at ht
  norm_num
  exact ht.symm

/-- The canonical L21 routing probabilities and routing map are computed from the
shared normalized input by the real norm-linear, chunk, and top-k graph nodes. -/
theorem l12_zigzag_moe_router_all_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5626)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9829)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5627)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9830)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9831)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5625)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9826)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9827)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hdec := l12ZMr_hdec initPM hPM hNorm
  obtain ⟨source0, source1, hs⟩ := hNorm
  have hNorm' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  have hwEq := l12ZMr_weight_eq initSM initPM hInit
  have hwShape := l12ZMr_weight_shape initPM hPM
  have hwShapeSM :
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5624).shape = [64, 1024] := by
    rw [hwEq]
    exact hwShape
  have hlogits0 : Zigzag2Rel
      (fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5624))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5624))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5624))
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [← hwEq]
    exact Zigzag2Rel.norm_linear 2048 1024 64 hNorm' hwShapeSM
      (by decide) (by decide) (by decide) (by decide) hdec
  have hp0Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5624)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank0_shape hwShape
  have hp1Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5624)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank1_shape hwShape
  have hlogits : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5625)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9826)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9827)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [l12ZMr_red_sm5625 initSM, l12ZMr_red_sm5623 initSM,
      l12ZMr_red_sm8519 initSM, hwEq,
      l12ZMr_red_pm9826 initPM, l12ZMr_red_pm9827 initPM,
      l12ZMr_red_pm5625 initPM, l12ZMr_red_pm5623 initPM,
      l12ZMr_red_pm12114 initPM, l12ZMr_red_pm15388 initPM,
      l12ZMr_red_pm15390 initPM,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by decide) (by decide) (by decide) hs.rank0_shape hs.rank1_shape hwShape,
      l12ZMr_chunk_gather0 _ _ hp0Shape hp1Shape,
      l12ZMr_chunk_gather1 _ _ hp0Shape hp1Shape]
    exact hlogits0
  have hprobs := Zigzag2Rel.topk_routing_probs 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  have hmap := Zigzag2Rel.topk_routing_map 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  have hlogitsKeep := hlogits
  obtain ⟨logitSource0, logitSource1, hls⟩ := hlogits
  rw [l12ZMr_red_topk_probs sm_goal_1 initSM 523 l12ZMrSmTopk 0 5625 5626 5627 5628
      (by native_decide) (by native_decide) rfl (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l12ZMr_red_topk_probs pm_goal_1 initPM 1163 l12ZMrPmTopk0 0 9826 9828 9830 9832
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l12ZMr_red_topk_probs pm_goal_1 initPM 1164 l12ZMrPmTopk1 1 9827 9829 9831 9833
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l12ZMr_red_topk_map sm_goal_1 initSM 523 l12ZMrSmTopk 0 5625 5626 5627 5628
      (by native_decide) (by native_decide) rfl (by decide) (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l12ZMr_red_topk_map pm_goal_1 initPM 1163 l12ZMrPmTopk0 0 9826 9828 9830 9832
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l12ZMr_red_topk_map pm_goal_1 initPM 1164 l12ZMrPmTopk1 1 9827 9829 9831 9833
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact ⟨hprobs, hmap, hlogitsKeep⟩

/-- Public router pair retained for downstream expert composition. -/
theorem l12_zigzag_moe_router_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5622)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9818)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9819)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5626)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9829)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5627)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9830)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9831)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have h := l12_zigzag_moe_router_all_from_norm_input
    initSM initPM hPM hInit hNorm
  exact ⟨h.1, h.2.1⟩

/-- The canonical L21 routing outputs are closed directly from the exact L20
output relation.  The normalized input, router weight agreement and shape,
packed-CU decode, logits, gather/chunk transport, and both top-k projections
are all derived internally. -/
theorem l12_zigzag_moe_router_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5626)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9828)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9829)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5627)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9830)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9831)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hNorm := l12_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l12_zigzag_moe_router_from_norm_input initSM initPM hPM hInit hNorm

#print axioms l12_zigzag_moe_router_from_norm_input
#print axioms l12_zigzag_moe_router_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns

