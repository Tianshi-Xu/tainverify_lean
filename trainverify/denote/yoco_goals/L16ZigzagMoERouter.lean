/- Canonical Goal 1, layer 16: faithful router probabilities and map. -/
import denote.yoco_goals.L16ZigzagMoENormRouter
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

private theorem l16ZMr_chunk_gather0 (x0 x1 : Tensor)
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

private theorem l16ZMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l16ZMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5946],
    outs := [8753, 8757, 8761, 8765, 8769], params := [5] }
private def l16ZMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10742],
    outs := [15412, 14628, 14638, 14652, 14664], params := [5] }
private def l16ZMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10743],
    outs := [15414, 14629, 14639, 14653, 14665], params := [5] }
private def l16ZMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8753], outs := [5947] }
private def l16ZMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15412, 15414],
    outs := [12234], params := [0] }
private def l16ZMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [12234], outs := [5947] }
private def l16ZMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5947, 5948], outs := [5949] }
private def l16ZMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5947, 5948], outs := [5949] }
private def l16ZMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5949], outs := [10750], params := [0] }
private def l16ZMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5949], outs := [10751], params := [0] }
private def l16ZMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5949],
    outs := [5950, 5951, 5952], params := [8, 1] }
private def l16ZMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [10750],
    outs := [10752, 10754, 10756], params := [8, 1] }
private def l16ZMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [10751],
    outs := [10753, 10755, 10757], params := [8, 1] }

private theorem l16ZMr_red_sm8753 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8753 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5946 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 724 l16ZMrSmRef
    5946 8753 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5946
    [8753, 8757, 8761, 8765, 8769] 5 rfl 8753 (by decide)

private theorem l16ZMr_red_pm15412 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15412 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10742 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1587 l16ZMrPmRef0
    10742 15412 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10742
    [15412, 14628, 14638, 14652, 14664] 5 rfl 15412 (by decide)

private theorem l16ZMr_red_pm15414 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15414 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10743 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1588 l16ZMrPmRef1
    10743 15414 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10743
    [15414, 14629, 14639, 14653, 14665] 5 rfl 15414 (by decide)

private theorem l16ZMr_red_sm5947 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5947 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8753 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 725 l16ZMrSmFloat
    8753 5947 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8753 5947 []

private theorem l16ZMr_red_pm12234 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12234 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15412,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15414] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1592 l16ZMrPmGather
    15412 15414 12234 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15412, 15414] 12234 0]
  rfl

private theorem l16ZMr_red_pm5947 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5947 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 12234 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1600 l16ZMrPmFloat1
    12234 5947 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 12234 5947 []

private theorem l16ZMr_red_sm5949 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5949 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5947)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5948) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 729 l16ZMrSmNormLinear
    5947 5948 5949 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5947 5948 5949 []

private theorem l16ZMr_red_pm5949 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5949 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5947)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5948) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1608 l16ZMrPmNormLinear1
    5947 5948 5949 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5947 5948 5949 []

private theorem l16ZMr_red_pm10750 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10750 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5949) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1614 l16ZMrPmChunk0
    5949 10750 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5949 10750 0

private theorem l16ZMr_red_pm10751 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10751 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5949) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1615 l16ZMrPmChunk1
    5949 10751 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l16ZMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5949 10751 0

private def l16ZMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l16ZMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l16ZMrTopkNode rnk logits probs mapTid scores)
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
      unfold l16ZMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l16ZMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l16ZMrTopkNode rnk logits probs mapTid scores)
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
      unfold l16ZMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l16ZMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5948 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5948 ∉ n.outs) := by
  native_decide

private theorem l16ZMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5948 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5948 := by
  have hi := (hInit initGoal_5948 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5948 pm_goal_1.numRanks _ rfl,
    show initGoal_5948.tps = [{rank := 0, tid := 5948}] from rfl,
    show initGoal_5948.ts = 5948 from rfl,
    show initGoal_5948.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5948 (by native_decide) l16ZMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5948 (by native_decide) l16ZMr_weight_not_written.2]
  exact hi

private theorem l16ZMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5948).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5948 (by native_decide) l16ZMr_weight_not_written.2]
  exact hPM 5948 [64, 1024] (by native_decide)

private theorem l16ZMr_hdec (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
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

/-- The canonical L16 routing probabilities and routing map are computed from the
shared normalized input by the real norm-linear, chunk, and top-k graph nodes. -/
theorem l16_zigzag_moe_router_all_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5950)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10752)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10753)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5951)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10754)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10755)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5949)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10750)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10751)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hdec := l16ZMr_hdec initPM hPM hNorm
  obtain ⟨source0, source1, hs⟩ := hNorm
  have hNorm' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  have hwEq := l16ZMr_weight_eq initSM initPM hInit
  have hwShape := l16ZMr_weight_shape initPM hPM
  have hwShapeSM :
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5948).shape = [64, 1024] := by
    rw [hwEq]
    exact hwShape
  have hlogits0 : Zigzag2Rel
      (fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5948))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5948))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5948))
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [← hwEq]
    exact Zigzag2Rel.norm_linear 2048 1024 64 hNorm' hwShapeSM
      (by decide) (by decide) (by decide) (by decide) hdec
  have hp0Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5948)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank0_shape hwShape
  have hp1Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5948)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank1_shape hwShape
  have hlogits : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5949)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10750)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10751)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [l16ZMr_red_sm5949 initSM, l16ZMr_red_sm5947 initSM,
      l16ZMr_red_sm8753 initSM, hwEq,
      l16ZMr_red_pm10750 initPM, l16ZMr_red_pm10751 initPM,
      l16ZMr_red_pm5949 initPM, l16ZMr_red_pm5947 initPM,
      l16ZMr_red_pm12234 initPM, l16ZMr_red_pm15412 initPM,
      l16ZMr_red_pm15414 initPM,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by decide) (by decide) (by decide) hs.rank0_shape hs.rank1_shape hwShape,
      l16ZMr_chunk_gather0 _ _ hp0Shape hp1Shape,
      l16ZMr_chunk_gather1 _ _ hp0Shape hp1Shape]
    exact hlogits0
  have hprobs := Zigzag2Rel.topk_routing_probs 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  have hmap := Zigzag2Rel.topk_routing_map 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  have hlogitsKeep := hlogits
  obtain ⟨logitSource0, logitSource1, hls⟩ := hlogits
  rw [l16ZMr_red_topk_probs sm_goal_1 initSM 733 l16ZMrSmTopk 0 5949 5950 5951 5952
      (by native_decide) (by native_decide) rfl (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l16ZMr_red_topk_probs pm_goal_1 initPM 1619 l16ZMrPmTopk0 0 10750 10752 10754 10756
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l16ZMr_red_topk_probs pm_goal_1 initPM 1620 l16ZMrPmTopk1 1 10751 10753 10755 10757
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l16ZMr_red_topk_map sm_goal_1 initSM 733 l16ZMrSmTopk 0 5949 5950 5951 5952
      (by native_decide) (by native_decide) rfl (by decide) (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l16ZMr_red_topk_map pm_goal_1 initPM 1619 l16ZMrPmTopk0 0 10750 10752 10754 10756
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l16ZMr_red_topk_map pm_goal_1 initPM 1620 l16ZMrPmTopk1 1 10751 10753 10755 10757
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact ⟨hprobs, hmap, hlogitsKeep⟩

/-- Public router pair retained for downstream expert composition. -/
theorem l16_zigzag_moe_router_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10742)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10743)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5950)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10752)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10753)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5951)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10754)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10755)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have h := l16_zigzag_moe_router_all_from_norm_input
    initSM initPM hPM hInit hNorm
  exact ⟨h.1, h.2.1⟩

/-- The canonical L16 routing outputs are closed directly from the exact L16 attention residual
output relation.  The normalized input, router weight agreement and shape,
packed-CU decode, logits, gather/chunk transport, and both top-k projections
are all derived internally. -/
theorem l16_zigzag_moe_router_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5944)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10738)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10739)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5950)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10752)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10753)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5951)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10754)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10755)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hNorm := l16_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l16_zigzag_moe_router_from_norm_input initSM initPM hPM hInit hNorm

#print axioms l16_zigzag_moe_router_from_norm_input
#print axioms l16_zigzag_moe_router_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
