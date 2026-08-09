/- Canonical Goal 1, layer 12: faithful router probabilities and map. -/
import denote.yoco_goals.L12Block2ZigzagMoENormRouter
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

private theorem l12B2ZMr_chunk_gather0 (x0 x1 : Tensor)
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

private theorem l12B2ZMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l12B2ZMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5676],
    outs := [8558, 8562, 8566, 8570, 8574], params := [5] }
private def l12B2ZMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9972],
    outs := [15392, 14048, 14058, 14072, 14084], params := [5] }
private def l12B2ZMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9973],
    outs := [15394, 14049, 14059, 14073, 14085], params := [5] }
private def l12B2ZMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8558], outs := [5677] }
private def l12B2ZMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15392, 15394],
    outs := [12134], params := [0] }
private def l12B2ZMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [12134], outs := [5677] }
private def l12B2ZMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5677, 5678], outs := [5679] }
private def l12B2ZMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [5677, 5678], outs := [5679] }
private def l12B2ZMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [5679], outs := [9980], params := [0] }
private def l12B2ZMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [5679], outs := [9981], params := [0] }
private def l12B2ZMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [5679],
    outs := [5680, 5681, 5682], params := [8, 1] }
private def l12B2ZMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [9980],
    outs := [9982, 9984, 9986], params := [8, 1] }
private def l12B2ZMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [9981],
    outs := [9983, 9985, 9987], params := [8, 1] }

private theorem l12B2ZMr_red_sm8558 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8558 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5676 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 549 l12B2ZMrSmRef
    5676 8558 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 5676
    [8558, 8562, 8566, 8570, 8574] 5 rfl 8558 (by decide)

private theorem l12B2ZMr_red_pm15392 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15392 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9972 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1207 l12B2ZMrPmRef0
    9972 15392 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 9972
    [15392, 14048, 14058, 14072, 14084] 5 rfl 15392 (by decide)

private theorem l12B2ZMr_red_pm15394 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15394 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9973 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1208 l12B2ZMrPmRef1
    9973 15394 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 9973
    [15394, 14049, 14059, 14073, 14085] 5 rfl 15394 (by decide)

private theorem l12B2ZMr_red_sm5677 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5677 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8558 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 550 l12B2ZMrSmFloat
    8558 5677 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8558 5677 []

private theorem l12B2ZMr_red_pm12134 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12134 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15392,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15394] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1212 l12B2ZMrPmGather
    15392 15394 12134 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15392, 15394] 12134 0]
  rfl

private theorem l12B2ZMr_red_pm5677 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5677 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 12134 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1220 l12B2ZMrPmFloat1
    12134 5677 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 12134 5677 []

private theorem l12B2ZMr_red_sm5679 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5679 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5677)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 5678) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 554 l12B2ZMrSmNormLinear
    5677 5678 5679 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 5677 5678 5679 []

private theorem l12B2ZMr_red_pm5679 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 5679 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 5677)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5678) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1228 l12B2ZMrPmNormLinear1
    5677 5678 5679 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 5677 5678 5679 []

private theorem l12B2ZMr_red_pm9980 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9980 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 5679) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1234 l12B2ZMrPmChunk0
    5679 9980 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 5679 9980 0

private theorem l12B2ZMr_red_pm9981 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9981 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 5679) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1235 l12B2ZMrPmChunk1
    5679 9981 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l12B2ZMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 5679 9981 0

private def l12B2ZMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l12B2ZMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l12B2ZMrTopkNode rnk logits probs mapTid scores)
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
      unfold l12B2ZMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l12B2ZMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l12B2ZMrTopkNode rnk logits probs mapTid scores)
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
      unfold l12B2ZMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l12B2ZMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 5678 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 5678 ∉ n.outs) := by
  native_decide

private theorem l12B2ZMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5678 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 5678 := by
  have hi := (hInit initGoal_5678 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_5678 pm_goal_1.numRanks _ rfl,
    show initGoal_5678.tps = [{rank := 0, tid := 5678}] from rfl,
    show initGoal_5678.ts = 5678 from rfl,
    show initGoal_5678.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      5678 (by native_decide) l12B2ZMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5678 (by native_decide) l12B2ZMr_weight_not_written.2]
  exact hi

private theorem l12B2ZMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 5678).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      5678 (by native_decide) l12B2ZMr_weight_not_written.2]
  exact hPM 5678 [64, 1024] (by native_decide)

private theorem l12B2ZMr_hdec (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5676)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9972)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9973)
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
theorem l12b2_zigzag_moe_router_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5676)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9972)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5680)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9982)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5681)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9984)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9985)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hdec := l12B2ZMr_hdec initPM hPM hNorm
  obtain ⟨source0, source1, hs⟩ := hNorm
  have hNorm' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5676)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9972)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9973)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  have hwEq := l12B2ZMr_weight_eq initSM initPM hInit
  have hwShape := l12B2ZMr_weight_shape initPM hPM
  have hwShapeSM :
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5678).shape = [64, 1024] := by
    rw [hwEq]
    exact hwShape
  have hlogits0 : Zigzag2Rel
      (fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 5676)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5678))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9972)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5678))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9973)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5678))
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [← hwEq]
    exact Zigzag2Rel.norm_linear 2048 1024 64 hNorm' hwShapeSM
      (by decide) (by decide) (by decide) (by decide) hdec
  have hp0Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9972)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5678)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank0_shape hwShape
  have hp1Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 9973)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 5678)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank1_shape hwShape
  have hlogits : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5679)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9980)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9981)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [l12B2ZMr_red_sm5679 initSM, l12B2ZMr_red_sm5677 initSM,
      l12B2ZMr_red_sm8558 initSM, hwEq,
      l12B2ZMr_red_pm9980 initPM, l12B2ZMr_red_pm9981 initPM,
      l12B2ZMr_red_pm5679 initPM, l12B2ZMr_red_pm5677 initPM,
      l12B2ZMr_red_pm12134 initPM, l12B2ZMr_red_pm15392 initPM,
      l12B2ZMr_red_pm15394 initPM,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by decide) (by decide) (by decide) hs.rank0_shape hs.rank1_shape hwShape,
      l12B2ZMr_chunk_gather0 _ _ hp0Shape hp1Shape,
      l12B2ZMr_chunk_gather1 _ _ hp0Shape hp1Shape]
    exact hlogits0
  have hprobs := Zigzag2Rel.topk_routing_probs 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  have hmap := Zigzag2Rel.topk_routing_map 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  obtain ⟨logitSource0, logitSource1, hls⟩ := hlogits
  rw [l12B2ZMr_red_topk_probs sm_goal_1 initSM 558 l12B2ZMrSmTopk 0 5679 5680 5681 5682
      (by native_decide) (by native_decide) rfl (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l12B2ZMr_red_topk_probs pm_goal_1 initPM 1239 l12B2ZMrPmTopk0 0 9980 9982 9984 9986
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l12B2ZMr_red_topk_probs pm_goal_1 initPM 1240 l12B2ZMrPmTopk1 1 9981 9983 9985 9987
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l12B2ZMr_red_topk_map sm_goal_1 initSM 558 l12B2ZMrSmTopk 0 5679 5680 5681 5682
      (by native_decide) (by native_decide) rfl (by decide) (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l12B2ZMr_red_topk_map pm_goal_1 initPM 1239 l12B2ZMrPmTopk0 0 9980 9982 9984 9986
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l12B2ZMr_red_topk_map pm_goal_1 initPM 1240 l12B2ZMrPmTopk1 1 9981 9983 9985 9987
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact ⟨hprobs, hmap⟩

/-- The canonical L21 routing outputs are closed directly from the exact L20
output relation.  The normalized input, router weight agreement and shape,
packed-CU decode, logits, gather/chunk transport, and both top-k projections
are all derived internally. -/
theorem l12b2_zigzag_moe_router_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5674)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9968)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9969)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5680)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9982)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5681)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9984)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9985)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hNorm := l12b2_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l12b2_zigzag_moe_router_from_norm_input initSM initPM hPM hInit hNorm

#print axioms l12b2_zigzag_moe_router_from_norm_input
#print axioms l12b2_zigzag_moe_router_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns

