/- Canonical Goal 1, layer 17: faithful router probabilities and map. -/
import denote.yoco_goals.L17ZigzagMoENormRouter
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

private theorem l17ZMr_chunk_gather0 (x0 x1 : Tensor)
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

private theorem l17ZMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l17ZMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6000],
    outs := [8792, 8796, 8800, 8804, 8808], params := [5] }
private def l17ZMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [10896],
    outs := [15416, 14744, 14754, 14768, 14780], params := [5] }
private def l17ZMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [10897],
    outs := [15418, 14745, 14755, 14769, 14781], params := [5] }
private def l17ZMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8792], outs := [6001] }
private def l17ZMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15416, 15418],
    outs := [12254], params := [0] }
private def l17ZMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [12254], outs := [6001] }
private def l17ZMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [6001, 6002], outs := [6003] }
private def l17ZMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [6001, 6002], outs := [6003] }
private def l17ZMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [6003], outs := [10904], params := [0] }
private def l17ZMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [6003], outs := [10905], params := [0] }
private def l17ZMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [6003],
    outs := [6004, 6005, 6006], params := [8, 1] }
private def l17ZMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [10904],
    outs := [10906, 10908, 10910], params := [8, 1] }
private def l17ZMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [10905],
    outs := [10907, 10909, 10911], params := [8, 1] }

private theorem l17ZMr_red_sm8792 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8792 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6000 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 759 l17ZMrSmRef
    6000 8792 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6000
    [8792, 8796, 8800, 8804, 8808] 5 rfl 8792 (by decide)

private theorem l17ZMr_red_pm15416 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15416 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10896 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1663 l17ZMrPmRef0
    10896 15416 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 10896
    [15416, 14744, 14754, 14768, 14780] 5 rfl 15416 (by decide)

private theorem l17ZMr_red_pm15418 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15418 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 10897 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1664 l17ZMrPmRef1
    10897 15418 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 10897
    [15418, 14745, 14755, 14769, 14781] 5 rfl 15418 (by decide)

private theorem l17ZMr_red_sm6001 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6001 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8792 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 760 l17ZMrSmFloat
    8792 6001 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8792 6001 []

private theorem l17ZMr_red_pm12254 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12254 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15416,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15418] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1668 l17ZMrPmGather
    15416 15418 12254 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15416, 15418] 12254 0]
  rfl

private theorem l17ZMr_red_pm6001 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 6001 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 12254 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1676 l17ZMrPmFloat1
    12254 6001 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 12254 6001 []

private theorem l17ZMr_red_sm6003 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6003 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6001)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6002) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 764 l17ZMrSmNormLinear
    6001 6002 6003 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 6001 6002 6003 []

private theorem l17ZMr_red_pm6003 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 6003 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 6001)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6002) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1684 l17ZMrPmNormLinear1
    6001 6002 6003 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 6001 6002 6003 []

private theorem l17ZMr_red_pm10904 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10904 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 6003) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1690 l17ZMrPmChunk0
    6003 10904 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 6003 10904 0

private theorem l17ZMr_red_pm10905 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 10905 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 6003) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1691 l17ZMrPmChunk1
    6003 10905 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l17ZMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 6003 10905 0

private def l17ZMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l17ZMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l17ZMrTopkNode rnk logits probs mapTid scores)
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
      unfold l17ZMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l17ZMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l17ZMrTopkNode rnk logits probs mapTid scores)
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
      unfold l17ZMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l17ZMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 6002 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 6002 ∉ n.outs) := by
  native_decide

private theorem l17ZMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6002 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6002 := by
  have hi := (hInit initGoal_6002 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6002 pm_goal_1.numRanks _ rfl,
    show initGoal_6002.tps = [{rank := 0, tid := 6002}] from rfl,
    show initGoal_6002.ts = 6002 from rfl,
    show initGoal_6002.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      6002 (by native_decide) l17ZMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      6002 (by native_decide) l17ZMr_weight_not_written.2]
  exact hi

private theorem l17ZMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6002).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      6002 (by native_decide) l17ZMr_weight_not_written.2]
  exact hPM 6002 [64, 1024] (by native_decide)

private theorem l17ZMr_hdec (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10896)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10897)
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

/-- The canonical L17 routing probabilities and routing map are computed from the
shared normalized input by the real norm-linear, chunk, and top-k graph nodes. -/
theorem l17_zigzag_moe_router_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10896)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10897)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6004)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10906)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10907)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6005)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10908)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10909)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hdec := l17ZMr_hdec initPM hPM hNorm
  obtain ⟨source0, source1, hs⟩ := hNorm
  have hNorm' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6000)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10896)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10897)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  have hwEq := l17ZMr_weight_eq initSM initPM hInit
  have hwShape := l17ZMr_weight_shape initPM hPM
  have hwShapeSM :
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6002).shape = [64, 1024] := by
    rw [hwEq]
    exact hwShape
  have hlogits0 : Zigzag2Rel
      (fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6000)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6002))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10896)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6002))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10897)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6002))
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [← hwEq]
    exact Zigzag2Rel.norm_linear 2048 1024 64 hNorm' hwShapeSM
      (by decide) (by decide) (by decide) (by decide) hdec
  have hp0Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10896)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6002)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank0_shape hwShape
  have hp1Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 10897)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6002)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank1_shape hwShape
  have hlogits : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6003)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10904)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10905)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [l17ZMr_red_sm6003 initSM, l17ZMr_red_sm6001 initSM,
      l17ZMr_red_sm8792 initSM, hwEq,
      l17ZMr_red_pm10904 initPM, l17ZMr_red_pm10905 initPM,
      l17ZMr_red_pm6003 initPM, l17ZMr_red_pm6001 initPM,
      l17ZMr_red_pm12254 initPM, l17ZMr_red_pm15416 initPM,
      l17ZMr_red_pm15418 initPM,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by decide) (by decide) (by decide) hs.rank0_shape hs.rank1_shape hwShape,
      l17ZMr_chunk_gather0 _ _ hp0Shape hp1Shape,
      l17ZMr_chunk_gather1 _ _ hp0Shape hp1Shape]
    exact hlogits0
  have hprobs := Zigzag2Rel.topk_routing_probs 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  have hmap := Zigzag2Rel.topk_routing_map 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  obtain ⟨logitSource0, logitSource1, hls⟩ := hlogits
  rw [l17ZMr_red_topk_probs sm_goal_1 initSM 768 l17ZMrSmTopk 0 6003 6004 6005 6006
      (by native_decide) (by native_decide) rfl (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l17ZMr_red_topk_probs pm_goal_1 initPM 1695 l17ZMrPmTopk0 0 10904 10906 10908 10910
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l17ZMr_red_topk_probs pm_goal_1 initPM 1696 l17ZMrPmTopk1 1 10905 10907 10909 10911
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l17ZMr_red_topk_map sm_goal_1 initSM 768 l17ZMrSmTopk 0 6003 6004 6005 6006
      (by native_decide) (by native_decide) rfl (by decide) (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l17ZMr_red_topk_map pm_goal_1 initPM 1695 l17ZMrPmTopk0 0 10904 10906 10908 10910
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l17ZMr_red_topk_map pm_goal_1 initPM 1696 l17ZMrPmTopk1 1 10905 10907 10909 10911
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact ⟨hprobs, hmap⟩

/-- The canonical L17 routing outputs are closed directly from the exact L17 attention residual
output relation.  The normalized input, router weight agreement and shape,
packed-CU decode, logits, gather/chunk transport, and both top-k projections
are all derived internally. -/
theorem l17_zigzag_moe_router_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5998)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10892)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10893)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6004)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10906)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10907)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6005)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10908)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10909)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hNorm := l17_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l17_zigzag_moe_router_from_norm_input initSM initPM hPM hInit hNorm

#print axioms l17_zigzag_moe_router_from_norm_input
#print axioms l17_zigzag_moe_router_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
