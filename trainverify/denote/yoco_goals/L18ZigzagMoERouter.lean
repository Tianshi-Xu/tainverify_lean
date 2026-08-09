/- Canonical Goal 1, layer 18: faithful router probabilities and map. -/
import denote.yoco_goals.L18ZigzagMoENormRouter
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

private theorem l18ZMr_chunk_gather0 (x0 x1 : Tensor)
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

private theorem l18ZMr_chunk_gather1 (x0 x1 : Tensor)
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

private def l18ZMrSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6054],
    outs := [8831, 8835, 8839, 8843, 8847], params := [5] }
private def l18ZMrPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11050],
    outs := [15420, 14860, 14870, 14884, 14896], params := [5] }
private def l18ZMrPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11051],
    outs := [15422, 14861, 14871, 14885, 14897], params := [5] }
private def l18ZMrSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8831], outs := [6055] }
private def l18ZMrPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15420, 15422],
    outs := [12274], params := [0] }
private def l18ZMrPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [12274], outs := [6055] }
private def l18ZMrSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [6055, 6056], outs := [6057] }
private def l18ZMrPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [6055, 6056], outs := [6057] }
private def l18ZMrPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [6057], outs := [11058], params := [0] }
private def l18ZMrPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [6057], outs := [11059], params := [0] }
private def l18ZMrSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [6057],
    outs := [6058, 6059, 6060], params := [8, 1] }
private def l18ZMrPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [11058],
    outs := [11060, 11062, 11064], params := [8, 1] }
private def l18ZMrPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [11059],
    outs := [11061, 11063, 11065], params := [8, 1] }

private theorem l18ZMr_red_sm8831 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8831 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6054 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 794 l18ZMrSmRef
    6054 8831 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6054
    [8831, 8835, 8839, 8843, 8847] 5 rfl 8831 (by decide)

private theorem l18ZMr_red_pm15420 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15420 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11050 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1739 l18ZMrPmRef0
    11050 15420 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11050
    [15420, 14860, 14870, 14884, 14896] 5 rfl 15420 (by decide)

private theorem l18ZMr_red_pm15422 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15422 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11051 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1740 l18ZMrPmRef1
    11051 15422 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11051
    [15422, 14861, 14871, 14885, 14897] 5 rfl 15422 (by decide)

private theorem l18ZMr_red_sm6055 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6055 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8831 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 795 l18ZMrSmFloat
    8831 6055 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8831 6055 []

private theorem l18ZMr_red_pm12274 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12274 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15420,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15422] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1744 l18ZMrPmGather
    15420 15422 12274 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15420, 15422] 12274 0]
  rfl

private theorem l18ZMr_red_pm6055 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 6055 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 12274 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1752 l18ZMrPmFloat1
    12274 6055 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 12274 6055 []

private theorem l18ZMr_red_sm6057 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6057 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6055)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6056) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 799 l18ZMrSmNormLinear
    6055 6056 6057 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 6055 6056 6057 []

private theorem l18ZMr_red_pm6057 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 6057 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 6055)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6056) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1760 l18ZMrPmNormLinear1
    6055 6056 6057 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 6055 6056 6057 []

private theorem l18ZMr_red_pm11058 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11058 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 6057) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1766 l18ZMrPmChunk0
    6057 11058 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 6057 11058 0

private theorem l18ZMr_red_pm11059 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11059 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 6057) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1767 l18ZMrPmChunk1
    6057 11059 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold l18ZMrPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 6057 11059 0

private def l18ZMrTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem l18ZMr_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l18ZMrTopkNode rnk logits probs mapTid scores)
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
      unfold l18ZMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l18ZMr_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = l18ZMrTopkNode rnk logits probs mapTid scores)
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
      unfold l18ZMrTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem l18ZMr_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 6056 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 6056 ∉ n.outs) := by
  native_decide

private theorem l18ZMr_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6056 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6056 := by
  have hi := (hInit initGoal_6056 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6056 pm_goal_1.numRanks _ rfl,
    show initGoal_6056.tps = [{rank := 0, tid := 6056}] from rfl,
    show initGoal_6056.ts = 6056 from rfl,
    show initGoal_6056.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      6056 (by native_decide) l18ZMr_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      6056 (by native_decide) l18ZMr_weight_not_written.2]
  exact hi

private theorem l18ZMr_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6056).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      6056 (by native_decide) l18ZMr_weight_not_written.2]
  exact hPM 6056 [64, 1024] (by native_decide)

private theorem l18ZMr_hdec (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6054)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11050)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11051)
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

/-- The canonical L18 routing probabilities and routing map are computed from the
shared normalized input by the real norm-linear, chunk, and top-k graph nodes. -/
theorem l18_zigzag_moe_router_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6054)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11050)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11051)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11060)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11061)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11062)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11063)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hdec := l18ZMr_hdec initPM hPM hNorm
  obtain ⟨source0, source1, hs⟩ := hNorm
  have hNorm' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6054)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11050)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11051)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  have hwEq := l18ZMr_weight_eq initSM initPM hInit
  have hwShape := l18ZMr_weight_shape initPM hPM
  have hwShapeSM :
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6056).shape = [64, 1024] := by
    rw [hwEq]
    exact hwShape
  have hlogits0 : Zigzag2Rel
      (fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6054)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6056))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11050)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6056))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11051)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6056))
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [← hwEq]
    exact Zigzag2Rel.norm_linear 2048 1024 64 hNorm' hwShapeSM
      (by decide) (by decide) (by decide) (by decide) hdec
  have hp0Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11050)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6056)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank0_shape hwShape
  have hp1Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11051)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6056)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank1_shape hwShape
  have hlogits : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6057)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [l18ZMr_red_sm6057 initSM, l18ZMr_red_sm6055 initSM,
      l18ZMr_red_sm8831 initSM, hwEq,
      l18ZMr_red_pm11058 initPM, l18ZMr_red_pm11059 initPM,
      l18ZMr_red_pm6057 initPM, l18ZMr_red_pm6055 initPM,
      l18ZMr_red_pm12274 initPM, l18ZMr_red_pm15420 initPM,
      l18ZMr_red_pm15422 initPM,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by decide) (by decide) (by decide) hs.rank0_shape hs.rank1_shape hwShape,
      l18ZMr_chunk_gather0 _ _ hp0Shape hp1Shape,
      l18ZMr_chunk_gather1 _ _ hp0Shape hp1Shape]
    exact hlogits0
  have hprobs := Zigzag2Rel.topk_routing_probs 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  have hmap := Zigzag2Rel.topk_routing_map 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  obtain ⟨logitSource0, logitSource1, hls⟩ := hlogits
  rw [l18ZMr_red_topk_probs sm_goal_1 initSM 803 l18ZMrSmTopk 0 6057 6058 6059 6060
      (by native_decide) (by native_decide) rfl (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l18ZMr_red_topk_probs pm_goal_1 initPM 1771 l18ZMrPmTopk0 0 11058 11060 11062 11064
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l18ZMr_red_topk_probs pm_goal_1 initPM 1772 l18ZMrPmTopk1 1 11059 11061 11063 11065
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l18ZMr_red_topk_map sm_goal_1 initSM 803 l18ZMrSmTopk 0 6057 6058 6059 6060
      (by native_decide) (by native_decide) rfl (by decide) (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l18ZMr_red_topk_map pm_goal_1 initPM 1771 l18ZMrPmTopk0 0 11058 11060 11062 11064
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    l18ZMr_red_topk_map pm_goal_1 initPM 1772 l18ZMrPmTopk1 1 11059 11061 11063 11065
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact ⟨hprobs, hmap⟩

/-- The canonical L18 routing outputs are closed directly from the exact L18 attention residual
output relation.  The normalized input, router weight agreement and shape,
packed-CU decode, logits, gather/chunk transport, and both top-k projections
are all derived internally. -/
theorem l18_zigzag_moe_router_from_attention_output (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6058)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11060)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11061)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6059)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11062)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11063)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hNorm := l18_zigzag_moe_norm_from_attention_output initSM initPM hInit hAttention
  exact l18_zigzag_moe_router_from_norm_input initSM initPM hPM hInit hNorm

#print axioms l18_zigzag_moe_router_from_norm_input
#print axioms l18_zigzag_moe_router_from_attention_output

end
end TrainVerify.Denote.GeneratedPatterns
