/- Canonical Goal 1, layer 23: faithful router probabilities and map. -/
import denote.yoco_goals.CanonicalL23GateDown
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

private theorem cL23r_chunk_gather0 (x0 x1 : Tensor)
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

private theorem cL23r_chunk_gather1 (x0 x1 : Tensor)
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

private def cL23rSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6216],
    outs := [8948, 8952, 8956, 8960, 8964], params := [5] }
private def cL23rPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11512],
    outs := [15432, 15208, 15218, 15232, 15244], params := [5] }
private def cL23rPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11513],
    outs := [15434, 15209, 15219, 15233, 15245], params := [5] }
private def cL23rSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8948], outs := [6217] }
private def cL23rPmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [15432, 15434],
    outs := [12334], params := [0] }
private def cL23rPmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [12334], outs := [6217] }
private def cL23rSmNormLinear : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [6217, 6218], outs := [6219] }
private def cL23rPmNormLinear1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [6217, 6218], outs := [6219] }
private def cL23rPmChunk0 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [6219], outs := [11520], params := [0] }
private def cL23rPmChunk1 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [6219], outs := [11521], params := [0] }
private def cL23rSmTopk : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [6219],
    outs := [6220, 6221, 6222], params := [8, 1] }
private def cL23rPmTopk0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_topk_routing", ins := [11520],
    outs := [11522, 11524, 11526], params := [8, 1] }
private def cL23rPmTopk1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_topk_routing", ins := [11521],
    outs := [11523, 11525, 11527], params := [8, 1] }

private theorem cL23r_red_sm8948 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8948 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 6216 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 899 cL23rSmRef
    6216 8948 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23rSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6216
    [8948, 8952, 8956, 8960, 8964] 5 rfl 8948 (by decide)

private theorem cL23r_red_pm15432 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15432 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11512 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1967 cL23rPmRef0
    11512 15432 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23rPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11512
    [15432, 15208, 15218, 15232, 15244] 5 rfl 15432 (by decide)

private theorem cL23r_red_pm15434 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15434 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 11513 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1968 cL23rPmRef1
    11513 15434 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23rPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11513
    [15434, 15209, 15219, 15233, 15245] 5 rfl 15434 (by decide)

private theorem cL23r_red_sm6217 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6217 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8948 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 900 cL23rSmFloat
    8948 6217 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23rSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 8948 6217 []

private theorem cL23r_red_pm12334 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 12334 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15432,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15434] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1972 cL23rPmGather
    15432 15434 12334 (fun x y => allGatherPrimDimN 0 2 0 [x, y])
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23rPmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  unfold applyNodeDistributed
  rw [if_neg (by decide),
    applyNodeRingAttn_eq_applyNode_of_not_ring _ _ _ (by decide) (by decide),
    applyNode_allGatherPrimDimN_out pm_goal_1 s 0 [15432, 15434] 12334 0]
  rfl

private theorem cL23r_red_pm6217 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 6217 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 12334 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1980 cL23rPmFloat1
    12334 6217 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23rPmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 12334 6217 []

private theorem cL23r_red_sm6219 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6219 =
      fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6217)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 6218) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 904 cL23rSmNormLinear
    6217 6218 6219 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23rSmNormLinear
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm_goal_1 s 0 6217 6218 6219 []

private theorem cL23r_red_pm6219 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 6219 =
      fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 6217)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6218) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 1988 cL23rPmNormLinear1
    6217 6218 6219 fw_norm_linear (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL23rPmNormLinear1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm_goal_1 s 1 6217 6218 6219 []

private theorem cL23r_red_pm11520 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11520 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributedFaithful pm_goal_1 initPM 6219) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1994 cL23rPmChunk0
    6219 11520 (chunkPrimDimN 0 2 0) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23rPmChunk0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 0 6219 11520 0

private theorem cL23r_red_pm11521 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 11521 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributedFaithful pm_goal_1 initPM 6219) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1995 cL23rPmChunk1
    6219 11521 (chunkPrimDimN 0 2 1) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL23rPmChunk1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_chunkPrimDimN_out pm_goal_1 s 1 6219 11521 0

private def cL23rTopkNode (rnk logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rnk, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

private theorem cL23r_red_topk_probs (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = cL23rTopkNode rnk logits probs mapTid scores)
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
      unfold cL23rTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_probs_out g s rnk logits probs mapTid scores [8, 1])
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem cL23r_red_topk_map (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (rnk logits probs mapTid scores : Nat)
    (hk : k < g.nodes.length) (hn : g.nodes[k]'hk = node)
    (hnode : node = cL23rTopkNode rnk logits probs mapTid scores)
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
      unfold cL23rTopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_map_out g s rnk logits probs mapTid scores [8, 1]
        hne)
    ha haw hp hpw
  rw [hr]
  rcases hsh with hsh | hsh <;> rw [hsh] <;> rfl

private theorem cL23r_weight_not_written :
    (∀ n ∈ sm_goal_1.nodes, 6218 ∉ n.outs) ∧
      (∀ n ∈ pm_goal_1.nodes, 6218 ∉ n.outs) := by
  native_decide

private theorem cL23r_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 6218 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6218 := by
  have hi := (hInit initGoal_6218 (by native_decide)).2.2
  rw [reconstructForGoal_of_not_replicated initGoal_6218 pm_goal_1.numRanks _ rfl,
    show initGoal_6218.tps = [{rank := 0, tid := 6218}] from rfl,
    show initGoal_6218.ts = 6218 from rfl,
    show initGoal_6218.gatherDim = 0 from rfl] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM
      6218 (by native_decide) cL23r_weight_not_written.1,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      6218 (by native_decide) cL23r_weight_not_written.2]
  exact hi

private theorem cL23r_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6218).shape = [64, 1024] := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM
      6218 (by native_decide) cL23r_weight_not_written.2]
  exact hPM 6218 [64, 1024] (by native_decide)

private theorem cL23r_hdec (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11513)
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

/-- The canonical L23 routing probabilities and routing map are computed from the
shared normalized input by the real norm-linear, chunk, and top-k graph nodes. -/
theorem canonical_l23_router_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11513)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6220)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11522)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11523)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] ∧
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6221)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11524)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11525)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 64] [2048, 64] := by
  have hdec := cL23r_hdec initPM hPM hNorm
  obtain ⟨source0, source1, hs⟩ := hNorm
  have hNorm' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11512)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11513)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  have hwEq := cL23r_weight_eq initSM initPM hInit
  have hwShape := cL23r_weight_shape initPM hPM
  have hwShapeSM :
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6218).shape = [64, 1024] := by
    rw [hwEq]
    exact hwShape
  have hlogits0 : Zigzag2Rel
      (fw_norm_linear (denoteGraphDistributedFaithful sm_goal_1 initSM 6216)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6218))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11512)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6218))
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11513)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6218))
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [← hwEq]
    exact Zigzag2Rel.norm_linear 2048 1024 64 hNorm' hwShapeSM
      (by decide) (by decide) (by decide) (by decide) hdec
  have hp0Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11512)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6218)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank0_shape hwShape
  have hp1Shape :
      (fw_norm_linear (denoteGraphDistributedFaithful pm_goal_1 initPM 11513)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 6218)).shape = [2048, 64] :=
    fw_norm_linear_shape_2d 2048 1024 64 _ _ (by decide) hs.rank1_shape hwShape
  have hlogits : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6219)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11520)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11521)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 64] [2048, 64] := by
    rw [cL23r_red_sm6219 initSM, cL23r_red_sm6217 initSM,
      cL23r_red_sm8948 initSM, hwEq,
      cL23r_red_pm11520 initPM, cL23r_red_pm11521 initPM,
      cL23r_red_pm6219 initPM, cL23r_red_pm6217 initPM,
      cL23r_red_pm12334 initPM, cL23r_red_pm15432 initPM,
      cL23r_red_pm15434 initPM,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by decide) (by decide) (by decide) hs.rank0_shape hs.rank1_shape hwShape,
      cL23r_chunk_gather0 _ _ hp0Shape hp1Shape,
      cL23r_chunk_gather1 _ _ hp0Shape hp1Shape]
    exact hlogits0
  have hprobs := Zigzag2Rel.topk_routing_probs 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  have hmap := Zigzag2Rel.topk_routing_map 2048 64 8 hlogits
    (by decide) (by decide) (by decide) hdec
  obtain ⟨logitSource0, logitSource1, hls⟩ := hlogits
  rw [cL23r_red_topk_probs sm_goal_1 initSM 908 cL23rSmTopk 0 6219 6220 6221 6222
      (by native_decide) (by native_decide) rfl (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    cL23r_red_topk_probs pm_goal_1 initPM 1999 cL23rPmTopk0 0 11520 11522 11524 11526
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    cL23r_red_topk_probs pm_goal_1 initPM 2000 cL23rPmTopk1 1 11521 11523 11525 11527
      (by native_decide) (by native_decide) rfl (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    cL23r_red_topk_map sm_goal_1 initSM 908 cL23rSmTopk 0 6219 6220 6221 6222
      (by native_decide) (by native_decide) rfl (by decide) (Or.inr hls.full_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    cL23r_red_topk_map pm_goal_1 initPM 1999 cL23rPmTopk0 0 11520 11522 11524 11526
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank0_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide),
    cL23r_red_topk_map pm_goal_1 initPM 2000 cL23rPmTopk1 1 11521 11523 11525 11527
      (by native_decide) (by native_decide) rfl (by decide) (Or.inl hls.rank1_shape)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact ⟨hprobs, hmap⟩

end
end TrainVerify.Denote.GeneratedPatterns
