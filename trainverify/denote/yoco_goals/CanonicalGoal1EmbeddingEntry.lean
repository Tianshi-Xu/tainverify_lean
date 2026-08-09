/- Goal-1 exact-scope faithful embedding/AllToAll external entry. -/
import denote.yoco_goals.Goal_1
import denote.EmbeddingHiddenShard
import denote.Gather2Rel

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def g1eSmEmbedding : NodeDecl :=
  { rank := 0, op := "OpName.FW_embedding", ins := [4930, 4932], outs := [4933] }
private def g1eSmFloat : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [4933], outs := [4934] }
private def g1ePmEmbedding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_embedding", ins := [4930, 7746], outs := [7748] }
private def g1ePmEmbedding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_embedding", ins := [4930, 7747], outs := [7749] }
private def g1ePmAllToAll0 : NodeDecl :=
  { rank := 0, op := "OpName.AllToAllPrim", ins := [7748, 7749], outs := [7744], params := [1, 0] }
private def g1ePmAllToAll1 : NodeDecl :=
  { rank := 1, op := "OpName.AllToAllPrim", ins := [7748, 7749], outs := [7745], params := [1, 0] }
private def g1ePmFloat0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [7744], outs := [7754] }
private def g1ePmFloat1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [7745], outs := [7755] }

private theorem g1e_sm_all_nonempty :
    ∀ n ∈ sm_goal_1.nodes, n.outs ≠ [] := by native_decide

private theorem g1e_pm_all_nonempty :
    ∀ n ∈ pm_goal_1.nodes, n.outs ≠ [] := by native_decide

private theorem g1e_sm_nonempty (k : Nat) :
    ∀ n ∈ sm_goal_1.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact g1e_sm_all_nonempty n (List.mem_of_mem_drop hn)

private theorem g1e_pm_nonempty (k : Nat) :
    ∀ n ∈ pm_goal_1.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact g1e_pm_all_nonempty n (List.mem_of_mem_drop hn)

private theorem g1e_red_sm4933 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4933 =
      fw_embedding (denoteGraphDistributedFaithful sm_goal_1 initSM 4930)
        (denoteGraphDistributedFaithful sm_goal_1 initSM 4932) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 initSM 0 g1eSmEmbedding
    4930 4932 4933 fw_embedding
    (by native_decide) (by native_decide) ?_
    (g1e_sm_nonempty 1) (by native_decide)
    (g1e_sm_nonempty 0) (by native_decide) (by native_decide)
  intro s
  unfold g1eSmEmbedding
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_embedding_out sm_goal_1 s 0 4930 4932 4933

private theorem g1e_red_sm4934 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 4934 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 4933 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 1 g1eSmFloat
    4933 4934 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (g1e_sm_nonempty 2) (by native_decide)
    (g1e_sm_nonempty 1) (by native_decide)
  intro s
  unfold g1eSmFloat
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm_goal_1 s 0 4933 4934 []

private theorem g1e_red_pm7748 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7748 =
      fw_embedding (denoteGraphDistributedFaithful pm_goal_1 initPM 4930)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 7746) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 0 g1ePmEmbedding0
    4930 7746 7748 fw_embedding
    (by native_decide) (by native_decide) ?_
    (g1e_pm_nonempty 1) (by native_decide)
    (g1e_pm_nonempty 0) (by native_decide) (by native_decide)
  intro s
  unfold g1ePmEmbedding0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_embedding_out pm_goal_1 s 0 4930 7746 7748

private theorem g1e_red_pm7749 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7749 =
      fw_embedding (denoteGraphDistributedFaithful pm_goal_1 initPM 4930)
        (denoteGraphDistributedFaithful pm_goal_1 initPM 7747) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 14 g1ePmEmbedding1
    4930 7747 7749 fw_embedding
    (by native_decide) (by native_decide) ?_
    (g1e_pm_nonempty 15) (by native_decide)
    (g1e_pm_nonempty 14) (by native_decide) (by native_decide)
  intro s
  unfold g1ePmEmbedding1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_embedding_out pm_goal_1 s 1 4930 7747 7749

private theorem g1e_red_pm7744 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7744 =
      allToAllPrimWithDims 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 7748,
         denoteGraphDistributedFaithful pm_goal_1 initPM 7749] 1 0 := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 28 g1ePmAllToAll0
    7748 7749 7744 (fun a b => allToAllPrimWithDims 2 0 [a, b] 1 0)
    (by native_decide) (by native_decide) ?_
    (g1e_pm_nonempty 29) (by native_decide)
    (g1e_pm_nonempty 28) (by native_decide) (by native_decide)
  intro s
  unfold g1ePmAllToAll0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_allToAllPrimWithDims_out pm_goal_1 s 0 [7748, 7749] 7744 1 0

private theorem g1e_red_pm7745 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7745 =
      allToAllPrimWithDims 2 1
        [denoteGraphDistributedFaithful pm_goal_1 initPM 7748,
         denoteGraphDistributedFaithful pm_goal_1 initPM 7749] 1 0 := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 initPM 29 g1ePmAllToAll1
    7748 7749 7745 (fun a b => allToAllPrimWithDims 2 1 [a, b] 1 0)
    (by native_decide) (by native_decide) ?_
    (g1e_pm_nonempty 30) (by native_decide)
    (g1e_pm_nonempty 29) (by native_decide) (by native_decide)
  intro s
  unfold g1ePmAllToAll1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_allToAllPrimWithDims_out pm_goal_1 s 1 [7748, 7749] 7745 1 0

private theorem g1e_red_pm7754 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7754 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7744 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 30 g1ePmFloat0
    7744 7754 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (g1e_pm_nonempty 31) (by native_decide)
    (g1e_pm_nonempty 30) (by native_decide)
  intro s
  unfold g1ePmFloat0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 0 7744 7754 []

private theorem g1e_red_pm7755 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 7755 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 7745 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 31 g1ePmFloat1
    7745 7755 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (g1e_pm_nonempty 32) (by native_decide)
    (g1e_pm_nonempty 31) (by native_decide)
  intro s
  unfold g1ePmFloat1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm_goal_1 s 1 7745 7755 []

private theorem g1e_sm_leaf (initSM : Store) (tid : Tid)
    (hw : ∀ n ∈ sm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM tid = initSM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
    initSM tid (by native_decide) hw

private theorem g1e_pm_leaf (initPM : Store) (tid : Tid)
    (hw : ∀ n ∈ pm_goal_1.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) hw

/-- Exact `sm_goal_1`/`pm_goal_1` faithful entry.  Its only caller premises are
external store-shape and generated-init contracts; no computed lineage premise is
assumed.  The proof reduces every embedding, AllToAll, and float node in this
exact graph scope before applying the graph-independent hidden-shard algebra. -/
theorem canonical_goal_1_embedding_entry (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM) :
    Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4934)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7754)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7755)
      [4096, 1024] [2048, 1024] := by
  have hsm4930 := g1e_sm_leaf initSM 4930 (by native_decide)
  have hsm4932 := g1e_sm_leaf initSM 4932 (by native_decide)
  have hpm4930 := g1e_pm_leaf initPM 4930 (by native_decide)
  have hpm7746 := g1e_pm_leaf initPM 7746 (by native_decide)
  have hpm7747 := g1e_pm_leaf initPM 7747 (by native_decide)
  have hsIds : (denoteGraphDistributedFaithful sm_goal_1 initSM 4930).shape = [4096] := by
    rw [hsm4930]
    exact hSM 4930 [4096] (by native_decide)
  have hpIds : (denoteGraphDistributedFaithful pm_goal_1 initPM 4930).shape = [4096] := by
    rw [hpm4930]
    exact hPM 4930 [4096] (by native_decide)
  have hpW0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7746).shape = [154880, 512] := by
    rw [hpm7746]
    exact hPM 7746 [154880, 512] (by native_decide)
  have hpW1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7747).shape = [154880, 512] := by
    rw [hpm7747]
    exact hPM 7747 [154880, 512] (by native_decide)
  have hIds := (hInit initGoal_4930 (by native_decide)).2.2
  have hWeight := (hInit initGoal_4932 (by native_decide)).2.2
  simp only [initGoal_4930, pm_goal_1, List.map, reconstructForGoal,
    Bool.false_eq_true, if_false, reconstructWithDim_singleton] at hIds
  simp only [initGoal_4932, pm_goal_1, List.map, reconstructForGoal,
    Bool.false_eq_true, if_false] at hWeight
  have h7746 : (initPM 7746).shape = [154880, 512] :=
    hPM 7746 [154880, 512] (by native_decide)
  have h7746ne : ([154880, 512] : Shape) ≠ [1] := by decide
  have hWeight' : initSM 4932 = allGatherPrimDimN 1 2 0 [initPM 7746, initPM 7747] := by
    rw [hWeight]
    unfold reconstructWithDim
    simp only [List.head?_cons, Option.map_some, Option.getD_some, h7746,
      if_neg h7746ne]
  have hAlg := fw_embedding_hidden_shards_allToAll_two 2048 154880 512
    (denoteGraphDistributedFaithful pm_goal_1 initPM 4930)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 7746)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 7747)
    (by decide) (by decide) (by decide) hpIds hpW0 hpW1
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [g1e_red_sm4934, g1e_red_sm4933, g1e_red_pm7754, g1e_red_pm7755,
      g1e_red_pm7744, g1e_red_pm7745, g1e_red_pm7748, g1e_red_pm7749,
      hsm4930, hpm4930, hIds, hsm4932, hWeight', hpm7746, hpm7747]
    exact hAlg
  · rw [g1e_red_sm4934, g1e_red_sm4933, fw_embedding_shape, hsIds]
    have hsW : (denoteGraphDistributedFaithful sm_goal_1 initSM 4932).shape =
        [154880, 1024] := by
      rw [hsm4932]
      exact hSM 4932 [154880, 1024] (by native_decide)
    rw [hsW]
    rfl
  · rw [g1e_red_pm7754, g1e_red_pm7744, g1e_red_pm7748, g1e_red_pm7749]
    have hhead : (([fw_embedding (denoteGraphDistributedFaithful pm_goal_1 initPM 4930)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 7746),
        fw_embedding (denoteGraphDistributedFaithful pm_goal_1 initPM 4930)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 7747)].head?.map
          (fun t => t.shape)).getD []) = [4096, 512] := by
      simp only [List.head?, Option.map, Option.getD]
      rw [fw_embedding_shape, hpIds, hpW0]
      rfl
    rw [allToAllPrimWithDims_shape 2 0 _ 1 0 [4096, 512] hhead (by decide)]
    decide
  · rw [g1e_red_pm7755, g1e_red_pm7745, g1e_red_pm7748, g1e_red_pm7749]
    have hhead : (([fw_embedding (denoteGraphDistributedFaithful pm_goal_1 initPM 4930)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 7746),
        fw_embedding (denoteGraphDistributedFaithful pm_goal_1 initPM 4930)
          (denoteGraphDistributedFaithful pm_goal_1 initPM 7747)].head?.map
          (fun t => t.shape)).getD []) = [4096, 512] := by
      simp only [List.head?, Option.map, Option.getD]
      rw [fw_embedding_shape, hpIds, hpW0]
      rfl
    rw [allToAllPrimWithDims_shape 2 1 _ 1 0 [4096, 512] hhead (by decide)]
    decide

#print axioms canonical_goal_1_embedding_entry

end
end TrainVerify.Denote.GeneratedPatterns
