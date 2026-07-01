/- Auto-generated pattern proof file (proof filled in 2026-07-01).
   Pattern: 5
   Hash: 70ae1240263b50ea
   Goals: 5
   Op flavour: FW_embedding vocab-parallel (SM=1 op, PM=2 shard embeddings + 1 AllReducePrim)
-/
import denote.yoco_goals.BridgeKit

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_5_goalIds : List Nat := [5]
inductive pattern_5_target : Prop → Prop
  | goal_5 : pattern_5_target goal_5_stmt

def pattern_5_stmt : Prop :=
  ∀ {target : Prop}, pattern_5_target target → target

-- ============================================================
-- Denotation helpers for goal_5's tid 4680.
-- ============================================================

/-- SM side: `denoteGraph sm initSM 4680` reduces to the single `FW_embedding`
    call at `sm.nodes[0]`. -/
theorem denote_sm_4680 (initSM : Store) :
    denoteGraph sm initSM 4680 = fw_embedding (initSM 4677) (initSM 4679) := by
  have h := sm_val initSM 0 4680 (by native_decide) (by native_decide)
  rw [h]
  simp only [sm, List.take, List.getElem_cons_zero, denoteGraph_nodes_nil]
  rw [applyNode_fw_embedding_out]

/-- PM shard 0 (rank 0): tid 7391 = `fw_embedding_offset 0`. -/
theorem denote_pm_prefix_7391 (initPM : Store) :
    denoteGraph {pm with nodes := pm.nodes.take 26} initPM 7391 =
      fw_embedding_offset 0 (initPM 4677) (initPM 7389) := by
  have h := pm_val_prefix initPM 26 0 (by native_decide) (by native_decide) 7391 (by native_decide)
  rw [h]
  have hnode : (pm.nodes.take 26)[0]'(by native_decide) =
      { rank := 0, op := "OpName.FW_embedding", ins := [4677, 7389], outs := [7391], params := [0] } := by
    native_decide
  simp only [hnode, List.take, denoteGraph_nodes_nil]
  rw [applyNode_fw_embedding_offset_out]

/-- PM shard 1 (rank 1): tid 7392 = `fw_embedding_offset 77440`. -/
theorem denote_pm_prefix_7392 (initPM : Store) :
    denoteGraph {pm with nodes := pm.nodes.take 26} initPM 7392 =
      fw_embedding_offset 77440 (initPM 4677) (initPM 7390) := by
  have h := pm_val_prefix initPM 26 13 (by native_decide) (by native_decide) 7392 (by native_decide)
  rw [h]
  have hnode : (pm.nodes.take 26)[13]'(by native_decide) =
      { rank := 1, op := "OpName.FW_embedding", ins := [4677, 7390], outs := [7392], params := [77440] } := by
    native_decide
  simp only [hnode]
  rw [applyNode_fw_embedding_offset_out]
  -- Reduce inner store lookups 4677 / 7390 back to initPM (they're not written in the take-13 prefix)
  have h4677 : denoteGraph {pm with nodes := (pm.nodes.take 26).take 13} initPM 4677 = initPM 4677 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs
    native_decide
  have h7390 : denoteGraph {pm with nodes := (pm.nodes.take 26).take 13} initPM 7390 = initPM 7390 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs
    native_decide
  rw [h4677, h7390]

/-- PM main: tid 4680 = `allReducePrim` of the two shard embeddings. -/
theorem denote_pm_4680 (initPM : Store) :
    denoteGraph pm initPM 4680 =
    allReducePrim 2 0
      [fw_embedding_offset 0 (initPM 4677) (initPM 7389),
       fw_embedding_offset 77440 (initPM 4677) (initPM 7390)] := by
  have h := pm_val initPM 26 4680 (by native_decide) (by native_decide)
  rw [h]
  have hnode : pm.nodes[26]'(by native_decide) =
      { rank := 0, op := "OpName.AllReducePrim", ins := [7391, 7392], outs := [4680] } := by
    native_decide
  simp only [hnode]
  rw [applyNode_allReducePrim_out]
  have hR : pm.numRanks = 2 := by native_decide
  -- Reduce inner store lookups via the prefix theorems, using `show` to force the goal
  -- into a form where the {pm with nodes := ...} pattern is visible to `rw`.
  show allReducePrim pm.numRanks 0
      ([7391, 7392].map (denoteGraph {pm with nodes := pm.nodes.take 26} initPM)) = _
  rw [hR]
  simp only [List.map, denote_pm_prefix_7391, denote_pm_prefix_7392]

-- ============================================================
-- Main proof: goal_5_stmt (full CoarseLineageHoldsWithInit).
-- ============================================================

theorem prove_goal_5 : goal_5_stmt := by
  intro initSM initPM hSM hPM _hInit
  simp only [goal_5]
  -- Shape witnesses from `hSM` / `hPM` on the leaf tids.
  have h4677_sm : (initSM 4677).shape = [4096] :=
    hSM 4677 [4096] (by native_decide)
  have h4679_sm : (initSM 4679).shape = [154880, 1024] :=
    hSM 4679 [154880, 1024] (by native_decide)
  have h4677_pm : (initPM 4677).shape = [4096] :=
    hPM 4677 [4096] (by native_decide)
  have h7389_pm : (initPM 7389).shape = [77440, 1024] :=
    hPM 7389 [77440, 1024] (by native_decide)
  have h7390_pm : (initPM 7390).shape = [77440, 1024] :=
    hPM 7390 [77440, 1024] (by native_decide)
  refine ⟨?shape_sm, ?shape_pm, ?value⟩
  case shape_sm =>
    rw [denote_sm_4680 initSM, fw_embedding_shape, h4677_sm, h4679_sm]
    rfl
  case shape_pm =>
    simp only [List.map]
    rw [denote_pm_4680 initPM]
    have hhead : ([fw_embedding_offset 0 (initPM 4677) (initPM 7389),
                   fw_embedding_offset 77440 (initPM 4677) (initPM 7390)]).head?
                 = some (fw_embedding_offset 0 (initPM 4677) (initPM 7389)) := rfl
    rw [allReducePrim_shape 2 0 _ _ hhead]
    rw [fw_embedding_offset_shape, h4677_pm, h7389_pm]
    rfl
  case value =>
    -- Reduce to `SM = PM` via singleton reconstructWithDim.
    simp only [List.map, reconstructWithDim_singleton]
    rw [denote_sm_4680 initSM, denote_pm_4680 initPM]
    -- Get the sharding hypothesis for the SM weight tid 4679 from `_hInit initGoal_4679`.
    have hg4679 := _hInit initGoal_4679 (by native_decide)
    unfold InitGoalHolds at hg4679
    have hpmR : pm.numRanks = 2 := by native_decide
    obtain ⟨_, _, hval⟩ := hg4679
    simp only [initGoal_4679, hpmR, List.map] at hval
    have hshape7389 : (initPM 7389).shape = [77440, 1024] := h7389_pm
    have hreconstr :
        reconstructWithDim 0 2 0 [initPM 7389, initPM 7390] =
        allGatherPrimDimN 0 2 0 [initPM 7389, initPM 7390] := by
      unfold reconstructWithDim
      simp only [List.head?_cons, Option.map_some, Option.getD_some, hshape7389]
      rfl
    rw [hreconstr] at hval
    rw [hval]
    -- The SM ids tid 4677 is a singleton init tp, so `initSM 4677 = initPM 4677`.
    have hg4677 := _hInit initGoal_4677 (by native_decide)
    unfold InitGoalHolds at hg4677
    obtain ⟨_, _, hval2⟩ := hg4677
    simp only [initGoal_4677, hpmR, List.map, reconstructWithDim_singleton] at hval2
    rw [hval2]
    -- Apply the vocab-parallel embedding correctness lemma.
    have hWs_head :
        (([initPM 7389, initPM 7390] : List Tensor).head?.map (fun t => t.shape)).getD [] =
        [77440, 1024] := by
      simp only [List.head?_cons, Option.map_some, Option.getD_some]
      exact h7389_pm
    have hWs_shape : ∀ r (_ : r < 2),
        (([initPM 7389, initPM 7390]).getD r (zeroTensor [77440, 1024])).shape =
        [77440, 1024] := by
      intro r hr
      interval_cases r
      · exact h7389_pm
      · exact h7390_pm
    have hlen : ([initPM 7389, initPM 7390] : List Tensor).length = 2 := rfl
    have h := fw_embedding_eq_allReduce_offset_shards 2 77440 1024
      (by decide) (by decide) (by decide)
      (initPM 4677) [initPM 7389, initPM 7390] hlen hWs_head hWs_shape
    rw [h]
    -- Reduce List.ofFn on Fin 2 to the explicit 2-element list.
    have hofFn :
        (List.ofFn (fun r : Fin 2 =>
          fw_embedding_offset (r.val * 77440) (initPM 4677)
            ([initPM 7389, initPM 7390].getD r.val (zeroTensor [77440, 1024])))) =
        [fw_embedding_offset 0 (initPM 4677) (initPM 7389),
         fw_embedding_offset 77440 (initPM 4677) (initPM 7390)] := rfl
    rw [hofFn]

-- ============================================================
-- Pattern wrapper.
-- ============================================================

theorem prove_pattern_5 : pattern_5_stmt := by
  intro _ hpat
  cases hpat
  exact prove_goal_5

end TrainVerify.Denote.GeneratedPatterns
