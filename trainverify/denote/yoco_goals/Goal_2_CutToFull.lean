/- Verified non-base ring-tail cut-to-full bridge for YOCO goal 2. -/
import denote.yoco_goals.Goal_2
import denote.yoco_goals.RingTailBridge
import denote.yoco_goals.BridgeKit
import denote.yoco_goals.RingFixedPointBridge
import denote.yoco_goals.ZigzagL11Body

set_option linter.style.longLine false
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated

open TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote.GeneratedStructuralFacts

private theorem sm_goal_2_ring_self (initSM : Store) :
    denoteGraph sm_goal_2 (denoteGraph_ringAttn sm initSM) 4674 =
      denoteGraph_ringAttn sm initSM 4674 := by
  let s := denoteGraph_ringAttn sm initSM
  have hnode : ∀ n ∈ sm_goal_2.nodes, applyNode sm s n = s := by
    intro n hn
    simp only [sm_goal_2, List.mem_cons, List.not_mem_nil, or_false] at hn
    rw [hn]
    exact node_fixed_on_ring_final sm initSM 926 _ (by native_decide) (by native_decide)
      (sm_wellFormed _ (by native_decide)) (by decide) (by decide)
      (by native_decide) (by native_decide) (by native_decide)
  unfold denoteGraph
  rw [show applyNode sm_goal_2 = applyNode sm from
    applyNode_congr_numRanks _ _ (by native_decide)]
  exact congrFun (foldl_applyNode_fixed sm sm_goal_2.nodes s hnode) 4674

private theorem pm_goal_2_ring_self (initPM : Store) :
    denoteGraph pm_goal_2 (denoteGraph_ringAttn pm initPM) 4674 =
      denoteGraph_ringAttn pm initPM 4674 := by
  let s := denoteGraph_ringAttn pm initPM
  have hnode : ∀ n ∈ pm_goal_2.nodes, applyNode pm s n = s := by
    intro n hn
    simp only [pm_goal_2, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact node_fixed_on_ring_final pm initPM 12 _ (by native_decide) (by native_decide)
        (pm_wellFormed _ (by native_decide)) (by decide) (by decide)
        (by native_decide) (by native_decide) (by native_decide)
    · exact node_fixed_on_ring_final pm initPM 25 _ (by native_decide) (by native_decide)
        (pm_wellFormed _ (by native_decide)) (by decide) (by decide)
        (by native_decide) (by native_decide) (by native_decide)
    · exact node_fixed_on_ring_final pm initPM 1916 _ (by native_decide) (by native_decide)
        (pm_wellFormed _ (by native_decide)) (by decide) (by decide)
        (by native_decide) (by native_decide) (by native_decide)
    · exact node_fixed_on_ring_final pm initPM 1917 _ (by native_decide) (by native_decide)
        (pm_wellFormed _ (by native_decide)) (by decide) (by decide)
        (by native_decide) (by native_decide) (by native_decide)
    · exact node_fixed_on_ring_final pm initPM 1919 _ (by native_decide) (by native_decide)
        (pm_wellFormed _ (by native_decide)) (by decide) (by decide)
        (by native_decide) (by native_decide) (by native_decide)
  unfold denoteGraph
  rw [show applyNode pm_goal_2 = applyNode pm from
    applyNode_congr_numRanks _ _ (by native_decide)]
  exact congrFun (foldl_applyNode_fixed pm pm_goal_2.nodes s hnode) 4674


/-- Full ring-aware Goal 2 statement under the real YOCO input contract. -/
def goal_2_stmt_ringAttn_full : Prop :=
  ∀ (initSM initPM : Store),
    StoreShapesHold initSM smInitEnv →
    StoreShapesHold initPM pmInitEnv →
    InitGoalsHold pm.numRanks initGoals initSM initPM →
    WellFormed_YOCOMoE_A04B initSM initPM →
    InitGoalHolds pm.numRanks goal_2
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)

/-- Non-base cut-to-full bridge for Goal 2. -/
theorem goal_2_cut_to_full_ringAttn (h : goal_2_stmt_cut) :
    goal_2_stmt_ringAttn_full := by
  intro initSM initPM hSM hPM hInit hWF
  let smStore := denoteGraph_ringAttn sm initSM
  let pmStore := denoteGraph_ringAttn pm initPM
  have hBase : InitGoalsHold pm.numRanks initGoals smStore pmStore := by
    exact initGoals_preserved_ringAttn initSM initPM hInit
  have h5930 : InitGoalHolds pm.numRanks intermediateGoal_5930 smStore pmStore := by
    exact recon_intermediateGoal_5930_ringAttn initSM initPM hSM hPM hInit hWF
  have hInitCut : InitGoalsHold pm_goal_2.numRanks goal_2_cut_initGoals smStore pmStore := by
    rw [goal_2_cut_initGoals]
    apply InitGoalsHold_append
    · exact hBase
    · intro g hg
      simp only [List.mem_singleton] at hg
      rw [hg]
      exact h5930
  have h_initGoal_4678 := hInitCut initGoal_4678 (by native_decide)
  have h_intermediateGoal_5930 := hInitCut intermediateGoal_5930 (by native_decide)
  have h_initGoal_5931 := hInitCut initGoal_5931 (by native_decide)
  have hSMcut : StoreShapesHold smStore sm_goal_2InitEnv := by
    intro tid sh hsh
    rw [sm_goal_2InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [sm_goal_2InitShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [initGoal_4678] using h_initGoal_4678.1
    · simpa [intermediateGoal_5930] using h_intermediateGoal_5930.1
    · simpa [initGoal_5931] using h_initGoal_5931.1
  have hPMcut : StoreShapesHold pmStore pm_goal_2InitEnv := by
    intro tid sh hsh
    rw [pm_goal_2InitEnv] at hsh
    have hmem := mem_of_shapeEnvOfList_eq_some hsh
    simp only [pm_goal_2InitShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hp := congrArg (fun xs => xs.getD 0 []) h_initGoal_4678.2.1
      simpa [initGoal_4678] using hp
    · have hp := congrArg (fun xs => xs.getD 0 []) h_initGoal_5931.2.1
      simpa [initGoal_5931] using hp
    · have hp := congrArg (fun xs => xs.getD 0 []) h_intermediateGoal_5930.2.1
      simpa [intermediateGoal_5930] using hp
    · have hp := congrArg (fun xs => xs.getD 1 []) h_intermediateGoal_5930.2.1
      simpa [intermediateGoal_5930] using hp
  have hcut := h smStore pmStore hSMcut hPMcut hInitCut
  unfold CoarseLineageHoldsWithInit at hcut
  simp only [goal_2, List.map] at hcut
  have hts := hcut.1
  have htps := hcut.2.1
  have hv := hcut.2.2
  rw [sm_goal_2_ring_self initSM] at hts
  rw [pm_goal_2_ring_self initPM] at htps
  rw [sm_goal_2_ring_self initSM, pm_goal_2_ring_self initPM] at hv
  refine ⟨?_, ?_, ?_⟩
  · change (denoteGraph_ringAttn sm initSM 4674).shape = [4096]
    exact hts
  · change [(denoteGraph_ringAttn pm initPM 4674).shape] = [[4096]]
    exact htps
  · simpa [goal_2, reconstructForGoal, reconstructWithDim] using hv

end TrainVerify.Denote.GeneratedGoals
