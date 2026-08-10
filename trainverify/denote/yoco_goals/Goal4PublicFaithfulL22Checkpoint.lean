/- Goal 4 faithful checkpoint through layer 22. -/
import denote.yoco_goals.Goal4PublicFaithfulL21Checkpoint
import denote.yoco_goals.CanonicalL23Router
import denote.ZigzagCollective

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective
noncomputable section
structure Goal4L22Checkpoint (initSM initPM : Store) : Prop where
  base : Goal4L21Checkpoint initSM initPM
  output22 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6214)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11508)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11509)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024]
theorem goal4_l22_checkpoint_from_l21 (initSM initPM : Store)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hClasses : InputValueClassesHold pmInputValueClasses initPM)
    (hPacked6252 : PackedCuSeqlensWF (initPM 6252) 4096 2)
    (mid : Goal4L21Checkpoint initSM initPM) : Goal4L22Checkpoint initSM initPM := by
  have hInput : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6193)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11444) (denoteGraphDistributedFaithful pm_goal_1 initPM 11445)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024] := mid.output21
  have hCache : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722) (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024] := mid.base.base.base.base.base.base.base.base.base.base.base.cache
  have hQ : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6201)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11454) (denoteGraphDistributedFaithful pm_goal_1 initPM 11455)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 16, 64] [2048, 16, 64] :=
    canonical_l22_q_relation_from_l21 initSM initPM hPM1 hInit1 hInput
  have hK : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6202)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11466) (denoteGraphDistributedFaithful pm_goal_1 initPM 11467)
      [4096, 4, 64] [2048, 4, 64] := canonical_l22_k_ordinary_relation initSM initPM hPM1 hInit1 hCache
  have hV : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6203)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11472) (denoteGraphDistributedFaithful pm_goal_1 initPM 11473)
      [4096, 4, 64] [2048, 4, 64] := canonical_l22_v_ordinary_relation initSM initPM hPM1 hInit1 hCache
  have hA22 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6206)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11478) (denoteGraphDistributedFaithful pm_goal_1 initPM 11479)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 16, 64] [2048, 16, 64] :=
    canonical_l22_attention_from_qkv initSM initPM hInit1 hClasses hPacked6252 hQ hK hV
  have hResidual22 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 8933)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 16442) (denoteGraphDistributedFaithful pm_goal_1 initPM 16450)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024] :=
    canonical_l22_residual_from_layer21_output initSM initPM hInput
  have hwEq : denoteGraphDistributedFaithful sm_goal_1 initSM 6210 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6210 := by
    have hi := (hInit1 initGoal_6210 (by native_decide)).2.2
    rw [reconstructForGoal_of_not_replicated initGoal_6210 pm_goal_1.numRanks _ rfl,
      show initGoal_6210.tps = [{rank := 0, tid := 6210}] from rfl,
      show initGoal_6210.ts = 6210 from rfl, show initGoal_6210.gatherDim = 0 from rfl] at hi
    simp only [List.map, reconstructWithDim] at hi
    unfold denoteGraphDistributedFaithful
    rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM 6210 (by native_decide) (by native_decide),
      foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6210 (by native_decide) (by native_decide)]
    exact hi
  have hwShape : (denoteGraphDistributedFaithful pm_goal_1 initPM 6210).shape = [1024, 1024] := by
    unfold denoteGraphDistributedFaithful
    rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6210 (by native_decide) (by native_decide)]
    exact hPM1 6210 [1024, 1024] (by native_decide)
  exact { base := mid, output22 := canonical_l22_output_from_inputs initSM initPM hResidual22 hA22 hwEq hwShape }
theorem goal4_l22_checkpoint_of_external (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_4InitEnv) (hPM : StoreShapesHold initPM pm_goal_4InitEnv)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hContract : Goal4ExternalInputContract initSM initPM) : Goal4L22Checkpoint initSM initPM := by
  have hPM1 := goal4_goal1_pm_shapes initSM initPM hInit
  have hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM := hInit
  have h6252 : initPM 6252 = initPM 6250 := hContract.2.1.eq_of_mem
    (c := pmInputValueClasses[1]'(by native_decide)) (by native_decide) (by native_decide) (by native_decide)
  have hPacked6252 : PackedCuSeqlensWF (initPM 6252) 4096 2 := by
    rw [h6252]; exact hContract.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact goal4_l22_checkpoint_from_l21 initSM initPM hPM1 hInit1 hContract.2.1 hPacked6252
    (goal4_l21_checkpoint_of_external initSM initPM hSM hPM hInit hContract)
end
end TrainVerify.Denote.GeneratedPatterns
