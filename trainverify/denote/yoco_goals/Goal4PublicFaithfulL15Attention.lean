/- Goal 4 faithful layer-15 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL14Checkpoint
import denote.yoco_goals.L15ZigzagMoERouter
import denote.yoco_goals.CanonicalL15ShardedKVAttention
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
structure Goal4L15Checkpoint (initSM initPM : Store) : Prop where
  base : Goal4L14Checkpoint initSM initPM
  output15 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5923)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 10674)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 10675)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024]
  l17 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5898)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 10603)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5926) [4096, 64] [2048, 64]
theorem goal4_l15_attention_from_l14
    (initSM initPM : Store)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hClasses : InputValueClassesHold pmInputValueClasses initPM)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (mid : Goal4L14Checkpoint initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5890)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10584)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10585)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hIncoming : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5869)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10520) (denoteGraphDistributedFaithful pm_goal_1 initPM 10521)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024] := mid.output14
  have hCache : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722) (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024] := mid.base.base.base.base.cache
  have hCu4 : denoteGraphDistributedFaithful pm_goal_4 initPM 5880 = initPM 5880 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes initPM 5880 (by native_decide) (by native_decide)
  have hCu1 : denoteGraphDistributedFaithful pm_goal_1 initPM 5880 = initPM 5880 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 5880 (by native_decide) (by native_decide)
  have hAlias4 : denoteGraphDistributedFaithful pm_goal_4 initPM 5880 = denoteGraphDistributedFaithful pm_goal_1 initPM 6252 :=
    goal4_canonical_cu_alias initPM hClasses 5880 (by decide)
  have hAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 5880 = denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hCu1, ← hCu4]; exact hAlias4
  exact canonical_l15_attention_residual_from_incoming_and_cache initSM initPM hPM1 hInit1 hIncoming hCache hAlias hDec
end
end TrainVerify.Denote.GeneratedPatterns
