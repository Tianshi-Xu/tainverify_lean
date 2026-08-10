/- Goal 4 faithful layer-18 checkpoint, physically split for bounded elaboration. -/
import denote.yoco_goals.Goal4PublicFaithfulL17Checkpoint
import denote.yoco_goals.L18ZigzagMoERouter
import denote.yoco_goals.CanonicalL18ShardedKVAttention
set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
noncomputable section
structure Goal4L18Checkpoint (initSM initPM : Store) : Prop where
  base : Goal4L17Checkpoint initSM initPM
  output18 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6085)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11136)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 11137)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024]
  l20 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 6060)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 11065)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 6088) [4096, 64] [2048, 64]
theorem goal4_l18_attention_from_l17
    (initSM initPM : Store)
    (hPM1 : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hClasses : InputValueClassesHold pmInputValueClasses initPM)
    (hDec : decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096])
    (mid : Goal4L17Checkpoint initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6052)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11046)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hIncoming : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 6031)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 10982) (denoteGraphDistributedFaithful pm_goal_1 initPM 10983)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024] := mid.output17
  have hCache : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722) (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024] := mid.base.base.base.base.base.base.base.cache
  have hCu4 : denoteGraphDistributedFaithful pm_goal_4 initPM 6042 = initPM 6042 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes initPM 6042 (by native_decide) (by native_decide)
  have hCu1 : denoteGraphDistributedFaithful pm_goal_1 initPM 6042 = initPM 6042 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM 6042 (by native_decide) (by native_decide)
  have hAlias4 : denoteGraphDistributedFaithful pm_goal_4 initPM 6042 = denoteGraphDistributedFaithful pm_goal_1 initPM 6252 :=
    goal4_canonical_cu_alias initPM hClasses 6042 (by decide)
  have hAlias : denoteGraphDistributedFaithful pm_goal_1 initPM 6042 = denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [hCu1, ← hCu4]; exact hAlias4
  exact canonical_l18_attention_residual_from_incoming_and_cache initSM initPM hPM1 hInit1 hIncoming hCache hAlias hDec
end
end TrainVerify.Denote.GeneratedPatterns
