/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler
import denote.InputValueClasses

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GPTKInit

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_000001 : RelationFact :=
  .sharded 1603 [3057, 3058, 3059, 3060] 1 [100, 16] [100, 4]

private def anchor_sm_shape_1603 : RelationFact :=
  .tensorShape .sm 1603 [100, 16]

private def state_000000 : RelationState where
  facts := [anchor_sm_shape_1603, fact_000001]
  nonempty := by decide

private def state_000001 : RelationState where
  facts := [anchor_sm_shape_1603]
  nonempty := by decide

end
end TrainVerify.Denote.GPTKInit


open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.Generated
def sm : GraphDecl := { numRanks := 1, nodes := [], replicaGroups := [] }
def pm : GraphDecl := { numRanks := 4, nodes := [], replicaGroups := [] }
def smInputValueClasses : List InputValueClass := []
def pmInputValueClasses : List InputValueClass := []
def smInitEnv : ShapeEnv := shapeEnvOfList [(1603, [100, 16])]
def pmInitEnv : ShapeEnv := shapeEnvOfList [(3057, [100, 4]), (3058, [100, 4]), (3059, [100, 4]), (3060, [100, 4])]
def initGoal_1603 : LineageGoal := { ts := 1603, tsShape := [100, 16], tps := [{ rank := 0, tid := 3057 }, { rank := 1, tid := 3058 }, { rank := 2, tid := 3059 }, { rank := 3, tid := 3060 }], tpShapes := [[100, 4], [100, 4], [100, 4], [100, 4]], gatherDim := 1 }
def initGoals : List LineageGoal := [initGoal_1603]
end TrainVerify.Denote.Generated


namespace TrainVerify.Denote.GPTKInit

private theorem GPTKInit_anchor_sm_shape_1603_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM TrainVerify.Denote.Generated.smInitEnv)
    (hPM : StoreShapesHold initPM TrainVerify.Denote.Generated.pmInitEnv)
    (hInit : InitGoalsHold TrainVerify.Denote.Generated.pm.numRanks TrainVerify.Denote.Generated.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold TrainVerify.Denote.Generated.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold TrainVerify.Denote.Generated.pmInputValueClasses initPM)
    : anchor_sm_shape_1603.Holds initSM initPM := by
  unfold anchor_sm_shape_1603 RelationFact.Holds StoreSide.read
  exact hSM 1603 [100, 16] (by native_decide)
private theorem GPTKInit_fact_000001_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM TrainVerify.Denote.Generated.smInitEnv)
    (hPM : StoreShapesHold initPM TrainVerify.Denote.Generated.pmInitEnv)
    (hInit : InitGoalsHold TrainVerify.Denote.Generated.pm.numRanks TrainVerify.Denote.Generated.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold TrainVerify.Denote.Generated.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold TrainVerify.Denote.Generated.pmInputValueClasses initPM)
    : fact_000001.Holds initSM initPM := by
  unfold fact_000001 RelationFact.Holds StoreSide.read
  -- ordered PM TIDs: [3057, 3058, 3059, 3060]
  have hi := hInit TrainVerify.Denote.Generated.initGoal_1603 (by native_decide)
  have htps : TrainVerify.Denote.Generated.initGoal_1603.tps = [{ rank := 0, tid := 3057 }, { rank := 1, tid := 3058 }, { rank := 2, tid := 3059 }, { rank := 3, tid := 3060 }] := by native_decide
  have hfull := hSM 1603 [100, 16] (by native_decide)
  have hp0 := hPM 3057 [100, 4] (by native_decide)
  have hp1 := hPM 3058 [100, 4] (by native_decide)
  have hp2 := hPM 3059 [100, 4] (by native_decide)
  have hp3 := hPM 3060 [100, 4] (by native_decide)
  have hrel := ShardedRel.of_init_goal TrainVerify.Denote.Generated.pm.numRanks TrainVerify.Denote.Generated.initGoal_1603 initSM initPM 1 [100, 16] [100, 4]
    hi (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by
      rw [htps]
      simp only [List.map_cons, List.map_nil, List.head?_cons,
        Option.map_some, Option.getD_some]
      rw [hp0]
      native_decide)
    hfull
    (by
      intro shard hshard
      rw [htps] at hshard
      simp only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hshard
      rcases hshard with rfl | hshard
      · exact hp0
      rcases hshard with rfl | hshard
      · exact hp1
      rcases hshard with rfl | hshard
      · exact hp2
      subst shard
      exact hp3)
    (by native_decide) (by native_decide)
  simpa [TrainVerify.Denote.Generated.initGoal_1603] using hrel
private theorem GPTKInit_initial_state
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM TrainVerify.Denote.Generated.smInitEnv)
    (hPM : StoreShapesHold initPM TrainVerify.Denote.Generated.pmInitEnv)
    (hInit : InitGoalsHold TrainVerify.Denote.Generated.pm.numRanks TrainVerify.Denote.Generated.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold TrainVerify.Denote.Generated.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold TrainVerify.Denote.Generated.pmInputValueClasses initPM)
    : state_000000.Holds initSM initPM := by
  intro fact hfact
  unfold state_000000 at hfact
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfact
  rcases hfact with rfl | hfact
  · exact GPTKInit_anchor_sm_shape_1603_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues
  subst fact
  exact GPTKInit_fact_000001_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues

end TrainVerify.Denote.GPTKInit
