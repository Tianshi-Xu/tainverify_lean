import denote.yoco3b_heldout.Goal_2

open TrainVerify.Denote

namespace TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal1

def smInputValueClasses : List InputValueClass := [
  { source := "yoco3b:cu-seqlens", tids := [6304, 6305, 6350, 6351, 6396, 6397, 6442, 6443, 6488, 6489, 6534, 6535, 6580, 6581, 6626, 6627, 6672, 6673, 6718, 6719, 6757, 6758, 6791, 6792, 6825, 6826, 6859, 6860, 6893, 6894, 6927, 6928, 6961, 6962, 6995, 6996, 7029, 7030, 7063, 7064, 7097, 7098, 7131, 7132, 7165, 7166, 7199, 7200, 7233, 7234, 7267, 7268, 7301, 7302, 7335, 7336, 7369, 7370, 7403, 7404, 7432, 7443, 7444, 7480, 7481, 7517, 7518, 7554, 7555, 7591, 7592, 7628, 7629, 7665, 7666, 7702, 7703, 7739, 7740, 7776, 7777, 7804] }
]

def pmInputValueClasses : List InputValueClass := [
  { source := "yoco3b:cu-seqlens", tids := [6304, 6305, 6350, 6351, 6396, 6397, 6442, 6443, 6488, 6489, 6534, 6535, 6580, 6581, 6626, 6627, 6672, 6673, 6718, 6719, 6757, 6758, 6791, 6792, 6825, 6826, 6859, 6860, 6893, 6894, 6927, 6928, 6961, 6962, 6995, 6996, 7029, 7030, 7063, 7064, 7097, 7098, 7131, 7132, 7165, 7166, 7199, 7200, 7233, 7234, 7267, 7268, 7301, 7302, 7335, 7336, 7369, 7370, 7403, 7404, 7432, 7443, 7444, 7480, 7481, 7517, 7518, 7554, 7555, 7591, 7592, 7628, 7629, 7665, 7666, 7702, 7703, 7739, 7740, 7776, 7777, 7804] }
]

/-- Caller-certified external assumptions required by the faithful full Goal 1 statement.
The metadata identity is intentionally inherited from the pinned held-out caller contract;
it is not presented as recovered generator provenance. -/
def Goal1ExternalInputContract (initSM initPM : Store) : Prop :=
  InputValueClassesHold
      TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal2.smInputValueClasses initSM ∧
  InputValueClassesHold
      TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal2.pmInputValueClasses initPM ∧
  ZigzagCollective.PackedCuSeqlensWF (initPM 7804) 8192 2 ∧
  (∀ l < 8192, scalarToNat (valAt (initPM 6281) l) < 154880)

def goal_1_full_initGoals : List LineageGoal := Generated.initGoals

def goal_1_stmt_full : Prop :=
  CoarseLineageHoldsWithInitDistributedFaithfulWithContract
    Generated.sm Generated.pm Generated.goal_1
    Generated.smInitEnv Generated.pmInitEnv goal_1_full_initGoals
    Goal1ExternalInputContract

end TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal1
