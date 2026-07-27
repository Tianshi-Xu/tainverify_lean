/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.FaithfulPlainBridge
import denote.yoco_goals.Layer1DistributedMigration
import denote.yoco_goals.Goal5Bridge_Auto

/-!
# The head of the self-decoder chain

`goal_5` (tid `4680`) is the output of the vocab-parallel embedding: the single
model computes it in one shot, while the parallel model has each rank embed its
half of the table (offsets `0` and `77440`) and sums with an `AllReducePrim`.

Its existing proof, `goal_5_intermediate`, is stated over `denoteGraph` — the
base evaluator, one step further down the chain than the tracks used elsewhere
in this campaign. But nothing in the prefix producing `4680` is intercepted by
any evaluator (an embedding and an all-reduce), so `denote_faithful_eq_plain_of_prefix`
carries the result straight over.

This unblocks the head of the chain: `4680 → 4681 → 4683 → 7383/7392/…`.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_goal_5_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks goal_5
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hplain := goal_5_intermediate initSM initPM hSM hPM hInit
  -- SM node 0 is the embedding; nothing after it writes 4680, and the empty
  -- prefix trivially contains no intercepted operator.
  have hsm : denoteGraphDistributedFaithful sm initSM 4680 = denoteGraph sm initSM 4680 := by
    refine denote_faithful_eq_plain_of_prefix sm initSM 4680 1
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM node 26 is the all-reduce that produces 4680.
  have hpm : denoteGraphDistributedFaithful pm initPM 4680 = denoteGraph pm initPM 4680 := by
    refine denote_faithful_eq_plain_of_prefix pm initPM 4680 27
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  unfold InitGoalHolds at hplain ⊢
  simp only [goal_5, List.map] at hplain ⊢
  rw [hsm, hpm]
  exact hplain

end

end TrainVerify.Denote.GeneratedPatterns
