/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.FaithfulDistributedBridge
import denote.yoco_goals.Layer0DistributedMigration

/-!
# Self-decoder goals on the faithful track, by transport

The self-decoder region (SM 0–471, PM 0–1002) contains none of the three
operators on which the faithful evaluator differs from `applyNodeDistributed`, so
a goal whose writers all lie in that region has the same denotation under both.
`denote_faithful_eq_distributed_of_prefix` turns that observation into a rewrite,
and the existing `_distributed` results transport unchanged.

`4714` — the MoE all-to-all output of self-decoder block 0 — is the worked
example that fixes the pattern. Both sides are discharged by `native_decide` on
the generated graph:

* SM: last writer of `4714` is node 31, and `sm.nodes.take 32` is collective-free;
* PM: last writer is node 108, and `pm.nodes.take 109` is collective-free.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 1000000 in
private theorem sd_sm_4714_suffix : ∀ n ∈ sm.nodes.drop 32, n.outs ≠ [] := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sd_sm_4714_not_written : ∀ n ∈ sm.nodes.drop 32, (4714 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sd_sm_4714_prefix_clean : ∀ n ∈ sm.nodes.take 32,
    n.op ≠ "OpName.FW_maybe_shuffle" ∧
    n.op ≠ "OpName.FW_maybe_unshuffle" ∧
    n.op ≠ "OpName.FW_attn_zigzag" := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sd_pm_4714_suffix : ∀ n ∈ pm.nodes.drop 109, n.outs ≠ [] := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sd_pm_4714_not_written : ∀ n ∈ pm.nodes.drop 109, (4714 : Tid) ∉ n.outs := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem sd_pm_4714_prefix_clean : ∀ n ∈ pm.nodes.take 109,
    n.op ≠ "OpName.FW_maybe_shuffle" ∧
    n.op ≠ "OpName.FW_maybe_unshuffle" ∧
    n.op ≠ "OpName.FW_attn_zigzag" := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4714_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4714
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hsm : denoteGraphDistributedFaithful sm initSM 4714 =
      denoteGraphDistributed sm initSM 4714 :=
    denote_faithful_eq_distributed_of_prefix sm initSM 4714 32
      sd_sm_4714_suffix sd_sm_4714_not_written sd_sm_4714_prefix_clean
  have hpm : denoteGraphDistributedFaithful pm initPM 4714 =
      denoteGraphDistributed pm initPM 4714 :=
    denote_faithful_eq_distributed_of_prefix pm initPM 4714 109
      sd_pm_4714_suffix sd_pm_4714_not_written sd_pm_4714_prefix_clean
  have hd := recon_intermediateGoal_4714_distributed initSM initPM hSM hPM hInit
  exact InitGoalHolds_transfer_one_piece pm.numRanks intermediateGoal_4714
    rfl hsm hpm hd

end

end TrainVerify.Denote.GeneratedPatterns
