/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.GeneratedMultirefCertificates
import denote.yoco_goals.SDRegionBridge
import denote.yoco_goals.SDTLayer6C_0

/-!
# Two-shard fan-out goals, reduced from their faithful parents

The replicated case is handled in `SDFanOutRep`. This is the other shape: the
parent goal is a genuine two-shard gather, and the multiref simply forwards each
rank's shard. Both sides reduce with `applyNode_fw_multiref_at`, and the
reconstruction is the parent's, unchanged — so the goal follows without touching
`reconstructWithDim` at all.

`7747` fixes the template: SM node 275 forwards `5060`, PM nodes 611/612 forward
that goal's two shards `8695` / `8696`.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_7747_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7747
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hparent := recon_intermediateGoal_5060_faithful initSM initPM hSM hPM hInit
  have rSM : denoteGraphDistributedFaithful sm initSM 7747 =
      denoteGraphDistributedFaithful sm initSM 5060 :=
    denoteGraphDistributedFaithful_multiref sm initSM multirefCert_sm_7747_7747
  have rPM0 : denoteGraphDistributedFaithful pm initPM 15221 =
      denoteGraphDistributedFaithful pm initPM 8695 :=
    denoteGraphDistributedFaithful_multiref pm initPM multirefCert_pm_7747_15221
  have rPM1 : denoteGraphDistributedFaithful pm initPM 15229 =
      denoteGraphDistributedFaithful pm initPM 8696 :=
    denoteGraphDistributedFaithful_multiref pm initPM multirefCert_pm_7747_15229
  -- The goal's reconstruction is the parent's with each tid rewritten, so the
  -- parent's three components transfer directly.
  obtain ⟨h1, h2, h3⟩ := hparent
  unfold InitGoalHolds
  simp only [intermediateGoal_7747, List.map]
  refine ⟨?_, ?_, ?_⟩
  · rw [rSM]; exact h1
  · rw [rPM0, rPM1]
    simpa [intermediateGoal_5060, List.map] using h2
  · show denoteGraphDistributedFaithful sm initSM 7747 =
      reconstructForGoal intermediateGoal_7747 pm.numRanks
        [denoteGraphDistributedFaithful pm initPM 15221,
         denoteGraphDistributedFaithful pm initPM 15229]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl), rSM, rPM0, rPM1]
    have h3' := h3
    unfold InitGoalHolds at h3'
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h3'
    simpa [intermediateGoal_5060, intermediateGoal_7747, List.map] using h3'

end

end TrainVerify.Denote.GeneratedPatterns
