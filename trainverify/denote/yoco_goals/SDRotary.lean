/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.FaithfulReduce4
import denote.MultirefGeneral
import denote.yoco_goals.SDPH4685
import denote.yoco_goals.SDPH4687

/-!
# Rotary embedding

`FW_rotary_embedding` takes four inputs and produces two outputs, so it needs
`reduce4` plus the `fst`/`snd` projections.

One asymmetry: the SM node reads the cos/sin table as `4691`, the PM node as
`11853`. Those are not unrelated tids — `11853` is the first output of an
arity-12 `FW_multiref` off `4691`, so it reduces straight back to it.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def rotSm : NodeDecl :=
  { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687],
    outs := [4692, 4693], params := [16, 4] }

private def rotPm : NodeDecl :=
  { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687],
    outs := [4692, 4693], params := [16, 4] }

private def rotPmTable : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864],
    params := [12] }

set_option maxRecDepth 1000000 in
private theorem rot_sn : sm.nodes[8]'(by native_decide) = rotSm := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rot_pn : pm.nodes[42]'(by native_decide) = rotPm := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem rot_ptn : pm.nodes[14]'(by native_decide) = rotPmTable := by
  native_decide

-- The PM side reads `11853`, an output of the arity-12 fan-out of `4691`.
set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem rot_table_agree (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm initSM 4691 =
      denoteGraphDistributedFaithful pm initPM 11853 := by
  have r : denoteGraphDistributedFaithful pm initPM 11853 =
      denoteGraphDistributedFaithful pm initPM 4691 := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 14 rotPmTable 4691 11853
      (fun x => x) (by native_decide) rot_ptn ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
    intro st
    unfold rotPmTable
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_multiref_at pm st 1 4691 [11853, 11854, 11855, 11856, 11857, 11858, 11859, 11860, 11861, 11862, 11863, 11864] 12 rfl 11853 (by decide)
  rw [r]
  have hwg := hInit initGoal_4691 (by native_decide)
  have hs : denoteGraphDistributedFaithful sm initSM 4691 = initSM 4691 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 4691
      layer1_sm_nodes_nonempty (by native_decide)
  have hp : denoteGraphDistributedFaithful pm initPM 4691 = initPM 4691 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 4691
      layer1_pm_nodes_nonempty (by native_decide)
  rw [hs, hp]
  have := hwg.2.2
  rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at this
  exact this

-- `4690` (positions) is an init tid neither graph writes.
set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem rot_pos_agree (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributedFaithful sm initSM 4690 =
      denoteGraphDistributedFaithful pm initPM 4690 := by
  have hwg := hInit initGoal_4690 (by native_decide)
  have hs : denoteGraphDistributedFaithful sm initSM 4690 = initSM 4690 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM 4690
      layer1_sm_nodes_nonempty (by native_decide)
  have hp : denoteGraphDistributedFaithful pm initPM 4690 = initPM 4690 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM 4690
      layer1_pm_nodes_nonempty (by native_decide)
  rw [hs, hp]
  have := hwg.2.2
  rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at this
  exact this

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4692_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4692
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hq := recon_intermediateGoal_4685_faithful initSM initPM hSM hPM hInit
  have hk := recon_intermediateGoal_4687_faithful initSM initPM hSM hPM hInit
  have hqv : denoteGraphDistributedFaithful sm initSM 4685 =
      denoteGraphDistributedFaithful pm initPM 4685 := by
    have h := hq.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have hkv : denoteGraphDistributedFaithful sm initSM 4687 =
      denoteGraphDistributedFaithful pm initPM 4687 := by
    have h := hk.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have rSM : denoteGraphDistributedFaithful sm initSM 4692 =
      (fw_rotary_embedding (denoteGraphDistributedFaithful sm initSM 4691)
        (denoteGraphDistributedFaithful sm initSM 4690)
        (denoteGraphDistributedFaithful sm initSM 4685)
        (denoteGraphDistributedFaithful sm initSM 4687) 16 4).1 := by
    refine denoteGraphDistributedFaithful_reduce4 sm initSM 8 rotSm 4691 4690 4685 4687 4692
      (fun a b c d => (fw_rotary_embedding a b c d 16 4).1)
      (by native_decide) rot_sn ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    intro st
    unfold rotSm
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_rotary_embedding_fst_out sm st 0 16 4 4691 4690 4685 4687 4692 4693
  have rPM : denoteGraphDistributedFaithful pm initPM 4692 =
      (fw_rotary_embedding (denoteGraphDistributedFaithful pm initPM 11853)
        (denoteGraphDistributedFaithful pm initPM 4690)
        (denoteGraphDistributedFaithful pm initPM 4685)
        (denoteGraphDistributedFaithful pm initPM 4687) 16 4).1 := by
    refine denoteGraphDistributedFaithful_reduce4 pm initPM 42 rotPm 11853 4690 4685 4687 4692
      (fun a b c d => (fw_rotary_embedding a b c d 16 4).1)
      (by native_decide) rot_pn ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    intro st
    unfold rotPm
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_rotary_embedding_fst_out pm st 1 16 4 11853 4690 4685 4687 4692 4693
  have hval : denoteGraphDistributedFaithful sm initSM 4692 =
      denoteGraphDistributedFaithful pm initPM 4692 := by
    rw [rSM, rPM, rot_table_agree initSM initPM hInit, rot_pos_agree initSM initPM hInit,
      hqv, hkv]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4692).shape = [4096, 16, 64] := by
    rw [rSM, fw_rotary_embedding_fst_shape]
    exact (hq).1
  unfold InitGoalHolds
  simp only [intermediateGoal_4692, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_intermediateGoal_4693_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4693
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have hq := recon_intermediateGoal_4685_faithful initSM initPM hSM hPM hInit
  have hk := recon_intermediateGoal_4687_faithful initSM initPM hSM hPM hInit
  have hqv : denoteGraphDistributedFaithful sm initSM 4685 =
      denoteGraphDistributedFaithful pm initPM 4685 := by
    have h := hq.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have hkv : denoteGraphDistributedFaithful sm initSM 4687 =
      denoteGraphDistributedFaithful pm initPM 4687 := by
    have h := hk.2.2
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)] at h
    exact h
  have rSM : denoteGraphDistributedFaithful sm initSM 4693 =
      (fw_rotary_embedding (denoteGraphDistributedFaithful sm initSM 4691)
        (denoteGraphDistributedFaithful sm initSM 4690)
        (denoteGraphDistributedFaithful sm initSM 4685)
        (denoteGraphDistributedFaithful sm initSM 4687) 16 4).2 := by
    refine denoteGraphDistributedFaithful_reduce4 sm initSM 8 rotSm 4691 4690 4685 4687 4693
      (fun a b c d => (fw_rotary_embedding a b c d 16 4).2)
      (by native_decide) rot_sn ?_
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    intro st
    unfold rotSm
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_rotary_embedding_snd_out sm st 0 16 4 4691 4690 4685 4687 4692 4693 (by decide)
  have rPM : denoteGraphDistributedFaithful pm initPM 4693 =
      (fw_rotary_embedding (denoteGraphDistributedFaithful pm initPM 11853)
        (denoteGraphDistributedFaithful pm initPM 4690)
        (denoteGraphDistributedFaithful pm initPM 4685)
        (denoteGraphDistributedFaithful pm initPM 4687) 16 4).2 := by
    refine denoteGraphDistributedFaithful_reduce4 pm initPM 42 rotPm 11853 4690 4685 4687 4693
      (fun a b c d => (fw_rotary_embedding a b c d 16 4).2)
      (by native_decide) rot_pn ?_
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (fun n hn => layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    intro st
    unfold rotPm
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_rotary_embedding_snd_out pm st 1 16 4 11853 4690 4685 4687 4692 4693 (by decide)
  have hval : denoteGraphDistributedFaithful sm initSM 4693 =
      denoteGraphDistributedFaithful pm initPM 4693 := by
    rw [rSM, rPM, rot_table_agree initSM initPM hInit, rot_pos_agree initSM initPM hInit,
      hqv, hkv]
  have hshape : (denoteGraphDistributedFaithful sm initSM 4693).shape = [4096, 4, 64] := by
    rw [rSM, fw_rotary_embedding_snd_shape]
    exact (hk).1
  unfold InitGoalHolds
  simp only [intermediateGoal_4693, List.map]
  exact ⟨hshape, by rw [← hval]; exact congrArg (fun z => [z]) hshape,
    by rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
       simp only [reconstructWithDim]
       exact hval⟩

end

end TrainVerify.Denote.GeneratedPatterns
