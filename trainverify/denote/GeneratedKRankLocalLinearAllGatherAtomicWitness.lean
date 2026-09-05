/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def input_0 : RelationFact :=
  .sharded 100 [200, 201, 202] 1 [2, 9, 5] [2, 3, 5]

private def output_0 : RelationFact :=
  .sharded 300 [400, 401, 402] 1 [2, 9, 7] [2, 3, 7]

private def input_1 : RelationFact :=
  .sharded 101 [210, 211, 212] 1 [2, 9, 5] [2, 3, 5]

private def output_1 : RelationFact :=
  .sharded 301 [410, 411, 412] 1 [2, 9, 7] [2, 3, 7]

private def joined : RelationFact :=
  .joined 300 900 [2, 9, 7]

private def weight_eq_0 : RelationFact :=
  .tensorEq .sm 500 .pm 500

private def weight_shape_0 : RelationFact :=
  .tensorShape .pm 500 [7, 5]

private def weight_eq_1 : RelationFact :=
  .tensorEq .sm 501 .pm 501

private def weight_shape_1 : RelationFact :=
  .tensorShape .pm 501 [7, 5]

private def anchor : RelationFact :=
  .tensorShape .sm 100 [2, 9, 5]

private def state_pre : RelationState where
  facts := [input_0, input_1, weight_eq_0, weight_shape_0, weight_eq_1, weight_shape_1]
  nonempty := by decide

private def state_post : RelationState where
  facts := [output_1, joined]
  nonempty := by decide

end
end TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness

namespace TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] }, { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }] }
private def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }, { rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }, { rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401, 402], outs := [900], params := [1] }, { rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] }] }
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
private def segment_generic_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] }, { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }]
private def segment_generic_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }, { rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }, { rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401, 402], outs := [900], params := [1] }, { rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] }]
@[irreducible] private def segment_generic_smFinal (smStore : Store) : Store :=
  segment_generic_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore
@[irreducible] private def segment_generic_pmFinal (pmStore : Store) : Store :=
  segment_generic_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore

private theorem segment_generic_frame (smStore pmStore : Store)
    (hstate : state_pre.Holds smStore pmStore) :
    state_pre.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore) := by
  unfold segment_generic_smFinal segment_generic_pmFinal
  apply RelationState.Holds.fold_frame segment_generic_sm_nodes segment_generic_pm_nodes smStore pmStore hstate
  · native_decide
  · native_decide
  · native_decide
  · native_decide

private theorem segment_generic_sm_linear_writer_1 (smStore : Store) :
    segment_generic_smFinal smStore 300 = fw_linear (segment_generic_smFinal smStore 100) (segment_generic_smFinal smStore 500) := by
  unfold segment_generic_smFinal
  let smNodes : List NodeDecl := segment_generic_sm_nodes
  let smFinal := smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore
  change smFinal 300 = fw_linear (smFinal 100) (smFinal 500)
  have hPrefix1_0 : ((smNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore) 100 = smFinal 100 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph (smNodes.drop 1) ((smNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore) 100 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show smNodes.take 1 ++ smNodes.drop 1 = smNodes by exact List.take_append_drop 1 smNodes] at h
    exact h.symm
  have hPrefix1_1 : ((smNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore) 500 = smFinal 500 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph (smNodes.drop 1) ((smNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore) 500 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show smNodes.take 1 ++ smNodes.drop 1 = smNodes by exact List.take_append_drop 1 smNodes] at h
    exact h.symm
  change (smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore) 300 = _
  rw [show smNodes = smNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] }] ++ smNodes.drop 2 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph smStore (smNodes.take 1) (smNodes.drop 2)
    { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [300] } 300 (fun t => fw_linear (t 100) (t 500)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph t 0 100 500 300
    ) (by native_decide) (by native_decide)]
  rw [hPrefix1_0, hPrefix1_1]

private theorem segment_generic_pm_linear_writer_2 (pmStore : Store) :
    segment_generic_pmFinal pmStore 400 = fw_linear (segment_generic_pmFinal pmStore 200) (segment_generic_pmFinal pmStore 500) := by
  unfold segment_generic_pmFinal
  let pmNodes : List NodeDecl := segment_generic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore
  change pmFinal 400 = fw_linear (pmFinal 200) (pmFinal 500)
  have hPrefix2_0 : ((pmNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 200 = pmFinal 200 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 0) ((pmNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 200 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 0 ++ pmNodes.drop 0 = pmNodes by exact List.take_append_drop 0 pmNodes] at h
    exact h.symm
  have hPrefix2_1 : ((pmNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 500 = pmFinal 500 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 0) ((pmNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 500 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 0 ++ pmNodes.drop 0 = pmNodes by exact List.take_append_drop 0 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 400 = _
  rw [show pmNodes = pmNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] }] ++ pmNodes.drop 1 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
    { rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [400] } 400 (fun t => fw_linear (t 200) (t 500)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph t 0 200 500 400
    ) (by native_decide) (by native_decide)]
  rw [hPrefix2_0, hPrefix2_1]

private theorem segment_generic_pm_linear_writer_3 (pmStore : Store) :
    segment_generic_pmFinal pmStore 401 = fw_linear (segment_generic_pmFinal pmStore 201) (segment_generic_pmFinal pmStore 500) := by
  unfold segment_generic_pmFinal
  let pmNodes : List NodeDecl := segment_generic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore
  change pmFinal 401 = fw_linear (pmFinal 201) (pmFinal 500)
  have hPrefix3_0 : ((pmNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 201 = pmFinal 201 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 2) ((pmNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 201 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 2 ++ pmNodes.drop 2 = pmNodes by exact List.take_append_drop 2 pmNodes] at h
    exact h.symm
  have hPrefix3_1 : ((pmNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 500 = pmFinal 500 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 2) ((pmNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 500 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 2 ++ pmNodes.drop 2 = pmNodes by exact List.take_append_drop 2 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 401 = _
  rw [show pmNodes = pmNodes.take 2 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] }] ++ pmNodes.drop 3 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
    { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [401] } 401 (fun t => fw_linear (t 201) (t 500)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph t 1 201 500 401
    ) (by native_decide) (by native_decide)]
  rw [hPrefix3_0, hPrefix3_1]

private theorem segment_generic_pm_linear_writer_4 (pmStore : Store) :
    segment_generic_pmFinal pmStore 402 = fw_linear (segment_generic_pmFinal pmStore 202) (segment_generic_pmFinal pmStore 500) := by
  unfold segment_generic_pmFinal
  let pmNodes : List NodeDecl := segment_generic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore
  change pmFinal 402 = fw_linear (pmFinal 202) (pmFinal 500)
  have hPrefix4_0 : ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 202 = pmFinal 202 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 4) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 202 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 4 ++ pmNodes.drop 4 = pmNodes by exact List.take_append_drop 4 pmNodes] at h
    exact h.symm
  have hPrefix4_1 : ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 500 = pmFinal 500 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 4) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 500 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 4 ++ pmNodes.drop 4 = pmNodes by exact List.take_append_drop 4 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 402 = _
  rw [show pmNodes = pmNodes.take 4 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] }] ++ pmNodes.drop 5 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph pmStore (pmNodes.take 4) (pmNodes.drop 5)
    { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [402] } 402 (fun t => fw_linear (t 202) (t 500)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph t 2 202 500 402
    ) (by native_decide) (by native_decide)]
  rw [hPrefix4_0, hPrefix4_1]

private theorem segment_generic_sm_linear_writer_5 (smStore : Store) :
    segment_generic_smFinal smStore 301 = fw_linear (segment_generic_smFinal smStore 101) (segment_generic_smFinal smStore 501) := by
  unfold segment_generic_smFinal
  let smNodes : List NodeDecl := segment_generic_sm_nodes
  let smFinal := smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore
  change smFinal 301 = fw_linear (smFinal 101) (smFinal 501)
  have hPrefix5_0 : ((smNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore) 101 = smFinal 101 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph (smNodes.drop 0) ((smNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore) 101 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show smNodes.take 0 ++ smNodes.drop 0 = smNodes by exact List.take_append_drop 0 smNodes] at h
    exact h.symm
  have hPrefix5_1 : ((smNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore) 501 = smFinal 501 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph (smNodes.drop 0) ((smNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore) 501 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show smNodes.take 0 ++ smNodes.drop 0 = smNodes by exact List.take_append_drop 0 smNodes] at h
    exact h.symm
  change (smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph) smStore) 301 = _
  rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] }] ++ smNodes.drop 1 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph smStore (smNodes.take 0) (smNodes.drop 1)
    { rank := 0, op := "OpName.FW_linear", ins := [101, 501], outs := [301] } 301 (fun t => fw_linear (t 101) (t 501)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph t 0 101 501 301
    ) (by native_decide) (by native_decide)]
  rw [hPrefix5_0, hPrefix5_1]

private theorem segment_generic_pm_linear_writer_6 (pmStore : Store) :
    segment_generic_pmFinal pmStore 410 = fw_linear (segment_generic_pmFinal pmStore 210) (segment_generic_pmFinal pmStore 501) := by
  unfold segment_generic_pmFinal
  let pmNodes : List NodeDecl := segment_generic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore
  change pmFinal 410 = fw_linear (pmFinal 210) (pmFinal 501)
  have hPrefix6_0 : ((pmNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 210 = pmFinal 210 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 1) ((pmNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 210 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 1 ++ pmNodes.drop 1 = pmNodes by exact List.take_append_drop 1 pmNodes] at h
    exact h.symm
  have hPrefix6_1 : ((pmNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 501 = pmFinal 501 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 1) ((pmNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 501 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 1 ++ pmNodes.drop 1 = pmNodes by exact List.take_append_drop 1 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 410 = _
  rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] }] ++ pmNodes.drop 2 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2)
    { rank := 0, op := "OpName.FW_linear", ins := [210, 501], outs := [410] } 410 (fun t => fw_linear (t 210) (t 501)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph t 0 210 501 410
    ) (by native_decide) (by native_decide)]
  rw [hPrefix6_0, hPrefix6_1]

private theorem segment_generic_pm_linear_writer_7 (pmStore : Store) :
    segment_generic_pmFinal pmStore 411 = fw_linear (segment_generic_pmFinal pmStore 211) (segment_generic_pmFinal pmStore 501) := by
  unfold segment_generic_pmFinal
  let pmNodes : List NodeDecl := segment_generic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore
  change pmFinal 411 = fw_linear (pmFinal 211) (pmFinal 501)
  have hPrefix7_0 : ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 211 = pmFinal 211 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 3) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 211 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 3 ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
    exact h.symm
  have hPrefix7_1 : ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 501 = pmFinal 501 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 3) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 501 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 3 ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 411 = _
  rw [show pmNodes = pmNodes.take 3 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] }] ++ pmNodes.drop 4 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph pmStore (pmNodes.take 3) (pmNodes.drop 4)
    { rank := 1, op := "OpName.FW_linear", ins := [211, 501], outs := [411] } 411 (fun t => fw_linear (t 211) (t 501)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph t 1 211 501 411
    ) (by native_decide) (by native_decide)]
  rw [hPrefix7_0, hPrefix7_1]

private theorem segment_generic_pm_linear_writer_8 (pmStore : Store) :
    segment_generic_pmFinal pmStore 412 = fw_linear (segment_generic_pmFinal pmStore 212) (segment_generic_pmFinal pmStore 501) := by
  unfold segment_generic_pmFinal
  let pmNodes : List NodeDecl := segment_generic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore
  change pmFinal 412 = fw_linear (pmFinal 212) (pmFinal 501)
  have hPrefix8_0 : ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 212 = pmFinal 212 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 6) ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 212 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 6 ++ pmNodes.drop 6 = pmNodes by exact List.take_append_drop 6 pmNodes] at h
    exact h.symm
  have hPrefix8_1 : ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 501 = pmFinal 501 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 6) ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 501 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 6 ++ pmNodes.drop 6 = pmNodes by exact List.take_append_drop 6 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 412 = _
  rw [show pmNodes = pmNodes.take 6 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] }] ++ pmNodes.drop 7 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph pmStore (pmNodes.take 6) (pmNodes.drop 7)
    { rank := 2, op := "OpName.FW_linear", ins := [212, 501], outs := [412] } 412 (fun t => fw_linear (t 212) (t 501)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph t 2 212 501 412
    ) (by native_decide) (by native_decide)]
  rw [hPrefix8_0, hPrefix8_1]

private theorem segment_generic_pm_gather_writer_0 (pmStore : Store) :
    segment_generic_pmFinal pmStore 900 = allGatherPrimDimN 1 3 0 [segment_generic_pmFinal pmStore 400, segment_generic_pmFinal pmStore 401, segment_generic_pmFinal pmStore 402] := by
  unfold segment_generic_pmFinal
  let pmNodes : List NodeDecl := segment_generic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore
  change pmFinal 900 = allGatherPrimDimN 1 3 0 [pmFinal 400, pmFinal 401, pmFinal 402]
  have hGatherPrefix0_0 : ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 400 = pmFinal 400 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 5) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 400 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 5 ++ pmNodes.drop 5 = pmNodes by exact List.take_append_drop 5 pmNodes] at h
    exact h.symm
  have hGatherPrefix0_1 : ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 401 = pmFinal 401 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 5) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 401 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 5 ++ pmNodes.drop 5 = pmNodes by exact List.take_append_drop 5 pmNodes] at h
    exact h.symm
  have hGatherPrefix0_2 : ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 402 = pmFinal 402 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph (pmNodes.drop 5) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 402 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 5 ++ pmNodes.drop 5 = pmNodes by exact List.take_append_drop 5 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph) pmStore) 900 = _
  rw [show pmNodes = pmNodes.take 5 ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401, 402], outs := [900], params := [1] }] ++ pmNodes.drop 6 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph pmStore (pmNodes.take 5) (pmNodes.drop 6)
    { rank := 0, op := "OpName.AllGatherPrim", ins := [400, 401, 402], outs := [900], params := [1] } 900 (fun t => allGatherPrimDimN 1 3 0 [t 400, t 401, t 402]) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_allGatherPrimDimN_out TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph t 0 [400, 401, 402] 900 1
    ) (by native_decide) (by native_decide)]
  rw [hGatherPrefix0_0, hGatherPrefix0_1, hGatherPrefix0_2]

private theorem segment_generic_transition_0_ll (smStore pmStore : Store)
    (hframe : state_pre.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore))
    : output_0.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore) := by
    let smFinal := segment_generic_smFinal smStore
    let pmFinal := segment_generic_pmFinal pmStore
    have hLocalIn0 : input_0.Holds smFinal pmFinal := hframe input_0 (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 200, pmFinal 201, pmFinal 202] 1 [2, 9, 5] [2, 3, 5] at hLocalIn0
    have hLocalEq0 : weight_eq_0.Holds smFinal pmFinal := hframe _ (by native_decide)
    change smFinal 500 = pmFinal 500 at hLocalEq0
    have hLocalWeightShape0 : weight_shape_0.Holds smFinal pmFinal := hframe _ (by native_decide)
    change (pmFinal 500).shape = [7, 5] at hLocalWeightShape0
    have hLocalSm0 : smFinal 300 = fw_linear (smFinal 100) (smFinal 500) := segment_generic_sm_linear_writer_1 smStore
    have hLocalPm0_0 : pmFinal 400 = fw_linear (pmFinal 200) (pmFinal 500) := segment_generic_pm_linear_writer_2 pmStore
    have hLocalPm0_1 : pmFinal 401 = fw_linear (pmFinal 201) (pmFinal 500) := segment_generic_pm_linear_writer_3 pmStore
    have hLocalPm0_2 : pmFinal 402 = fw_linear (pmFinal 202) (pmFinal 500) := segment_generic_pm_linear_writer_4 pmStore
    have hLocalComm0 := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmFinal 200, pmFinal 201, pmFinal 202].length) (b := 2) (s := 3) (i := 5) (o := 7) (xs := [pmFinal 200, pmFinal 201, pmFinal 202]) (w := pmFinal 500) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hLocalIn0.shard_shapes x hx) hLocalWeightShape0)
    have hLocalValue0 : smFinal 300 = allGatherPrimDimN 1 [pmFinal 400, pmFinal 401, pmFinal 402].length 0 [pmFinal 400, pmFinal 401, pmFinal 402] := by
      rw [hLocalSm0, hLocalEq0, hLocalIn0.full_value, hLocalComm0]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLocalPm0_0, ← hLocalPm0_1, ← hLocalPm0_2]
    have hLocalShape0_0 : (pmFinal 400).shape = [2, 3, 7] := by
      rw [hLocalPm0_0]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hLocalIn0.shard_shapes _ (by simp)) hLocalWeightShape0
    have hLocalShape0_1 : (pmFinal 401).shape = [2, 3, 7] := by
      rw [hLocalPm0_1]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hLocalIn0.shard_shapes _ (by simp)) hLocalWeightShape0
    have hLocalShape0_2 : (pmFinal 402).shape = [2, 3, 7] := by
      rw [hLocalPm0_2]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hLocalIn0.shard_shapes _ (by simp)) hLocalWeightShape0
    have hLocalOut0 : output_0.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 400, pmFinal 401, pmFinal 402] 1 [2, 9, 7] [2, 3, 7]
      refine { full_value := hLocalValue0, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hLocalValue0, allGatherPrimDimN_shape 1 [pmFinal 400, pmFinal 401, pmFinal 402].length [pmFinal 400, pmFinal 401, pmFinal 402] [2, 3, 7]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]; exact hLocalShape0_0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hLocalShape0_0
        · exact hLocalShape0_1
        · exact hLocalShape0_2
    exact hLocalOut0

private theorem segment_generic_transition_1_ll (smStore pmStore : Store)
    (hframe : state_pre.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore))
    : output_1.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore) := by
    let smFinal := segment_generic_smFinal smStore
    let pmFinal := segment_generic_pmFinal pmStore
    have hLocalIn1 : input_1.Holds smFinal pmFinal := hframe input_1 (by native_decide)
    change ShardedRel (smFinal 101) [pmFinal 210, pmFinal 211, pmFinal 212] 1 [2, 9, 5] [2, 3, 5] at hLocalIn1
    have hLocalEq1 : weight_eq_1.Holds smFinal pmFinal := hframe _ (by native_decide)
    change smFinal 501 = pmFinal 501 at hLocalEq1
    have hLocalWeightShape1 : weight_shape_1.Holds smFinal pmFinal := hframe _ (by native_decide)
    change (pmFinal 501).shape = [7, 5] at hLocalWeightShape1
    have hLocalSm1 : smFinal 301 = fw_linear (smFinal 101) (smFinal 501) := segment_generic_sm_linear_writer_5 smStore
    have hLocalPm1_0 : pmFinal 410 = fw_linear (pmFinal 210) (pmFinal 501) := segment_generic_pm_linear_writer_6 pmStore
    have hLocalPm1_1 : pmFinal 411 = fw_linear (pmFinal 211) (pmFinal 501) := segment_generic_pm_linear_writer_7 pmStore
    have hLocalPm1_2 : pmFinal 412 = fw_linear (pmFinal 212) (pmFinal 501) := segment_generic_pm_linear_writer_8 pmStore
    have hLocalComm1 := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmFinal 210, pmFinal 211, pmFinal 212].length) (b := 2) (s := 3) (i := 5) (o := 7) (xs := [pmFinal 210, pmFinal 211, pmFinal 212]) (w := pmFinal 501) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hLocalIn1.shard_shapes x hx) hLocalWeightShape1)
    have hLocalValue1 : smFinal 301 = allGatherPrimDimN 1 [pmFinal 410, pmFinal 411, pmFinal 412].length 0 [pmFinal 410, pmFinal 411, pmFinal 412] := by
      rw [hLocalSm1, hLocalEq1, hLocalIn1.full_value, hLocalComm1]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLocalPm1_0, ← hLocalPm1_1, ← hLocalPm1_2]
    have hLocalShape1_0 : (pmFinal 410).shape = [2, 3, 7] := by
      rw [hLocalPm1_0]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hLocalIn1.shard_shapes _ (by simp)) hLocalWeightShape1
    have hLocalShape1_1 : (pmFinal 411).shape = [2, 3, 7] := by
      rw [hLocalPm1_1]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hLocalIn1.shard_shapes _ (by simp)) hLocalWeightShape1
    have hLocalShape1_2 : (pmFinal 412).shape = [2, 3, 7] := by
      rw [hLocalPm1_2]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hLocalIn1.shard_shapes _ (by simp)) hLocalWeightShape1
    have hLocalOut1 : output_1.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 301) [pmFinal 410, pmFinal 411, pmFinal 412] 1 [2, 9, 7] [2, 3, 7]
      refine { full_value := hLocalValue1, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hLocalValue1, allGatherPrimDimN_shape 1 [pmFinal 410, pmFinal 411, pmFinal 412].length [pmFinal 410, pmFinal 411, pmFinal 412] [2, 3, 7]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]; exact hLocalShape1_0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hLocalShape1_0
        · exact hLocalShape1_1
        · exact hLocalShape1_2
    exact hLocalOut1

private theorem segment_generic_transition_2_ag (smStore pmStore : Store)
    (hframe : state_pre.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore))
    (hFact0 : output_0.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore))
    : joined.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore) := by
    let smFinal := segment_generic_smFinal smStore
    let pmFinal := segment_generic_pmFinal pmStore
    have hGatherIn0 : output_0.Holds smFinal pmFinal := hFact0
    change ShardedRel (smFinal 300) [pmFinal 400, pmFinal 401, pmFinal 402] 1 [2, 9, 7] [2, 3, 7] at hGatherIn0
    have hGatherWriter0 : pmFinal 900 = allGatherPrimDimN 1 3 0 [pmFinal 400, pmFinal 401, pmFinal 402] := segment_generic_pm_gather_writer_0 pmStore
    have hJoinedValue0 : smFinal 300 = pmFinal 900 := by
      rw [TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather hGatherIn0]
      simp only [List.length_cons, List.length_nil]
      exact hGatherWriter0.symm
    have hJoinedOut0 : joined.Holds smFinal pmFinal := by
      change smFinal 300 = pmFinal 900 ∧ (smFinal 300).shape = [2, 9, 7] ∧ (pmFinal 900).shape = [2, 9, 7]
      refine ⟨hJoinedValue0, hGatherIn0.full_shape, ?_⟩
      rw [← hJoinedValue0]
      exact hGatherIn0.full_shape
    exact hJoinedOut0

private theorem segment_generic_publish_state (smStore pmStore : Store)
    (hstate : state_pre.Holds smStore pmStore) :
    state_post.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore) := by
    have hframe := segment_generic_frame smStore pmStore hstate
    have hFact0 : output_0.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore) := segment_generic_transition_0_ll smStore pmStore hframe
    have hFact1 : output_1.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore) := segment_generic_transition_1_ll smStore pmStore hframe
    have hFact2 : joined.Holds (segment_generic_smFinal smStore) (segment_generic_pmFinal pmStore) := segment_generic_transition_2_ag smStore pmStore hframe hFact0
    intro fact hfact
    have covered : fact ∈ [output_1, joined] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [output_1, joined] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · exact hFact1
      · exact hFact2
    · exact hframe fact old

private def segment_generic : ClosedDepSegmentCertificate TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.smGraph TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness.pmGraph state_pre state_post where
  smNodes := segment_generic_sm_nodes
  pmNodes := segment_generic_pm_nodes
  sound := by
    intro smStore pmStore hstate
    simpa [segment_generic_smFinal, segment_generic_pmFinal] using
      (segment_generic_publish_state smStore pmStore hstate)

#print axioms segment_generic
end
end TrainVerify.Denote.GeneratedKRankLocalLinearAllGatherAtomicWitness
