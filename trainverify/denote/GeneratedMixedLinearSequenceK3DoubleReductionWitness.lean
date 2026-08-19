/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def local_in : RelationFact :=
  .sharded 100 [200, 201, 202] 1 [2, 6, 5] [2, 2, 5]

private def local_out : RelationFact :=
  .sharded 101 [210, 211, 212] 1 [2, 6, 6] [2, 2, 6]

private def a2a1_out : RelationFact :=
  .sharded 101 [213, 214, 215] 2 [2, 6, 6] [2, 6, 2]

private def weight1 : RelationFact :=
  .sharded 130 [230, 231, 232] 1 [7, 6] [7, 2]

private def reduction1 : RelationFact :=
  .reduction 102 [240, 241, 242] [2, 6, 7]

private def a2a2_in : RelationFact :=
  .sharded 110 [250, 251, 252] 1 [2, 6, 6] [2, 2, 6]

private def a2a2_out : RelationFact :=
  .sharded 110 [253, 254, 255] 2 [2, 6, 6] [2, 6, 2]

private def weight2 : RelationFact :=
  .sharded 131 [270, 271, 272] 1 [8, 6] [8, 2]

private def reduction2 : RelationFact :=
  .reduction 103 [280, 281, 282] [2, 6, 8]

private def local_weight_eq : RelationFact :=
  .tensorEq .sm 500 .pm 500

private def local_weight_shape : RelationFact :=
  .tensorShape .pm 500 [6, 5]

private def anchor : RelationFact :=
  .tensorShape .sm 999 [1]

private def state_pre : RelationState where
  facts := [anchor, local_in, weight1, a2a2_in, weight2, local_weight_eq, local_weight_shape]
  nonempty := by decide

private def state_post : RelationState where
  facts := [anchor, local_out, a2a1_out, reduction1, a2a2_out, reduction2]
  nonempty := by decide

end
end TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness

namespace TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [] }
private def pmGraph : GraphDecl := { numRanks := 3, nodes := [] }
set_option maxRecDepth 100000
set_option maxHeartbeats 500000
private def segment_synthetic_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [101] }, { rank := 0, op := "OpName.FW_linear", ins := [101, 130], outs := [102] }, { rank := 0, op := "OpName.FW_linear", ins := [110, 131], outs := [103] }]
private def segment_synthetic_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [210] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [211] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [212] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [210, 211, 212], outs := [213], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [210, 211, 212], outs := [214], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [210, 211, 212], outs := [215], params := [1, 2] }, { rank := 0, op := "OpName.FW_linear", ins := [213, 230], outs := [240] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [250, 251, 252], outs := [253], params := [1, 2] }, { rank := 1, op := "OpName.FW_linear", ins := [214, 231], outs := [241] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [250, 251, 252], outs := [254], params := [1, 2] }, { rank := 2, op := "OpName.FW_linear", ins := [215, 232], outs := [242] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [250, 251, 252], outs := [255], params := [1, 2] }, { rank := 0, op := "OpName.FW_linear", ins := [253, 270], outs := [280] }, { rank := 1, op := "OpName.FW_linear", ins := [254, 271], outs := [281] }, { rank := 2, op := "OpName.FW_linear", ins := [255, 272], outs := [282] }]
@[irreducible] private def segment_synthetic_smFinal (smStore : Store) : Store :=
  segment_synthetic_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore
@[irreducible] private def segment_synthetic_pmFinal (pmStore : Store) : Store :=
  segment_synthetic_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore

private theorem segment_synthetic_frame (smStore pmStore : Store)
    (hstate : state_pre.Holds smStore pmStore) :
    state_pre.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := by
  unfold segment_synthetic_smFinal segment_synthetic_pmFinal
  apply RelationState.Holds.fold_frame segment_synthetic_sm_nodes segment_synthetic_pm_nodes smStore pmStore hstate
  · native_decide
  · native_decide
  · native_decide
  · native_decide

private theorem segment_synthetic_sm_linear_writer_1 (smStore : Store) :
    segment_synthetic_smFinal smStore 101 = fw_linear (segment_synthetic_smFinal smStore 100) (segment_synthetic_smFinal smStore 500) := by
  unfold segment_synthetic_smFinal
  let smNodes : List NodeDecl := segment_synthetic_sm_nodes
  let smFinal := smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore
  change smFinal 101 = fw_linear (smFinal 100) (smFinal 500)
  have hPrefix1_0 : ((smNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 100 = smFinal 100 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph (smNodes.drop 0) ((smNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 100 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show smNodes.take 0 ++ smNodes.drop 0 = smNodes by exact List.take_append_drop 0 smNodes] at h
    exact h.symm
  have hPrefix1_1 : ((smNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 500 = smFinal 500 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph (smNodes.drop 0) ((smNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 500 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show smNodes.take 0 ++ smNodes.drop 0 = smNodes by exact List.take_append_drop 0 smNodes] at h
    exact h.symm
  change (smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 101 = _
  rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [101] }] ++ smNodes.drop 1 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph smStore (smNodes.take 0) (smNodes.drop 1)
    { rank := 0, op := "OpName.FW_linear", ins := [100, 500], outs := [101] } 101 (fun t => fw_linear (t 100) (t 500)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph t 0 100 500 101
    ) (by native_decide) (by native_decide)]
  rw [hPrefix1_0, hPrefix1_1]

private theorem segment_synthetic_pm_linear_writer_2 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 210 = fw_linear (segment_synthetic_pmFinal pmStore 200) (segment_synthetic_pmFinal pmStore 500) := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  change pmFinal 210 = fw_linear (pmFinal 200) (pmFinal 500)
  have hPrefix2_0 : ((pmNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 200 = pmFinal 200 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 0) ((pmNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 200 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 0 ++ pmNodes.drop 0 = pmNodes by exact List.take_append_drop 0 pmNodes] at h
    exact h.symm
  have hPrefix2_1 : ((pmNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 500 = pmFinal 500 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 0) ((pmNodes.take 0).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 500 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 0 ++ pmNodes.drop 0 = pmNodes by exact List.take_append_drop 0 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 210 = _
  rw [show pmNodes = pmNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [210] }] ++ pmNodes.drop 1 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
    { rank := 0, op := "OpName.FW_linear", ins := [200, 500], outs := [210] } 210 (fun t => fw_linear (t 200) (t 500)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 0 200 500 210
    ) (by native_decide) (by native_decide)]
  rw [hPrefix2_0, hPrefix2_1]

private theorem segment_synthetic_pm_linear_writer_3 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 211 = fw_linear (segment_synthetic_pmFinal pmStore 201) (segment_synthetic_pmFinal pmStore 500) := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  change pmFinal 211 = fw_linear (pmFinal 201) (pmFinal 500)
  have hPrefix3_0 : ((pmNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 201 = pmFinal 201 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 1) ((pmNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 201 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 1 ++ pmNodes.drop 1 = pmNodes by exact List.take_append_drop 1 pmNodes] at h
    exact h.symm
  have hPrefix3_1 : ((pmNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 500 = pmFinal 500 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 1) ((pmNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 500 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 1 ++ pmNodes.drop 1 = pmNodes by exact List.take_append_drop 1 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 211 = _
  rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [211] }] ++ pmNodes.drop 2 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2)
    { rank := 1, op := "OpName.FW_linear", ins := [201, 500], outs := [211] } 211 (fun t => fw_linear (t 201) (t 500)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 1 201 500 211
    ) (by native_decide) (by native_decide)]
  rw [hPrefix3_0, hPrefix3_1]

private theorem segment_synthetic_pm_linear_writer_4 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 212 = fw_linear (segment_synthetic_pmFinal pmStore 202) (segment_synthetic_pmFinal pmStore 500) := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  change pmFinal 212 = fw_linear (pmFinal 202) (pmFinal 500)
  have hPrefix4_0 : ((pmNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 202 = pmFinal 202 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 2) ((pmNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 202 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 2 ++ pmNodes.drop 2 = pmNodes by exact List.take_append_drop 2 pmNodes] at h
    exact h.symm
  have hPrefix4_1 : ((pmNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 500 = pmFinal 500 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 2) ((pmNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 500 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 2 ++ pmNodes.drop 2 = pmNodes by exact List.take_append_drop 2 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 212 = _
  rw [show pmNodes = pmNodes.take 2 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [212] }] ++ pmNodes.drop 3 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
    { rank := 2, op := "OpName.FW_linear", ins := [202, 500], outs := [212] } 212 (fun t => fw_linear (t 202) (t 500)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 2 202 500 212
    ) (by native_decide) (by native_decide)]
  rw [hPrefix4_0, hPrefix4_1]

private theorem segment_synthetic_pm_a2a_writer_0_0 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 213 = allToAllPrimWithDims 3 0 ([210, 211, 212].map (segment_synthetic_pmFinal pmStore)) 1 2 := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  let inputTids : List Tid := [210, 211, 212]
  let outputTids : List Tid := [213, 214, 215]
  let rankCount := outputTids.length
  let xs := inputTids.map pmFinal
  change pmFinal 213 = allToAllPrimWithDims rankCount 0 xs 1 2
  have hA2APrefix0_0_0 : ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 210 = pmFinal 210 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 3) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 210 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 3 ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
    exact h.symm
  have hA2APrefix0_0_1 : ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 211 = pmFinal 211 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 3) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 211 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 3 ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
    exact h.symm
  have hA2APrefix0_0_2 : ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 212 = pmFinal 212 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 3) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 212 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 3 ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
    exact h.symm
  have hInputs : inputTids.map ((pmNodes.take 3).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) = xs := by
    simp only [inputTids, xs, List.map]
    rw [hA2APrefix0_0_0, hA2APrefix0_0_1, hA2APrefix0_0_2]
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 213 = _
  rw [show pmNodes = pmNodes.take 3 ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [210, 211, 212], outs := [213], params := [1, 2] }] ++ pmNodes.drop 4 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 3) (pmNodes.drop 4)
    { rank := 0, op := "OpName.AllToAllPrim", ins := [210, 211, 212], outs := [213], params := [1, 2] } 213 (fun t => allToAllPrimWithDims rankCount 0 (inputTids.map t) 1 2)]
  · rw [hInputs]
  · intro t
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
    simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
    have hRankCount : rankCount = TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph.numRanks := by native_decide
    rw [hRankCount]
    simpa [inputTids] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 0 inputTids 213 1 2
  · native_decide
  · native_decide

private theorem segment_synthetic_pm_a2a_writer_0_1 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 214 = allToAllPrimWithDims 3 1 ([210, 211, 212].map (segment_synthetic_pmFinal pmStore)) 1 2 := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  let inputTids : List Tid := [210, 211, 212]
  let outputTids : List Tid := [213, 214, 215]
  let rankCount := outputTids.length
  let xs := inputTids.map pmFinal
  change pmFinal 214 = allToAllPrimWithDims rankCount 1 xs 1 2
  have hA2APrefix0_1_0 : ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 210 = pmFinal 210 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 4) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 210 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 4 ++ pmNodes.drop 4 = pmNodes by exact List.take_append_drop 4 pmNodes] at h
    exact h.symm
  have hA2APrefix0_1_1 : ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 211 = pmFinal 211 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 4) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 211 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 4 ++ pmNodes.drop 4 = pmNodes by exact List.take_append_drop 4 pmNodes] at h
    exact h.symm
  have hA2APrefix0_1_2 : ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 212 = pmFinal 212 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 4) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 212 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 4 ++ pmNodes.drop 4 = pmNodes by exact List.take_append_drop 4 pmNodes] at h
    exact h.symm
  have hInputs : inputTids.map ((pmNodes.take 4).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) = xs := by
    simp only [inputTids, xs, List.map]
    rw [hA2APrefix0_1_0, hA2APrefix0_1_1, hA2APrefix0_1_2]
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 214 = _
  rw [show pmNodes = pmNodes.take 4 ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [210, 211, 212], outs := [214], params := [1, 2] }] ++ pmNodes.drop 5 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 4) (pmNodes.drop 5)
    { rank := 1, op := "OpName.AllToAllPrim", ins := [210, 211, 212], outs := [214], params := [1, 2] } 214 (fun t => allToAllPrimWithDims rankCount 1 (inputTids.map t) 1 2)]
  · rw [hInputs]
  · intro t
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
    simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
    have hRankCount : rankCount = TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph.numRanks := by native_decide
    rw [hRankCount]
    simpa [inputTids] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 1 inputTids 214 1 2
  · native_decide
  · native_decide

private theorem segment_synthetic_pm_a2a_writer_0_2 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 215 = allToAllPrimWithDims 3 2 ([210, 211, 212].map (segment_synthetic_pmFinal pmStore)) 1 2 := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  let inputTids : List Tid := [210, 211, 212]
  let outputTids : List Tid := [213, 214, 215]
  let rankCount := outputTids.length
  let xs := inputTids.map pmFinal
  change pmFinal 215 = allToAllPrimWithDims rankCount 2 xs 1 2
  have hA2APrefix0_2_0 : ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 210 = pmFinal 210 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 5) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 210 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 5 ++ pmNodes.drop 5 = pmNodes by exact List.take_append_drop 5 pmNodes] at h
    exact h.symm
  have hA2APrefix0_2_1 : ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 211 = pmFinal 211 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 5) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 211 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 5 ++ pmNodes.drop 5 = pmNodes by exact List.take_append_drop 5 pmNodes] at h
    exact h.symm
  have hA2APrefix0_2_2 : ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 212 = pmFinal 212 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 5) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 212 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 5 ++ pmNodes.drop 5 = pmNodes by exact List.take_append_drop 5 pmNodes] at h
    exact h.symm
  have hInputs : inputTids.map ((pmNodes.take 5).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) = xs := by
    simp only [inputTids, xs, List.map]
    rw [hA2APrefix0_2_0, hA2APrefix0_2_1, hA2APrefix0_2_2]
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 215 = _
  rw [show pmNodes = pmNodes.take 5 ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [210, 211, 212], outs := [215], params := [1, 2] }] ++ pmNodes.drop 6 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 5) (pmNodes.drop 6)
    { rank := 2, op := "OpName.AllToAllPrim", ins := [210, 211, 212], outs := [215], params := [1, 2] } 215 (fun t => allToAllPrimWithDims rankCount 2 (inputTids.map t) 1 2)]
  · rw [hInputs]
  · intro t
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
    simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
    have hRankCount : rankCount = TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph.numRanks := by native_decide
    rw [hRankCount]
    simpa [inputTids] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 2 inputTids 215 1 2
  · native_decide
  · native_decide

private theorem segment_synthetic_sm_linear_writer_5 (smStore : Store) :
    segment_synthetic_smFinal smStore 102 = fw_linear (segment_synthetic_smFinal smStore 101) (segment_synthetic_smFinal smStore 130) := by
  unfold segment_synthetic_smFinal
  let smNodes : List NodeDecl := segment_synthetic_sm_nodes
  let smFinal := smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore
  change smFinal 102 = fw_linear (smFinal 101) (smFinal 130)
  have hPrefix5_0 : ((smNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 101 = smFinal 101 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph (smNodes.drop 1) ((smNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 101 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show smNodes.take 1 ++ smNodes.drop 1 = smNodes by exact List.take_append_drop 1 smNodes] at h
    exact h.symm
  have hPrefix5_1 : ((smNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 130 = smFinal 130 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph (smNodes.drop 1) ((smNodes.take 1).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 130 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show smNodes.take 1 ++ smNodes.drop 1 = smNodes by exact List.take_append_drop 1 smNodes] at h
    exact h.symm
  change (smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 102 = _
  rw [show smNodes = smNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [101, 130], outs := [102] }] ++ smNodes.drop 2 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph smStore (smNodes.take 1) (smNodes.drop 2)
    { rank := 0, op := "OpName.FW_linear", ins := [101, 130], outs := [102] } 102 (fun t => fw_linear (t 101) (t 130)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph t 0 101 130 102
    ) (by native_decide) (by native_decide)]
  rw [hPrefix5_0, hPrefix5_1]

private theorem segment_synthetic_pm_linear_writer_6 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 240 = fw_linear (segment_synthetic_pmFinal pmStore 213) (segment_synthetic_pmFinal pmStore 230) := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  change pmFinal 240 = fw_linear (pmFinal 213) (pmFinal 230)
  have hPrefix6_0 : ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 213 = pmFinal 213 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 6) ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 213 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 6 ++ pmNodes.drop 6 = pmNodes by exact List.take_append_drop 6 pmNodes] at h
    exact h.symm
  have hPrefix6_1 : ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 230 = pmFinal 230 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 6) ((pmNodes.take 6).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 230 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 6 ++ pmNodes.drop 6 = pmNodes by exact List.take_append_drop 6 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 240 = _
  rw [show pmNodes = pmNodes.take 6 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [213, 230], outs := [240] }] ++ pmNodes.drop 7 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 6) (pmNodes.drop 7)
    { rank := 0, op := "OpName.FW_linear", ins := [213, 230], outs := [240] } 240 (fun t => fw_linear (t 213) (t 230)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 0 213 230 240
    ) (by native_decide) (by native_decide)]
  rw [hPrefix6_0, hPrefix6_1]

private theorem segment_synthetic_pm_linear_writer_7 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 241 = fw_linear (segment_synthetic_pmFinal pmStore 214) (segment_synthetic_pmFinal pmStore 231) := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  change pmFinal 241 = fw_linear (pmFinal 214) (pmFinal 231)
  have hPrefix7_0 : ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 214 = pmFinal 214 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 8) ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 214 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 8 ++ pmNodes.drop 8 = pmNodes by exact List.take_append_drop 8 pmNodes] at h
    exact h.symm
  have hPrefix7_1 : ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 231 = pmFinal 231 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 8) ((pmNodes.take 8).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 231 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 8 ++ pmNodes.drop 8 = pmNodes by exact List.take_append_drop 8 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 241 = _
  rw [show pmNodes = pmNodes.take 8 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [214, 231], outs := [241] }] ++ pmNodes.drop 9 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 8) (pmNodes.drop 9)
    { rank := 1, op := "OpName.FW_linear", ins := [214, 231], outs := [241] } 241 (fun t => fw_linear (t 214) (t 231)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 1 214 231 241
    ) (by native_decide) (by native_decide)]
  rw [hPrefix7_0, hPrefix7_1]

private theorem segment_synthetic_pm_linear_writer_8 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 242 = fw_linear (segment_synthetic_pmFinal pmStore 215) (segment_synthetic_pmFinal pmStore 232) := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  change pmFinal 242 = fw_linear (pmFinal 215) (pmFinal 232)
  have hPrefix8_0 : ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 215 = pmFinal 215 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 10) ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 215 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 10 ++ pmNodes.drop 10 = pmNodes by exact List.take_append_drop 10 pmNodes] at h
    exact h.symm
  have hPrefix8_1 : ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 232 = pmFinal 232 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 10) ((pmNodes.take 10).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 232 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 10 ++ pmNodes.drop 10 = pmNodes by exact List.take_append_drop 10 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 242 = _
  rw [show pmNodes = pmNodes.take 10 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [215, 232], outs := [242] }] ++ pmNodes.drop 11 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 10) (pmNodes.drop 11)
    { rank := 2, op := "OpName.FW_linear", ins := [215, 232], outs := [242] } 242 (fun t => fw_linear (t 215) (t 232)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 2 215 232 242
    ) (by native_decide) (by native_decide)]
  rw [hPrefix8_0, hPrefix8_1]

private theorem segment_synthetic_pm_a2a_writer_1_0 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 253 = allToAllPrimWithDims 3 0 ([250, 251, 252].map (segment_synthetic_pmFinal pmStore)) 1 2 := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  let inputTids : List Tid := [250, 251, 252]
  let outputTids : List Tid := [253, 254, 255]
  let rankCount := outputTids.length
  let xs := inputTids.map pmFinal
  change pmFinal 253 = allToAllPrimWithDims rankCount 0 xs 1 2
  have hA2APrefix1_0_0 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 250 = pmFinal 250 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 250 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
    exact h.symm
  have hA2APrefix1_0_1 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 251 = pmFinal 251 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 251 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
    exact h.symm
  have hA2APrefix1_0_2 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 252 = pmFinal 252 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 252 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
    exact h.symm
  have hInputs : inputTids.map ((pmNodes.take 7).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) = xs := by
    simp only [inputTids, xs, List.map]
    rw [hA2APrefix1_0_0, hA2APrefix1_0_1, hA2APrefix1_0_2]
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 253 = _
  rw [show pmNodes = pmNodes.take 7 ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [250, 251, 252], outs := [253], params := [1, 2] }] ++ pmNodes.drop 8 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 7) (pmNodes.drop 8)
    { rank := 0, op := "OpName.AllToAllPrim", ins := [250, 251, 252], outs := [253], params := [1, 2] } 253 (fun t => allToAllPrimWithDims rankCount 0 (inputTids.map t) 1 2)]
  · rw [hInputs]
  · intro t
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
    simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
    have hRankCount : rankCount = TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph.numRanks := by native_decide
    rw [hRankCount]
    simpa [inputTids] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 0 inputTids 253 1 2
  · native_decide
  · native_decide

private theorem segment_synthetic_pm_a2a_writer_1_1 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 254 = allToAllPrimWithDims 3 1 ([250, 251, 252].map (segment_synthetic_pmFinal pmStore)) 1 2 := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  let inputTids : List Tid := [250, 251, 252]
  let outputTids : List Tid := [253, 254, 255]
  let rankCount := outputTids.length
  let xs := inputTids.map pmFinal
  change pmFinal 254 = allToAllPrimWithDims rankCount 1 xs 1 2
  have hA2APrefix1_1_0 : ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 250 = pmFinal 250 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 9) ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 250 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 9 ++ pmNodes.drop 9 = pmNodes by exact List.take_append_drop 9 pmNodes] at h
    exact h.symm
  have hA2APrefix1_1_1 : ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 251 = pmFinal 251 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 9) ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 251 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 9 ++ pmNodes.drop 9 = pmNodes by exact List.take_append_drop 9 pmNodes] at h
    exact h.symm
  have hA2APrefix1_1_2 : ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 252 = pmFinal 252 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 9) ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 252 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 9 ++ pmNodes.drop 9 = pmNodes by exact List.take_append_drop 9 pmNodes] at h
    exact h.symm
  have hInputs : inputTids.map ((pmNodes.take 9).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) = xs := by
    simp only [inputTids, xs, List.map]
    rw [hA2APrefix1_1_0, hA2APrefix1_1_1, hA2APrefix1_1_2]
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 254 = _
  rw [show pmNodes = pmNodes.take 9 ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [250, 251, 252], outs := [254], params := [1, 2] }] ++ pmNodes.drop 10 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 9) (pmNodes.drop 10)
    { rank := 1, op := "OpName.AllToAllPrim", ins := [250, 251, 252], outs := [254], params := [1, 2] } 254 (fun t => allToAllPrimWithDims rankCount 1 (inputTids.map t) 1 2)]
  · rw [hInputs]
  · intro t
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
    simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
    have hRankCount : rankCount = TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph.numRanks := by native_decide
    rw [hRankCount]
    simpa [inputTids] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 1 inputTids 254 1 2
  · native_decide
  · native_decide

private theorem segment_synthetic_pm_a2a_writer_1_2 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 255 = allToAllPrimWithDims 3 2 ([250, 251, 252].map (segment_synthetic_pmFinal pmStore)) 1 2 := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  let inputTids : List Tid := [250, 251, 252]
  let outputTids : List Tid := [253, 254, 255]
  let rankCount := outputTids.length
  let xs := inputTids.map pmFinal
  change pmFinal 255 = allToAllPrimWithDims rankCount 2 xs 1 2
  have hA2APrefix1_2_0 : ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 250 = pmFinal 250 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 11) ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 250 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 11 ++ pmNodes.drop 11 = pmNodes by exact List.take_append_drop 11 pmNodes] at h
    exact h.symm
  have hA2APrefix1_2_1 : ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 251 = pmFinal 251 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 11) ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 251 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 11 ++ pmNodes.drop 11 = pmNodes by exact List.take_append_drop 11 pmNodes] at h
    exact h.symm
  have hA2APrefix1_2_2 : ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 252 = pmFinal 252 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 11) ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 252 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 11 ++ pmNodes.drop 11 = pmNodes by exact List.take_append_drop 11 pmNodes] at h
    exact h.symm
  have hInputs : inputTids.map ((pmNodes.take 11).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) = xs := by
    simp only [inputTids, xs, List.map]
    rw [hA2APrefix1_2_0, hA2APrefix1_2_1, hA2APrefix1_2_2]
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 255 = _
  rw [show pmNodes = pmNodes.take 11 ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [250, 251, 252], outs := [255], params := [1, 2] }] ++ pmNodes.drop 12 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 11) (pmNodes.drop 12)
    { rank := 2, op := "OpName.AllToAllPrim", ins := [250, 251, 252], outs := [255], params := [1, 2] } 255 (fun t => allToAllPrimWithDims rankCount 2 (inputTids.map t) 1 2)]
  · rw [hInputs]
  · intro t
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
    simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
    have hRankCount : rankCount = TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph.numRanks := by native_decide
    rw [hRankCount]
    simpa [inputTids] using applyNode_allToAllPrimWithDims_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 2 inputTids 255 1 2
  · native_decide
  · native_decide

private theorem segment_synthetic_sm_linear_writer_9 (smStore : Store) :
    segment_synthetic_smFinal smStore 103 = fw_linear (segment_synthetic_smFinal smStore 110) (segment_synthetic_smFinal smStore 131) := by
  unfold segment_synthetic_smFinal
  let smNodes : List NodeDecl := segment_synthetic_sm_nodes
  let smFinal := smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore
  change smFinal 103 = fw_linear (smFinal 110) (smFinal 131)
  have hPrefix9_0 : ((smNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 110 = smFinal 110 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph (smNodes.drop 2) ((smNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 110 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show smNodes.take 2 ++ smNodes.drop 2 = smNodes by exact List.take_append_drop 2 smNodes] at h
    exact h.symm
  have hPrefix9_1 : ((smNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 131 = smFinal 131 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph (smNodes.drop 2) ((smNodes.take 2).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 131 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show smNodes.take 2 ++ smNodes.drop 2 = smNodes by exact List.take_append_drop 2 smNodes] at h
    exact h.symm
  change (smNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph) smStore) 103 = _
  rw [show smNodes = smNodes.take 2 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [110, 131], outs := [103] }] ++ smNodes.drop 3 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph smStore (smNodes.take 2) (smNodes.drop 3)
    { rank := 0, op := "OpName.FW_linear", ins := [110, 131], outs := [103] } 103 (fun t => fw_linear (t 110) (t 131)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph t 0 110 131 103
    ) (by native_decide) (by native_decide)]
  rw [hPrefix9_0, hPrefix9_1]

private theorem segment_synthetic_pm_linear_writer_10 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 280 = fw_linear (segment_synthetic_pmFinal pmStore 253) (segment_synthetic_pmFinal pmStore 270) := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  change pmFinal 280 = fw_linear (pmFinal 253) (pmFinal 270)
  have hPrefix10_0 : ((pmNodes.take 12).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 253 = pmFinal 253 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 12) ((pmNodes.take 12).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 253 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 12 ++ pmNodes.drop 12 = pmNodes by exact List.take_append_drop 12 pmNodes] at h
    exact h.symm
  have hPrefix10_1 : ((pmNodes.take 12).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 270 = pmFinal 270 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 12) ((pmNodes.take 12).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 270 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 12 ++ pmNodes.drop 12 = pmNodes by exact List.take_append_drop 12 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 280 = _
  rw [show pmNodes = pmNodes.take 12 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [253, 270], outs := [280] }] ++ pmNodes.drop 13 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 12) (pmNodes.drop 13)
    { rank := 0, op := "OpName.FW_linear", ins := [253, 270], outs := [280] } 280 (fun t => fw_linear (t 253) (t 270)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 0 253 270 280
    ) (by native_decide) (by native_decide)]
  rw [hPrefix10_0, hPrefix10_1]

private theorem segment_synthetic_pm_linear_writer_11 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 281 = fw_linear (segment_synthetic_pmFinal pmStore 254) (segment_synthetic_pmFinal pmStore 271) := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  change pmFinal 281 = fw_linear (pmFinal 254) (pmFinal 271)
  have hPrefix11_0 : ((pmNodes.take 13).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 254 = pmFinal 254 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 13) ((pmNodes.take 13).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 254 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 13 ++ pmNodes.drop 13 = pmNodes by exact List.take_append_drop 13 pmNodes] at h
    exact h.symm
  have hPrefix11_1 : ((pmNodes.take 13).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 271 = pmFinal 271 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 13) ((pmNodes.take 13).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 271 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 13 ++ pmNodes.drop 13 = pmNodes by exact List.take_append_drop 13 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 281 = _
  rw [show pmNodes = pmNodes.take 13 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [254, 271], outs := [281] }] ++ pmNodes.drop 14 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 13) (pmNodes.drop 14)
    { rank := 1, op := "OpName.FW_linear", ins := [254, 271], outs := [281] } 281 (fun t => fw_linear (t 254) (t 271)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 1 254 271 281
    ) (by native_decide) (by native_decide)]
  rw [hPrefix11_0, hPrefix11_1]

private theorem segment_synthetic_pm_linear_writer_12 (pmStore : Store) :
    segment_synthetic_pmFinal pmStore 282 = fw_linear (segment_synthetic_pmFinal pmStore 255) (segment_synthetic_pmFinal pmStore 272) := by
  unfold segment_synthetic_pmFinal
  let pmNodes : List NodeDecl := segment_synthetic_pm_nodes
  let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore
  change pmFinal 282 = fw_linear (pmFinal 255) (pmFinal 272)
  have hPrefix12_0 : ((pmNodes.take 14).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 255 = pmFinal 255 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 14) ((pmNodes.take 14).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 255 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 14 ++ pmNodes.drop 14 = pmNodes by exact List.take_append_drop 14 pmNodes] at h
    exact h.symm
  have hPrefix12_1 : ((pmNodes.take 14).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 272 = pmFinal 272 := by
    have h := foldl_applyNodeDistributedFaithful_at_not_written TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph (pmNodes.drop 14) ((pmNodes.take 14).foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 272 (by native_decide) (by native_decide)
    rw [← List.foldl_append, show pmNodes.take 14 ++ pmNodes.drop 14 = pmNodes by exact List.take_append_drop 14 pmNodes] at h
    exact h.symm
  change (pmNodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph) pmStore) 282 = _
  rw [show pmNodes = pmNodes.take 14 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [255, 272], outs := [282] }] ++ pmNodes.drop 15 by native_decide]
  rw [foldl_faithful_middle_writer TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph pmStore (pmNodes.take 14) (pmNodes.drop 15)
    { rank := 2, op := "OpName.FW_linear", ins := [255, 272], outs := [282] } 282 (fun t => fw_linear (t 255) (t 272)) (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_fw_linear_out TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph t 2 255 272 282
    ) (by native_decide) (by native_decide)]
  rw [hPrefix12_0, hPrefix12_1]

private theorem segment_synthetic_transition_0_ll (smStore pmStore : Store)
    (hframe : state_pre.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore))
    : local_out.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := by
    let smFinal := segment_synthetic_smFinal smStore
    let pmFinal := segment_synthetic_pmFinal pmStore
    have hLocalIn0 : local_in.Holds smFinal pmFinal := hframe local_in (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 200, pmFinal 201, pmFinal 202] 1 [2, 6, 5] [2, 2, 5] at hLocalIn0
    have hLocalEq0 : local_weight_eq.Holds smFinal pmFinal := hframe _ (by native_decide)
    change smFinal 500 = pmFinal 500 at hLocalEq0
    have hLocalWeightShape0 : local_weight_shape.Holds smFinal pmFinal := hframe _ (by native_decide)
    change (pmFinal 500).shape = [6, 5] at hLocalWeightShape0
    have hLocalSm0 : smFinal 101 = fw_linear (smFinal 100) (smFinal 500) := segment_synthetic_sm_linear_writer_1 smStore
    have hLocalPm0_0 : pmFinal 210 = fw_linear (pmFinal 200) (pmFinal 500) := segment_synthetic_pm_linear_writer_2 pmStore
    have hLocalPm0_1 : pmFinal 211 = fw_linear (pmFinal 201) (pmFinal 500) := segment_synthetic_pm_linear_writer_3 pmStore
    have hLocalPm0_2 : pmFinal 212 = fw_linear (pmFinal 202) (pmFinal 500) := segment_synthetic_pm_linear_writer_4 pmStore
    have hLocalComm0 := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmFinal 200, pmFinal 201, pmFinal 202].length) (b := 2) (s := 2) (i := 5) (o := 6) (xs := [pmFinal 200, pmFinal 201, pmFinal 202]) (w := pmFinal 500) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hLocalIn0.shard_shapes x hx) hLocalWeightShape0)
    have hLocalValue0 : smFinal 101 = allGatherPrimDimN 1 [pmFinal 210, pmFinal 211, pmFinal 212].length 0 [pmFinal 210, pmFinal 211, pmFinal 212] := by
      rw [hLocalSm0, hLocalEq0, hLocalIn0.full_value, hLocalComm0]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLocalPm0_0, ← hLocalPm0_1, ← hLocalPm0_2]
    have hLocalShape0_0 : (pmFinal 210).shape = [2, 2, 6] := by
      rw [hLocalPm0_0]
      exact fw_linear_3d_shape 2 2 5 6 _ _ (hLocalIn0.shard_shapes _ (by simp)) hLocalWeightShape0
    have hLocalShape0_1 : (pmFinal 211).shape = [2, 2, 6] := by
      rw [hLocalPm0_1]
      exact fw_linear_3d_shape 2 2 5 6 _ _ (hLocalIn0.shard_shapes _ (by simp)) hLocalWeightShape0
    have hLocalShape0_2 : (pmFinal 212).shape = [2, 2, 6] := by
      rw [hLocalPm0_2]
      exact fw_linear_3d_shape 2 2 5 6 _ _ (hLocalIn0.shard_shapes _ (by simp)) hLocalWeightShape0
    have hLocalOut0 : local_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 101) [pmFinal 210, pmFinal 211, pmFinal 212] 1 [2, 6, 6] [2, 2, 6]
      refine { full_value := hLocalValue0, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hLocalValue0, allGatherPrimDimN_shape 1 [pmFinal 210, pmFinal 211, pmFinal 212].length [pmFinal 210, pmFinal 211, pmFinal 212] [2, 2, 6]]
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

private theorem segment_synthetic_transition_1_a2a (smStore pmStore : Store)
    (hframe : state_pre.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore))
    (hFact0 : local_out.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore))
    : a2a1_out.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := by
    let smFinal := segment_synthetic_smFinal smStore
    let pmFinal := segment_synthetic_pmFinal pmStore
    have hA2AIn0 : local_out.Holds smFinal pmFinal := hFact0
    change ShardedRel (smFinal 101) [pmFinal 210, pmFinal 211, pmFinal 212] 1 [2, 6, 6] [2, 2, 6] at hA2AIn0
    let inputTids0 : List Tid := [210, 211, 212]
    let outputTids0 : List Tid := [213, 214, 215]
    let rankCount0 := outputTids0.length
    have hRankCount0 : rankCount0 = TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph.numRanks := by native_decide
    let xs0 := inputTids0.map pmFinal
    have hHead0 : ((xs0.head?.map (fun t => t.shape)).getD []) = [2, 2, 6] := by
      simp only [xs0, inputTids0, List.map, List.head?, Option.map, Option.getD]
      exact hA2AIn0.shard_shapes _ (by simp)
    have hRankXs0 : rankCount0 = xs0.length := by simp [rankCount0, outputTids0, xs0, inputTids0]
    have hA2AWriter0_0 : pmFinal 213 = allToAllPrimWithDims rankCount0 0 xs0 1 2 := segment_synthetic_pm_a2a_writer_0_0 pmStore
    have hA2AShape0_0 : (pmFinal 213).shape = [2, 6, 2] := by
      rw [hA2AWriter0_0, allToAllPrimWithDims_shape rankCount0 0 xs0 1 2 [2, 2, 6] hHead0 (by native_decide)]
      native_decide
    have hA2AWriter0_1 : pmFinal 214 = allToAllPrimWithDims rankCount0 1 xs0 1 2 := segment_synthetic_pm_a2a_writer_0_1 pmStore
    have hA2AShape0_1 : (pmFinal 214).shape = [2, 6, 2] := by
      rw [hA2AWriter0_1, allToAllPrimWithDims_shape rankCount0 1 xs0 1 2 [2, 2, 6] hHead0 (by native_decide)]
      native_decide
    have hA2AWriter0_2 : pmFinal 215 = allToAllPrimWithDims rankCount0 2 xs0 1 2 := segment_synthetic_pm_a2a_writer_0_2 pmStore
    have hA2AShape0_2 : (pmFinal 215).shape = [2, 6, 2] := by
      rw [hA2AWriter0_2, allToAllPrimWithDims_shape rankCount0 2 xs0 1 2 [2, 2, 6] hHead0 (by native_decide)]
      native_decide
    have hOrdered0 : outputTids0.map pmFinal = List.ofFn (fun r : Fin rankCount0 => allToAllPrimWithDims rankCount0 r.1 xs0 1 2) := by
      simp only [outputTids0, rankCount0, List.map]
      rw [hA2AWriter0_0, hA2AWriter0_1, hA2AWriter0_2]
      rfl
    have hGatherShape0 : (allGatherPrimDimN 1 rankCount0 0 xs0).shape = [2, 6, 6] := by
      rw [hRankXs0]
      calc _ = (smFinal 101).shape := congrArg (fun t => t.shape) hA2AIn0.full_value.symm
           _ = _ := hA2AIn0.full_shape
    have hOdim0 : 2 < (allGatherPrimDimN 1 rankCount0 0 xs0).shape.length := by rw [hGatherShape0]; native_decide
    have hDiv0 : (allGatherPrimDimN 1 rankCount0 0 xs0).shape.getD 2 0 % rankCount0 = 0 := by rw [hGatherShape0]; native_decide
    have hOdimXs0 := hOdim0
    have hDivXs0 := hDiv0
    rw [hRankXs0] at hOdimXs0 hDivXs0
    have hA2AOut0 : a2a1_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 101) [pmFinal 213, pmFinal 214, pmFinal 215] 2 [2, 6, 6] [2, 6, 2]
      refine { full_value := ?_, full_shape := hA2AIn0.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [show [pmFinal 213, pmFinal 214, pmFinal 215] = outputTids0.map pmFinal by rfl, hOrdered0, List.length_ofFn]
        rw [hRankXs0, TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 1 2 xs0 (by simp [xs0, inputTids0]) hOdimXs0 hDivXs0]
        simp only [rankCount0, outputTids0, xs0, inputTids0, List.map, List.length_cons, List.length_nil]
        exact hA2AIn0.full_value
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hA2AShape0_0
        · exact hA2AShape0_1
        · exact hA2AShape0_2
    exact hA2AOut0

private theorem segment_synthetic_transition_2_rlin (smStore pmStore : Store)
    (hframe : state_pre.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore))
    (hFact1 : a2a1_out.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore))
    : reduction1.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := by
    let smFinal := segment_synthetic_smFinal smStore
    let pmFinal := segment_synthetic_pmFinal pmStore
    have hActivation0 : a2a1_out.Holds smFinal pmFinal := hFact1
    change ShardedRel (smFinal 101) ([213, 214, 215].map pmFinal) 2 [2, 6, 6] [2, 6, 2] at hActivation0
    have hReductionWeight0 : weight1.Holds smFinal pmFinal := hframe weight1 (by native_decide)
    change ShardedRel (smFinal 130) ([230, 231, 232].map pmFinal) 1 [7, 6] [7, 2] at hReductionWeight0
    let pmActivationTids0 : List Tid := [213, 214, 215]
    let pmWeightTids0 : List Tid := [230, 231, 232]
    let pmOutputTids0 : List Tid := [240, 241, 242]
    let rankCountR0 := pmWeightTids0.length
    have hReductionSm0 : smFinal 102 = fw_linear (smFinal 101) (smFinal 130) := segment_synthetic_sm_linear_writer_5 smStore
    have hReductionPm0_0 : pmFinal 240 = fw_linear (pmFinal 213) (pmFinal 230) := segment_synthetic_pm_linear_writer_6 pmStore
    have hReductionChunk0_0 : chunkPrim 3 0 (smFinal 101) = pmFinal 213 := by
      rw [hActivation0.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 0 2 6 2 (pmActivationTids0.map pmFinal)
        (by simp [rankCountR0, pmActivationTids0, pmWeightTids0]) hActivation0.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [pmActivationTids0] using hcancel
    have hReductionShape0_0 : (pmFinal 240).shape = [2, 6, 7] := by
      rw [hReductionPm0_0]
      have ha := hActivation0.shard_shapes (pmFinal 213) (by simp [pmActivationTids0])
      have hw := hReductionWeight0.shard_shapes (pmFinal 230) (by simp [pmWeightTids0])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionPm0_1 : pmFinal 241 = fw_linear (pmFinal 214) (pmFinal 231) := segment_synthetic_pm_linear_writer_7 pmStore
    have hReductionChunk0_1 : chunkPrim 3 1 (smFinal 101) = pmFinal 214 := by
      rw [hActivation0.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 1 2 6 2 (pmActivationTids0.map pmFinal)
        (by simp [rankCountR0, pmActivationTids0, pmWeightTids0]) hActivation0.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [pmActivationTids0] using hcancel
    have hReductionShape0_1 : (pmFinal 241).shape = [2, 6, 7] := by
      rw [hReductionPm0_1]
      have ha := hActivation0.shard_shapes (pmFinal 214) (by simp [pmActivationTids0])
      have hw := hReductionWeight0.shard_shapes (pmFinal 231) (by simp [pmWeightTids0])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionPm0_2 : pmFinal 242 = fw_linear (pmFinal 215) (pmFinal 232) := segment_synthetic_pm_linear_writer_8 pmStore
    have hReductionChunk0_2 : chunkPrim 3 2 (smFinal 101) = pmFinal 215 := by
      rw [hActivation0.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 2 2 6 2 (pmActivationTids0.map pmFinal)
        (by simp [rankCountR0, pmActivationTids0, pmWeightTids0]) hActivation0.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [pmActivationTids0] using hcancel
    have hReductionShape0_2 : (pmFinal 242).shape = [2, 6, 7] := by
      rw [hReductionPm0_2]
      have ha := hActivation0.shard_shapes (pmFinal 215) (by simp [pmActivationTids0])
      have hw := hReductionWeight0.shard_shapes (pmFinal 232) (by simp [pmWeightTids0])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionWeightGather0 : smFinal 130 = allGatherPrim rankCountR0 0 (pmWeightTids0.map pmFinal) := by
      change smFinal 130 = allGatherPrim 3 0 ([230, 231, 232].map pmFinal)
      rw [hReductionWeight0.full_value]
      have hhead : ((pmWeightTids0.map pmFinal).head?.map (fun t => t.shape)).getD [] = [7, 2] := by
        simpa [pmWeightTids0] using hReductionWeight0.shard_shapes _ (by simp [pmWeightTids0])
      simpa [rankCountR0, pmWeightTids0] using (allGatherPrimDimN_1_eq_allGatherPrim_2d 3 ([230, 231, 232].map pmFinal) 7 2 hhead (by native_decide) (by native_decide))
    have hReductionFullShape0 : (smFinal 102).shape = [2, 6, 7] := by
      rw [hReductionSm0]
      simp [fw_linear, hActivation0.full_shape, hReductionWeight0.full_shape]
      rfl
    have hReductionValue0 : smFinal 102 = allReducePrim (pmOutputTids0.map pmFinal).length 0 (pmOutputTids0.map pmFinal) := by
      rw [hReductionSm0, hReductionWeightGather0]
      have hComm := TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d 3 2 6 6 7 2 (smFinal 101) (pmWeightTids0.map pmFinal)
        hActivation0.full_shape (by native_decide) (by simp [rankCountR0, pmWeightTids0]) hReductionWeight0.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      have hContribs : List.ofFn (fun r : Fin 3 => fw_linear (chunkPrim 3 r.val (smFinal 101)) ((pmWeightTids0.map pmFinal).get ⟨r.val, by simpa [pmWeightTids0] using r.isLt⟩)) = [fw_linear (chunkPrim 3 0 (smFinal 101)) (pmFinal 230), fw_linear (chunkPrim 3 1 (smFinal 101)) (pmFinal 231), fw_linear (chunkPrim 3 2 (smFinal 101)) (pmFinal 232)] := by rfl
      rw [hContribs] at hComm
      simp [rankCountR0, pmWeightTids0, pmOutputTids0] at hComm ⊢
      rw [hReductionChunk0_0, hReductionChunk0_1, hReductionChunk0_2] at hComm
      rw [hComm]
      rw [← hReductionPm0_0, ← hReductionPm0_1, ← hReductionPm0_2]
    have hReductionOut0 : reduction1.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 102) (pmOutputTids0.map pmFinal) [2, 6, 7]
      refine { full_value := hReductionValue0, full_shape := hReductionFullShape0, contributions_nonempty := by simp [pmOutputTids0], contribution_shapes := ?_, reduced_shape := ?_ }
      · intro contribution hmem
        simp only [pmOutputTids0, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hReductionShape0_0
        · exact hReductionShape0_1
        · exact hReductionShape0_2
      · rw [← hReductionValue0]
        exact hReductionFullShape0
    exact hReductionOut0

private theorem segment_synthetic_transition_3_a2a (smStore pmStore : Store)
    (hframe : state_pre.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore))
    : a2a2_out.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := by
    let smFinal := segment_synthetic_smFinal smStore
    let pmFinal := segment_synthetic_pmFinal pmStore
    have hA2AIn1 : a2a2_in.Holds smFinal pmFinal := hframe a2a2_in (by native_decide)
    change ShardedRel (smFinal 110) [pmFinal 250, pmFinal 251, pmFinal 252] 1 [2, 6, 6] [2, 2, 6] at hA2AIn1
    let inputTids1 : List Tid := [250, 251, 252]
    let outputTids1 : List Tid := [253, 254, 255]
    let rankCount1 := outputTids1.length
    have hRankCount1 : rankCount1 = TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph.numRanks := by native_decide
    let xs1 := inputTids1.map pmFinal
    have hHead1 : ((xs1.head?.map (fun t => t.shape)).getD []) = [2, 2, 6] := by
      simp only [xs1, inputTids1, List.map, List.head?, Option.map, Option.getD]
      exact hA2AIn1.shard_shapes _ (by simp)
    have hRankXs1 : rankCount1 = xs1.length := by simp [rankCount1, outputTids1, xs1, inputTids1]
    have hA2AWriter1_0 : pmFinal 253 = allToAllPrimWithDims rankCount1 0 xs1 1 2 := segment_synthetic_pm_a2a_writer_1_0 pmStore
    have hA2AShape1_0 : (pmFinal 253).shape = [2, 6, 2] := by
      rw [hA2AWriter1_0, allToAllPrimWithDims_shape rankCount1 0 xs1 1 2 [2, 2, 6] hHead1 (by native_decide)]
      native_decide
    have hA2AWriter1_1 : pmFinal 254 = allToAllPrimWithDims rankCount1 1 xs1 1 2 := segment_synthetic_pm_a2a_writer_1_1 pmStore
    have hA2AShape1_1 : (pmFinal 254).shape = [2, 6, 2] := by
      rw [hA2AWriter1_1, allToAllPrimWithDims_shape rankCount1 1 xs1 1 2 [2, 2, 6] hHead1 (by native_decide)]
      native_decide
    have hA2AWriter1_2 : pmFinal 255 = allToAllPrimWithDims rankCount1 2 xs1 1 2 := segment_synthetic_pm_a2a_writer_1_2 pmStore
    have hA2AShape1_2 : (pmFinal 255).shape = [2, 6, 2] := by
      rw [hA2AWriter1_2, allToAllPrimWithDims_shape rankCount1 2 xs1 1 2 [2, 2, 6] hHead1 (by native_decide)]
      native_decide
    have hOrdered1 : outputTids1.map pmFinal = List.ofFn (fun r : Fin rankCount1 => allToAllPrimWithDims rankCount1 r.1 xs1 1 2) := by
      simp only [outputTids1, rankCount1, List.map]
      rw [hA2AWriter1_0, hA2AWriter1_1, hA2AWriter1_2]
      rfl
    have hGatherShape1 : (allGatherPrimDimN 1 rankCount1 0 xs1).shape = [2, 6, 6] := by
      rw [hRankXs1]
      calc _ = (smFinal 110).shape := congrArg (fun t => t.shape) hA2AIn1.full_value.symm
           _ = _ := hA2AIn1.full_shape
    have hOdim1 : 2 < (allGatherPrimDimN 1 rankCount1 0 xs1).shape.length := by rw [hGatherShape1]; native_decide
    have hDiv1 : (allGatherPrimDimN 1 rankCount1 0 xs1).shape.getD 2 0 % rankCount1 = 0 := by rw [hGatherShape1]; native_decide
    have hOdimXs1 := hOdim1
    have hDivXs1 := hDiv1
    rw [hRankXs1] at hOdimXs1 hDivXs1
    have hA2AOut1 : a2a2_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 253, pmFinal 254, pmFinal 255] 2 [2, 6, 6] [2, 6, 2]
      refine { full_value := ?_, full_shape := hA2AIn1.full_shape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [show [pmFinal 253, pmFinal 254, pmFinal 255] = outputTids1.map pmFinal by rfl, hOrdered1, List.length_ofFn]
        rw [hRankXs1, TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 1 2 xs1 (by simp [xs1, inputTids1]) hOdimXs1 hDivXs1]
        simp only [rankCount1, outputTids1, xs1, inputTids1, List.map, List.length_cons, List.length_nil]
        exact hA2AIn1.full_value
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hA2AShape1_0
        · exact hA2AShape1_1
        · exact hA2AShape1_2
    exact hA2AOut1

private theorem segment_synthetic_transition_4_rlin (smStore pmStore : Store)
    (hframe : state_pre.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore))
    (hFact3 : a2a2_out.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore))
    : reduction2.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := by
    let smFinal := segment_synthetic_smFinal smStore
    let pmFinal := segment_synthetic_pmFinal pmStore
    have hActivation1 : a2a2_out.Holds smFinal pmFinal := hFact3
    change ShardedRel (smFinal 110) ([253, 254, 255].map pmFinal) 2 [2, 6, 6] [2, 6, 2] at hActivation1
    have hReductionWeight1 : weight2.Holds smFinal pmFinal := hframe weight2 (by native_decide)
    change ShardedRel (smFinal 131) ([270, 271, 272].map pmFinal) 1 [8, 6] [8, 2] at hReductionWeight1
    let pmActivationTids1 : List Tid := [253, 254, 255]
    let pmWeightTids1 : List Tid := [270, 271, 272]
    let pmOutputTids1 : List Tid := [280, 281, 282]
    let rankCountR1 := pmWeightTids1.length
    have hReductionSm1 : smFinal 103 = fw_linear (smFinal 110) (smFinal 131) := segment_synthetic_sm_linear_writer_9 smStore
    have hReductionPm1_0 : pmFinal 280 = fw_linear (pmFinal 253) (pmFinal 270) := segment_synthetic_pm_linear_writer_10 pmStore
    have hReductionChunk1_0 : chunkPrim 3 0 (smFinal 110) = pmFinal 253 := by
      rw [hActivation1.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 0 2 6 2 (pmActivationTids1.map pmFinal)
        (by simp [rankCountR1, pmActivationTids1, pmWeightTids1]) hActivation1.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [pmActivationTids1] using hcancel
    have hReductionShape1_0 : (pmFinal 280).shape = [2, 6, 8] := by
      rw [hReductionPm1_0]
      have ha := hActivation1.shard_shapes (pmFinal 253) (by simp [pmActivationTids1])
      have hw := hReductionWeight1.shard_shapes (pmFinal 270) (by simp [pmWeightTids1])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionPm1_1 : pmFinal 281 = fw_linear (pmFinal 254) (pmFinal 271) := segment_synthetic_pm_linear_writer_11 pmStore
    have hReductionChunk1_1 : chunkPrim 3 1 (smFinal 110) = pmFinal 254 := by
      rw [hActivation1.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 1 2 6 2 (pmActivationTids1.map pmFinal)
        (by simp [rankCountR1, pmActivationTids1, pmWeightTids1]) hActivation1.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [pmActivationTids1] using hcancel
    have hReductionShape1_1 : (pmFinal 281).shape = [2, 6, 8] := by
      rw [hReductionPm1_1]
      have ha := hActivation1.shard_shapes (pmFinal 254) (by simp [pmActivationTids1])
      have hw := hReductionWeight1.shard_shapes (pmFinal 271) (by simp [pmWeightTids1])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionPm1_2 : pmFinal 282 = fw_linear (pmFinal 255) (pmFinal 272) := segment_synthetic_pm_linear_writer_12 pmStore
    have hReductionChunk1_2 : chunkPrim 3 2 (smFinal 110) = pmFinal 255 := by
      rw [hActivation1.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 2 2 6 2 (pmActivationTids1.map pmFinal)
        (by simp [rankCountR1, pmActivationTids1, pmWeightTids1]) hActivation1.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [pmActivationTids1] using hcancel
    have hReductionShape1_2 : (pmFinal 282).shape = [2, 6, 8] := by
      rw [hReductionPm1_2]
      have ha := hActivation1.shard_shapes (pmFinal 255) (by simp [pmActivationTids1])
      have hw := hReductionWeight1.shard_shapes (pmFinal 272) (by simp [pmWeightTids1])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionWeightGather1 : smFinal 131 = allGatherPrim rankCountR1 0 (pmWeightTids1.map pmFinal) := by
      change smFinal 131 = allGatherPrim 3 0 ([270, 271, 272].map pmFinal)
      rw [hReductionWeight1.full_value]
      have hhead : ((pmWeightTids1.map pmFinal).head?.map (fun t => t.shape)).getD [] = [8, 2] := by
        simpa [pmWeightTids1] using hReductionWeight1.shard_shapes _ (by simp [pmWeightTids1])
      simpa [rankCountR1, pmWeightTids1] using (allGatherPrimDimN_1_eq_allGatherPrim_2d 3 ([270, 271, 272].map pmFinal) 8 2 hhead (by native_decide) (by native_decide))
    have hReductionFullShape1 : (smFinal 103).shape = [2, 6, 8] := by
      rw [hReductionSm1]
      simp [fw_linear, hActivation1.full_shape, hReductionWeight1.full_shape]
      rfl
    have hReductionValue1 : smFinal 103 = allReducePrim (pmOutputTids1.map pmFinal).length 0 (pmOutputTids1.map pmFinal) := by
      rw [hReductionSm1, hReductionWeightGather1]
      have hComm := TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d 3 2 6 6 8 2 (smFinal 110) (pmWeightTids1.map pmFinal)
        hActivation1.full_shape (by native_decide) (by simp [rankCountR1, pmWeightTids1]) hReductionWeight1.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      have hContribs : List.ofFn (fun r : Fin 3 => fw_linear (chunkPrim 3 r.val (smFinal 110)) ((pmWeightTids1.map pmFinal).get ⟨r.val, by simpa [pmWeightTids1] using r.isLt⟩)) = [fw_linear (chunkPrim 3 0 (smFinal 110)) (pmFinal 270), fw_linear (chunkPrim 3 1 (smFinal 110)) (pmFinal 271), fw_linear (chunkPrim 3 2 (smFinal 110)) (pmFinal 272)] := by rfl
      rw [hContribs] at hComm
      simp [rankCountR1, pmWeightTids1, pmOutputTids1] at hComm ⊢
      rw [hReductionChunk1_0, hReductionChunk1_1, hReductionChunk1_2] at hComm
      rw [hComm]
      rw [← hReductionPm1_0, ← hReductionPm1_1, ← hReductionPm1_2]
    have hReductionOut1 : reduction2.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 103) (pmOutputTids1.map pmFinal) [2, 6, 8]
      refine { full_value := hReductionValue1, full_shape := hReductionFullShape1, contributions_nonempty := by simp [pmOutputTids1], contribution_shapes := ?_, reduced_shape := ?_ }
      · intro contribution hmem
        simp only [pmOutputTids1, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hReductionShape1_0
        · exact hReductionShape1_1
        · exact hReductionShape1_2
      · rw [← hReductionValue1]
        exact hReductionFullShape1
    exact hReductionOut1

private theorem segment_synthetic_publish_state (smStore pmStore : Store)
    (hstate : state_pre.Holds smStore pmStore) :
    state_post.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := by
    have hframe := segment_synthetic_frame smStore pmStore hstate
    have hFact0 : local_out.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := segment_synthetic_transition_0_ll smStore pmStore hframe
    have hFact1 : a2a1_out.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := segment_synthetic_transition_1_a2a smStore pmStore hframe hFact0
    have hFact2 : reduction1.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := segment_synthetic_transition_2_rlin smStore pmStore hframe hFact1
    have hFact3 : a2a2_out.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := segment_synthetic_transition_3_a2a smStore pmStore hframe
    have hFact4 : reduction2.Holds (segment_synthetic_smFinal smStore) (segment_synthetic_pmFinal pmStore) := segment_synthetic_transition_4_rlin smStore pmStore hframe hFact3
    intro fact hfact
    have covered : fact ∈ [local_out, a2a1_out, reduction1, a2a2_out, reduction2] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [local_out, a2a1_out, reduction1, a2a2_out, reduction2] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl | rfl | rfl | rfl
      · exact hFact0
      · exact hFact1
      · exact hFact2
      · exact hFact3
      · exact hFact4
    · exact hframe fact old

private def segment_synthetic : ClosedDepSegmentCertificate TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.smGraph TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness.pmGraph state_pre state_post where
  smNodes := segment_synthetic_sm_nodes
  pmNodes := segment_synthetic_pm_nodes
  sound := by
    intro smStore pmStore hstate
    simpa [segment_synthetic_smFinal, segment_synthetic_pmFinal] using
      (segment_synthetic_publish_state smStore pmStore hstate)

#print axioms segment_synthetic
end
end TrainVerify.Denote.GeneratedMixedLinearSequenceK3DoubleReductionWitness
