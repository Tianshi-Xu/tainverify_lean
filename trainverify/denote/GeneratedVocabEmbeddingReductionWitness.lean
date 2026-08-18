/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.SyntheticEmbedding

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_weight : RelationFact :=
  .sharded 50 [60, 61, 62] 0 [21, 12] [7, 12]

private def fact_reduction : RelationFact :=
  .reduction 100 [200, 201, 202] [1, 8, 12]

private def authority_ids_eq_40 : RelationFact :=
  .tensorEq .sm 40 .pm 40

private def authority_ids_shape_40 : RelationFact :=
  .tensorShape .pm 40 [1, 8]

private def anchor : RelationFact :=
  .tensorShape .sm 999 [1]

private def state_pre : RelationState where
  facts := [anchor, authority_ids_eq_40, authority_ids_shape_40, fact_weight]
  nonempty := by decide

private def state_post : RelationState where
  facts := [anchor, authority_ids_eq_40, authority_ids_shape_40, fact_reduction]
  nonempty := by decide

end
end TrainVerify.Denote.SyntheticEmbedding

namespace TrainVerify.Denote.SyntheticEmbedding
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] }] }
private def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200], params := [0] }, { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201], params := [7] }, { rank := 2, op := "OpName.FW_embedding", ins := [40, 62], outs := [202], params := [14] }] }
set_option maxHeartbeats 500000 in
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticEmbedding.smGraph SyntheticEmbedding.pmGraph state_pre state_post where
  smNodes := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] }]
  pmNodes := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200], params := [0] }, { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201], params := [7] }, { rank := 2, op := "OpName.FW_embedding", ins := [40, 62], outs := [202], params := [14] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] }]
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200], params := [0] }, { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201], params := [7] }, { rank := 2, op := "OpName.FW_embedding", ins := [40, 62], outs := [202], params := [14] }]
    let pmWeightTids : List Tid := [60, 61, 62]
    let pmOutputTids : List Tid := [200, 201, 202]
    let rankCount := pmWeightTids.length
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticEmbedding.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticEmbedding.pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hWeight : fact_weight.Holds smFinal pmFinal := hframe fact_weight (by native_decide)
    change ShardedRel (smFinal 50) (pmWeightTids.map pmFinal) 0 [21, 12] [7, 12] at hWeight
    have hIdsEqStore : smStore 40 = pmStore 40 := by
      have h := hstate authority_ids_eq_40 (by native_decide)
      change smStore 40 = pmStore 40 at h
      exact h
    have hIdsShapeStore : (pmStore 40).shape = [1, 8] := by
      have h := hstate authority_ids_shape_40 (by native_decide)
      change (pmStore 40).shape = [1, 8] at h
      exact h
    have hSmIds : smFinal 40 = smStore 40 := by
      unfold smFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.smGraph smNodes smStore 40
        (by native_decide) (by native_decide)
    have hSmWeight : smFinal 50 = smStore 50 := by
      unfold smFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.smGraph smNodes smStore 50
        (by native_decide) (by native_decide)
    have hPmIds : pmFinal 40 = pmStore 40 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.pmGraph pmNodes pmStore 40
        (by native_decide) (by native_decide)
    have hIdsEq : smFinal 40 = pmFinal 40 := by
      rw [hSmIds, hPmIds]
      exact hIdsEqStore
    have hIdsShape : (pmFinal 40).shape = [1, 8] := by
      rw [hPmIds]
      exact hIdsShapeStore
    have hSmWriter : smFinal 100 = fw_embedding (smStore 40) (smStore 50) := by
      unfold smFinal smNodes
      simp only [List.foldl]
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
        (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
      · exact applyNode_fw_embedding_out SyntheticEmbedding.smGraph smStore 0 40 50 100
      · decide
      · decide
    have hPmWeight0 : pmFinal 60 = pmStore 60 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.pmGraph pmNodes pmStore 60
        (by native_decide) (by native_decide)
    have hPmWriter0 : pmFinal 200 = fw_embedding_offset 0 (pmFinal 40) (pmFinal 60) := by
      calc
        pmFinal 200 = fw_embedding_offset 0 (((pmNodes.take 0)).foldl
            (applyNodeDistributedFaithful SyntheticEmbedding.pmGraph) pmStore 40) (((pmNodes.take 0)).foldl
            (applyNodeDistributedFaithful SyntheticEmbedding.pmGraph) pmStore 60) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticEmbedding.pmGraph) pmStore) 200 = _
          rw [show pmNodes = (pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200], params := [0] }] ++ (pmNodes.drop 1) by native_decide]
          apply foldl_faithful_middle_writer SyntheticEmbedding.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
            { rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200], params := [0] } 200 (fun t => fw_embedding_offset 0 (t 40) (t 60))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_offset_out SyntheticEmbedding.pmGraph t 0 0 40 60 200
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding_offset 0 (pmStore 40) (pmStore 60) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.pmGraph (pmNodes.take 0) pmStore 40 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.pmGraph (pmNodes.take 0) pmStore 60 (by native_decide) (by native_decide)]
        _ = fw_embedding_offset 0 (pmFinal 40) (pmFinal 60) := by rw [hPmWeight0, hPmIds]
    have hPmWeightShape0 : (pmFinal 60).shape = [7, 12] :=
      hWeight.shard_shapes _ (by simp [pmWeightTids])
    have hPmWeight1 : pmFinal 61 = pmStore 61 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.pmGraph pmNodes pmStore 61
        (by native_decide) (by native_decide)
    have hPmWriter1 : pmFinal 201 = fw_embedding_offset 7 (pmFinal 40) (pmFinal 61) := by
      calc
        pmFinal 201 = fw_embedding_offset 7 (((pmNodes.take 1)).foldl
            (applyNodeDistributedFaithful SyntheticEmbedding.pmGraph) pmStore 40) (((pmNodes.take 1)).foldl
            (applyNodeDistributedFaithful SyntheticEmbedding.pmGraph) pmStore 61) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticEmbedding.pmGraph) pmStore) 201 = _
          rw [show pmNodes = (pmNodes.take 1) ++ [{ rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201], params := [7] }] ++ (pmNodes.drop 2) by native_decide]
          apply foldl_faithful_middle_writer SyntheticEmbedding.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2)
            { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201], params := [7] } 201 (fun t => fw_embedding_offset 7 (t 40) (t 61))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_offset_out SyntheticEmbedding.pmGraph t 1 7 40 61 201
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding_offset 7 (pmStore 40) (pmStore 61) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.pmGraph (pmNodes.take 1) pmStore 40 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.pmGraph (pmNodes.take 1) pmStore 61 (by native_decide) (by native_decide)]
        _ = fw_embedding_offset 7 (pmFinal 40) (pmFinal 61) := by rw [hPmWeight1, hPmIds]
    have hPmWeightShape1 : (pmFinal 61).shape = [7, 12] :=
      hWeight.shard_shapes _ (by simp [pmWeightTids])
    have hPmWeight2 : pmFinal 62 = pmStore 62 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.pmGraph pmNodes pmStore 62
        (by native_decide) (by native_decide)
    have hPmWriter2 : pmFinal 202 = fw_embedding_offset 14 (pmFinal 40) (pmFinal 62) := by
      calc
        pmFinal 202 = fw_embedding_offset 14 (((pmNodes.take 2)).foldl
            (applyNodeDistributedFaithful SyntheticEmbedding.pmGraph) pmStore 40) (((pmNodes.take 2)).foldl
            (applyNodeDistributedFaithful SyntheticEmbedding.pmGraph) pmStore 62) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticEmbedding.pmGraph) pmStore) 202 = _
          rw [show pmNodes = (pmNodes.take 2) ++ [{ rank := 2, op := "OpName.FW_embedding", ins := [40, 62], outs := [202], params := [14] }] ++ (pmNodes.drop 3) by native_decide]
          apply foldl_faithful_middle_writer SyntheticEmbedding.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
            { rank := 2, op := "OpName.FW_embedding", ins := [40, 62], outs := [202], params := [14] } 202 (fun t => fw_embedding_offset 14 (t 40) (t 62))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
              (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_offset_out SyntheticEmbedding.pmGraph t 2 14 40 62 202
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding_offset 14 (pmStore 40) (pmStore 62) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.pmGraph (pmNodes.take 2) pmStore 40 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticEmbedding.pmGraph (pmNodes.take 2) pmStore 62 (by native_decide) (by native_decide)]
        _ = fw_embedding_offset 14 (pmFinal 40) (pmFinal 62) := by rw [hPmWeight2, hPmIds]
    have hPmWeightShape2 : (pmFinal 62).shape = [7, 12] :=
      hWeight.shard_shapes _ (by simp [pmWeightTids])
    have hFullShape : (smFinal 100).shape = [1, 8, 12] := by
      rw [hSmWriter, ← hSmIds, ← hSmWeight, fw_embedding_shape, hIdsEq, hIdsShape, hWeight.full_shape]
      rfl
    have hOutValue : smFinal 100 =
        allReducePrim (pmOutputTids.map pmFinal).length 0 (pmOutputTids.map pmFinal) := by
      rw [hSmWriter, ← hSmIds, ← hSmWeight, hIdsEq, hWeight.full_value]
      have hBase := TrainVerify.Denote.fw_embedding_eq_allReduce_offset_shards
        (numParts := rankCount) (shard := 7) (hidden := 12)
        (hparts := by simp [rankCount, pmWeightTids]) (hshard := by omega) (hhid := by omega)
        (ids := pmFinal 40) (Ws := pmWeightTids.map pmFinal)
        (hlen := by simp [rankCount])
        (hWs_head := by
          simp only [pmWeightTids, List.map, List.head?, Option.map, Option.getD]
          exact hWeight.shard_shapes _ (by simp [pmWeightTids]))
        (hWs_shape := by
          intro r hr
          simp only [rankCount, pmWeightTids, List.length_cons, List.length_nil] at hr
          match r with
          | 0 => simpa [pmWeightTids, List.getD] using hPmWeightShape0
          | 1 => simpa [pmWeightTids, List.getD] using hPmWeightShape1
          | 2 => simpa [pmWeightTids, List.getD] using hPmWeightShape2
          | n + 3 => omega)
      simp only [pmWeightTids, pmOutputTids, rankCount, List.map, List.length_cons, List.length_nil,
        List.ofFn_succ, List.ofFn_zero, List.getD] at hBase ⊢
      simp at hBase ⊢
      rw [hBase]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
    have hout : fact_reduction.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 100) (pmOutputTids.map pmFinal) [1, 8, 12]
      refine {
        full_value := hOutValue
        full_shape := hFullShape
        contributions_nonempty := by simp [pmOutputTids]
        contribution_shapes := ?_
        reduced_shape := ?_
      }
      · intro contribution hmem
        simp only [pmOutputTids, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        have hContributionShape0 : (pmFinal 200).shape = [1, 8, 12] := by
          rw [hPmWriter0, fw_embedding_offset_shape, hIdsShape, hPmWeightShape0]
          rfl
        have hContributionShape1 : (pmFinal 201).shape = [1, 8, 12] := by
          rw [hPmWriter1, fw_embedding_offset_shape, hIdsShape, hPmWeightShape1]
          rfl
        have hContributionShape2 : (pmFinal 202).shape = [1, 8, 12] := by
          rw [hPmWriter2, fw_embedding_offset_shape, hIdsShape, hPmWeightShape2]
          rfl
        rcases hmem with h0 | h1 | h2
        · subst contribution
          exact hContributionShape0
        · subst contribution
          exact hContributionShape1
        · subst contribution
          exact hContributionShape2
      · rw [← hOutValue]
        exact hFullShape
    exact RelationState.Holds.mono_insert hframe hout (by native_decide)

#print axioms segment_000000
end
end TrainVerify.Denote.SyntheticEmbedding
