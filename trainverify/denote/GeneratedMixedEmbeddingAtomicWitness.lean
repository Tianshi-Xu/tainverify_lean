/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.SyntheticMixedEmbedding

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_hidden_weight : RelationFact :=
  .sharded 50 [60, 61, 62] 1 [7, 12] [7, 4]

private def fact_vocab_weight : RelationFact :=
  .sharded 51 [80, 81, 82] 0 [21, 12] [7, 12]

private def fact_hidden_output : RelationFact :=
  .sharded 100 [200, 201, 202] 2 [1, 8, 12] [1, 8, 4]

private def fact_reduction : RelationFact :=
  .reduction 101 [300, 301, 302] [1, 8, 12]

private def hidden_eq : RelationFact :=
  .tensorEq .sm 40 .pm 40

private def hidden_shape : RelationFact :=
  .tensorShape .pm 40 [1, 8]

private def vocab_eq : RelationFact :=
  .tensorEq .sm 41 .pm 41

private def vocab_shape : RelationFact :=
  .tensorShape .pm 41 [1, 8]

private def anchor : RelationFact :=
  .tensorShape .sm 999 [1]

private def state_pre : RelationState where
  facts := [anchor, hidden_eq, hidden_shape, vocab_eq, vocab_shape, fact_hidden_weight, fact_vocab_weight]
  nonempty := by decide

private def state_post : RelationState where
  facts := [anchor, hidden_eq, hidden_shape, vocab_eq, vocab_shape, fact_hidden_output, fact_reduction]
  nonempty := by decide

end
end TrainVerify.Denote.SyntheticMixedEmbedding

namespace TrainVerify.Denote.SyntheticMixedEmbedding
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] }, { rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] }] }
private def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] }, { rank := 0, op := "OpName.FW_embedding", ins := [41, 80], outs := [300], params := [0] }, { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] }, { rank := 1, op := "OpName.FW_embedding", ins := [41, 81], outs := [301], params := [7] }, { rank := 2, op := "OpName.FW_embedding", ins := [40, 62], outs := [202] }, { rank := 2, op := "OpName.FW_embedding", ins := [41, 82], outs := [302], params := [14] }] }
set_option maxHeartbeats 800000 in
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticMixedEmbedding.smGraph SyntheticMixedEmbedding.pmGraph state_pre state_post where
  smNodes := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] }, { rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] }]
  pmNodes := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] }, { rank := 0, op := "OpName.FW_embedding", ins := [41, 80], outs := [300], params := [0] }, { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] }, { rank := 1, op := "OpName.FW_embedding", ins := [41, 81], outs := [301], params := [7] }, { rank := 2, op := "OpName.FW_embedding", ins := [40, 62], outs := [202] }, { rank := 2, op := "OpName.FW_embedding", ins := [41, 82], outs := [302], params := [14] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] }, { rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] }]
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] }, { rank := 0, op := "OpName.FW_embedding", ins := [41, 80], outs := [300], params := [0] }, { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] }, { rank := 1, op := "OpName.FW_embedding", ins := [41, 81], outs := [301], params := [7] }, { rank := 2, op := "OpName.FW_embedding", ins := [40, 62], outs := [202] }, { rank := 2, op := "OpName.FW_embedding", ins := [41, 82], outs := [302], params := [14] }]
    let hiddenPmWeightTids : List Tid := [60, 61, 62]
    let hiddenPmOutputTids : List Tid := [200, 201, 202]
    let vocabPmWeightTids : List Tid := [80, 81, 82]
    let vocabPmOutputTids : List Tid := [300, 301, 302]
    let rankCount := hiddenPmWeightTids.length
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hSmHiddenIds : smFinal 40 = smStore 40 := by
      unfold smFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.smGraph smNodes smStore 40 (by native_decide) (by native_decide)
    have hSmHiddenWeight : smFinal 50 = smStore 50 := by
      unfold smFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.smGraph smNodes smStore 50 (by native_decide) (by native_decide)
    have hSmVocabIds : smFinal 41 = smStore 41 := by
      unfold smFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.smGraph smNodes smStore 41 (by native_decide) (by native_decide)
    have hSmVocabWeight : smFinal 51 = smStore 51 := by
      unfold smFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.smGraph smNodes smStore 51 (by native_decide) (by native_decide)
    have hPmHiddenIds : pmFinal 40 = pmStore 40 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph pmNodes pmStore 40 (by native_decide) (by native_decide)
    have hPmVocabIds : pmFinal 41 = pmStore 41 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph pmNodes pmStore 41 (by native_decide) (by native_decide)
    have hHiddenIdsEqStore : smStore 40 = pmStore 40 := by
      have h := hstate hidden_eq (by native_decide)
      change smStore 40 = pmStore 40 at h
      exact h
    have hHiddenIdsShapeStore : (pmStore 40).shape = [1, 8] := by
      have h := hstate hidden_shape (by native_decide)
      change (pmStore 40).shape = [1, 8] at h
      exact h
    have hHiddenIdsEq : smFinal 40 = pmFinal 40 := by
      rw [hSmHiddenIds, hPmHiddenIds]
      exact hHiddenIdsEqStore
    have hHiddenIdsShape : (pmFinal 40).shape = [1, 8] := by
      rw [hPmHiddenIds]
      exact hHiddenIdsShapeStore
    have hVocabIdsEqStore : smStore 41 = pmStore 41 := by
      have h := hstate vocab_eq (by native_decide)
      change smStore 41 = pmStore 41 at h
      exact h
    have hVocabIdsShapeStore : (pmStore 41).shape = [1, 8] := by
      have h := hstate vocab_shape (by native_decide)
      change (pmStore 41).shape = [1, 8] at h
      exact h
    have hVocabIdsEq : smFinal 41 = pmFinal 41 := by
      rw [hSmVocabIds, hPmVocabIds]
      exact hVocabIdsEqStore
    have hVocabIdsShape : (pmFinal 41).shape = [1, 8] := by
      rw [hPmVocabIds]
      exact hVocabIdsShapeStore
    have hHiddenSmWriterInput : smFinal 50 = smStore 50 := by
      unfold smFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.smGraph smNodes smStore 50 (by native_decide) (by native_decide)
    have hHiddenSmWriter : smFinal 100 = fw_embedding (smFinal 40) (smFinal 50) := by
      calc
        smFinal 100 = fw_embedding (((smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.smGraph) smStore 40) (((smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.smGraph) smStore 50) := by
          change (smNodes.foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.smGraph) smStore) 100 = _
          rw [show smNodes = (smNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] }] ++ (smNodes.drop 1) by native_decide]
          apply foldl_faithful_middle_writer SyntheticMixedEmbedding.smGraph smStore (smNodes.take 0) (smNodes.drop 1) { rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] } 100 (fun t => fw_embedding (t 40) (t 50))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_out SyntheticMixedEmbedding.smGraph t 0 40 50 100
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding (smStore 40) (smStore 50) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.smGraph (smNodes.take 0) smStore 40 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.smGraph (smNodes.take 0) smStore 50 (by native_decide) (by native_decide)]
        _ = fw_embedding (smFinal 40) (smFinal 50) := by rw [hHiddenSmWriterInput, hSmHiddenIds]
    have hVocabSmWriterInput : smFinal 51 = smStore 51 := by
      unfold smFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.smGraph smNodes smStore 51 (by native_decide) (by native_decide)
    have hVocabSmWriter : smFinal 101 = fw_embedding (smFinal 41) (smFinal 51) := by
      calc
        smFinal 101 = fw_embedding (((smNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.smGraph) smStore 41) (((smNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.smGraph) smStore 51) := by
          change (smNodes.foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.smGraph) smStore) 101 = _
          rw [show smNodes = (smNodes.take 1) ++ [{ rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] }] ++ (smNodes.drop 2) by native_decide]
          apply foldl_faithful_middle_writer SyntheticMixedEmbedding.smGraph smStore (smNodes.take 1) (smNodes.drop 2) { rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] } 101 (fun t => fw_embedding (t 41) (t 51))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_out SyntheticMixedEmbedding.smGraph t 0 41 51 101
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding (smStore 41) (smStore 51) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.smGraph (smNodes.take 1) smStore 41 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.smGraph (smNodes.take 1) smStore 51 (by native_decide) (by native_decide)]
        _ = fw_embedding (smFinal 41) (smFinal 51) := by rw [hVocabSmWriterInput, hSmVocabIds]
    have hHiddenPmWriter0Input : pmFinal 60 = pmStore 60 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph pmNodes pmStore 60 (by native_decide) (by native_decide)
    have hHiddenPmWriter0 : pmFinal 200 = fw_embedding (pmFinal 40) (pmFinal 60) := by
      calc
        pmFinal 200 = fw_embedding (((pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 40) (((pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 60) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore) 200 = _
          rw [show pmNodes = (pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] }] ++ (pmNodes.drop 1) by native_decide]
          apply foldl_faithful_middle_writer SyntheticMixedEmbedding.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1) { rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] } 200 (fun t => fw_embedding (t 40) (t 60))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_out SyntheticMixedEmbedding.pmGraph t 0 40 60 200
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding (pmStore 40) (pmStore 60) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 0) pmStore 40 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 0) pmStore 60 (by native_decide) (by native_decide)]
        _ = fw_embedding (pmFinal 40) (pmFinal 60) := by rw [hHiddenPmWriter0Input, hPmHiddenIds]
    have hHiddenWeightShape0 : (pmFinal 60).shape = [7, 4] :=
      (hframe fact_hidden_weight (by native_decide)).shard_shapes _ (by simp [hiddenPmWeightTids])
    have hHiddenPmWriter1Input : pmFinal 61 = pmStore 61 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph pmNodes pmStore 61 (by native_decide) (by native_decide)
    have hHiddenPmWriter1 : pmFinal 201 = fw_embedding (pmFinal 40) (pmFinal 61) := by
      calc
        pmFinal 201 = fw_embedding (((pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 40) (((pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 61) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore) 201 = _
          rw [show pmNodes = (pmNodes.take 2) ++ [{ rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] }] ++ (pmNodes.drop 3) by native_decide]
          apply foldl_faithful_middle_writer SyntheticMixedEmbedding.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3) { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] } 201 (fun t => fw_embedding (t 40) (t 61))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_out SyntheticMixedEmbedding.pmGraph t 1 40 61 201
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding (pmStore 40) (pmStore 61) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 2) pmStore 40 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 2) pmStore 61 (by native_decide) (by native_decide)]
        _ = fw_embedding (pmFinal 40) (pmFinal 61) := by rw [hHiddenPmWriter1Input, hPmHiddenIds]
    have hHiddenWeightShape1 : (pmFinal 61).shape = [7, 4] :=
      (hframe fact_hidden_weight (by native_decide)).shard_shapes _ (by simp [hiddenPmWeightTids])
    have hHiddenPmWriter2Input : pmFinal 62 = pmStore 62 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph pmNodes pmStore 62 (by native_decide) (by native_decide)
    have hHiddenPmWriter2 : pmFinal 202 = fw_embedding (pmFinal 40) (pmFinal 62) := by
      calc
        pmFinal 202 = fw_embedding (((pmNodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 40) (((pmNodes.take 4)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 62) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore) 202 = _
          rw [show pmNodes = (pmNodes.take 4) ++ [{ rank := 2, op := "OpName.FW_embedding", ins := [40, 62], outs := [202] }] ++ (pmNodes.drop 5) by native_decide]
          apply foldl_faithful_middle_writer SyntheticMixedEmbedding.pmGraph pmStore (pmNodes.take 4) (pmNodes.drop 5) { rank := 2, op := "OpName.FW_embedding", ins := [40, 62], outs := [202] } 202 (fun t => fw_embedding (t 40) (t 62))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_out SyntheticMixedEmbedding.pmGraph t 2 40 62 202
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding (pmStore 40) (pmStore 62) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 4) pmStore 40 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 4) pmStore 62 (by native_decide) (by native_decide)]
        _ = fw_embedding (pmFinal 40) (pmFinal 62) := by rw [hHiddenPmWriter2Input, hPmHiddenIds]
    have hHiddenWeightShape2 : (pmFinal 62).shape = [7, 4] :=
      (hframe fact_hidden_weight (by native_decide)).shard_shapes _ (by simp [hiddenPmWeightTids])
    have hVocabPmWriter0Input : pmFinal 80 = pmStore 80 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph pmNodes pmStore 80 (by native_decide) (by native_decide)
    have hVocabPmWriter0 : pmFinal 300 = fw_embedding_offset 0 (pmFinal 41) (pmFinal 80) := by
      calc
        pmFinal 300 = fw_embedding_offset 0 (((pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 41) (((pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 80) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore) 300 = _
          rw [show pmNodes = (pmNodes.take 1) ++ [{ rank := 0, op := "OpName.FW_embedding", ins := [41, 80], outs := [300], params := [0] }] ++ (pmNodes.drop 2) by native_decide]
          apply foldl_faithful_middle_writer SyntheticMixedEmbedding.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2) { rank := 0, op := "OpName.FW_embedding", ins := [41, 80], outs := [300], params := [0] } 300 (fun t => fw_embedding_offset 0 (t 41) (t 80))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_offset_out SyntheticMixedEmbedding.pmGraph t 0 0 41 80 300
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding_offset 0 (pmStore 41) (pmStore 80) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 1) pmStore 41 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 1) pmStore 80 (by native_decide) (by native_decide)]
        _ = fw_embedding_offset 0 (pmFinal 41) (pmFinal 80) := by rw [hVocabPmWriter0Input, hPmVocabIds]
    have hVocabWeightShape0 : (pmFinal 80).shape = [7, 12] :=
      (hframe fact_vocab_weight (by native_decide)).shard_shapes _ (by simp [vocabPmWeightTids])
    have hVocabPmWriter1Input : pmFinal 81 = pmStore 81 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph pmNodes pmStore 81 (by native_decide) (by native_decide)
    have hVocabPmWriter1 : pmFinal 301 = fw_embedding_offset 7 (pmFinal 41) (pmFinal 81) := by
      calc
        pmFinal 301 = fw_embedding_offset 7 (((pmNodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 41) (((pmNodes.take 3)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 81) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore) 301 = _
          rw [show pmNodes = (pmNodes.take 3) ++ [{ rank := 1, op := "OpName.FW_embedding", ins := [41, 81], outs := [301], params := [7] }] ++ (pmNodes.drop 4) by native_decide]
          apply foldl_faithful_middle_writer SyntheticMixedEmbedding.pmGraph pmStore (pmNodes.take 3) (pmNodes.drop 4) { rank := 1, op := "OpName.FW_embedding", ins := [41, 81], outs := [301], params := [7] } 301 (fun t => fw_embedding_offset 7 (t 41) (t 81))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_offset_out SyntheticMixedEmbedding.pmGraph t 1 7 41 81 301
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding_offset 7 (pmStore 41) (pmStore 81) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 3) pmStore 41 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 3) pmStore 81 (by native_decide) (by native_decide)]
        _ = fw_embedding_offset 7 (pmFinal 41) (pmFinal 81) := by rw [hVocabPmWriter1Input, hPmVocabIds]
    have hVocabWeightShape1 : (pmFinal 81).shape = [7, 12] :=
      (hframe fact_vocab_weight (by native_decide)).shard_shapes _ (by simp [vocabPmWeightTids])
    have hVocabPmWriter2Input : pmFinal 82 = pmStore 82 := by
      unfold pmFinal
      exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph pmNodes pmStore 82 (by native_decide) (by native_decide)
    have hVocabPmWriter2 : pmFinal 302 = fw_embedding_offset 14 (pmFinal 41) (pmFinal 82) := by
      calc
        pmFinal 302 = fw_embedding_offset 14 (((pmNodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 41) (((pmNodes.take 5)).foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore 82) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedEmbedding.pmGraph) pmStore) 302 = _
          rw [show pmNodes = (pmNodes.take 5) ++ [{ rank := 2, op := "OpName.FW_embedding", ins := [41, 82], outs := [302], params := [14] }] ++ (pmNodes.drop 6) by native_decide]
          apply foldl_faithful_middle_writer SyntheticMixedEmbedding.pmGraph pmStore (pmNodes.take 5) (pmNodes.drop 6) { rank := 2, op := "OpName.FW_embedding", ins := [41, 82], outs := [302], params := [14] } 302 (fun t => fw_embedding_offset 14 (t 41) (t 82))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_embedding_offset_out SyntheticMixedEmbedding.pmGraph t 2 14 41 82 302
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_embedding_offset 14 (pmStore 41) (pmStore 82) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 5) pmStore 41 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedEmbedding.pmGraph (pmNodes.take 5) pmStore 82 (by native_decide) (by native_decide)]
        _ = fw_embedding_offset 14 (pmFinal 41) (pmFinal 82) := by rw [hVocabPmWriter2Input, hPmVocabIds]
    have hVocabWeightShape2 : (pmFinal 82).shape = [7, 12] :=
      (hframe fact_vocab_weight (by native_decide)).shard_shapes _ (by simp [vocabPmWeightTids])
    have hHiddenWeight : fact_hidden_weight.Holds smFinal pmFinal := hframe fact_hidden_weight (by native_decide)
    change ShardedRel (smFinal 50) (hiddenPmWeightTids.map pmFinal) 1 [7, 12] [7, 4] at hHiddenWeight
    have hHiddenFullShape : (smFinal 100).shape = [1, 8, 12] := by
      rw [hHiddenSmWriter, fw_embedding_shape, hHiddenIdsEq, hHiddenIdsShape, hHiddenWeight.full_shape]
      rfl
    have hHiddenValue : smFinal 100 = allGatherPrimDimN 2 (hiddenPmOutputTids.map pmFinal).length 0 (hiddenPmOutputTids.map pmFinal) := by
      rw [hHiddenSmWriter, hHiddenIdsEq, hHiddenWeight.full_value]
      have hBase := TrainVerify.Denote.fw_embedding_hidden_shards_k_rank (K := rankCount) (b := 1) (tokens := 8) (vocab := 7) (hidden := 4)
        (ids := pmFinal 40) (Ws := hiddenPmWeightTids.map pmFinal)
        (hK := by simp [rankCount, hiddenPmWeightTids]) (hb := by omega) (htokens := by omega) (hvocab := by omega) (hhidden := by omega)
        (hlen := by simp [rankCount]) (hids := hHiddenIdsShape)
        (hWs := by intro W hW; simpa [hiddenPmWeightTids] using hHiddenWeight.shard_shapes W (by simpa [hiddenPmWeightTids] using hW))
      simp only [hiddenPmWeightTids, hiddenPmOutputTids, rankCount, List.map, List.length_cons, List.length_nil] at hBase ⊢
      rw [hBase]
      rw [← hHiddenPmWriter0, ← hHiddenPmWriter1, ← hHiddenPmWriter2]
    have hHiddenOut : fact_hidden_output.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 100) (hiddenPmOutputTids.map pmFinal) 2 [1, 8, 12] [1, 8, 4]
      refine { full_value := hHiddenValue, full_shape := hHiddenFullShape, shards_nonempty := by simp [hiddenPmOutputTids], gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := by simp [hiddenPmOutputTids, List.set, List.getD] }
      intro shard hmem
      simp only [hiddenPmOutputTids, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
      have hHiddenOutputShape0 : (pmFinal 200).shape = [1, 8, 4] := by
        rw [hHiddenPmWriter0, fw_embedding_shape, hHiddenIdsShape, hHiddenWeightShape0]
        rfl
      have hHiddenOutputShape1 : (pmFinal 201).shape = [1, 8, 4] := by
        rw [hHiddenPmWriter1, fw_embedding_shape, hHiddenIdsShape, hHiddenWeightShape1]
        rfl
      have hHiddenOutputShape2 : (pmFinal 202).shape = [1, 8, 4] := by
        rw [hHiddenPmWriter2, fw_embedding_shape, hHiddenIdsShape, hHiddenWeightShape2]
        rfl
      rcases hmem with h0 | h1 | h2
      · subst shard
        exact hHiddenOutputShape0
      · subst shard
        exact hHiddenOutputShape1
      · subst shard
        exact hHiddenOutputShape2
    have hVocabWeight : fact_vocab_weight.Holds smFinal pmFinal := hframe fact_vocab_weight (by native_decide)
    change ShardedRel (smFinal 51) (vocabPmWeightTids.map pmFinal) 0 [21, 12] [7, 12] at hVocabWeight
    have hVocabFullShape : (smFinal 101).shape = [1, 8, 12] := by
      rw [hVocabSmWriter, fw_embedding_shape, hVocabIdsEq, hVocabIdsShape, hVocabWeight.full_shape]
      rfl
    have hVocabValue : smFinal 101 = allReducePrim (vocabPmOutputTids.map pmFinal).length 0 (vocabPmOutputTids.map pmFinal) := by
      rw [hVocabSmWriter, hVocabIdsEq, hVocabWeight.full_value]
      have hBase := TrainVerify.Denote.fw_embedding_eq_allReduce_offset_shards (numParts := rankCount) (shard := 7) (hidden := 12)
        (hparts := by simp [rankCount, hiddenPmWeightTids]) (hshard := by omega) (hhid := by omega)
        (ids := pmFinal 41) (Ws := vocabPmWeightTids.map pmFinal) (hlen := by simp [rankCount, hiddenPmWeightTids, vocabPmWeightTids])
        (hWs_head := by simp only [vocabPmWeightTids, List.map, List.head?, Option.map, Option.getD]; exact hVocabWeight.shard_shapes _ (by simp [vocabPmWeightTids]))
        (hWs_shape := by intro r hr; simp only [rankCount, hiddenPmWeightTids, List.length_cons, List.length_nil] at hr; match r with
          | 0 => simpa [vocabPmWeightTids, List.getD] using hVocabWeightShape0
          | 1 => simpa [vocabPmWeightTids, List.getD] using hVocabWeightShape1
          | 2 => simpa [vocabPmWeightTids, List.getD] using hVocabWeightShape2
          | n + 3 => omega)
      simp only [hiddenPmWeightTids, vocabPmWeightTids, vocabPmOutputTids, rankCount, List.map, List.length_cons, List.length_nil, List.ofFn_succ, List.ofFn_zero, List.getD] at hBase ⊢
      simp at hBase ⊢
      rw [hBase]
      rw [← hVocabPmWriter0, ← hVocabPmWriter1, ← hVocabPmWriter2]
    have hVocabOut : fact_reduction.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 101) (vocabPmOutputTids.map pmFinal) [1, 8, 12]
      refine { full_value := hVocabValue, full_shape := hVocabFullShape, contributions_nonempty := by simp [vocabPmOutputTids], contribution_shapes := ?_, reduced_shape := by rw [← hVocabValue]; exact hVocabFullShape }
      intro contribution hmem
      simp only [vocabPmOutputTids, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
      have hVocabOutputShape0 : (pmFinal 300).shape = [1, 8, 12] := by
        rw [hVocabPmWriter0, fw_embedding_offset_shape, hVocabIdsShape, hVocabWeightShape0]
        rfl
      have hVocabOutputShape1 : (pmFinal 301).shape = [1, 8, 12] := by
        rw [hVocabPmWriter1, fw_embedding_offset_shape, hVocabIdsShape, hVocabWeightShape1]
        rfl
      have hVocabOutputShape2 : (pmFinal 302).shape = [1, 8, 12] := by
        rw [hVocabPmWriter2, fw_embedding_offset_shape, hVocabIdsShape, hVocabWeightShape2]
        rfl
      rcases hmem with h0 | h1 | h2
      · subst contribution
        exact hVocabOutputShape0
      · subst contribution
        exact hVocabOutputShape1
      · subst contribution
        exact hVocabOutputShape2
    let mid : RelationState := { facts := fact_hidden_output :: state_pre.facts, nonempty := by simp }
    have hmid : mid.Holds smFinal pmFinal := by
      exact RelationState.Holds.mono_insert (before := state_pre) (after := mid) (fresh := fact_hidden_output) hframe hHiddenOut (by native_decide)
    exact RelationState.Holds.mono_insert (before := mid) (after := state_post) (fresh := fact_reduction) hmid hVocabOut (by native_decide)

#print axioms segment_000000
end
end TrainVerify.Denote.SyntheticMixedEmbedding
