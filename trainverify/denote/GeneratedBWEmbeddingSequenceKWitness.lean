import denote.GraphGears
import denote.BWEmbeddingSequenceShardK
import denote.BWEmbeddingVocabShardK
import denote.RelationCompiler
open TrainVerify.Denote

namespace BWSeqGraphK1
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.ChunkPrim", ins := [2], outs := [200], params := [1] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }] }
end BWSeqGraphK1
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWSeqK1

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100] 1 [3, 2, 5] [3, 2, 5]

private def fact_i : RelationFact :=
  .chunked 2 [200] 1 [3, 2] [3, 2]

private def fact_w : RelationFact :=
  .sharded 3 [3] 0 [11, 5] [11, 5]

private def fact_o : RelationFact :=
  .reduction 4 [300] [11, 5]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [3, 2, 5]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSeqGraphK1.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSeqGraphK1.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK1.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK1.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK1.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK1.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK1.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK1.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 300 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK1.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 300 = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.pm) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.pm) pmStore 200) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.pm) pmStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK1.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } 300
      (fun t => bw_embedding (t 100) (t 200) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK1.pm t 0 100 200 3 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK1.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.pm) pmStore 200 = (segment_000000_pm_final pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK1.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.pm) pmStore 3 = (segment_000000_pm_final pmStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK1.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 300 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.pm) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.pm) pmStore 200) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK1.pm) pmStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 1) [pmFinal 100] 1 [3, 2, 5] [3, 2, 5] at hg
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ChunkedRel (smFinal 2) [pmFinal 200] 1 [3, 2] [3, 2] at hi
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 3] 0 [11, 5] [11, 5] at hw
  have hwEq : smFinal 3 = pmFinal 3 := by
    rw [hw.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes (pmFinal 3) (by simp)]; native_decide)
  have hgValue : smFinal 1 = allGatherPrimDimN 1 1 0 [pmFinal 100] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1)
    (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 300 =
    bw_embedding (pmFinal 100)
      (pmFinal 200) (pmFinal 3) at hPm0
  have hComm := TrainVerify.Denote.bw_embedding_seqchunk_K 1 3 2 5 11
    [pmFinal 100] (smFinal 2) (pmFinal 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) hg.shard_shapes hi.full_shape
    (hw.shard_shapes (pmFinal 3) (by simp))
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hComm
  have hIdChunk0 := hi.chunk_values 0 (by simp)
  simp [List.getD] at hIdChunk0
  have hValue : smFinal 4 = tensorSum [pmFinal 300] := by
    rw [hSm, hgValue, hwEq, hComm]
    rw [← hIdChunk0]
    rw [← hPm0]
  have hValueReduce : smFinal 4 =
      allReducePrim [pmFinal 300].length 0 [pmFinal 300] := by
    rw [hValue]
    rfl
  have hFullShape : (smFinal 4).shape = [11, 5] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hShape0 : (pmFinal 300).shape = [11, 5] := by
    rw [hPm0, bw_embedding_shape]
    exact hw.shard_shapes _ (by simp)
  have hout : fact_o.Holds smFinal pmFinal := by
    change ReductionRel (smFinal 4) [pmFinal 300] [11, 5]
    refine {
      full_value := hValueReduce
      full_shape := hFullShape
      contributions_nonempty := by simp
      contribution_shapes := ?_
      reduced_shape := ?_
    }
    · intro contribution hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl
      · exact hShape0
    · rw [← hValueReduce]
      exact hFullShape
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate
    BWSeqGraphK1.sm BWSeqGraphK1.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWSeqK1

namespace BWSeqGraphK2
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.ChunkPrim", ins := [2], outs := [200], params := [1] }, { rank := 1, op := "OpName.ChunkPrim", ins := [2], outs := [201], params := [1] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] }] }
end BWSeqGraphK2
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWSeqK2

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100, 101] 1 [1, 16, 64] [1, 8, 64]

private def fact_i : RelationFact :=
  .chunked 2 [200, 201] 1 [1, 16] [1, 8]

private def fact_w : RelationFact :=
  .sharded 3 [3] 0 [16, 64] [16, 64]

private def fact_o : RelationFact :=
  .reduction 4 [300, 301] [16, 64]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [1, 16, 64]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSeqGraphK2.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK2.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK2.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK2.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK2.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK2.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK2.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 300 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 300 = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 200) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } 300
      (fun t => bw_embedding (t 100) (t 200) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK2.pm t 0 100 200 3 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 200 = (segment_000000_pm_final pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 3 = (segment_000000_pm_final pmStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 300 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 200) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 301 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) ((segment_000000_pm_final pmStore) 3) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 301 = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 101) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 201) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } 301
      (fun t => bw_embedding (t 101) (t 201) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK2.pm t 1 101 201 3 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 101
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 201 = (segment_000000_pm_final pmStore) 201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 201
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 3 = (segment_000000_pm_final pmStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 301 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) ((segment_000000_pm_final pmStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 101) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 201) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK2.pm) pmStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) ((segment_000000_pm_final pmStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 1) [pmFinal 100, pmFinal 101] 1 [1, 16, 64] [1, 8, 64] at hg
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ChunkedRel (smFinal 2) [pmFinal 200, pmFinal 201] 1 [1, 16] [1, 8] at hi
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 3] 0 [16, 64] [16, 64] at hw
  have hwEq : smFinal 3 = pmFinal 3 := by
    rw [hw.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes (pmFinal 3) (by simp)]; native_decide)
  have hgValue : smFinal 1 = allGatherPrimDimN 1 2 0 [pmFinal 100, pmFinal 101] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1)
    (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 300 =
    bw_embedding (pmFinal 100)
      (pmFinal 200) (pmFinal 3) at hPm0
  have hPm1 := segment_000000_hPmWriter1 pmStore
  change pmFinal 301 =
    bw_embedding (pmFinal 101)
      (pmFinal 201) (pmFinal 3) at hPm1
  have hComm := TrainVerify.Denote.bw_embedding_seqchunk_K 2 1 8 64 16
    [pmFinal 100, pmFinal 101] (smFinal 2) (pmFinal 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) hg.shard_shapes hi.full_shape
    (hw.shard_shapes (pmFinal 3) (by simp))
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hComm
  have hIdChunk0 := hi.chunk_values 0 (by simp)
  simp [List.getD] at hIdChunk0
  have hIdChunk1 := hi.chunk_values 1 (by simp)
  simp [List.getD] at hIdChunk1
  have hValue : smFinal 4 = tensorSum [pmFinal 300, pmFinal 301] := by
    rw [hSm, hgValue, hwEq, hComm]
    rw [← hIdChunk0]
    rw [← hPm0]
    rw [← hIdChunk1]
    rw [← hPm1]
  have hValueReduce : smFinal 4 =
      allReducePrim [pmFinal 300, pmFinal 301].length 0 [pmFinal 300, pmFinal 301] := by
    rw [hValue]
    rfl
  have hFullShape : (smFinal 4).shape = [16, 64] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hShape0 : (pmFinal 300).shape = [16, 64] := by
    rw [hPm0, bw_embedding_shape]
    exact hw.shard_shapes _ (by simp)
  have hShape1 : (pmFinal 301).shape = [16, 64] := by
    rw [hPm1, bw_embedding_shape]
    exact hw.shard_shapes _ (by simp)
  have hout : fact_o.Holds smFinal pmFinal := by
    change ReductionRel (smFinal 4) [pmFinal 300, pmFinal 301] [16, 64]
    refine {
      full_value := hValueReduce
      full_shape := hFullShape
      contributions_nonempty := by simp
      contribution_shapes := ?_
      reduced_shape := ?_
    }
    · intro contribution hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hShape0
      · exact hShape1
    · rw [← hValueReduce]
      exact hFullShape
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate
    BWSeqGraphK2.sm BWSeqGraphK2.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWSeqK2

namespace BWSeqGraphK3
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.ChunkPrim", ins := [2], outs := [200], params := [1] }, { rank := 1, op := "OpName.ChunkPrim", ins := [2], outs := [201], params := [1] }, { rank := 2, op := "OpName.ChunkPrim", ins := [2], outs := [202], params := [1] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] }, { rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] }] }
end BWSeqGraphK3
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWSeqK3

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100, 101, 102] 1 [2, 15, 7] [2, 5, 7]

private def fact_i : RelationFact :=
  .chunked 2 [200, 201, 202] 1 [2, 15] [2, 5]

private def fact_w : RelationFact :=
  .sharded 3 [3] 0 [13, 7] [13, 7]

private def fact_o : RelationFact :=
  .reduction 4 [300, 301, 302] [13, 7]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [2, 15, 7]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] }, { rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSeqGraphK3.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK3.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK3.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK3.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 300 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 300 = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 200) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } 300
      (fun t => bw_embedding (t 100) (t 200) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK3.pm t 0 100 200 3 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 200 = (segment_000000_pm_final pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 3 = (segment_000000_pm_final pmStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 300 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 200) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 301 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) ((segment_000000_pm_final pmStore) 3) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 301 = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 101) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 201) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } 301
      (fun t => bw_embedding (t 101) (t 201) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK3.pm t 1 101 201 3 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 101
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 201 = (segment_000000_pm_final pmStore) 201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 201
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 3 = (segment_000000_pm_final pmStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 301 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) ((segment_000000_pm_final pmStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 101) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 201) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) ((segment_000000_pm_final pmStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 302 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) ((segment_000000_pm_final pmStore) 3) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 302 = bw_embedding (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 102) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 202) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] } 302
      (fun t => bw_embedding (t 102) (t 202) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK3.pm t 2 102 202 3 302
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] } :: (segment_000000_pm_nodes.drop 3)) 102
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 202 = (segment_000000_pm_final pmStore) 202 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] } :: (segment_000000_pm_nodes.drop 3)) 202
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 3 = (segment_000000_pm_final pmStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] } :: (segment_000000_pm_nodes.drop 3)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 302 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) ((segment_000000_pm_final pmStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 102) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 202) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK3.pm) pmStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) ((segment_000000_pm_final pmStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 1) [pmFinal 100, pmFinal 101, pmFinal 102] 1 [2, 15, 7] [2, 5, 7] at hg
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ChunkedRel (smFinal 2) [pmFinal 200, pmFinal 201, pmFinal 202] 1 [2, 15] [2, 5] at hi
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 3] 0 [13, 7] [13, 7] at hw
  have hwEq : smFinal 3 = pmFinal 3 := by
    rw [hw.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes (pmFinal 3) (by simp)]; native_decide)
  have hgValue : smFinal 1 = allGatherPrimDimN 1 3 0 [pmFinal 100, pmFinal 101, pmFinal 102] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1)
    (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 300 =
    bw_embedding (pmFinal 100)
      (pmFinal 200) (pmFinal 3) at hPm0
  have hPm1 := segment_000000_hPmWriter1 pmStore
  change pmFinal 301 =
    bw_embedding (pmFinal 101)
      (pmFinal 201) (pmFinal 3) at hPm1
  have hPm2 := segment_000000_hPmWriter2 pmStore
  change pmFinal 302 =
    bw_embedding (pmFinal 102)
      (pmFinal 202) (pmFinal 3) at hPm2
  have hComm := TrainVerify.Denote.bw_embedding_seqchunk_K 3 2 5 7 13
    [pmFinal 100, pmFinal 101, pmFinal 102] (smFinal 2) (pmFinal 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) hg.shard_shapes hi.full_shape
    (hw.shard_shapes (pmFinal 3) (by simp))
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hComm
  have hIdChunk0 := hi.chunk_values 0 (by simp)
  simp [List.getD] at hIdChunk0
  have hIdChunk1 := hi.chunk_values 1 (by simp)
  simp [List.getD] at hIdChunk1
  have hIdChunk2 := hi.chunk_values 2 (by simp)
  simp [List.getD] at hIdChunk2
  have hValue : smFinal 4 = tensorSum [pmFinal 300, pmFinal 301, pmFinal 302] := by
    rw [hSm, hgValue, hwEq, hComm]
    rw [← hIdChunk0]
    rw [← hPm0]
    rw [← hIdChunk1]
    rw [← hPm1]
    rw [← hIdChunk2]
    rw [← hPm2]
  have hValueReduce : smFinal 4 =
      allReducePrim [pmFinal 300, pmFinal 301, pmFinal 302].length 0 [pmFinal 300, pmFinal 301, pmFinal 302] := by
    rw [hValue]
    rfl
  have hFullShape : (smFinal 4).shape = [13, 7] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hShape0 : (pmFinal 300).shape = [13, 7] := by
    rw [hPm0, bw_embedding_shape]
    exact hw.shard_shapes _ (by simp)
  have hShape1 : (pmFinal 301).shape = [13, 7] := by
    rw [hPm1, bw_embedding_shape]
    exact hw.shard_shapes _ (by simp)
  have hShape2 : (pmFinal 302).shape = [13, 7] := by
    rw [hPm2, bw_embedding_shape]
    exact hw.shard_shapes _ (by simp)
  have hout : fact_o.Holds smFinal pmFinal := by
    change ReductionRel (smFinal 4) [pmFinal 300, pmFinal 301, pmFinal 302] [13, 7]
    refine {
      full_value := hValueReduce
      full_shape := hFullShape
      contributions_nonempty := by simp
      contribution_shapes := ?_
      reduced_shape := ?_
    }
    · intro contribution hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hShape0
      · exact hShape1
      · exact hShape2
    · rw [← hValueReduce]
      exact hFullShape
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate
    BWSeqGraphK3.sm BWSeqGraphK3.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWSeqK3

namespace BWSeqGraphK4
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.ChunkPrim", ins := [2], outs := [200], params := [1] }, { rank := 1, op := "OpName.ChunkPrim", ins := [2], outs := [201], params := [1] }, { rank := 2, op := "OpName.ChunkPrim", ins := [2], outs := [202], params := [1] }, { rank := 3, op := "OpName.ChunkPrim", ins := [2], outs := [203], params := [1] }, { rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] }, { rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] }, { rank := 3, op := "OpName.BW_embedding", ins := [103, 203, 3], outs := [303] }] }
end BWSeqGraphK4
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWSeqK4

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100, 101, 102, 103] 1 [1, 16, 64] [1, 4, 64]

private def fact_i : RelationFact :=
  .chunked 2 [200, 201, 202, 203] 1 [1, 16] [1, 4]

private def fact_w : RelationFact :=
  .sharded 3 [3] 0 [16, 64] [16, 64]

private def fact_o : RelationFact :=
  .reduction 4 [300, 301, 302, 303] [16, 64]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [1, 16, 64]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }, { rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] }, { rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] }, { rank := 3, op := "OpName.BW_embedding", ins := [103, 203, 3], outs := [303] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWSeqGraphK4.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK4.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK4.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK4.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 300 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 300 = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 200) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } 300
      (fun t => bw_embedding (t 100) (t 200) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK4.pm t 0 100 200 3 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 200 = (segment_000000_pm_final pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3 = (segment_000000_pm_final pmStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [100, 200, 3], outs := [300] } :: (segment_000000_pm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 300 = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 100) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 200) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 200) ((segment_000000_pm_final pmStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 301 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) ((segment_000000_pm_final pmStore) 3) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 301 = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 101) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 201) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } 301
      (fun t => bw_embedding (t 101) (t 201) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK4.pm t 1 101 201 3 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 101
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 201 = (segment_000000_pm_final pmStore) 201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 201
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3 = (segment_000000_pm_final pmStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [101, 201, 3], outs := [301] } :: (segment_000000_pm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 301 = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) ((segment_000000_pm_final pmStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 101) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 201) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 201) ((segment_000000_pm_final pmStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 302 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) ((segment_000000_pm_final pmStore) 3) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 302 = bw_embedding (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 102) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 202) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] } 302
      (fun t => bw_embedding (t 102) (t 202) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK4.pm t 2 102 202 3 302
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] } :: (segment_000000_pm_nodes.drop 3)) 102
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 202 = (segment_000000_pm_final pmStore) 202 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] } :: (segment_000000_pm_nodes.drop 3)) 202
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3 = (segment_000000_pm_final pmStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [102, 202, 3], outs := [302] } :: (segment_000000_pm_nodes.drop 3)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 302 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) ((segment_000000_pm_final pmStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 102) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 202) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 202) ((segment_000000_pm_final pmStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 303 = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 203) ((segment_000000_pm_final pmStore) 3) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl
      (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_embedding", ins := [103, 203, 3], outs := [303] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 303 = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 103) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 203) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_embedding", ins := [103, 203, 3], outs := [303] } 303
      (fun t => bw_embedding (t 103) (t 203) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWSeqGraphK4.pm t 3 103 203 3 303
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 103 = (segment_000000_pm_final pmStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_embedding", ins := [103, 203, 3], outs := [303] } :: (segment_000000_pm_nodes.drop 4)) 103
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 203 = (segment_000000_pm_final pmStore) 203 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_embedding", ins := [103, 203, 3], outs := [303] } :: (segment_000000_pm_nodes.drop 4)) 203
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3 = (segment_000000_pm_final pmStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWSeqGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_embedding", ins := [103, 203, 3], outs := [303] } :: (segment_000000_pm_nodes.drop 4)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 303 = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 203) ((segment_000000_pm_final pmStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 103) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 203) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWSeqGraphK4.pm) pmStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 203) ((segment_000000_pm_final pmStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 1) [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] 1 [1, 16, 64] [1, 4, 64] at hg
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ChunkedRel (smFinal 2) [pmFinal 200, pmFinal 201, pmFinal 202, pmFinal 203] 1 [1, 16] [1, 4] at hi
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 3] 0 [16, 64] [16, 64] at hw
  have hwEq : smFinal 3 = pmFinal 3 := by
    rw [hw.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes (pmFinal 3) (by simp)]; native_decide)
  have hgValue : smFinal 1 = allGatherPrimDimN 1 4 0 [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1)
    (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 300 =
    bw_embedding (pmFinal 100)
      (pmFinal 200) (pmFinal 3) at hPm0
  have hPm1 := segment_000000_hPmWriter1 pmStore
  change pmFinal 301 =
    bw_embedding (pmFinal 101)
      (pmFinal 201) (pmFinal 3) at hPm1
  have hPm2 := segment_000000_hPmWriter2 pmStore
  change pmFinal 302 =
    bw_embedding (pmFinal 102)
      (pmFinal 202) (pmFinal 3) at hPm2
  have hPm3 := segment_000000_hPmWriter3 pmStore
  change pmFinal 303 =
    bw_embedding (pmFinal 103)
      (pmFinal 203) (pmFinal 3) at hPm3
  have hComm := TrainVerify.Denote.bw_embedding_seqchunk_K 4 1 4 64 16
    [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] (smFinal 2) (pmFinal 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) hg.shard_shapes hi.full_shape
    (hw.shard_shapes (pmFinal 3) (by simp))
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hComm
  have hIdChunk0 := hi.chunk_values 0 (by simp)
  simp [List.getD] at hIdChunk0
  have hIdChunk1 := hi.chunk_values 1 (by simp)
  simp [List.getD] at hIdChunk1
  have hIdChunk2 := hi.chunk_values 2 (by simp)
  simp [List.getD] at hIdChunk2
  have hIdChunk3 := hi.chunk_values 3 (by simp)
  simp [List.getD] at hIdChunk3
  have hValue : smFinal 4 = tensorSum [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] := by
    rw [hSm, hgValue, hwEq, hComm]
    rw [← hIdChunk0]
    rw [← hPm0]
    rw [← hIdChunk1]
    rw [← hPm1]
    rw [← hIdChunk2]
    rw [← hPm2]
    rw [← hIdChunk3]
    rw [← hPm3]
  have hValueReduce : smFinal 4 =
      allReducePrim [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303].length 0 [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] := by
    rw [hValue]
    rfl
  have hFullShape : (smFinal 4).shape = [16, 64] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hShape0 : (pmFinal 300).shape = [16, 64] := by
    rw [hPm0, bw_embedding_shape]
    exact hw.shard_shapes _ (by simp)
  have hShape1 : (pmFinal 301).shape = [16, 64] := by
    rw [hPm1, bw_embedding_shape]
    exact hw.shard_shapes _ (by simp)
  have hShape2 : (pmFinal 302).shape = [16, 64] := by
    rw [hPm2, bw_embedding_shape]
    exact hw.shard_shapes _ (by simp)
  have hShape3 : (pmFinal 303).shape = [16, 64] := by
    rw [hPm3, bw_embedding_shape]
    exact hw.shard_shapes _ (by simp)
  have hout : fact_o.Holds smFinal pmFinal := by
    change ReductionRel (smFinal 4) [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] [16, 64]
    refine {
      full_value := hValueReduce
      full_shape := hFullShape
      contributions_nonempty := by simp
      contribution_shapes := ?_
      reduced_shape := ?_
    }
    · intro contribution hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact hShape0
      · exact hShape1
      · exact hShape2
      · exact hShape3
    · rw [← hValueReduce]
      exact hFullShape
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate
    BWSeqGraphK4.sm BWSeqGraphK4.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWSeqK4

namespace BWVocabGraphK1
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }] }
end BWVocabGraphK1
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWVocabK1

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .joined 1 10 [2, 5, 7]

private def fact_i : RelationFact :=
  .sharded 2 [2] 0 [2, 5] [2, 5]

private def fact_w : RelationFact :=
  .sharded 3 [100] 0 [5, 7] [5, 7]

private def fact_o : RelationFact :=
  .sharded 4 [300] 0 [5, 7] [5, 7]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [2, 5, 7]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK1.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWVocabGraphK1.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK1.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK1.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK1.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) pmStore 10) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) pmStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK1.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } 300
      (fun t => bw_embedding_offset 0 (t 10) (t 2) (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_offset_out BWVocabGraphK1.pm t 0 0 10 2 100 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) pmStore 10 = (segment_000000_pm_final pmStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK1.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK1.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK1.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by
    calc
      _ = bw_embedding_offset 0 (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) pmStore 10) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK1.pm) pmStore 100) := hout_prefix
      _ = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change smFinal 1 = pmFinal 10 ∧ _ ∧ _ at hg
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 2] 0 [2, 5] [2, 5] at hi
  have hiEq : smFinal 2 = pmFinal 2 := by
    rw [hi.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hi.shard_shapes (pmFinal 2) (by simp)]; native_decide)
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 100] 0 [5, 7] [5, 7] at hw
  have hwV : smFinal 3 = allGatherPrimDimN 0 1 0 [pmFinal 100] := by
    simpa only [List.length_cons, List.length_nil] using hw.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 300 = bw_embedding_offset 0 (pmFinal 10) (pmFinal 2) (pmFinal 100) at hPm0
  have hwShape0 := hw.shard_shapes (pmFinal 100) (by simp)
  have houtShape0 : (pmFinal 300).shape = [5, 7] := by
    rw [hPm0, bw_embedding_offset_shape]
    exact hwShape0
  have hComm := TrainVerify.Denote.bw_embedding_eq_allGather_offset_k 1 5 7
    (by decide) (by decide) (by decide)
    (pmFinal 10) (pmFinal 2) [pmFinal 100]
    (by rfl) hw.shard_shapes
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hComm
  have hValue : smFinal 4 = allGatherPrimDimN 0 1 0 [pmFinal 300] := by
    rw [hSm, hg.1, hiEq, hwV, hComm]
    rw [← hPm0]
  have hValueL : smFinal 4 = allGatherPrimDimN 0 [pmFinal 300].length 0 [pmFinal 300] := by
    simpa only [List.length_cons, List.length_nil] using hValue
  have hFullShape : (smFinal 4).shape = [5, 7] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hout : fact_o.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 4) [pmFinal 300] 0 [5, 7] [5, 7]
    refine {
      full_value := hValueL
      full_shape := hFullShape
      shards_nonempty := by simp
      gather_dim_lt := by native_decide
      shard_shapes := ?_
      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
    }
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl
    · exact houtShape0
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate BWVocabGraphK1.sm BWVocabGraphK1.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWVocabK1

namespace BWVocabGraphK2
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }, { rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] }] }
end BWVocabGraphK2
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWVocabK2

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .joined 1 10 [2, 5, 7]

private def fact_i : RelationFact :=
  .sharded 2 [2] 0 [2, 5] [2, 5]

private def fact_w : RelationFact :=
  .sharded 3 [100, 101] 0 [10, 7] [5, 7]

private def fact_o : RelationFact :=
  .sharded 4 [300, 301] 0 [10, 7] [5, 7]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [2, 5, 7]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }, { rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK2.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWVocabGraphK2.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK2.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK2.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK2.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 10) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } 300
      (fun t => bw_embedding_offset 0 (t 10) (t 2) (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_offset_out BWVocabGraphK2.pm t 0 0 10 2 100 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 10 = (segment_000000_pm_final pmStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by
    calc
      _ = bw_embedding_offset 0 (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 10) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 100) := hout_prefix
      _ = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 301 = bw_embedding_offset 5 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 301 = bw_embedding_offset 5 (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 10) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 101) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } 301
      (fun t => bw_embedding_offset 5 (t 10) (t 2) (t 101)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_offset_out BWVocabGraphK2.pm t 1 5 10 2 101 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 10 = (segment_000000_pm_final pmStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } :: (segment_000000_pm_nodes.drop 2)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } :: (segment_000000_pm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK2.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } :: (segment_000000_pm_nodes.drop 2)) 101
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 301 = bw_embedding_offset 5 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by
    calc
      _ = bw_embedding_offset 5 (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 10) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK2.pm) pmStore 101) := hout_prefix
      _ = bw_embedding_offset 5 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change smFinal 1 = pmFinal 10 ∧ _ ∧ _ at hg
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 2] 0 [2, 5] [2, 5] at hi
  have hiEq : smFinal 2 = pmFinal 2 := by
    rw [hi.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hi.shard_shapes (pmFinal 2) (by simp)]; native_decide)
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 100, pmFinal 101] 0 [10, 7] [5, 7] at hw
  have hwV : smFinal 3 = allGatherPrimDimN 0 2 0 [pmFinal 100, pmFinal 101] := by
    simpa only [List.length_cons, List.length_nil] using hw.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 300 = bw_embedding_offset 0 (pmFinal 10) (pmFinal 2) (pmFinal 100) at hPm0
  have hwShape0 := hw.shard_shapes (pmFinal 100) (by simp)
  have houtShape0 : (pmFinal 300).shape = [5, 7] := by
    rw [hPm0, bw_embedding_offset_shape]
    exact hwShape0
  have hPm1 := segment_000000_hPmWriter1 pmStore
  change pmFinal 301 = bw_embedding_offset 5 (pmFinal 10) (pmFinal 2) (pmFinal 101) at hPm1
  have hwShape1 := hw.shard_shapes (pmFinal 101) (by simp)
  have houtShape1 : (pmFinal 301).shape = [5, 7] := by
    rw [hPm1, bw_embedding_offset_shape]
    exact hwShape1
  have hComm := TrainVerify.Denote.bw_embedding_eq_allGather_offset_k 2 5 7
    (by decide) (by decide) (by decide)
    (pmFinal 10) (pmFinal 2) [pmFinal 100, pmFinal 101]
    (by rfl) hw.shard_shapes
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hComm
  have hValue : smFinal 4 = allGatherPrimDimN 0 2 0 [pmFinal 300, pmFinal 301] := by
    rw [hSm, hg.1, hiEq, hwV, hComm]
    rw [← hPm0, ← hPm1]
  have hValueL : smFinal 4 = allGatherPrimDimN 0 [pmFinal 300, pmFinal 301].length 0 [pmFinal 300, pmFinal 301] := by
    simpa only [List.length_cons, List.length_nil] using hValue
  have hFullShape : (smFinal 4).shape = [10, 7] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hout : fact_o.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 4) [pmFinal 300, pmFinal 301] 0 [10, 7] [5, 7]
    refine {
      full_value := hValueL
      full_shape := hFullShape
      shards_nonempty := by simp
      gather_dim_lt := by native_decide
      shard_shapes := ?_
      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
    }
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact houtShape0
    · exact houtShape1
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate BWVocabGraphK2.sm BWVocabGraphK2.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWVocabK2

namespace BWVocabGraphK3
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }, { rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] }, { rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] }] }
end BWVocabGraphK3
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWVocabK3

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .joined 1 10 [2, 5, 7]

private def fact_i : RelationFact :=
  .sharded 2 [2] 0 [2, 5] [2, 5]

private def fact_w : RelationFact :=
  .sharded 3 [100, 101, 102] 0 [15, 7] [5, 7]

private def fact_o : RelationFact :=
  .sharded 4 [300, 301, 302] 0 [15, 7] [5, 7]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [2, 5, 7]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }, { rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] }, { rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK3.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWVocabGraphK3.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 10) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } 300
      (fun t => bw_embedding_offset 0 (t 10) (t 2) (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_offset_out BWVocabGraphK3.pm t 0 0 10 2 100 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 10 = (segment_000000_pm_final pmStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by
    calc
      _ = bw_embedding_offset 0 (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 10) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 100) := hout_prefix
      _ = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 301 = bw_embedding_offset 5 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 301 = bw_embedding_offset 5 (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 10) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 101) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } 301
      (fun t => bw_embedding_offset 5 (t 10) (t 2) (t 101)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_offset_out BWVocabGraphK3.pm t 1 5 10 2 101 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 10 = (segment_000000_pm_final pmStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } :: (segment_000000_pm_nodes.drop 2)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } :: (segment_000000_pm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } :: (segment_000000_pm_nodes.drop 2)) 101
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 301 = bw_embedding_offset 5 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by
    calc
      _ = bw_embedding_offset 5 (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 10) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 101) := hout_prefix
      _ = bw_embedding_offset 5 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 302 = bw_embedding_offset 10 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 102) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 302 = bw_embedding_offset 10 (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 10) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 2) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 102) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] } 302
      (fun t => bw_embedding_offset 10 (t 10) (t 2) (t 102)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_offset_out BWVocabGraphK3.pm t 2 10 10 2 102 302
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 10 = (segment_000000_pm_final pmStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] } :: (segment_000000_pm_nodes.drop 3)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] } :: (segment_000000_pm_nodes.drop 3)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK3.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] } :: (segment_000000_pm_nodes.drop 3)) 102
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 302 = bw_embedding_offset 10 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 102) := by
    calc
      _ = bw_embedding_offset 10 (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 10) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 2) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK3.pm) pmStore 102) := hout_prefix
      _ = bw_embedding_offset 10 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 102) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change smFinal 1 = pmFinal 10 ∧ _ ∧ _ at hg
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 2] 0 [2, 5] [2, 5] at hi
  have hiEq : smFinal 2 = pmFinal 2 := by
    rw [hi.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hi.shard_shapes (pmFinal 2) (by simp)]; native_decide)
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 100, pmFinal 101, pmFinal 102] 0 [15, 7] [5, 7] at hw
  have hwV : smFinal 3 = allGatherPrimDimN 0 3 0 [pmFinal 100, pmFinal 101, pmFinal 102] := by
    simpa only [List.length_cons, List.length_nil] using hw.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 300 = bw_embedding_offset 0 (pmFinal 10) (pmFinal 2) (pmFinal 100) at hPm0
  have hwShape0 := hw.shard_shapes (pmFinal 100) (by simp)
  have houtShape0 : (pmFinal 300).shape = [5, 7] := by
    rw [hPm0, bw_embedding_offset_shape]
    exact hwShape0
  have hPm1 := segment_000000_hPmWriter1 pmStore
  change pmFinal 301 = bw_embedding_offset 5 (pmFinal 10) (pmFinal 2) (pmFinal 101) at hPm1
  have hwShape1 := hw.shard_shapes (pmFinal 101) (by simp)
  have houtShape1 : (pmFinal 301).shape = [5, 7] := by
    rw [hPm1, bw_embedding_offset_shape]
    exact hwShape1
  have hPm2 := segment_000000_hPmWriter2 pmStore
  change pmFinal 302 = bw_embedding_offset 10 (pmFinal 10) (pmFinal 2) (pmFinal 102) at hPm2
  have hwShape2 := hw.shard_shapes (pmFinal 102) (by simp)
  have houtShape2 : (pmFinal 302).shape = [5, 7] := by
    rw [hPm2, bw_embedding_offset_shape]
    exact hwShape2
  have hComm := TrainVerify.Denote.bw_embedding_eq_allGather_offset_k 3 5 7
    (by decide) (by decide) (by decide)
    (pmFinal 10) (pmFinal 2) [pmFinal 100, pmFinal 101, pmFinal 102]
    (by rfl) hw.shard_shapes
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hComm
  have hValue : smFinal 4 = allGatherPrimDimN 0 3 0 [pmFinal 300, pmFinal 301, pmFinal 302] := by
    rw [hSm, hg.1, hiEq, hwV, hComm]
    rw [← hPm0, ← hPm1, ← hPm2]
  have hValueL : smFinal 4 = allGatherPrimDimN 0 [pmFinal 300, pmFinal 301, pmFinal 302].length 0 [pmFinal 300, pmFinal 301, pmFinal 302] := by
    simpa only [List.length_cons, List.length_nil] using hValue
  have hFullShape : (smFinal 4).shape = [15, 7] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hout : fact_o.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 4) [pmFinal 300, pmFinal 301, pmFinal 302] 0 [15, 7] [5, 7]
    refine {
      full_value := hValueL
      full_shape := hFullShape
      shards_nonempty := by simp
      gather_dim_lt := by native_decide
      shard_shapes := ?_
      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
    }
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact houtShape0
    · exact houtShape1
    · exact houtShape2
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate BWVocabGraphK3.sm BWVocabGraphK3.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWVocabK3

namespace BWVocabGraphK4
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }, { rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] }, { rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] }, { rank := 3, op := "OpName.BW_embedding", ins := [10, 2, 103], outs := [303], params := [15] }] }
end BWVocabGraphK4
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWVocabK4

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .joined 1 10 [2, 5, 7]

private def fact_i : RelationFact :=
  .sharded 2 [2] 0 [2, 5] [2, 5]

private def fact_w : RelationFact :=
  .sharded 3 [100, 101, 102, 103] 0 [20, 7] [5, 7]

private def fact_o : RelationFact :=
  .sharded 4 [300, 301, 302, 303] 0 [20, 7] [5, 7]

private def unused_anchor : RelationFact :=
  .tensorShape .sm 1 [2, 5, 7]

private def state_before : RelationState where
  facts := [fact_g, fact_i, fact_w]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_i, fact_w, fact_o]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }, { rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] }, { rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] }, { rank := 3, op := "OpName.BW_embedding", ins := [10, 2, 103], outs := [303], params := [15] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) s

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK4.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWVocabGraphK4.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 1)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) smStore 1) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) smStore 2) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } 300
      (fun t => bw_embedding_offset 0 (t 10) (t 2) (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_offset_out BWVocabGraphK4.pm t 0 0 10 2 100 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10 = (segment_000000_pm_final pmStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [10, 2, 100], outs := [300], params := [0] } :: (segment_000000_pm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 300 = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by
    calc
      _ = bw_embedding_offset 0 (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 100) := hout_prefix
      _ = bw_embedding_offset 0 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 100) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 301 = bw_embedding_offset 5 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 301 = bw_embedding_offset 5 (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 101) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } 301
      (fun t => bw_embedding_offset 5 (t 10) (t 2) (t 101)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_offset_out BWVocabGraphK4.pm t 1 5 10 2 101 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10 = (segment_000000_pm_final pmStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } :: (segment_000000_pm_nodes.drop 2)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } :: (segment_000000_pm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [10, 2, 101], outs := [301], params := [5] } :: (segment_000000_pm_nodes.drop 2)) 101
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 301 = bw_embedding_offset 5 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by
    calc
      _ = bw_embedding_offset 5 (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 101) := hout_prefix
      _ = bw_embedding_offset 5 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 101) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 302 = bw_embedding_offset 10 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 102) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 302 = bw_embedding_offset 10 (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 102) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] } 302
      (fun t => bw_embedding_offset 10 (t 10) (t 2) (t 102)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_offset_out BWVocabGraphK4.pm t 2 10 10 2 102 302
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10 = (segment_000000_pm_final pmStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] } :: (segment_000000_pm_nodes.drop 3)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] } :: (segment_000000_pm_nodes.drop 3)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [10, 2, 102], outs := [302], params := [10] } :: (segment_000000_pm_nodes.drop 3)) 102
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 302 = bw_embedding_offset 10 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 102) := by
    calc
      _ = bw_embedding_offset 10 (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 102) := hout_prefix
      _ = bw_embedding_offset 10 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 102) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPmWriter3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 303 = bw_embedding_offset 15 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 103) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_embedding", ins := [10, 2, 103], outs := [303], params := [15] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 303 = bw_embedding_offset 15 (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 103) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_embedding", ins := [10, 2, 103], outs := [303], params := [15] } 303
      (fun t => bw_embedding_offset 15 (t 10) (t 2) (t 103)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_offset_out BWVocabGraphK4.pm t 3 15 10 2 103 303
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10 = (segment_000000_pm_final pmStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_embedding", ins := [10, 2, 103], outs := [303], params := [15] } :: (segment_000000_pm_nodes.drop 4)) 10
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_embedding", ins := [10, 2, 103], outs := [303], params := [15] } :: (segment_000000_pm_nodes.drop 4)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 103 = (segment_000000_pm_final pmStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWVocabGraphK4.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_embedding", ins := [10, 2, 103], outs := [303], params := [15] } :: (segment_000000_pm_nodes.drop 4)) 103
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 303 = bw_embedding_offset 15 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 103) := by
    calc
      _ = bw_embedding_offset 15 (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 10) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWVocabGraphK4.pm) pmStore 103) := hout_prefix
      _ = bw_embedding_offset 15 ((segment_000000_pm_final pmStore) 10) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 103) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change smFinal 1 = pmFinal 10 ∧ _ ∧ _ at hg
  have hi : fact_i.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 2] 0 [2, 5] [2, 5] at hi
  have hiEq : smFinal 2 = pmFinal 2 := by
    rw [hi.full_value]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hi.shard_shapes (pmFinal 2) (by simp)]; native_decide)
  have hw : fact_w.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] 0 [20, 7] [5, 7] at hw
  have hwV : smFinal 3 = allGatherPrimDimN 0 4 0 [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] := by
    simpa only [List.length_cons, List.length_nil] using hw.full_value
  have hSm := segment_000000_hSmWriter smStore
  change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
  have hPm0 := segment_000000_hPmWriter0 pmStore
  change pmFinal 300 = bw_embedding_offset 0 (pmFinal 10) (pmFinal 2) (pmFinal 100) at hPm0
  have hwShape0 := hw.shard_shapes (pmFinal 100) (by simp)
  have houtShape0 : (pmFinal 300).shape = [5, 7] := by
    rw [hPm0, bw_embedding_offset_shape]
    exact hwShape0
  have hPm1 := segment_000000_hPmWriter1 pmStore
  change pmFinal 301 = bw_embedding_offset 5 (pmFinal 10) (pmFinal 2) (pmFinal 101) at hPm1
  have hwShape1 := hw.shard_shapes (pmFinal 101) (by simp)
  have houtShape1 : (pmFinal 301).shape = [5, 7] := by
    rw [hPm1, bw_embedding_offset_shape]
    exact hwShape1
  have hPm2 := segment_000000_hPmWriter2 pmStore
  change pmFinal 302 = bw_embedding_offset 10 (pmFinal 10) (pmFinal 2) (pmFinal 102) at hPm2
  have hwShape2 := hw.shard_shapes (pmFinal 102) (by simp)
  have houtShape2 : (pmFinal 302).shape = [5, 7] := by
    rw [hPm2, bw_embedding_offset_shape]
    exact hwShape2
  have hPm3 := segment_000000_hPmWriter3 pmStore
  change pmFinal 303 = bw_embedding_offset 15 (pmFinal 10) (pmFinal 2) (pmFinal 103) at hPm3
  have hwShape3 := hw.shard_shapes (pmFinal 103) (by simp)
  have houtShape3 : (pmFinal 303).shape = [5, 7] := by
    rw [hPm3, bw_embedding_offset_shape]
    exact hwShape3
  have hComm := TrainVerify.Denote.bw_embedding_eq_allGather_offset_k 4 5 7
    (by decide) (by decide) (by decide)
    (pmFinal 10) (pmFinal 2) [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103]
    (by rfl) hw.shard_shapes
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hComm
  have hValue : smFinal 4 = allGatherPrimDimN 0 4 0 [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] := by
    rw [hSm, hg.1, hiEq, hwV, hComm]
    rw [← hPm0, ← hPm1, ← hPm2, ← hPm3]
  have hValueL : smFinal 4 = allGatherPrimDimN 0 [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303].length 0 [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] := by
    simpa only [List.length_cons, List.length_nil] using hValue
  have hFullShape : (smFinal 4).shape = [20, 7] := by
    rw [hSm, bw_embedding_shape]
    exact hw.full_shape
  have hout : fact_o.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 4) [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] 0 [20, 7] [5, 7]
    refine {
      full_value := hValueL
      full_shape := hFullShape
      shards_nonempty := by simp
      gather_dim_lt := by native_decide
      shard_shapes := ?_
      shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
    }
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact houtShape0
    · exact houtShape1
    · exact houtShape2
    · exact houtShape3
  intro fact hfact
  have covered : fact ∈ [fact_o] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_o] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate BWVocabGraphK4.sm BWVocabGraphK4.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
end
end TrainVerify.Denote.GeneratedBWVocabK4
