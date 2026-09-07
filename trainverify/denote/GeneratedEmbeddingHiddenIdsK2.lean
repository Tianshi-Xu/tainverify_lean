import denote.RelationCompiler
import denote.EmbeddingHiddenShard
import denote.EmbeddingSequenceShard
set_option maxHeartbeats 500000
open TrainVerify.Denote
namespace EmbeddingHiddenIdsK2Graph
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] }, { rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] }] }
def pm : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] }, { rank := 0, op := "OpName.ChunkPrim", ins := [41], outs := [300], params := [1] }, { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] }, { rank := 1, op := "OpName.ChunkPrim", ins := [41], outs := [301], params := [1] }, { rank := 0, op := "OpName.FW_embedding", ins := [300, 51], outs := [400] }, { rank := 1, op := "OpName.FW_embedding", ins := [301, 51], outs := [401] }] }
end EmbeddingHiddenIdsK2Graph
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.EmbeddingHiddenIdsK2

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def weight : RelationFact :=
  .sharded 50 [60, 61] 1 [7, 8] [7, 4]

private def hidden_out : RelationFact :=
  .sharded 100 [200, 201] 2 [1, 4, 8] [1, 4, 4]

private def ids_out : RelationFact :=
  .chunked 41 [300, 301] 1 [1, 4] [1, 2]

private def sequence_out : RelationFact :=
  .sharded 101 [400, 401] 1 [1, 4, 12] [1, 2, 12]

private def eq_40 : RelationFact :=
  .tensorEq .sm 40 .pm 40

private def shape_40 : RelationFact :=
  .tensorShape .pm 40 [1, 4]

private def eq_41 : RelationFact :=
  .tensorEq .sm 41 .pm 41

private def shape_41 : RelationFact :=
  .tensorShape .pm 41 [1, 4]

private def eq_51 : RelationFact :=
  .tensorEq .sm 51 .pm 51

private def shape_51 : RelationFact :=
  .tensorShape .pm 51 [7, 12]

private def anchor : RelationFact :=
  .tensorShape .sm 999 [1]

private def state_before : RelationState where
  facts := [anchor, weight, eq_40, shape_40, eq_41, shape_41, eq_51, shape_51]
  nonempty := by decide

private def state_after : RelationState where
  facts := [anchor, weight, eq_40, shape_40, eq_41, shape_41, eq_51, shape_51, hidden_out, ids_out, sequence_out]
  nonempty := by decide

set_option maxHeartbeats 500000
private def segment_000000_smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] }, { rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] }]
private def segment_000000_pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] }, { rank := 0, op := "OpName.ChunkPrim", ins := [41], outs := [300], params := [1] }, { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] }, { rank := 1, op := "OpName.ChunkPrim", ins := [41], outs := [301], params := [1] }, { rank := 0, op := "OpName.FW_embedding", ins := [300, 51], outs := [400] }, { rank := 1, op := "OpName.FW_embedding", ins := [301, 51], outs := [401] }]
private def segment_000000_chunkTids : List Tid := [300, 301]
private def segment_000000_outputTids : List Tid := [400, 401]
private def segment_000000_rankCount : Nat := segment_000000_chunkTids.length
@[irreducible] private def segment_000000_smFinal (store : Store) : Store :=
  segment_000000_smNodes.foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) store
@[irreducible] private def segment_000000_pmFinal (store : Store) : Store :=
  segment_000000_pmNodes.foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) store

private theorem segment_000000_hSmEmbedding (smStore : Store) :
    (segment_000000_smFinal smStore) 101 = fw_embedding ((segment_000000_smFinal smStore) 41) ((segment_000000_smFinal smStore) 51) := by
  have hfinal : (segment_000000_smFinal smStore) = segment_000000_smNodes.foldl
      (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore := by
    unfold segment_000000_smFinal
    rfl
  have hSmEmbedding_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 1) ++ [{ rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] }] ++ (segment_000000_smNodes.drop 2) := by
    native_decide
  have hSmEmbedding_prefix : (segment_000000_smFinal smStore) 101 = fw_embedding (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 41) (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 51) := by
    rw [hfinal, hSmEmbedding_nodes]
    exact foldl_faithful_middle_writer EmbeddingHiddenIdsK2Graph.sm smStore
      (segment_000000_smNodes.take 1) (segment_000000_smNodes.drop 2)
      { rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] } 101
      (fun t => fw_embedding (t 41) (t 51)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_embedding_out EmbeddingHiddenIdsK2Graph.sm t 0 41 51 101
      ) (by native_decide) (by native_decide)
  have hSmEmbedding_read_0 : ((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 41 = (segment_000000_smFinal smStore) 41 := by
    rw [hfinal, hSmEmbedding_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.sm smStore
      (segment_000000_smNodes.take 1) ({ rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] } :: (segment_000000_smNodes.drop 2)) 41
      (by native_decide) (by native_decide)
  have hSmEmbedding_read_1 : ((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 51 = (segment_000000_smFinal smStore) 51 := by
    rw [hfinal, hSmEmbedding_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.sm smStore
      (segment_000000_smNodes.take 1) ({ rank := 0, op := "OpName.FW_embedding", ins := [41, 51], outs := [101] } :: (segment_000000_smNodes.drop 2)) 51
      (by native_decide) (by native_decide)
  have hSmEmbedding : (segment_000000_smFinal smStore) 101 = fw_embedding ((segment_000000_smFinal smStore) 41) ((segment_000000_smFinal smStore) 51) := by
    calc
      _ = fw_embedding (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 41) (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 51) := hSmEmbedding_prefix
      _ = fw_embedding ((segment_000000_smFinal smStore) 41) ((segment_000000_smFinal smStore) 51) := by rw [hSmEmbedding_read_0, hSmEmbedding_read_1]
  exact hSmEmbedding

private theorem segment_000000_hChunk0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 300 = chunkPrimDimN 1 segment_000000_rankCount 0 ((segment_000000_pmFinal pmStore) 41) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl
      (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hRankCount : segment_000000_rankCount = EmbeddingHiddenIdsK2Graph.pm.numRanks := by rfl
  have hChunk0_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 1) ++ [{ rank := 0, op := "OpName.ChunkPrim", ins := [41], outs := [300], params := [1] }] ++ (segment_000000_pmNodes.drop 2) := by
    native_decide
  have hChunk0_prefix : (segment_000000_pmFinal pmStore) 300 = chunkPrimDimN 1 segment_000000_rankCount 0 (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 41) := by
    rw [hfinal, hChunk0_nodes]
    exact foldl_faithful_middle_writer EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 1) (segment_000000_pmNodes.drop 2)
      { rank := 0, op := "OpName.ChunkPrim", ins := [41], outs := [300], params := [1] } 300
      (fun t => chunkPrimDimN 1 segment_000000_rankCount 0 (t 41)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa using applyNode_chunkPrimDimN_out EmbeddingHiddenIdsK2Graph.pm t 0 41 300 1
      ) (by native_decide) (by native_decide)
  have hChunk0_read_0 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 41 = (segment_000000_pmFinal pmStore) 41 := by
    rw [hfinal, hChunk0_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 0, op := "OpName.ChunkPrim", ins := [41], outs := [300], params := [1] } :: (segment_000000_pmNodes.drop 2)) 41
      (by native_decide) (by native_decide)
  have hChunk0 : (segment_000000_pmFinal pmStore) 300 = chunkPrimDimN 1 segment_000000_rankCount 0 ((segment_000000_pmFinal pmStore) 41) := by
    calc
      _ = chunkPrimDimN 1 segment_000000_rankCount 0 (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 41) := hChunk0_prefix
      _ = chunkPrimDimN 1 segment_000000_rankCount 0 ((segment_000000_pmFinal pmStore) 41) := by rw [hChunk0_read_0]
  exact hChunk0

private theorem segment_000000_hChunk1 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 301 = chunkPrimDimN 1 segment_000000_rankCount 1 ((segment_000000_pmFinal pmStore) 41) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl
      (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hRankCount : segment_000000_rankCount = EmbeddingHiddenIdsK2Graph.pm.numRanks := by rfl
  have hChunk1_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 3) ++ [{ rank := 1, op := "OpName.ChunkPrim", ins := [41], outs := [301], params := [1] }] ++ (segment_000000_pmNodes.drop 4) := by
    native_decide
  have hChunk1_prefix : (segment_000000_pmFinal pmStore) 301 = chunkPrimDimN 1 segment_000000_rankCount 1 (((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 41) := by
    rw [hfinal, hChunk1_nodes]
    exact foldl_faithful_middle_writer EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 3) (segment_000000_pmNodes.drop 4)
      { rank := 1, op := "OpName.ChunkPrim", ins := [41], outs := [301], params := [1] } 301
      (fun t => chunkPrimDimN 1 segment_000000_rankCount 1 (t 41)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa using applyNode_chunkPrimDimN_out EmbeddingHiddenIdsK2Graph.pm t 1 41 301 1
      ) (by native_decide) (by native_decide)
  have hChunk1_read_0 : ((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 41 = (segment_000000_pmFinal pmStore) 41 := by
    rw [hfinal, hChunk1_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 3) ({ rank := 1, op := "OpName.ChunkPrim", ins := [41], outs := [301], params := [1] } :: (segment_000000_pmNodes.drop 4)) 41
      (by native_decide) (by native_decide)
  have hChunk1 : (segment_000000_pmFinal pmStore) 301 = chunkPrimDimN 1 segment_000000_rankCount 1 ((segment_000000_pmFinal pmStore) 41) := by
    calc
      _ = chunkPrimDimN 1 segment_000000_rankCount 1 (((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 41) := hChunk1_prefix
      _ = chunkPrimDimN 1 segment_000000_rankCount 1 ((segment_000000_pmFinal pmStore) 41) := by rw [hChunk1_read_0]
  exact hChunk1

private theorem segment_000000_hPmEmbedding0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 400 = fw_embedding ((segment_000000_pmFinal pmStore) 300) ((segment_000000_pmFinal pmStore) 51) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl
      (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hPmEmbedding0_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 4) ++ [{ rank := 0, op := "OpName.FW_embedding", ins := [300, 51], outs := [400] }] ++ (segment_000000_pmNodes.drop 5) := by
    native_decide
  have hPmEmbedding0_prefix : (segment_000000_pmFinal pmStore) 400 = fw_embedding (((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 300) (((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 51) := by
    rw [hfinal, hPmEmbedding0_nodes]
    exact foldl_faithful_middle_writer EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 4) (segment_000000_pmNodes.drop 5)
      { rank := 0, op := "OpName.FW_embedding", ins := [300, 51], outs := [400] } 400
      (fun t => fw_embedding (t 300) (t 51)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_embedding_out EmbeddingHiddenIdsK2Graph.pm t 0 300 51 400
      ) (by native_decide) (by native_decide)
  have hPmEmbedding0_read_0 : ((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 300 = (segment_000000_pmFinal pmStore) 300 := by
    rw [hfinal, hPmEmbedding0_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 4) ({ rank := 0, op := "OpName.FW_embedding", ins := [300, 51], outs := [400] } :: (segment_000000_pmNodes.drop 5)) 300
      (by native_decide) (by native_decide)
  have hPmEmbedding0_read_1 : ((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 51 = (segment_000000_pmFinal pmStore) 51 := by
    rw [hfinal, hPmEmbedding0_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 4) ({ rank := 0, op := "OpName.FW_embedding", ins := [300, 51], outs := [400] } :: (segment_000000_pmNodes.drop 5)) 51
      (by native_decide) (by native_decide)
  have hPmEmbedding0 : (segment_000000_pmFinal pmStore) 400 = fw_embedding ((segment_000000_pmFinal pmStore) 300) ((segment_000000_pmFinal pmStore) 51) := by
    calc
      _ = fw_embedding (((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 300) (((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 51) := hPmEmbedding0_prefix
      _ = fw_embedding ((segment_000000_pmFinal pmStore) 300) ((segment_000000_pmFinal pmStore) 51) := by rw [hPmEmbedding0_read_0, hPmEmbedding0_read_1]
  exact hPmEmbedding0

private theorem segment_000000_hPmEmbedding1 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 401 = fw_embedding ((segment_000000_pmFinal pmStore) 301) ((segment_000000_pmFinal pmStore) 51) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl
      (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hPmEmbedding1_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 5) ++ [{ rank := 1, op := "OpName.FW_embedding", ins := [301, 51], outs := [401] }] ++ (segment_000000_pmNodes.drop 6) := by
    native_decide
  have hPmEmbedding1_prefix : (segment_000000_pmFinal pmStore) 401 = fw_embedding (((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 301) (((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 51) := by
    rw [hfinal, hPmEmbedding1_nodes]
    exact foldl_faithful_middle_writer EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 5) (segment_000000_pmNodes.drop 6)
      { rank := 1, op := "OpName.FW_embedding", ins := [301, 51], outs := [401] } 401
      (fun t => fw_embedding (t 301) (t 51)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_embedding_out EmbeddingHiddenIdsK2Graph.pm t 1 301 51 401
      ) (by native_decide) (by native_decide)
  have hPmEmbedding1_read_0 : ((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 301 = (segment_000000_pmFinal pmStore) 301 := by
    rw [hfinal, hPmEmbedding1_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 5) ({ rank := 1, op := "OpName.FW_embedding", ins := [301, 51], outs := [401] } :: (segment_000000_pmNodes.drop 6)) 301
      (by native_decide) (by native_decide)
  have hPmEmbedding1_read_1 : ((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 51 = (segment_000000_pmFinal pmStore) 51 := by
    rw [hfinal, hPmEmbedding1_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 5) ({ rank := 1, op := "OpName.FW_embedding", ins := [301, 51], outs := [401] } :: (segment_000000_pmNodes.drop 6)) 51
      (by native_decide) (by native_decide)
  have hPmEmbedding1 : (segment_000000_pmFinal pmStore) 401 = fw_embedding ((segment_000000_pmFinal pmStore) 301) ((segment_000000_pmFinal pmStore) 51) := by
    calc
      _ = fw_embedding (((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 301) (((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 51) := hPmEmbedding1_prefix
      _ = fw_embedding ((segment_000000_pmFinal pmStore) 301) ((segment_000000_pmFinal pmStore) 51) := by rw [hPmEmbedding1_read_0, hPmEmbedding1_read_1]
  exact hPmEmbedding1

private theorem segment_000000_hHiddenSm (smStore : Store) :
    (segment_000000_smFinal smStore) 100 = fw_embedding ((segment_000000_smFinal smStore) 40) ((segment_000000_smFinal smStore) 50) := by
  have hfinal : (segment_000000_smFinal smStore) = segment_000000_smNodes.foldl
      (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore := by
    unfold segment_000000_smFinal
    rfl
  have hHiddenSm_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] }] ++ (segment_000000_smNodes.drop 1) := by
    native_decide
  have hHiddenSm_prefix : (segment_000000_smFinal smStore) 100 = fw_embedding (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 40) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 50) := by
    rw [hfinal, hHiddenSm_nodes]
    exact foldl_faithful_middle_writer EmbeddingHiddenIdsK2Graph.sm smStore
      (segment_000000_smNodes.take 0) (segment_000000_smNodes.drop 1)
      { rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] } 100
      (fun t => fw_embedding (t 40) (t 50)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_embedding_out EmbeddingHiddenIdsK2Graph.sm t 0 40 50 100
      ) (by native_decide) (by native_decide)
  have hHiddenSm_read_0 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 40 = (segment_000000_smFinal smStore) 40 := by
    rw [hfinal, hHiddenSm_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.sm smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] } :: (segment_000000_smNodes.drop 1)) 40
      (by native_decide) (by native_decide)
  have hHiddenSm_read_1 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 50 = (segment_000000_smFinal smStore) 50 := by
    rw [hfinal, hHiddenSm_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.sm smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_embedding", ins := [40, 50], outs := [100] } :: (segment_000000_smNodes.drop 1)) 50
      (by native_decide) (by native_decide)
  have hHiddenSm : (segment_000000_smFinal smStore) 100 = fw_embedding ((segment_000000_smFinal smStore) 40) ((segment_000000_smFinal smStore) 50) := by
    calc
      _ = fw_embedding (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 40) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.sm) smStore 50) := hHiddenSm_prefix
      _ = fw_embedding ((segment_000000_smFinal smStore) 40) ((segment_000000_smFinal smStore) 50) := by rw [hHiddenSm_read_0, hHiddenSm_read_1]
  exact hHiddenSm

private theorem segment_000000_hHiddenPm0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 200 = fw_embedding ((segment_000000_pmFinal pmStore) 40) ((segment_000000_pmFinal pmStore) 60) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl
      (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hHiddenPm0_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] }] ++ (segment_000000_pmNodes.drop 1) := by
    native_decide
  have hHiddenPm0_prefix : (segment_000000_pmFinal pmStore) 200 = fw_embedding (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 40) (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 60) := by
    rw [hfinal, hHiddenPm0_nodes]
    exact foldl_faithful_middle_writer EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 0) (segment_000000_pmNodes.drop 1)
      { rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] } 200
      (fun t => fw_embedding (t 40) (t 60)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_embedding_out EmbeddingHiddenIdsK2Graph.pm t 0 40 60 200
      ) (by native_decide) (by native_decide)
  have hHiddenPm0_read_0 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 40 = (segment_000000_pmFinal pmStore) 40 := by
    rw [hfinal, hHiddenPm0_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] } :: (segment_000000_pmNodes.drop 1)) 40
      (by native_decide) (by native_decide)
  have hHiddenPm0_read_1 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 60 = (segment_000000_pmFinal pmStore) 60 := by
    rw [hfinal, hHiddenPm0_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_embedding", ins := [40, 60], outs := [200] } :: (segment_000000_pmNodes.drop 1)) 60
      (by native_decide) (by native_decide)
  have hHiddenPm0 : (segment_000000_pmFinal pmStore) 200 = fw_embedding ((segment_000000_pmFinal pmStore) 40) ((segment_000000_pmFinal pmStore) 60) := by
    calc
      _ = fw_embedding (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 40) (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 60) := hHiddenPm0_prefix
      _ = fw_embedding ((segment_000000_pmFinal pmStore) 40) ((segment_000000_pmFinal pmStore) 60) := by rw [hHiddenPm0_read_0, hHiddenPm0_read_1]
  exact hHiddenPm0

private theorem segment_000000_hHiddenPm1 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 201 = fw_embedding ((segment_000000_pmFinal pmStore) 40) ((segment_000000_pmFinal pmStore) 61) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl
      (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hHiddenPm1_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 2) ++ [{ rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] }] ++ (segment_000000_pmNodes.drop 3) := by
    native_decide
  have hHiddenPm1_prefix : (segment_000000_pmFinal pmStore) 201 = fw_embedding (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 40) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 61) := by
    rw [hfinal, hHiddenPm1_nodes]
    exact foldl_faithful_middle_writer EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 2) (segment_000000_pmNodes.drop 3)
      { rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] } 201
      (fun t => fw_embedding (t 40) (t 61)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_embedding_out EmbeddingHiddenIdsK2Graph.pm t 1 40 61 201
      ) (by native_decide) (by native_decide)
  have hHiddenPm1_read_0 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 40 = (segment_000000_pmFinal pmStore) 40 := by
    rw [hfinal, hHiddenPm1_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] } :: (segment_000000_pmNodes.drop 3)) 40
      (by native_decide) (by native_decide)
  have hHiddenPm1_read_1 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 61 = (segment_000000_pmFinal pmStore) 61 := by
    rw [hfinal, hHiddenPm1_nodes]
    exact foldl_faithful_prefix_read_eq_final EmbeddingHiddenIdsK2Graph.pm pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 1, op := "OpName.FW_embedding", ins := [40, 61], outs := [201] } :: (segment_000000_pmNodes.drop 3)) 61
      (by native_decide) (by native_decide)
  have hHiddenPm1 : (segment_000000_pmFinal pmStore) 201 = fw_embedding ((segment_000000_pmFinal pmStore) 40) ((segment_000000_pmFinal pmStore) 61) := by
    calc
      _ = fw_embedding (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 40) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful EmbeddingHiddenIdsK2Graph.pm) pmStore 61) := hHiddenPm1_prefix
      _ = fw_embedding ((segment_000000_pmFinal pmStore) 40) ((segment_000000_pmFinal pmStore) 61) := by rw [hHiddenPm1_read_0, hHiddenPm1_read_1]
  exact hHiddenPm1

private theorem segment_000000_ids_relation (smStore pmStore : Store)
    (hIdsEq : (segment_000000_smFinal smStore) 41 =
      (segment_000000_pmFinal pmStore) 41)
    (hIdsShape : ((segment_000000_pmFinal pmStore) 41).shape = [1, 4]) :
    ChunkedRel ((segment_000000_smFinal smStore) 41)
      (segment_000000_chunkTids.map (segment_000000_pmFinal pmStore)) 1
      [1, 2 * segment_000000_chunkTids.length] [1, 2] := by
  have hChunk0 := segment_000000_hChunk0 pmStore
  have hChunk1 := segment_000000_hChunk1 pmStore
  have hOrderedChunks :
      segment_000000_chunkTids.map (segment_000000_pmFinal pmStore) =
        List.ofFn (fun r : Fin segment_000000_rankCount =>
          chunkPrimDimN 1 segment_000000_rankCount r.1 ((segment_000000_pmFinal pmStore) 41)) := by
    change [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301] = [chunkPrimDimN 1 segment_000000_rankCount 0 ((segment_000000_pmFinal pmStore) 41), chunkPrimDimN 1 segment_000000_rankCount 1 ((segment_000000_pmFinal pmStore) 41)]
    rw [hChunk0, hChunk1]
  refine {
    full_value := ?_
    full_shape := ?_
    shards_nonempty := ?_
    gather_dim_lt := ?_
    shard_shapes := ?_
    shape_contract := ?_
    chunk_values := ?_
  }
  · rw [hIdsEq, hOrderedChunks]
    simp only [List.length_ofFn]
    symm
    exact allGatherPrimDimN_chunks_ofFn 1 segment_000000_rankCount
      ((segment_000000_pmFinal pmStore) 41)
      (by simp [segment_000000_rankCount, segment_000000_chunkTids])
      (by rw [hIdsShape]; native_decide)
      (by rw [hIdsShape]; simp [segment_000000_rankCount, segment_000000_chunkTids])
  · rw [hIdsEq, hIdsShape]
    simp [segment_000000_chunkTids]
  · simp [segment_000000_chunkTids]
  · native_decide
  · intro shard hmem
    simp only [segment_000000_chunkTids, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [hChunk0, chunkPrimDimN_shape 1 segment_000000_rankCount 0
          ((segment_000000_pmFinal pmStore) 41) [1, 4] hIdsShape
          (by simp [segment_000000_rankCount, segment_000000_chunkTids])]
      native_decide
    · rw [hChunk1, chunkPrimDimN_shape 1 segment_000000_rankCount 1
          ((segment_000000_pmFinal pmStore) 41) [1, 4] hIdsShape
          (by simp [segment_000000_rankCount, segment_000000_chunkTids])]
      native_decide
  · simp [segment_000000_chunkTids, List.set, List.getD]
  · intro r hr
    simp only [segment_000000_chunkTids, List.map, List.length_cons, List.length_nil] at hr
    have cases : r = 0 ∨ r = 1 := by omega
    rcases cases with h0 | h1
    · subst r
      simp only [segment_000000_chunkTids, List.map, List.length_cons, List.length_nil]
      rw [hIdsEq]
      simpa [segment_000000_rankCount, segment_000000_chunkTids, List.getD] using hChunk0
    · subst r
      simp only [segment_000000_chunkTids, List.map, List.length_cons, List.length_nil]
      rw [hIdsEq]
      simpa [segment_000000_rankCount, segment_000000_chunkTids, List.getD] using hChunk1

set_option maxHeartbeats 500000 in
private theorem segment_000000_hidden_out (smStore pmStore : Store)
    (hw : weight.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore))
    (hidEq : (segment_000000_smFinal smStore) 40 = (segment_000000_pmFinal pmStore) 40)
    (hidShape : ((segment_000000_pmFinal pmStore) 40).shape = [1, 4]) :
    hidden_out.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  let smFinal := segment_000000_smFinal smStore
  let pmFinal := segment_000000_pmFinal pmStore
  change smFinal 40 = pmFinal 40 at hidEq
  change (pmFinal 40).shape = [1, 4] at hidShape
  change ShardedRel (smFinal 50) [pmFinal 60, pmFinal 61] 1 [7, 8] [7, 4] at hw
  have hsm := segment_000000_hHiddenSm smStore
  change smFinal 100 = fw_embedding (smFinal 40) (smFinal 50) at hsm
  have hp0 := segment_000000_hHiddenPm0 pmStore
  change pmFinal 200 = fw_embedding (pmFinal 40) (pmFinal 60) at hp0
  have hshape0 : (pmFinal 200).shape = [1, 4, 4] := by rw [hp0, fw_embedding_shape, hidShape, hw.shard_shapes (pmFinal 60) (by simp)]; rfl
  have hp1 := segment_000000_hHiddenPm1 pmStore
  change pmFinal 201 = fw_embedding (pmFinal 40) (pmFinal 61) at hp1
  have hshape1 : (pmFinal 201).shape = [1, 4, 4] := by rw [hp1, fw_embedding_shape, hidShape, hw.shard_shapes (pmFinal 61) (by simp)]; rfl
  have hcomm := TrainVerify.Denote.fw_embedding_hidden_shards_k_rank (K := 2) (b := 1) (tokens := 4) (vocab := 7) (hidden := 4) (ids := pmFinal 40) (Ws := [pmFinal 60, pmFinal 61]) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp) hidShape (by intro W hW; exact hw.shard_shapes W hW)
  have hvalue : smFinal 100 = allGatherPrimDimN 2 2 0 [pmFinal 200, pmFinal 201] := by rw [hsm, hidEq, hw.full_value]; simp only [List.length_cons, List.length_nil]; rw [hcomm]; simp only [List.map]; rw [←hp0, ←hp1]
  change ShardedRel (smFinal 100) [pmFinal 200, pmFinal 201] 2 [1, 4, 8] [1, 4, 4]
  refine { full_value := ?_, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp }
  · simpa only [List.length_cons, List.length_nil] using hvalue
  · rw [hsm, fw_embedding_shape, hidEq, hidShape, hw.full_shape]; rfl
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hshape0
    · exact hshape1

private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
    let smNodes : List NodeDecl := segment_000000_smNodes
    let pmNodes : List NodeDecl := segment_000000_pmNodes
    let chunkTids : List Tid := segment_000000_chunkTids
    let outputTids : List Tid := segment_000000_outputTids
    let rankCount := segment_000000_rankCount
    let smFinal := segment_000000_smFinal smStore
    let pmFinal := segment_000000_pmFinal pmStore
    have hframe : state_before.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000000_smFinal segment_000000_pmFinal
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · simp only [smNodes]
        native_decide
      · simp only [pmNodes]
        native_decide
    have hIdsEq : smFinal 41 = pmFinal 41 := by
      simpa [eq_41, RelationFact.Holds, StoreSide.read] using
        (hframe eq_41 (by native_decide))
    have hIdsShape : (pmFinal 41).shape = [1, 4] := by
      simpa [shape_41, RelationFact.Holds, StoreSide.read] using
        (hframe shape_41 (by native_decide))
    have hWeightEq : smFinal 51 = pmFinal 51 := by
      simpa [eq_51, RelationFact.Holds, StoreSide.read] using
        (hframe eq_51 (by native_decide))
    have hWeightShape : (pmFinal 51).shape = [7, 12] := by
      simpa [shape_51, RelationFact.Holds, StoreSide.read] using
        (hframe shape_51 (by native_decide))
    let idsShards := chunkTids.map pmFinal
    have hIds :
        ChunkedRel (smFinal 41) idsShards 1
          [1, 2 * idsShards.length] [1, 2] := by
      exact segment_000000_ids_relation smStore pmStore hIdsEq hIdsShape
    have hIdsOut : ids_out.Holds smFinal pmFinal := by
      unfold ids_out RelationFact.Holds
      simpa only [idsShards, chunkTids,
        segment_000000_chunkTids, List.map, List.length_cons, List.length_nil] using hIds
    have hSmEmbedding : smFinal 101 =
        fw_embedding (smFinal 41) (smFinal 51) := by
      exact segment_000000_hSmEmbedding smStore
    have hPmEmbedding0 : pmFinal 400 =
        fw_embedding (pmFinal 300) (pmFinal 51) := by
      exact segment_000000_hPmEmbedding0 pmStore
    have hPmEmbedding1 : pmFinal 401 =
        fw_embedding (pmFinal 301) (pmFinal 51) := by
      exact segment_000000_hPmEmbedding1 pmStore
    have hWeightLast :
        lastD (pmFinal 51).shape = 12 := by
      rw [hWeightShape]
      rfl
    have hEmbedding :=
      ShardedRel.fw_embedding_shared_weight_dim1
        (idsShards := idsShards)
        (b := 1) (s := 2) (hidden := 12)
        hIds.toShardedRel hWeightEq hWeightLast
        (by native_decide) (by native_decide) (by native_decide)
    have hout : sequence_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 101) (outputTids.map pmFinal) 1
        [1, 4, 12] [1, 2, 12]
      rw [hSmEmbedding]
      simp only [idsShards, chunkTids, outputTids,
        segment_000000_chunkTids, segment_000000_outputTids, List.map,
        List.length_cons, List.length_nil] at hEmbedding ⊢
      rw [← hPmEmbedding0, ← hPmEmbedding1] at hEmbedding
      exact hEmbedding
    have hHiddenEq := hframe eq_40 (by native_decide)
    have hHiddenShape := hframe shape_40 (by native_decide)
    change smFinal 40 = pmFinal 40 at hHiddenEq
    change (pmFinal 40).shape = [1, 4] at hHiddenShape
    have hHidden := segment_000000_hidden_out smStore pmStore (hframe weight (by native_decide)) hHiddenEq hHiddenShape
    intro fact hfact
    have covered : fact ∈ [ids_out, sequence_out, hidden_out] ++ state_before.facts := by
      exact (show state_after.facts ⊆ [ids_out, sequence_out, hidden_out] ++ state_before.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl | rfl
      · exact hIdsOut
      · exact hout
      · exact hHidden
    · exact hframe fact old

private def segment_000000 :
    ClosedDepSegmentCertificate EmbeddingHiddenIdsK2Graph.sm EmbeddingHiddenIdsK2Graph.pm state_before state_after where
  smNodes := segment_000000_smNodes
  pmNodes := segment_000000_pmNodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000000_smFinal, segment_000000_pmFinal] using
      segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end TrainVerify.Denote.EmbeddingHiddenIdsK2
