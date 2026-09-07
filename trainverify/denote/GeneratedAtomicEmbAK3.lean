import denote.GraphGears
import denote.BWEmbeddingHiddenShardK
import denote.BWEmbeddingSequenceShardK
import denote.RelationCompiler
open TrainVerify.Denote
namespace BWEmbeddingMixedK3B2S5V13D7Graph
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.ChunkPrim", ins := [6], outs := [100], params := [1] }, { rank := 1, op := "OpName.ChunkPrim", ins := [6], outs := [101], params := [1] }, { rank := 2, op := "OpName.ChunkPrim", ins := [6], outs := [102], params := [1] }, { rank := 0, op := "OpName.BW_embedding", ins := [103, 2, 109], outs := [112] }, { rank := 1, op := "OpName.BW_embedding", ins := [104, 2, 110], outs := [113] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [115], params := [2, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [116], params := [2, 1] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [117], params := [2, 1] }, { rank := 2, op := "OpName.BW_embedding", ins := [105, 2, 111], outs := [114] }, { rank := 0, op := "OpName.BW_embedding", ins := [115, 100, 7], outs := [118] }, { rank := 1, op := "OpName.BW_embedding", ins := [116, 101, 7], outs := [119] }, { rank := 2, op := "OpName.BW_embedding", ins := [117, 102, 7], outs := [120] }] }
end BWEmbeddingMixedK3B2S5V13D7Graph
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.BWEmbeddingMixedK3B2S5V13D7

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def hg : RelationFact :=
  .sharded 1 [103, 104, 105] 2 [2, 15, 21] [2, 15, 7]

private def hi : RelationFact :=
  .sharded 2 [2] 0 [2, 15] [2, 15]

private def hw : RelationFact :=
  .sharded 3 [109, 110, 111] 1 [13, 21] [13, 7]

private def ai : RelationFact :=
  .sharded 5 [106, 107, 108] 2 [2, 15, 21] [2, 15, 7]

private def qi : RelationFact :=
  .chunked 6 [100, 101, 102] 1 [2, 15] [2, 5]

private def qw : RelationFact :=
  .sharded 7 [7] 0 [14, 21] [14, 21]

private def ho : RelationFact :=
  .sharded 4 [112, 113, 114] 1 [13, 21] [13, 7]

private def ao : RelationFact :=
  .sharded 5 [115, 116, 117] 1 [2, 15, 21] [2, 5, 21]

private def qo : RelationFact :=
  .reduction 8 [118, 119, 120] [14, 21]

private def anchor : RelationFact :=
  .tensorShape .sm 2 [2, 15]

private def state_before : RelationState where
  facts := [anchor, hg, hi, hw, ai, qi, qw]
  nonempty := by decide

private def state_after : RelationState where
  facts := [anchor, hg, hi, hw, ai, qi, qw, ho, qo]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [103, 2, 109], outs := [112] }, { rank := 1, op := "OpName.BW_embedding", ins := [104, 2, 110], outs := [113] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [115], params := [2, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [116], params := [2, 1] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [117], params := [2, 1] }, { rank := 2, op := "OpName.BW_embedding", ins := [105, 2, 111], outs := [114] }, { rank := 0, op := "OpName.BW_embedding", ins := [115, 100, 7], outs := [118] }, { rank := 1, op := "OpName.BW_embedding", ins := [116, 101, 7], outs := [119] }, { rank := 2, op := "OpName.BW_embedding", ins := [117, 102, 7], outs := [120] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) s
private theorem segment_000000_HSm (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK3B2S5V13D7Graph.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_HPm0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 112 = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 109) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [103, 2, 109], outs := [112] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 112 = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 103) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 109) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [103, 2, 109], outs := [112] } 112
      (fun t => bw_embedding (t 103) (t 2) (t 109)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK3B2S5V13D7Graph.pm t 0 103 2 109 112
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 103 = (segment_000000_pm_final pmStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [103, 2, 109], outs := [112] } :: (segment_000000_pm_nodes.drop 1)) 103
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [103, 2, 109], outs := [112] } :: (segment_000000_pm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 109 = (segment_000000_pm_final pmStore) 109 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [103, 2, 109], outs := [112] } :: (segment_000000_pm_nodes.drop 1)) 109
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 112 = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 109) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 103) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 109) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 109) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_HPm1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 113 = bw_embedding ((segment_000000_pm_final pmStore) 104) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 110) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [104, 2, 110], outs := [113] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 113 = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 104) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 110) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_embedding", ins := [104, 2, 110], outs := [113] } 113
      (fun t => bw_embedding (t 104) (t 2) (t 110)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK3B2S5V13D7Graph.pm t 1 104 2 110 113
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 104 = (segment_000000_pm_final pmStore) 104 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [104, 2, 110], outs := [113] } :: (segment_000000_pm_nodes.drop 2)) 104
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [104, 2, 110], outs := [113] } :: (segment_000000_pm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 110 = (segment_000000_pm_final pmStore) 110 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [104, 2, 110], outs := [113] } :: (segment_000000_pm_nodes.drop 2)) 110
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 113 = bw_embedding ((segment_000000_pm_final pmStore) 104) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 110) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 104) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 110) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 104) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 110) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_HPm2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 114 = bw_embedding ((segment_000000_pm_final pmStore) 105) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 111) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [105, 2, 111], outs := [114] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 114 = bw_embedding (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 105) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 111) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.BW_embedding", ins := [105, 2, 111], outs := [114] } 114
      (fun t => bw_embedding (t 105) (t 2) (t 111)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK3B2S5V13D7Graph.pm t 2 105 2 111 114
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 105 = (segment_000000_pm_final pmStore) 105 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [105, 2, 111], outs := [114] } :: (segment_000000_pm_nodes.drop 6)) 105
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [105, 2, 111], outs := [114] } :: (segment_000000_pm_nodes.drop 6)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 111 = (segment_000000_pm_final pmStore) 111 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.BW_embedding", ins := [105, 2, 111], outs := [114] } :: (segment_000000_pm_nodes.drop 6)) 111
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 114 = bw_embedding ((segment_000000_pm_final pmStore) 105) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 111) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 105) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 111) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 105) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 111) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QSm (smStore : Store) :
    (segment_000000_sm_final smStore) 8 = bw_embedding ((segment_000000_sm_final smStore) 5) ((segment_000000_sm_final smStore) 6) ((segment_000000_sm_final smStore) 7) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 8 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 5) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 6) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } 8
      (fun t => bw_embedding (t 5) (t 6) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK3B2S5V13D7Graph.sm t 0 5 6 7 8
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 5 = (segment_000000_sm_final smStore) 5 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } :: (segment_000000_sm_nodes.drop 1)) 5
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 6 = (segment_000000_sm_final smStore) 6 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } :: (segment_000000_sm_nodes.drop 1)) 6
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 7 = (segment_000000_sm_final smStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } :: (segment_000000_sm_nodes.drop 1)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 8 = bw_embedding ((segment_000000_sm_final smStore) 5) ((segment_000000_sm_final smStore) 6) ((segment_000000_sm_final smStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 5) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 6) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.sm) smStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 5) ((segment_000000_sm_final smStore) 6) ((segment_000000_sm_final smStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QPm0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 118 = bw_embedding ((segment_000000_pm_final pmStore) 115) ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 7) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 6) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [115, 100, 7], outs := [118] }] ++ (segment_000000_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 118 = bw_embedding (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 115) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 100) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 6) (segment_000000_pm_nodes.drop 7)
      { rank := 0, op := "OpName.BW_embedding", ins := [115, 100, 7], outs := [118] } 118
      (fun t => bw_embedding (t 115) (t 100) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK3B2S5V13D7Graph.pm t 0 115 100 7 118
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 115 = (segment_000000_pm_final pmStore) 115 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 0, op := "OpName.BW_embedding", ins := [115, 100, 7], outs := [118] } :: (segment_000000_pm_nodes.drop 7)) 115
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 0, op := "OpName.BW_embedding", ins := [115, 100, 7], outs := [118] } :: (segment_000000_pm_nodes.drop 7)) 100
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 7 = (segment_000000_pm_final pmStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 6) ({ rank := 0, op := "OpName.BW_embedding", ins := [115, 100, 7], outs := [118] } :: (segment_000000_pm_nodes.drop 7)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 118 = bw_embedding ((segment_000000_pm_final pmStore) 115) ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 115) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 100) (((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 115) ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QPm1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 119 = bw_embedding ((segment_000000_pm_final pmStore) 116) ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 7) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [116, 101, 7], outs := [119] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 119 = bw_embedding (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 116) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 101) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 1, op := "OpName.BW_embedding", ins := [116, 101, 7], outs := [119] } 119
      (fun t => bw_embedding (t 116) (t 101) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK3B2S5V13D7Graph.pm t 1 116 101 7 119
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 116 = (segment_000000_pm_final pmStore) 116 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 1, op := "OpName.BW_embedding", ins := [116, 101, 7], outs := [119] } :: (segment_000000_pm_nodes.drop 8)) 116
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 1, op := "OpName.BW_embedding", ins := [116, 101, 7], outs := [119] } :: (segment_000000_pm_nodes.drop 8)) 101
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 7 = (segment_000000_pm_final pmStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 1, op := "OpName.BW_embedding", ins := [116, 101, 7], outs := [119] } :: (segment_000000_pm_nodes.drop 8)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 119 = bw_embedding ((segment_000000_pm_final pmStore) 116) ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 116) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 101) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 116) ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QPm2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 120 = bw_embedding ((segment_000000_pm_final pmStore) 117) ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 7) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 8) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [117, 102, 7], outs := [120] }] ++ (segment_000000_pm_nodes.drop 9) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 120 = bw_embedding (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 117) (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 102) (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 8) (segment_000000_pm_nodes.drop 9)
      { rank := 2, op := "OpName.BW_embedding", ins := [117, 102, 7], outs := [120] } 120
      (fun t => bw_embedding (t 117) (t 102) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK3B2S5V13D7Graph.pm t 2 117 102 7 120
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 117 = (segment_000000_pm_final pmStore) 117 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 2, op := "OpName.BW_embedding", ins := [117, 102, 7], outs := [120] } :: (segment_000000_pm_nodes.drop 9)) 117
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 2, op := "OpName.BW_embedding", ins := [117, 102, 7], outs := [120] } :: (segment_000000_pm_nodes.drop 9)) 102
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 7 = (segment_000000_pm_final pmStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 2, op := "OpName.BW_embedding", ins := [117, 102, 7], outs := [120] } :: (segment_000000_pm_nodes.drop 9)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 120 = bw_embedding ((segment_000000_pm_final pmStore) 117) ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 117) (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 102) (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) pmStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 117) ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hAllToAll0 (store : Store) : (segment_000000_pm_final store) 115 = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 0 [(segment_000000_pm_final store) 106, (segment_000000_pm_final store) 107, (segment_000000_pm_final store) 108] 2 1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [115], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 115 = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 0 [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 106, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 107, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 108] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 0, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [115], params := [2, 1] } 115
      (fun t => allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 0 [t 106, t 107, t 108] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out BWEmbeddingMixedK3B2S5V13D7Graph.pm t 0 [106, 107, 108] 115 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 106 = (segment_000000_pm_final store) 106 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [115], params := [2, 1] } :: (segment_000000_pm_nodes.drop 3)) 106
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 107 = (segment_000000_pm_final store) 107 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [115], params := [2, 1] } :: (segment_000000_pm_nodes.drop 3)) 107
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 108 = (segment_000000_pm_final store) 108 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 2) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [115], params := [2, 1] } :: (segment_000000_pm_nodes.drop 3)) 108
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 115 = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 0 [(segment_000000_pm_final store) 106, (segment_000000_pm_final store) 107, (segment_000000_pm_final store) 108] 2 1 := by
    calc
      _ = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 0 [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 106, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 107, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 108] 2 1 := hout_prefix
      _ = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 0 [(segment_000000_pm_final store) 106, (segment_000000_pm_final store) 107, (segment_000000_pm_final store) 108] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hAllToAll1 (store : Store) : (segment_000000_pm_final store) 116 = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 1 [(segment_000000_pm_final store) 106, (segment_000000_pm_final store) 107, (segment_000000_pm_final store) 108] 2 1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [116], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 116 = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 1 [((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 106, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 107, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 108] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [116], params := [2, 1] } 116
      (fun t => allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 1 [t 106, t 107, t 108] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out BWEmbeddingMixedK3B2S5V13D7Graph.pm t 1 [106, 107, 108] 116 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 106 = (segment_000000_pm_final store) 106 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [116], params := [2, 1] } :: (segment_000000_pm_nodes.drop 4)) 106
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 107 = (segment_000000_pm_final store) 107 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [116], params := [2, 1] } :: (segment_000000_pm_nodes.drop 4)) 107
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 108 = (segment_000000_pm_final store) 108 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [116], params := [2, 1] } :: (segment_000000_pm_nodes.drop 4)) 108
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 116 = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 1 [(segment_000000_pm_final store) 106, (segment_000000_pm_final store) 107, (segment_000000_pm_final store) 108] 2 1 := by
    calc
      _ = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 1 [((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 106, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 107, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 108] 2 1 := hout_prefix
      _ = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 1 [(segment_000000_pm_final store) 106, (segment_000000_pm_final store) 107, (segment_000000_pm_final store) 108] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hAllToAll2 (store : Store) : (segment_000000_pm_final store) 117 = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 2 [(segment_000000_pm_final store) 106, (segment_000000_pm_final store) 107, (segment_000000_pm_final store) 108] 2 1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [117], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 117 = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 2 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 106, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 107, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 108] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 2, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [117], params := [2, 1] } 117
      (fun t => allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 2 [t 106, t 107, t 108] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out BWEmbeddingMixedK3B2S5V13D7Graph.pm t 2 [106, 107, 108] 117 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 106 = (segment_000000_pm_final store) 106 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [117], params := [2, 1] } :: (segment_000000_pm_nodes.drop 5)) 106
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 107 = (segment_000000_pm_final store) 107 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [117], params := [2, 1] } :: (segment_000000_pm_nodes.drop 5)) 107
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 108 = (segment_000000_pm_final store) 108 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK3B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 4) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [106, 107, 108], outs := [117], params := [2, 1] } :: (segment_000000_pm_nodes.drop 5)) 108
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 117 = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 2 [(segment_000000_pm_final store) 106, (segment_000000_pm_final store) 107, (segment_000000_pm_final store) 108] 2 1 := by
    calc
      _ = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 2 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 106, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 107, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK3B2S5V13D7Graph.pm) store 108] 2 1 := hout_prefix
      _ = allToAllPrimWithDims BWEmbeddingMixedK3B2S5V13D7Graph.pm.numRanks 2 [(segment_000000_pm_final store) 106, (segment_000000_pm_final store) 107, (segment_000000_pm_final store) 108] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_before.Holds smStore pmStore) : state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hai : ai.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 5) [pmFinal 106, pmFinal 107, pmFinal 108] 2 [2, 15, 21] [2, 15, 7] at hai
  have hA0 : pmFinal 115 = allToAllPrimWithDims 3 0 [pmFinal 106, pmFinal 107, pmFinal 108] 2 1 := segment_000000_hAllToAll0 pmStore
  have hA1 : pmFinal 116 = allToAllPrimWithDims 3 1 [pmFinal 106, pmFinal 107, pmFinal 108] 2 1 := segment_000000_hAllToAll1 pmStore
  have hA2 : pmFinal 117 = allToAllPrimWithDims 3 2 [pmFinal 106, pmFinal 107, pmFinal 108] 2 1 := segment_000000_hAllToAll2 pmStore
  have hHead : (([pmFinal 106, pmFinal 107, pmFinal 108].head?.map (fun t => t.shape)).getD []) = [2, 15, 7] := hai.shard_shapes _ (by simp)
  have hAV : smFinal 5 = allGatherPrimDimN 2 3 0 [pmFinal 106, pmFinal 107, pmFinal 108] := by simpa only [List.length_cons,List.length_nil] using hai.full_value
  have hGS : (allGatherPrimDimN 2 3 0 [pmFinal 106, pmFinal 107, pmFinal 108]).shape = [2, 15, 21] := by rw [←hAV]; exact hai.full_shape
  have hOd : 1 < (allGatherPrimDimN 2 3 0 [pmFinal 106, pmFinal 107, pmFinal 108]).shape.length := by rw [hGS]; decide
  have hDv : (allGatherPrimDimN 2 3 0 [pmFinal 106, pmFinal 107, pmFinal 108]).shape.getD 1 0 % 3 = 0 := by rw [hGS]; decide
  have hAS0 : (pmFinal 115).shape = [2, 5, 21] := by rw [hA0,allToAllPrimWithDims_shape 3 0 [pmFinal 106, pmFinal 107, pmFinal 108] 2 1 [2, 15, 7] hHead (by decide)]; decide
  have hAS1 : (pmFinal 116).shape = [2, 5, 21] := by rw [hA1,allToAllPrimWithDims_shape 3 1 [pmFinal 106, pmFinal 107, pmFinal 108] 2 1 [2, 15, 7] hHead (by decide)]; decide
  have hAS2 : (pmFinal 117).shape = [2, 5, 21] := by rw [hA2,allToAllPrimWithDims_shape 3 2 [pmFinal 106, pmFinal 107, pmFinal 108] 2 1 [2, 15, 7] hHead (by decide)]; decide
  have hOrd : [pmFinal 115, pmFinal 116, pmFinal 117] = List.ofFn (fun r : Fin 3 => allToAllPrimWithDims 3 r.1 [pmFinal 106, pmFinal 107, pmFinal 108] 2 1) := by rw [hA0, hA1, hA2]; rfl
  have hAC : allGatherPrimDimN 1 [pmFinal 115, pmFinal 116, pmFinal 117].length 0 [pmFinal 115, pmFinal 116, pmFinal 117] = allGatherPrimDimN 2 3 0 [pmFinal 106, pmFinal 107, pmFinal 108] := by rw [hOrd]; simpa only [List.length_cons,List.length_nil,List.length_ofFn] using (TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 2 1 [pmFinal 106, pmFinal 107, pmFinal 108] (by simp) hOd hDv)
  have houtA : ao.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 5) [pmFinal 115, pmFinal 116, pmFinal 117] 1 [2, 15, 21] [2, 5, 21]
    refine { full_value := ?_, full_shape := hai.full_shape, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
    · rw [hAC]; exact hAV
    · simp only [List.forall_mem_cons]; exact ⟨hAS0, hAS1, hAS2, List.forall_mem_nil _⟩
    · simp only [List.length_cons,List.length_nil]; decide
  have houtH : ho.Holds smFinal pmFinal := by
    have hg : hg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 1) [pmFinal 103, pmFinal 104, pmFinal 105] 2 [2, 15, 21] [2, 15, 7] at hg
    have hgV : smFinal 1 = allGatherPrimDimN 2 3 0 [pmFinal 103, pmFinal 104, pmFinal 105] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hi : hi.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 2) [pmFinal 2] 0 [2, 15] [2, 15] at hi
    have hiShape := hi.shard_shapes (pmFinal 2) (by simp)
    have hiEq : smFinal 2 = pmFinal 2 := by
      rw [hi.full_value]
      exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hiShape]; native_decide)
    have hw : hw.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 3) [pmFinal 109, pmFinal 110, pmFinal 111] 1 [13, 21] [13, 7] at hw
    have hwV : smFinal 3 = allGatherPrimDimN 1 3 0 [pmFinal 109, pmFinal 110, pmFinal 111] := by
      simpa only [List.length_cons, List.length_nil] using hw.full_value
    have hSm := segment_000000_HSm smStore
    change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
    have hPm0 := segment_000000_HPm0 pmStore
    change pmFinal 112 = bw_embedding (pmFinal 103) (pmFinal 2) (pmFinal 109) at hPm0
    have houtShape0 : (pmFinal 112).shape = [13, 7] := by
      rw [hPm0, bw_embedding_shape]
      exact hw.shard_shapes (pmFinal 109) (by simp)
    have hPm1 := segment_000000_HPm1 pmStore
    change pmFinal 113 = bw_embedding (pmFinal 104) (pmFinal 2) (pmFinal 110) at hPm1
    have houtShape1 : (pmFinal 113).shape = [13, 7] := by
      rw [hPm1, bw_embedding_shape]
      exact hw.shard_shapes (pmFinal 110) (by simp)
    have hPm2 := segment_000000_HPm2 pmStore
    change pmFinal 114 = bw_embedding (pmFinal 105) (pmFinal 2) (pmFinal 111) at hPm2
    have houtShape2 : (pmFinal 114).shape = [13, 7] := by
      rw [hPm2, bw_embedding_shape]
      exact hw.shard_shapes (pmFinal 111) (by simp)
    have hComm := TrainVerify.Denote.bw_embedding_hidden_allGather_rank3 3 2 15 13 7
      [pmFinal 103, pmFinal 104, pmFinal 105] [pmFinal 109, pmFinal 110, pmFinal 111] (pmFinal 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rfl) (by rfl) hg.shard_shapes hw.shard_shapes hiShape
    simp only [List.zipWith] at hComm
    have hValue : smFinal 4 = allGatherPrimDimN 1 3 0 [pmFinal 112, pmFinal 113, pmFinal 114] := by
      rw [hSm, hgV, hiEq, hwV, hComm]
      rw [← hPm0, ← hPm1, ← hPm2]
    have hValueL : smFinal 4 = allGatherPrimDimN 1 [pmFinal 112, pmFinal 113, pmFinal 114].length 0 [pmFinal 112, pmFinal 113, pmFinal 114] := by
      simpa only [List.length_cons, List.length_nil] using hValue
    have hFullShape : (smFinal 4).shape = [13, 21] := by
      rw [hSm, bw_embedding_shape]
      exact hw.full_shape
    have hout : ho.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 4) [pmFinal 112, pmFinal 113, pmFinal 114] 1 [13, 21] [13, 7]
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
    exact hout
  have houtQ : qo.Holds smFinal pmFinal := by
    have hg : ao.Holds smFinal pmFinal := houtA
    change ShardedRel (smFinal 5) [pmFinal 115, pmFinal 116, pmFinal 117] 1 [2, 15, 21] [2, 5, 21] at hg
    have hi : qi.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ChunkedRel (smFinal 6) [pmFinal 100, pmFinal 101, pmFinal 102] 1 [2, 15] [2, 5] at hi
    have hw : qw.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 7) [pmFinal 7] 0 [14, 21] [14, 21] at hw
    have hwEq : smFinal 7 = pmFinal 7 := by
      rw [hw.full_value]
      exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes (pmFinal 7) (by simp)]; native_decide)
    have hgValue : smFinal 5 = allGatherPrimDimN 1 3 0 [pmFinal 115, pmFinal 116, pmFinal 117] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hSm := segment_000000_QSm smStore
    change smFinal 8 = bw_embedding (smFinal 5)
      (smFinal 6) (smFinal 7) at hSm
    have hPm0 := segment_000000_QPm0 pmStore
    change pmFinal 118 =
      bw_embedding (pmFinal 115)
        (pmFinal 100) (pmFinal 7) at hPm0
    have hPm1 := segment_000000_QPm1 pmStore
    change pmFinal 119 =
      bw_embedding (pmFinal 116)
        (pmFinal 101) (pmFinal 7) at hPm1
    have hPm2 := segment_000000_QPm2 pmStore
    change pmFinal 120 =
      bw_embedding (pmFinal 117)
        (pmFinal 102) (pmFinal 7) at hPm2
    have hComm := TrainVerify.Denote.bw_embedding_seqchunk_K 3 2 5 21 14
      [pmFinal 115, pmFinal 116, pmFinal 117] (smFinal 6) (pmFinal 7)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rfl) hg.shard_shapes hi.full_shape
      (hw.shard_shapes (pmFinal 7) (by simp))
    simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hComm
    have hIdChunk0 := hi.chunk_values 0 (by simp)
    simp [List.getD] at hIdChunk0
    have hIdChunk1 := hi.chunk_values 1 (by simp)
    simp [List.getD] at hIdChunk1
    have hIdChunk2 := hi.chunk_values 2 (by simp)
    simp [List.getD] at hIdChunk2
    have hValue : smFinal 8 = tensorSum [pmFinal 118, pmFinal 119, pmFinal 120] := by
      rw [hSm, hgValue, hwEq, hComm]
      rw [← hIdChunk0]
      rw [← hPm0]
      rw [← hIdChunk1]
      rw [← hPm1]
      rw [← hIdChunk2]
      rw [← hPm2]
    have hValueReduce : smFinal 8 =
        allReducePrim [pmFinal 118, pmFinal 119, pmFinal 120].length 0 [pmFinal 118, pmFinal 119, pmFinal 120] := by
      rw [hValue]
      rfl
    have hFullShape : (smFinal 8).shape = [14, 21] := by
      rw [hSm, bw_embedding_shape]
      exact hw.full_shape
    have hShape0 : (pmFinal 118).shape = [14, 21] := by
      rw [hPm0, bw_embedding_shape]
      exact hw.shard_shapes _ (by simp)
    have hShape1 : (pmFinal 119).shape = [14, 21] := by
      rw [hPm1, bw_embedding_shape]
      exact hw.shard_shapes _ (by simp)
    have hShape2 : (pmFinal 120).shape = [14, 21] := by
      rw [hPm2, bw_embedding_shape]
      exact hw.shard_shapes _ (by simp)
    have hout : qo.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 8) [pmFinal 118, pmFinal 119, pmFinal 120] [14, 21]
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
    exact hout
  intro fact hfact
  have hc : fact ∈ [ho, ao, qo] ++ state_before.facts := (show state_after.facts ⊆ [ho, ao, qo] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at hc
  rcases hc with fresh | old
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh
    rcases fresh with rfl | rfl | rfl
    · exact houtH
    · exact houtA
    · exact houtQ
  · exact hframe fact old
private def segment_000000 : ClosedDepSegmentCertificate BWEmbeddingMixedK3B2S5V13D7Graph.sm BWEmbeddingMixedK3B2S5V13D7Graph.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000_sound
end
end TrainVerify.Denote.BWEmbeddingMixedK3B2S5V13D7
