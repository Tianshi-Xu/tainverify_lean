import denote.GraphGears
import denote.BWEmbeddingHiddenShardK
import denote.BWEmbeddingSequenceShardK
import denote.RelationCompiler
open TrainVerify.Denote
namespace BWEmbeddingMixedK2B2S5V13D7Graph
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.ChunkPrim", ins := [6], outs := [100], params := [1] }, { rank := 1, op := "OpName.ChunkPrim", ins := [6], outs := [101], params := [1] }, { rank := 0, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [108] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [110], params := [2, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [111], params := [2, 1] }, { rank := 1, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [109] }, { rank := 0, op := "OpName.BW_embedding", ins := [110, 100, 7], outs := [112] }, { rank := 1, op := "OpName.BW_embedding", ins := [111, 101, 7], outs := [113] }] }
end BWEmbeddingMixedK2B2S5V13D7Graph
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.BWEmbeddingMixedK2B2S5V13D7

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def hg : RelationFact :=
  .sharded 1 [102, 103] 2 [2, 10, 14] [2, 10, 7]

private def hi : RelationFact :=
  .sharded 2 [2] 0 [2, 10] [2, 10]

private def hw : RelationFact :=
  .sharded 3 [106, 107] 1 [13, 14] [13, 7]

private def ai : RelationFact :=
  .sharded 5 [104, 105] 2 [2, 10, 14] [2, 10, 7]

private def qi : RelationFact :=
  .chunked 6 [100, 101] 1 [2, 10] [2, 5]

private def qw : RelationFact :=
  .sharded 7 [7] 0 [14, 14] [14, 14]

private def ho : RelationFact :=
  .sharded 4 [108, 109] 1 [13, 14] [13, 7]

private def ao : RelationFact :=
  .sharded 5 [110, 111] 1 [2, 10, 14] [2, 5, 14]

private def qo : RelationFact :=
  .reduction 8 [112, 113] [14, 14]

private def anchor : RelationFact :=
  .tensorShape .sm 2 [2, 10]

private def state_before : RelationState where
  facts := [anchor, hg, hi, hw, ai, qi, qw]
  nonempty := by decide

private def state_after : RelationState where
  facts := [anchor, hg, hi, hw, ai, qi, qw, ho, qo]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [108] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [110], params := [2, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [111], params := [2, 1] }, { rank := 1, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [109] }, { rank := 0, op := "OpName.BW_embedding", ins := [110, 100, 7], outs := [112] }, { rank := 1, op := "OpName.BW_embedding", ins := [111, 101, 7], outs := [113] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) s
private theorem segment_000000_HSm (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK2B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK2B2S5V13D7Graph.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_HPm0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 108 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 106) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [108] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 108 = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 102) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 106) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [108] } 108
      (fun t => bw_embedding (t 102) (t 2) (t 106)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK2B2S5V13D7Graph.pm t 0 102 2 106 108
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [108] } :: (segment_000000_pm_nodes.drop 1)) 102
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [108] } :: (segment_000000_pm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 106 = (segment_000000_pm_final pmStore) 106 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [102, 2, 106], outs := [108] } :: (segment_000000_pm_nodes.drop 1)) 106
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 108 = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 106) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 102) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 106) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 106) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_HPm1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 109 = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 107) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [109] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 109 = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 103) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 107) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [109] } 109
      (fun t => bw_embedding (t 103) (t 2) (t 107)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK2B2S5V13D7Graph.pm t 1 103 2 107 109
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 103 = (segment_000000_pm_final pmStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [109] } :: (segment_000000_pm_nodes.drop 4)) 103
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [109] } :: (segment_000000_pm_nodes.drop 4)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 107 = (segment_000000_pm_final pmStore) 107 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_embedding", ins := [103, 2, 107], outs := [109] } :: (segment_000000_pm_nodes.drop 4)) 107
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 109 = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 107) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 103) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 107) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 107) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QSm (smStore : Store) :
    (segment_000000_sm_final smStore) 8 = bw_embedding ((segment_000000_sm_final smStore) 5) ((segment_000000_sm_final smStore) 6) ((segment_000000_sm_final smStore) 7) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 8 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 5) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 6) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK2B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } 8
      (fun t => bw_embedding (t 5) (t 6) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK2B2S5V13D7Graph.sm t 0 5 6 7 8
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 5 = (segment_000000_sm_final smStore) 5 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } :: (segment_000000_sm_nodes.drop 1)) 5
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 6 = (segment_000000_sm_final smStore) 6 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } :: (segment_000000_sm_nodes.drop 1)) 6
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 7 = (segment_000000_sm_final smStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } :: (segment_000000_sm_nodes.drop 1)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 8 = bw_embedding ((segment_000000_sm_final smStore) 5) ((segment_000000_sm_final smStore) 6) ((segment_000000_sm_final smStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 5) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 6) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.sm) smStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 5) ((segment_000000_sm_final smStore) 6) ((segment_000000_sm_final smStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QPm0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 112 = bw_embedding ((segment_000000_pm_final pmStore) 110) ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 7) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [110, 100, 7], outs := [112] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 112 = bw_embedding (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 110) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 100) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 0, op := "OpName.BW_embedding", ins := [110, 100, 7], outs := [112] } 112
      (fun t => bw_embedding (t 110) (t 100) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK2B2S5V13D7Graph.pm t 0 110 100 7 112
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 110 = (segment_000000_pm_final pmStore) 110 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_embedding", ins := [110, 100, 7], outs := [112] } :: (segment_000000_pm_nodes.drop 5)) 110
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_embedding", ins := [110, 100, 7], outs := [112] } :: (segment_000000_pm_nodes.drop 5)) 100
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 7 = (segment_000000_pm_final pmStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_embedding", ins := [110, 100, 7], outs := [112] } :: (segment_000000_pm_nodes.drop 5)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 112 = bw_embedding ((segment_000000_pm_final pmStore) 110) ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 110) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 100) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 110) ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QPm1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 113 = bw_embedding ((segment_000000_pm_final pmStore) 111) ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 7) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [111, 101, 7], outs := [113] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 113 = bw_embedding (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 111) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 101) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 1, op := "OpName.BW_embedding", ins := [111, 101, 7], outs := [113] } 113
      (fun t => bw_embedding (t 111) (t 101) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK2B2S5V13D7Graph.pm t 1 111 101 7 113
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 111 = (segment_000000_pm_final pmStore) 111 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_embedding", ins := [111, 101, 7], outs := [113] } :: (segment_000000_pm_nodes.drop 6)) 111
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_embedding", ins := [111, 101, 7], outs := [113] } :: (segment_000000_pm_nodes.drop 6)) 101
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 7 = (segment_000000_pm_final pmStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_embedding", ins := [111, 101, 7], outs := [113] } :: (segment_000000_pm_nodes.drop 6)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 113 = bw_embedding ((segment_000000_pm_final pmStore) 111) ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 111) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 101) (((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) pmStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 111) ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hAllToAll0 (store : Store) : (segment_000000_pm_final store) 110 = allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 0 [(segment_000000_pm_final store) 104, (segment_000000_pm_final store) 105] 2 1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [110], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 110 = allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 0 [((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 104, ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 105] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK2B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [110], params := [2, 1] } 110
      (fun t => allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 0 [t 104, t 105] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out BWEmbeddingMixedK2B2S5V13D7Graph.pm t 0 [104, 105] 110 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 104 = (segment_000000_pm_final store) 104 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [110], params := [2, 1] } :: (segment_000000_pm_nodes.drop 2)) 104
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 105 = (segment_000000_pm_final store) 105 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [110], params := [2, 1] } :: (segment_000000_pm_nodes.drop 2)) 105
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 110 = allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 0 [(segment_000000_pm_final store) 104, (segment_000000_pm_final store) 105] 2 1 := by
    calc
      _ = allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 0 [((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 104, ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 105] 2 1 := hout_prefix
      _ = allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 0 [(segment_000000_pm_final store) 104, (segment_000000_pm_final store) 105] 2 1 := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_hAllToAll1 (store : Store) : (segment_000000_pm_final store) 111 = allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 1 [(segment_000000_pm_final store) 104, (segment_000000_pm_final store) 105] 2 1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [111], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 111 = allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 1 [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 104, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 105] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK2B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 1, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [111], params := [2, 1] } 111
      (fun t => allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 1 [t 104, t 105] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out BWEmbeddingMixedK2B2S5V13D7Graph.pm t 1 [104, 105] 111 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 104 = (segment_000000_pm_final store) 104 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [111], params := [2, 1] } :: (segment_000000_pm_nodes.drop 3)) 104
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 105 = (segment_000000_pm_final store) 105 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK2B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [104, 105], outs := [111], params := [2, 1] } :: (segment_000000_pm_nodes.drop 3)) 105
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 111 = allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 1 [(segment_000000_pm_final store) 104, (segment_000000_pm_final store) 105] 2 1 := by
    calc
      _ = allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 1 [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 104, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK2B2S5V13D7Graph.pm) store 105] 2 1 := hout_prefix
      _ = allToAllPrimWithDims BWEmbeddingMixedK2B2S5V13D7Graph.pm.numRanks 1 [(segment_000000_pm_final store) 104, (segment_000000_pm_final store) 105] 2 1 := by rw [hout_read_0, hout_read_1]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_before.Holds smStore pmStore) : state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hai : ai.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 5) [pmFinal 104, pmFinal 105] 2 [2, 10, 14] [2, 10, 7] at hai
  have hA0 : pmFinal 110 = allToAllPrimWithDims 2 0 [pmFinal 104, pmFinal 105] 2 1 := segment_000000_hAllToAll0 pmStore
  have hA1 : pmFinal 111 = allToAllPrimWithDims 2 1 [pmFinal 104, pmFinal 105] 2 1 := segment_000000_hAllToAll1 pmStore
  have hHead : (([pmFinal 104, pmFinal 105].head?.map (fun t => t.shape)).getD []) = [2, 10, 7] := hai.shard_shapes _ (by simp)
  have hAV : smFinal 5 = allGatherPrimDimN 2 2 0 [pmFinal 104, pmFinal 105] := by simpa only [List.length_cons,List.length_nil] using hai.full_value
  have hGS : (allGatherPrimDimN 2 2 0 [pmFinal 104, pmFinal 105]).shape = [2, 10, 14] := by rw [←hAV]; exact hai.full_shape
  have hOd : 1 < (allGatherPrimDimN 2 2 0 [pmFinal 104, pmFinal 105]).shape.length := by rw [hGS]; decide
  have hDv : (allGatherPrimDimN 2 2 0 [pmFinal 104, pmFinal 105]).shape.getD 1 0 % 2 = 0 := by rw [hGS]; decide
  have hAS0 : (pmFinal 110).shape = [2, 5, 14] := by rw [hA0,allToAllPrimWithDims_shape 2 0 [pmFinal 104, pmFinal 105] 2 1 [2, 10, 7] hHead (by decide)]; decide
  have hAS1 : (pmFinal 111).shape = [2, 5, 14] := by rw [hA1,allToAllPrimWithDims_shape 2 1 [pmFinal 104, pmFinal 105] 2 1 [2, 10, 7] hHead (by decide)]; decide
  have hOrd : [pmFinal 110, pmFinal 111] = List.ofFn (fun r : Fin 2 => allToAllPrimWithDims 2 r.1 [pmFinal 104, pmFinal 105] 2 1) := by rw [hA0, hA1]; rfl
  have hAC : allGatherPrimDimN 1 [pmFinal 110, pmFinal 111].length 0 [pmFinal 110, pmFinal 111] = allGatherPrimDimN 2 2 0 [pmFinal 104, pmFinal 105] := by rw [hOrd]; simpa only [List.length_cons,List.length_nil,List.length_ofFn] using (TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 2 1 [pmFinal 104, pmFinal 105] (by simp) hOd hDv)
  have houtA : ao.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 5) [pmFinal 110, pmFinal 111] 1 [2, 10, 14] [2, 5, 14]
    refine { full_value := ?_, full_shape := hai.full_shape, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
    · rw [hAC]; exact hAV
    · simp only [List.forall_mem_cons]; exact ⟨hAS0, hAS1, List.forall_mem_nil _⟩
    · simp only [List.length_cons,List.length_nil]; decide
  have houtH : ho.Holds smFinal pmFinal := by
    have hg : hg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 1) [pmFinal 102, pmFinal 103] 2 [2, 10, 14] [2, 10, 7] at hg
    have hgV : smFinal 1 = allGatherPrimDimN 2 2 0 [pmFinal 102, pmFinal 103] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hi : hi.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 2) [pmFinal 2] 0 [2, 10] [2, 10] at hi
    have hiShape := hi.shard_shapes (pmFinal 2) (by simp)
    have hiEq : smFinal 2 = pmFinal 2 := by
      rw [hi.full_value]
      exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hiShape]; native_decide)
    have hw : hw.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 3) [pmFinal 106, pmFinal 107] 1 [13, 14] [13, 7] at hw
    have hwV : smFinal 3 = allGatherPrimDimN 1 2 0 [pmFinal 106, pmFinal 107] := by
      simpa only [List.length_cons, List.length_nil] using hw.full_value
    have hSm := segment_000000_HSm smStore
    change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
    have hPm0 := segment_000000_HPm0 pmStore
    change pmFinal 108 = bw_embedding (pmFinal 102) (pmFinal 2) (pmFinal 106) at hPm0
    have houtShape0 : (pmFinal 108).shape = [13, 7] := by
      rw [hPm0, bw_embedding_shape]
      exact hw.shard_shapes (pmFinal 106) (by simp)
    have hPm1 := segment_000000_HPm1 pmStore
    change pmFinal 109 = bw_embedding (pmFinal 103) (pmFinal 2) (pmFinal 107) at hPm1
    have houtShape1 : (pmFinal 109).shape = [13, 7] := by
      rw [hPm1, bw_embedding_shape]
      exact hw.shard_shapes (pmFinal 107) (by simp)
    have hComm := TrainVerify.Denote.bw_embedding_hidden_allGather_rank3 2 2 10 13 7
      [pmFinal 102, pmFinal 103] [pmFinal 106, pmFinal 107] (pmFinal 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rfl) (by rfl) hg.shard_shapes hw.shard_shapes hiShape
    simp only [List.zipWith] at hComm
    have hValue : smFinal 4 = allGatherPrimDimN 1 2 0 [pmFinal 108, pmFinal 109] := by
      rw [hSm, hgV, hiEq, hwV, hComm]
      rw [← hPm0, ← hPm1]
    have hValueL : smFinal 4 = allGatherPrimDimN 1 [pmFinal 108, pmFinal 109].length 0 [pmFinal 108, pmFinal 109] := by
      simpa only [List.length_cons, List.length_nil] using hValue
    have hFullShape : (smFinal 4).shape = [13, 14] := by
      rw [hSm, bw_embedding_shape]
      exact hw.full_shape
    have hout : ho.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 4) [pmFinal 108, pmFinal 109] 1 [13, 14] [13, 7]
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
    exact hout
  have houtQ : qo.Holds smFinal pmFinal := by
    have hg : ao.Holds smFinal pmFinal := houtA
    change ShardedRel (smFinal 5) [pmFinal 110, pmFinal 111] 1 [2, 10, 14] [2, 5, 14] at hg
    have hi : qi.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ChunkedRel (smFinal 6) [pmFinal 100, pmFinal 101] 1 [2, 10] [2, 5] at hi
    have hw : qw.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 7) [pmFinal 7] 0 [14, 14] [14, 14] at hw
    have hwEq : smFinal 7 = pmFinal 7 := by
      rw [hw.full_value]
      exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes (pmFinal 7) (by simp)]; native_decide)
    have hgValue : smFinal 5 = allGatherPrimDimN 1 2 0 [pmFinal 110, pmFinal 111] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hSm := segment_000000_QSm smStore
    change smFinal 8 = bw_embedding (smFinal 5)
      (smFinal 6) (smFinal 7) at hSm
    have hPm0 := segment_000000_QPm0 pmStore
    change pmFinal 112 =
      bw_embedding (pmFinal 110)
        (pmFinal 100) (pmFinal 7) at hPm0
    have hPm1 := segment_000000_QPm1 pmStore
    change pmFinal 113 =
      bw_embedding (pmFinal 111)
        (pmFinal 101) (pmFinal 7) at hPm1
    have hComm := TrainVerify.Denote.bw_embedding_seqchunk_K 2 2 5 14 14
      [pmFinal 110, pmFinal 111] (smFinal 6) (pmFinal 7)
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
    have hValue : smFinal 8 = tensorSum [pmFinal 112, pmFinal 113] := by
      rw [hSm, hgValue, hwEq, hComm]
      rw [← hIdChunk0]
      rw [← hPm0]
      rw [← hIdChunk1]
      rw [← hPm1]
    have hValueReduce : smFinal 8 =
        allReducePrim [pmFinal 112, pmFinal 113].length 0 [pmFinal 112, pmFinal 113] := by
      rw [hValue]
      rfl
    have hFullShape : (smFinal 8).shape = [14, 14] := by
      rw [hSm, bw_embedding_shape]
      exact hw.full_shape
    have hShape0 : (pmFinal 112).shape = [14, 14] := by
      rw [hPm0, bw_embedding_shape]
      exact hw.shard_shapes _ (by simp)
    have hShape1 : (pmFinal 113).shape = [14, 14] := by
      rw [hPm1, bw_embedding_shape]
      exact hw.shard_shapes _ (by simp)
    have hout : qo.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 8) [pmFinal 112, pmFinal 113] [14, 14]
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
private def segment_000000 : ClosedDepSegmentCertificate BWEmbeddingMixedK2B2S5V13D7Graph.sm BWEmbeddingMixedK2B2S5V13D7Graph.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000_sound
end
end TrainVerify.Denote.BWEmbeddingMixedK2B2S5V13D7
