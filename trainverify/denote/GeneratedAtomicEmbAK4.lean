import denote.GraphGears
import denote.BWEmbeddingHiddenShardK
import denote.BWEmbeddingSequenceShardK
import denote.RelationCompiler
open TrainVerify.Denote
namespace BWEmbeddingMixedK4B2S5V13D7Graph
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] }
def pm : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.ChunkPrim", ins := [6], outs := [100], params := [1] }, { rank := 1, op := "OpName.ChunkPrim", ins := [6], outs := [101], params := [1] }, { rank := 2, op := "OpName.ChunkPrim", ins := [6], outs := [102], params := [1] }, { rank := 3, op := "OpName.ChunkPrim", ins := [6], outs := [103], params := [1] }, { rank := 0, op := "OpName.BW_embedding", ins := [104, 2, 112], outs := [116] }, { rank := 1, op := "OpName.BW_embedding", ins := [105, 2, 113], outs := [117] }, { rank := 2, op := "OpName.BW_embedding", ins := [106, 2, 114], outs := [118] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [120], params := [2, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [121], params := [2, 1] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [122], params := [2, 1] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [123], params := [2, 1] }, { rank := 3, op := "OpName.BW_embedding", ins := [107, 2, 115], outs := [119] }, { rank := 0, op := "OpName.BW_embedding", ins := [120, 100, 7], outs := [124] }, { rank := 1, op := "OpName.BW_embedding", ins := [121, 101, 7], outs := [125] }, { rank := 2, op := "OpName.BW_embedding", ins := [122, 102, 7], outs := [126] }, { rank := 3, op := "OpName.BW_embedding", ins := [123, 103, 7], outs := [127] }] }
end BWEmbeddingMixedK4B2S5V13D7Graph
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.BWEmbeddingMixedK4B2S5V13D7

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def hg : RelationFact :=
  .sharded 1 [104, 105, 106, 107] 2 [2, 20, 28] [2, 20, 7]

private def hi : RelationFact :=
  .sharded 2 [2] 0 [2, 20] [2, 20]

private def hw : RelationFact :=
  .sharded 3 [112, 113, 114, 115] 1 [13, 28] [13, 7]

private def ai : RelationFact :=
  .sharded 5 [108, 109, 110, 111] 2 [2, 20, 28] [2, 20, 7]

private def qi : RelationFact :=
  .chunked 6 [100, 101, 102, 103] 1 [2, 20] [2, 5]

private def qw : RelationFact :=
  .sharded 7 [7] 0 [14, 28] [14, 28]

private def ho : RelationFact :=
  .sharded 4 [116, 117, 118, 119] 1 [13, 28] [13, 7]

private def ao : RelationFact :=
  .sharded 5 [120, 121, 122, 123] 1 [2, 20, 28] [2, 5, 28]

private def qo : RelationFact :=
  .reduction 8 [124, 125, 126, 127] [14, 28]

private def anchor : RelationFact :=
  .tensorShape .sm 2 [2, 20]

private def state_before : RelationState where
  facts := [anchor, hg, hi, hw, ai, qi, qw]
  nonempty := by decide

private def state_after : RelationState where
  facts := [anchor, hg, hi, hw, ai, qi, qw, ho, qo]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] }, { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_embedding", ins := [104, 2, 112], outs := [116] }, { rank := 1, op := "OpName.BW_embedding", ins := [105, 2, 113], outs := [117] }, { rank := 2, op := "OpName.BW_embedding", ins := [106, 2, 114], outs := [118] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [120], params := [2, 1] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [121], params := [2, 1] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [122], params := [2, 1] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [123], params := [2, 1] }, { rank := 3, op := "OpName.BW_embedding", ins := [107, 2, 115], outs := [119] }, { rank := 0, op := "OpName.BW_embedding", ins := [120, 100, 7], outs := [124] }, { rank := 1, op := "OpName.BW_embedding", ins := [121, 101, 7], outs := [125] }, { rank := 2, op := "OpName.BW_embedding", ins := [122, 102, 7], outs := [126] }, { rank := 3, op := "OpName.BW_embedding", ins := [123, 103, 7], outs := [127] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) s
private theorem segment_000000_HSm (smStore : Store) :
    (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 4 = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 3) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } 4
      (fun t => bw_embedding (t 1) (t 2) (t 3)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK4B2S5V13D7Graph.sm t 0 1 2 3 4
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 1 = (segment_000000_sm_final smStore) 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 1
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 2 = (segment_000000_sm_final smStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 3 = (segment_000000_sm_final smStore) 3 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_embedding", ins := [1, 2, 3], outs := [4] } :: (segment_000000_sm_nodes.drop 2)) 3
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 4 = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 1) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 2) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 3) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 1) ((segment_000000_sm_final smStore) 2) ((segment_000000_sm_final smStore) 3) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_HPm0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 116 = bw_embedding ((segment_000000_pm_final pmStore) 104) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 112) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [104, 2, 112], outs := [116] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 116 = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 104) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 112) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [104, 2, 112], outs := [116] } 116
      (fun t => bw_embedding (t 104) (t 2) (t 112)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 0 104 2 112 116
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 104 = (segment_000000_pm_final pmStore) 104 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [104, 2, 112], outs := [116] } :: (segment_000000_pm_nodes.drop 1)) 104
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [104, 2, 112], outs := [116] } :: (segment_000000_pm_nodes.drop 1)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 112 = (segment_000000_pm_final pmStore) 112 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [104, 2, 112], outs := [116] } :: (segment_000000_pm_nodes.drop 1)) 112
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 116 = bw_embedding ((segment_000000_pm_final pmStore) 104) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 112) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 104) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 112) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 104) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 112) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_HPm1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 117 = bw_embedding ((segment_000000_pm_final pmStore) 105) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 113) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [105, 2, 113], outs := [117] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 117 = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 105) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 113) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_embedding", ins := [105, 2, 113], outs := [117] } 117
      (fun t => bw_embedding (t 105) (t 2) (t 113)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 1 105 2 113 117
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 105 = (segment_000000_pm_final pmStore) 105 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [105, 2, 113], outs := [117] } :: (segment_000000_pm_nodes.drop 2)) 105
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [105, 2, 113], outs := [117] } :: (segment_000000_pm_nodes.drop 2)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 113 = (segment_000000_pm_final pmStore) 113 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_embedding", ins := [105, 2, 113], outs := [117] } :: (segment_000000_pm_nodes.drop 2)) 113
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 117 = bw_embedding ((segment_000000_pm_final pmStore) 105) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 113) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 105) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 113) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 105) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 113) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_HPm2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 118 = bw_embedding ((segment_000000_pm_final pmStore) 106) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 114) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [106, 2, 114], outs := [118] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 118 = bw_embedding (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 106) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 114) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_embedding", ins := [106, 2, 114], outs := [118] } 118
      (fun t => bw_embedding (t 106) (t 2) (t 114)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 2 106 2 114 118
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 106 = (segment_000000_pm_final pmStore) 106 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [106, 2, 114], outs := [118] } :: (segment_000000_pm_nodes.drop 3)) 106
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [106, 2, 114], outs := [118] } :: (segment_000000_pm_nodes.drop 3)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 114 = (segment_000000_pm_final pmStore) 114 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_embedding", ins := [106, 2, 114], outs := [118] } :: (segment_000000_pm_nodes.drop 3)) 114
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 118 = bw_embedding ((segment_000000_pm_final pmStore) 106) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 114) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 106) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 114) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 106) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 114) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_HPm3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 119 = bw_embedding ((segment_000000_pm_final pmStore) 107) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 115) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_embedding", ins := [107, 2, 115], outs := [119] }] ++ (segment_000000_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 119 = bw_embedding (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 107) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 115) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_embedding", ins := [107, 2, 115], outs := [119] } 119
      (fun t => bw_embedding (t 107) (t 2) (t 115)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 3 107 2 115 119
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 107 = (segment_000000_pm_final pmStore) 107 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_embedding", ins := [107, 2, 115], outs := [119] } :: (segment_000000_pm_nodes.drop 8)) 107
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2 = (segment_000000_pm_final pmStore) 2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_embedding", ins := [107, 2, 115], outs := [119] } :: (segment_000000_pm_nodes.drop 8)) 2
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 115 = (segment_000000_pm_final pmStore) 115 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_embedding", ins := [107, 2, 115], outs := [119] } :: (segment_000000_pm_nodes.drop 8)) 115
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 119 = bw_embedding ((segment_000000_pm_final pmStore) 107) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 115) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 107) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 2) (((segment_000000_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 115) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 107) ((segment_000000_pm_final pmStore) 2) ((segment_000000_pm_final pmStore) 115) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QSm (smStore : Store) :
    (segment_000000_sm_final smStore) 8 = bw_embedding ((segment_000000_sm_final smStore) 5) ((segment_000000_sm_final smStore) 6) ((segment_000000_sm_final smStore) 7) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 8 = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 5) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 6) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } 8
      (fun t => bw_embedding (t 5) (t 6) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK4B2S5V13D7Graph.sm t 0 5 6 7 8
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 5 = (segment_000000_sm_final smStore) 5 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } :: (segment_000000_sm_nodes.drop 1)) 5
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 6 = (segment_000000_sm_final smStore) 6 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } :: (segment_000000_sm_nodes.drop 1)) 6
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 7 = (segment_000000_sm_final smStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.sm smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_embedding", ins := [5, 6, 7], outs := [8] } :: (segment_000000_sm_nodes.drop 1)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 8 = bw_embedding ((segment_000000_sm_final smStore) 5) ((segment_000000_sm_final smStore) 6) ((segment_000000_sm_final smStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 5) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 6) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.sm) smStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_sm_final smStore) 5) ((segment_000000_sm_final smStore) 6) ((segment_000000_sm_final smStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QPm0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 124 = bw_embedding ((segment_000000_pm_final pmStore) 120) ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 7) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 8) ++ [{ rank := 0, op := "OpName.BW_embedding", ins := [120, 100, 7], outs := [124] }] ++ (segment_000000_pm_nodes.drop 9) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 124 = bw_embedding (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 120) (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 100) (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 8) (segment_000000_pm_nodes.drop 9)
      { rank := 0, op := "OpName.BW_embedding", ins := [120, 100, 7], outs := [124] } 124
      (fun t => bw_embedding (t 120) (t 100) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 0 120 100 7 124
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 120 = (segment_000000_pm_final pmStore) 120 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 0, op := "OpName.BW_embedding", ins := [120, 100, 7], outs := [124] } :: (segment_000000_pm_nodes.drop 9)) 120
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 100 = (segment_000000_pm_final pmStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 0, op := "OpName.BW_embedding", ins := [120, 100, 7], outs := [124] } :: (segment_000000_pm_nodes.drop 9)) 100
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7 = (segment_000000_pm_final pmStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 8) ({ rank := 0, op := "OpName.BW_embedding", ins := [120, 100, 7], outs := [124] } :: (segment_000000_pm_nodes.drop 9)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 124 = bw_embedding ((segment_000000_pm_final pmStore) 120) ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 120) (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 100) (((segment_000000_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 120) ((segment_000000_pm_final pmStore) 100) ((segment_000000_pm_final pmStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QPm1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 125 = bw_embedding ((segment_000000_pm_final pmStore) 121) ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 7) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 9) ++ [{ rank := 1, op := "OpName.BW_embedding", ins := [121, 101, 7], outs := [125] }] ++ (segment_000000_pm_nodes.drop 10) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 125 = bw_embedding (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 121) (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 101) (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 9) (segment_000000_pm_nodes.drop 10)
      { rank := 1, op := "OpName.BW_embedding", ins := [121, 101, 7], outs := [125] } 125
      (fun t => bw_embedding (t 121) (t 101) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 1 121 101 7 125
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 121 = (segment_000000_pm_final pmStore) 121 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 1, op := "OpName.BW_embedding", ins := [121, 101, 7], outs := [125] } :: (segment_000000_pm_nodes.drop 10)) 121
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 101 = (segment_000000_pm_final pmStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 1, op := "OpName.BW_embedding", ins := [121, 101, 7], outs := [125] } :: (segment_000000_pm_nodes.drop 10)) 101
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7 = (segment_000000_pm_final pmStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 1, op := "OpName.BW_embedding", ins := [121, 101, 7], outs := [125] } :: (segment_000000_pm_nodes.drop 10)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 125 = bw_embedding ((segment_000000_pm_final pmStore) 121) ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 121) (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 101) (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 121) ((segment_000000_pm_final pmStore) 101) ((segment_000000_pm_final pmStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QPm2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 126 = bw_embedding ((segment_000000_pm_final pmStore) 122) ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 7) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 10) ++ [{ rank := 2, op := "OpName.BW_embedding", ins := [122, 102, 7], outs := [126] }] ++ (segment_000000_pm_nodes.drop 11) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 126 = bw_embedding (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 122) (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 102) (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 10) (segment_000000_pm_nodes.drop 11)
      { rank := 2, op := "OpName.BW_embedding", ins := [122, 102, 7], outs := [126] } 126
      (fun t => bw_embedding (t 122) (t 102) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 2 122 102 7 126
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 122 = (segment_000000_pm_final pmStore) 122 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 10) ({ rank := 2, op := "OpName.BW_embedding", ins := [122, 102, 7], outs := [126] } :: (segment_000000_pm_nodes.drop 11)) 122
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 102 = (segment_000000_pm_final pmStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 10) ({ rank := 2, op := "OpName.BW_embedding", ins := [122, 102, 7], outs := [126] } :: (segment_000000_pm_nodes.drop 11)) 102
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7 = (segment_000000_pm_final pmStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 10) ({ rank := 2, op := "OpName.BW_embedding", ins := [122, 102, 7], outs := [126] } :: (segment_000000_pm_nodes.drop 11)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 126 = bw_embedding ((segment_000000_pm_final pmStore) 122) ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 122) (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 102) (((segment_000000_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 122) ((segment_000000_pm_final pmStore) 102) ((segment_000000_pm_final pmStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_QPm3 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 127 = bw_embedding ((segment_000000_pm_final pmStore) 123) ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 7) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 11) ++ [{ rank := 3, op := "OpName.BW_embedding", ins := [123, 103, 7], outs := [127] }] ++ (segment_000000_pm_nodes.drop 12) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 127 = bw_embedding (((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 123) (((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 103) (((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 11) (segment_000000_pm_nodes.drop 12)
      { rank := 3, op := "OpName.BW_embedding", ins := [123, 103, 7], outs := [127] } 127
      (fun t => bw_embedding (t 123) (t 103) (t 7)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_embedding_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 3 123 103 7 127
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 123 = (segment_000000_pm_final pmStore) 123 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 11) ({ rank := 3, op := "OpName.BW_embedding", ins := [123, 103, 7], outs := [127] } :: (segment_000000_pm_nodes.drop 12)) 123
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 103 = (segment_000000_pm_final pmStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 11) ({ rank := 3, op := "OpName.BW_embedding", ins := [123, 103, 7], outs := [127] } :: (segment_000000_pm_nodes.drop 12)) 103
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7 = (segment_000000_pm_final pmStore) 7 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm pmStore
      (segment_000000_pm_nodes.take 11) ({ rank := 3, op := "OpName.BW_embedding", ins := [123, 103, 7], outs := [127] } :: (segment_000000_pm_nodes.drop 12)) 7
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 127 = bw_embedding ((segment_000000_pm_final pmStore) 123) ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 7) := by
    calc
      _ = bw_embedding (((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 123) (((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 103) (((segment_000000_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) pmStore 7) := hout_prefix
      _ = bw_embedding ((segment_000000_pm_final pmStore) 123) ((segment_000000_pm_final pmStore) 103) ((segment_000000_pm_final pmStore) 7) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hAllToAll0 (store : Store) : (segment_000000_pm_final store) 120 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 0 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [120], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 120 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 0 [((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 0, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [120], params := [2, 1] } 120
      (fun t => allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 0 [t 108, t 109, t 110, t 111] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 0 [108, 109, 110, 111] 120 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108 = (segment_000000_pm_final store) 108 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 3) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [120], params := [2, 1] } :: (segment_000000_pm_nodes.drop 4)) 108
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109 = (segment_000000_pm_final store) 109 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 3) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [120], params := [2, 1] } :: (segment_000000_pm_nodes.drop 4)) 109
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110 = (segment_000000_pm_final store) 110 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 3) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [120], params := [2, 1] } :: (segment_000000_pm_nodes.drop 4)) 110
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111 = (segment_000000_pm_final store) 111 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 3) ({ rank := 0, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [120], params := [2, 1] } :: (segment_000000_pm_nodes.drop 4)) 111
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 120 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 0 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by
    calc
      _ = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 0 [((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110, ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111] 2 1 := hout_prefix
      _ = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 0 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hAllToAll1 (store : Store) : (segment_000000_pm_final store) 121 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 1 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [121], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 121 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 1 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 1, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [121], params := [2, 1] } 121
      (fun t => allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 1 [t 108, t 109, t 110, t 111] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 1 [108, 109, 110, 111] 121 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108 = (segment_000000_pm_final store) 108 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 4) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [121], params := [2, 1] } :: (segment_000000_pm_nodes.drop 5)) 108
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109 = (segment_000000_pm_final store) 109 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 4) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [121], params := [2, 1] } :: (segment_000000_pm_nodes.drop 5)) 109
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110 = (segment_000000_pm_final store) 110 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 4) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [121], params := [2, 1] } :: (segment_000000_pm_nodes.drop 5)) 110
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111 = (segment_000000_pm_final store) 111 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 4) ({ rank := 1, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [121], params := [2, 1] } :: (segment_000000_pm_nodes.drop 5)) 111
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 121 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 1 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by
    calc
      _ = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 1 [((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110, ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111] 2 1 := hout_prefix
      _ = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 1 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hAllToAll2 (store : Store) : (segment_000000_pm_final store) 122 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 2 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [122], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 122 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 2 [((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108, ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109, ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110, ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
      { rank := 2, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [122], params := [2, 1] } 122
      (fun t => allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 2 [t 108, t 109, t 110, t 111] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 2 [108, 109, 110, 111] 122 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108 = (segment_000000_pm_final store) 108 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [122], params := [2, 1] } :: (segment_000000_pm_nodes.drop 6)) 108
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109 = (segment_000000_pm_final store) 109 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [122], params := [2, 1] } :: (segment_000000_pm_nodes.drop 6)) 109
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110 = (segment_000000_pm_final store) 110 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [122], params := [2, 1] } :: (segment_000000_pm_nodes.drop 6)) 110
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111 = (segment_000000_pm_final store) 111 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 5) ({ rank := 2, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [122], params := [2, 1] } :: (segment_000000_pm_nodes.drop 6)) 111
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 122 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 2 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by
    calc
      _ = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 2 [((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108, ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109, ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110, ((segment_000000_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111] 2 1 := hout_prefix
      _ = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 2 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000000_hAllToAll3 (store : Store) : (segment_000000_pm_final store) 123 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 3 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 6) ++ [{ rank := 3, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [123], params := [2, 1] }] ++ (segment_000000_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final store) 123 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 3 [((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111] 2 1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 6) (segment_000000_pm_nodes.drop 7)
      { rank := 3, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [123], params := [2, 1] } 123
      (fun t => allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 3 [t 108, t 109, t 110, t 111] 2 1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using applyNode_allToAllPrimWithDims_out BWEmbeddingMixedK4B2S5V13D7Graph.pm t 3 [108, 109, 110, 111] 123 2 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108 = (segment_000000_pm_final store) 108 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 6) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [123], params := [2, 1] } :: (segment_000000_pm_nodes.drop 7)) 108
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109 = (segment_000000_pm_final store) 109 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 6) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [123], params := [2, 1] } :: (segment_000000_pm_nodes.drop 7)) 109
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110 = (segment_000000_pm_final store) 110 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 6) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [123], params := [2, 1] } :: (segment_000000_pm_nodes.drop 7)) 110
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111 = (segment_000000_pm_final store) 111 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final BWEmbeddingMixedK4B2S5V13D7Graph.pm store
      (segment_000000_pm_nodes.take 6) ({ rank := 3, op := "OpName.AllToAllPrim", ins := [108, 109, 110, 111], outs := [123], params := [2, 1] } :: (segment_000000_pm_nodes.drop 7)) 111
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final store) 123 = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 3 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by
    calc
      _ = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 3 [((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 108, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 109, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 110, ((segment_000000_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful BWEmbeddingMixedK4B2S5V13D7Graph.pm) store 111] 2 1 := hout_prefix
      _ = allToAllPrimWithDims BWEmbeddingMixedK4B2S5V13D7Graph.pm.numRanks 3 [(segment_000000_pm_final store) 108, (segment_000000_pm_final store) 109, (segment_000000_pm_final store) 110, (segment_000000_pm_final store) 111] 2 1 := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_before.Holds smStore pmStore) : state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hai : ai.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 5) [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 2 [2, 20, 28] [2, 20, 7] at hai
  have hA0 : pmFinal 120 = allToAllPrimWithDims 4 0 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 2 1 := segment_000000_hAllToAll0 pmStore
  have hA1 : pmFinal 121 = allToAllPrimWithDims 4 1 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 2 1 := segment_000000_hAllToAll1 pmStore
  have hA2 : pmFinal 122 = allToAllPrimWithDims 4 2 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 2 1 := segment_000000_hAllToAll2 pmStore
  have hA3 : pmFinal 123 = allToAllPrimWithDims 4 3 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 2 1 := segment_000000_hAllToAll3 pmStore
  have hHead : (([pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111].head?.map (fun t => t.shape)).getD []) = [2, 20, 7] := hai.shard_shapes _ (by simp)
  have hAV : smFinal 5 = allGatherPrimDimN 2 4 0 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] := by simpa only [List.length_cons,List.length_nil] using hai.full_value
  have hGS : (allGatherPrimDimN 2 4 0 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111]).shape = [2, 20, 28] := by rw [←hAV]; exact hai.full_shape
  have hOd : 1 < (allGatherPrimDimN 2 4 0 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111]).shape.length := by rw [hGS]; decide
  have hDv : (allGatherPrimDimN 2 4 0 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111]).shape.getD 1 0 % 4 = 0 := by rw [hGS]; decide
  have hAS0 : (pmFinal 120).shape = [2, 5, 28] := by rw [hA0,allToAllPrimWithDims_shape 4 0 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 2 1 [2, 20, 7] hHead (by decide)]; decide
  have hAS1 : (pmFinal 121).shape = [2, 5, 28] := by rw [hA1,allToAllPrimWithDims_shape 4 1 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 2 1 [2, 20, 7] hHead (by decide)]; decide
  have hAS2 : (pmFinal 122).shape = [2, 5, 28] := by rw [hA2,allToAllPrimWithDims_shape 4 2 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 2 1 [2, 20, 7] hHead (by decide)]; decide
  have hAS3 : (pmFinal 123).shape = [2, 5, 28] := by rw [hA3,allToAllPrimWithDims_shape 4 3 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 2 1 [2, 20, 7] hHead (by decide)]; decide
  have hOrd : [pmFinal 120, pmFinal 121, pmFinal 122, pmFinal 123] = List.ofFn (fun r : Fin 4 => allToAllPrimWithDims 4 r.1 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] 2 1) := by rw [hA0, hA1, hA2, hA3]; rfl
  have hAC : allGatherPrimDimN 1 [pmFinal 120, pmFinal 121, pmFinal 122, pmFinal 123].length 0 [pmFinal 120, pmFinal 121, pmFinal 122, pmFinal 123] = allGatherPrimDimN 2 4 0 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] := by rw [hOrd]; simpa only [List.length_cons,List.length_nil,List.length_ofFn] using (TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 2 1 [pmFinal 108, pmFinal 109, pmFinal 110, pmFinal 111] (by simp) hOd hDv)
  have houtA : ao.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 5) [pmFinal 120, pmFinal 121, pmFinal 122, pmFinal 123] 1 [2, 20, 28] [2, 5, 28]
    refine { full_value := ?_, full_shape := hai.full_shape, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
    · rw [hAC]; exact hAV
    · simp only [List.forall_mem_cons]; exact ⟨hAS0, hAS1, hAS2, hAS3, List.forall_mem_nil _⟩
    · simp only [List.length_cons,List.length_nil]; decide
  have houtH : ho.Holds smFinal pmFinal := by
    have hg : hg.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 1) [pmFinal 104, pmFinal 105, pmFinal 106, pmFinal 107] 2 [2, 20, 28] [2, 20, 7] at hg
    have hgV : smFinal 1 = allGatherPrimDimN 2 4 0 [pmFinal 104, pmFinal 105, pmFinal 106, pmFinal 107] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hi : hi.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 2) [pmFinal 2] 0 [2, 20] [2, 20] at hi
    have hiShape := hi.shard_shapes (pmFinal 2) (by simp)
    have hiEq : smFinal 2 = pmFinal 2 := by
      rw [hi.full_value]
      exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hiShape]; native_decide)
    have hw : hw.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 3) [pmFinal 112, pmFinal 113, pmFinal 114, pmFinal 115] 1 [13, 28] [13, 7] at hw
    have hwV : smFinal 3 = allGatherPrimDimN 1 4 0 [pmFinal 112, pmFinal 113, pmFinal 114, pmFinal 115] := by
      simpa only [List.length_cons, List.length_nil] using hw.full_value
    have hSm := segment_000000_HSm smStore
    change smFinal 4 = bw_embedding (smFinal 1) (smFinal 2) (smFinal 3) at hSm
    have hPm0 := segment_000000_HPm0 pmStore
    change pmFinal 116 = bw_embedding (pmFinal 104) (pmFinal 2) (pmFinal 112) at hPm0
    have houtShape0 : (pmFinal 116).shape = [13, 7] := by
      rw [hPm0, bw_embedding_shape]
      exact hw.shard_shapes (pmFinal 112) (by simp)
    have hPm1 := segment_000000_HPm1 pmStore
    change pmFinal 117 = bw_embedding (pmFinal 105) (pmFinal 2) (pmFinal 113) at hPm1
    have houtShape1 : (pmFinal 117).shape = [13, 7] := by
      rw [hPm1, bw_embedding_shape]
      exact hw.shard_shapes (pmFinal 113) (by simp)
    have hPm2 := segment_000000_HPm2 pmStore
    change pmFinal 118 = bw_embedding (pmFinal 106) (pmFinal 2) (pmFinal 114) at hPm2
    have houtShape2 : (pmFinal 118).shape = [13, 7] := by
      rw [hPm2, bw_embedding_shape]
      exact hw.shard_shapes (pmFinal 114) (by simp)
    have hPm3 := segment_000000_HPm3 pmStore
    change pmFinal 119 = bw_embedding (pmFinal 107) (pmFinal 2) (pmFinal 115) at hPm3
    have houtShape3 : (pmFinal 119).shape = [13, 7] := by
      rw [hPm3, bw_embedding_shape]
      exact hw.shard_shapes (pmFinal 115) (by simp)
    have hComm := TrainVerify.Denote.bw_embedding_hidden_allGather_rank3 4 2 20 13 7
      [pmFinal 104, pmFinal 105, pmFinal 106, pmFinal 107] [pmFinal 112, pmFinal 113, pmFinal 114, pmFinal 115] (pmFinal 2)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rfl) (by rfl) hg.shard_shapes hw.shard_shapes hiShape
    simp only [List.zipWith] at hComm
    have hValue : smFinal 4 = allGatherPrimDimN 1 4 0 [pmFinal 116, pmFinal 117, pmFinal 118, pmFinal 119] := by
      rw [hSm, hgV, hiEq, hwV, hComm]
      rw [← hPm0, ← hPm1, ← hPm2, ← hPm3]
    have hValueL : smFinal 4 = allGatherPrimDimN 1 [pmFinal 116, pmFinal 117, pmFinal 118, pmFinal 119].length 0 [pmFinal 116, pmFinal 117, pmFinal 118, pmFinal 119] := by
      simpa only [List.length_cons, List.length_nil] using hValue
    have hFullShape : (smFinal 4).shape = [13, 28] := by
      rw [hSm, bw_embedding_shape]
      exact hw.full_shape
    have hout : ho.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 4) [pmFinal 116, pmFinal 117, pmFinal 118, pmFinal 119] 1 [13, 28] [13, 7]
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
    exact hout
  have houtQ : qo.Holds smFinal pmFinal := by
    have hg : ao.Holds smFinal pmFinal := houtA
    change ShardedRel (smFinal 5) [pmFinal 120, pmFinal 121, pmFinal 122, pmFinal 123] 1 [2, 20, 28] [2, 5, 28] at hg
    have hi : qi.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ChunkedRel (smFinal 6) [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103] 1 [2, 20] [2, 5] at hi
    have hw : qw.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 7) [pmFinal 7] 0 [14, 28] [14, 28] at hw
    have hwEq : smFinal 7 = pmFinal 7 := by
      rw [hw.full_value]
      exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes (pmFinal 7) (by simp)]; native_decide)
    have hgValue : smFinal 5 = allGatherPrimDimN 1 4 0 [pmFinal 120, pmFinal 121, pmFinal 122, pmFinal 123] := by
      simpa only [List.length_cons, List.length_nil] using hg.full_value
    have hSm := segment_000000_QSm smStore
    change smFinal 8 = bw_embedding (smFinal 5)
      (smFinal 6) (smFinal 7) at hSm
    have hPm0 := segment_000000_QPm0 pmStore
    change pmFinal 124 =
      bw_embedding (pmFinal 120)
        (pmFinal 100) (pmFinal 7) at hPm0
    have hPm1 := segment_000000_QPm1 pmStore
    change pmFinal 125 =
      bw_embedding (pmFinal 121)
        (pmFinal 101) (pmFinal 7) at hPm1
    have hPm2 := segment_000000_QPm2 pmStore
    change pmFinal 126 =
      bw_embedding (pmFinal 122)
        (pmFinal 102) (pmFinal 7) at hPm2
    have hPm3 := segment_000000_QPm3 pmStore
    change pmFinal 127 =
      bw_embedding (pmFinal 123)
        (pmFinal 103) (pmFinal 7) at hPm3
    have hComm := TrainVerify.Denote.bw_embedding_seqchunk_K 4 2 5 28 14
      [pmFinal 120, pmFinal 121, pmFinal 122, pmFinal 123] (smFinal 6) (pmFinal 7)
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
    have hIdChunk3 := hi.chunk_values 3 (by simp)
    simp [List.getD] at hIdChunk3
    have hValue : smFinal 8 = tensorSum [pmFinal 124, pmFinal 125, pmFinal 126, pmFinal 127] := by
      rw [hSm, hgValue, hwEq, hComm]
      rw [← hIdChunk0]
      rw [← hPm0]
      rw [← hIdChunk1]
      rw [← hPm1]
      rw [← hIdChunk2]
      rw [← hPm2]
      rw [← hIdChunk3]
      rw [← hPm3]
    have hValueReduce : smFinal 8 =
        allReducePrim [pmFinal 124, pmFinal 125, pmFinal 126, pmFinal 127].length 0 [pmFinal 124, pmFinal 125, pmFinal 126, pmFinal 127] := by
      rw [hValue]
      rfl
    have hFullShape : (smFinal 8).shape = [14, 28] := by
      rw [hSm, bw_embedding_shape]
      exact hw.full_shape
    have hShape0 : (pmFinal 124).shape = [14, 28] := by
      rw [hPm0, bw_embedding_shape]
      exact hw.shard_shapes _ (by simp)
    have hShape1 : (pmFinal 125).shape = [14, 28] := by
      rw [hPm1, bw_embedding_shape]
      exact hw.shard_shapes _ (by simp)
    have hShape2 : (pmFinal 126).shape = [14, 28] := by
      rw [hPm2, bw_embedding_shape]
      exact hw.shard_shapes _ (by simp)
    have hShape3 : (pmFinal 127).shape = [14, 28] := by
      rw [hPm3, bw_embedding_shape]
      exact hw.shard_shapes _ (by simp)
    have hout : qo.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 8) [pmFinal 124, pmFinal 125, pmFinal 126, pmFinal 127] [14, 28]
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
private def segment_000000 : ClosedDepSegmentCertificate BWEmbeddingMixedK4B2S5V13D7Graph.sm BWEmbeddingMixedK4B2S5V13D7Graph.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by intro a b h; have z := segment_000000_sound a b h; unfold segment_000000_sm_final segment_000000_pm_final at z; exact z

#print axioms segment_000000_sound
end
end TrainVerify.Denote.BWEmbeddingMixedK4B2S5V13D7
