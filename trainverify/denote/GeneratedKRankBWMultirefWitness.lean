import denote.RelationCompiler
import denote.KRankBWMultiref
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace SyntheticBWMultiref
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_multiref", ins := [100, 101, 102, 103, 104], outs := [300] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_multiref", ins := [1000, 1100, 1200, 1300, 1400], outs := [9000] }, { rank := 1, op := "OpName.BW_multiref", ins := [1001, 1101, 1201, 1301, 1401], outs := [9001] }, { rank := 2, op := "OpName.BW_multiref", ins := [1002, 1102, 1202, 1302, 1402], outs := [9002] }] }
def fi0 : RelationFact := .sharded 100 [1000, 1001, 1002] 1 [2, 9, 7] [2, 3, 7]
def fi1 : RelationFact := .sharded 101 [1100, 1101, 1102] 1 [2, 9, 7] [2, 3, 7]
def fi2 : RelationFact := .sharded 102 [1200, 1201, 1202] 1 [2, 9, 7] [2, 3, 7]
def fi3 : RelationFact := .sharded 103 [1300, 1301, 1302] 1 [2, 9, 7] [2, 3, 7]
def fi4 : RelationFact := .sharded 104 [1400, 1401, 1402] 1 [2, 9, 7] [2, 3, 7]
def fo : RelationFact := .sharded 300 [9000, 9001, 9002] 1 [2, 9, 7] [2, 3, 7]
def state_000000 : RelationState where
  facts := [fi0, fi1, fi2, fi3, fi4]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fi0, fi1, fi2, fi3, fi4, fo]
  nonempty := by decide
set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_multiref", ins := [100, 101, 102, 103, 104], outs := [300] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_multiref", ins := [1000, 1100, 1200, 1300, 1400], outs := [9000] }, { rank := 1, op := "OpName.BW_multiref", ins := [1001, 1101, 1201, 1301, 1401], outs := [9001] }, { rank := 2, op := "OpName.BW_multiref", ins := [1002, 1102, 1202, 1302, 1402], outs := [9002] }]
private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) store
private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) store

private theorem segment_000000_hSmWriter (smStore : Store) :
    (segment_000000_sm_final smStore) 300 = tensorSum [(segment_000000_sm_final smStore) 100, (segment_000000_sm_final smStore) 101, (segment_000000_sm_final smStore) 102, (segment_000000_sm_final smStore) 103, (segment_000000_sm_final smStore) 104] := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_multiref", ins := [100, 101, 102, 103, 104], outs := [300] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 300 = tensorSum [((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 100, ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 101, ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 102, ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 103, ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 104] := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWMultiref.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_multiref", ins := [100, 101, 102, 103, 104], outs := [300] } 300
      (fun t => tensorSum [t 100, t 101, t 102, t 103, t 104]) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using (applyNode_bw_multiref_out SyntheticBWMultiref.smGraph t 0 [100, 101, 102, 103, 104] 300)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_multiref", ins := [100, 101, 102, 103, 104], outs := [300] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 101 = (segment_000000_sm_final smStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_multiref", ins := [100, 101, 102, 103, 104], outs := [300] } :: (segment_000000_sm_nodes.drop 1)) 101
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 102 = (segment_000000_sm_final smStore) 102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_multiref", ins := [100, 101, 102, 103, 104], outs := [300] } :: (segment_000000_sm_nodes.drop 1)) 102
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 103 = (segment_000000_sm_final smStore) 103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_multiref", ins := [100, 101, 102, 103, 104], outs := [300] } :: (segment_000000_sm_nodes.drop 1)) 103
      (by native_decide) (by native_decide)
  have hout_read_4 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 104 = (segment_000000_sm_final smStore) 104 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_multiref", ins := [100, 101, 102, 103, 104], outs := [300] } :: (segment_000000_sm_nodes.drop 1)) 104
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 300 = tensorSum [(segment_000000_sm_final smStore) 100, (segment_000000_sm_final smStore) 101, (segment_000000_sm_final smStore) 102, (segment_000000_sm_final smStore) 103, (segment_000000_sm_final smStore) 104] := by
    calc
      _ = tensorSum [((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 100, ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 101, ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 102, ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 103, ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.smGraph) smStore 104] := hout_prefix
      _ = tensorSum [(segment_000000_sm_final smStore) 100, (segment_000000_sm_final smStore) 101, (segment_000000_sm_final smStore) 102, (segment_000000_sm_final smStore) 103, (segment_000000_sm_final smStore) 104] := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3, hout_read_4]
  exact hout

private theorem segment_000000_hPmWriter0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 9000 = tensorSum [(segment_000000_pm_final pmStore) 1000, (segment_000000_pm_final pmStore) 1100, (segment_000000_pm_final pmStore) 1200, (segment_000000_pm_final pmStore) 1300, (segment_000000_pm_final pmStore) 1400] := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_multiref", ins := [1000, 1100, 1200, 1300, 1400], outs := [9000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 9000 = tensorSum [((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1000, ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1100, ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1200, ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1300, ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1400] := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_multiref", ins := [1000, 1100, 1200, 1300, 1400], outs := [9000] } 9000
      (fun t => tensorSum [t 1000, t 1100, t 1200, t 1300, t 1400]) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using (applyNode_bw_multiref_out SyntheticBWMultiref.pmGraph t 0 [1000, 1100, 1200, 1300, 1400] 9000)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_multiref", ins := [1000, 1100, 1200, 1300, 1400], outs := [9000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1100 = (segment_000000_pm_final pmStore) 1100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_multiref", ins := [1000, 1100, 1200, 1300, 1400], outs := [9000] } :: (segment_000000_pm_nodes.drop 1)) 1100
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1200 = (segment_000000_pm_final pmStore) 1200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_multiref", ins := [1000, 1100, 1200, 1300, 1400], outs := [9000] } :: (segment_000000_pm_nodes.drop 1)) 1200
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1300 = (segment_000000_pm_final pmStore) 1300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_multiref", ins := [1000, 1100, 1200, 1300, 1400], outs := [9000] } :: (segment_000000_pm_nodes.drop 1)) 1300
      (by native_decide) (by native_decide)
  have hout_read_4 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1400 = (segment_000000_pm_final pmStore) 1400 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_multiref", ins := [1000, 1100, 1200, 1300, 1400], outs := [9000] } :: (segment_000000_pm_nodes.drop 1)) 1400
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 9000 = tensorSum [(segment_000000_pm_final pmStore) 1000, (segment_000000_pm_final pmStore) 1100, (segment_000000_pm_final pmStore) 1200, (segment_000000_pm_final pmStore) 1300, (segment_000000_pm_final pmStore) 1400] := by
    calc
      _ = tensorSum [((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1000, ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1100, ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1200, ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1300, ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1400] := hout_prefix
      _ = tensorSum [(segment_000000_pm_final pmStore) 1000, (segment_000000_pm_final pmStore) 1100, (segment_000000_pm_final pmStore) 1200, (segment_000000_pm_final pmStore) 1300, (segment_000000_pm_final pmStore) 1400] := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3, hout_read_4]
  exact hout

private theorem segment_000000_hPmWriter1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 9001 = tensorSum [(segment_000000_pm_final pmStore) 1001, (segment_000000_pm_final pmStore) 1101, (segment_000000_pm_final pmStore) 1201, (segment_000000_pm_final pmStore) 1301, (segment_000000_pm_final pmStore) 1401] := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_multiref", ins := [1001, 1101, 1201, 1301, 1401], outs := [9001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 9001 = tensorSum [((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1001, ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1101, ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1201, ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1301, ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1401] := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_multiref", ins := [1001, 1101, 1201, 1301, 1401], outs := [9001] } 9001
      (fun t => tensorSum [t 1001, t 1101, t 1201, t 1301, t 1401]) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using (applyNode_bw_multiref_out SyntheticBWMultiref.pmGraph t 1 [1001, 1101, 1201, 1301, 1401] 9001)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_multiref", ins := [1001, 1101, 1201, 1301, 1401], outs := [9001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1101 = (segment_000000_pm_final pmStore) 1101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_multiref", ins := [1001, 1101, 1201, 1301, 1401], outs := [9001] } :: (segment_000000_pm_nodes.drop 2)) 1101
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1201 = (segment_000000_pm_final pmStore) 1201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_multiref", ins := [1001, 1101, 1201, 1301, 1401], outs := [9001] } :: (segment_000000_pm_nodes.drop 2)) 1201
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1301 = (segment_000000_pm_final pmStore) 1301 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_multiref", ins := [1001, 1101, 1201, 1301, 1401], outs := [9001] } :: (segment_000000_pm_nodes.drop 2)) 1301
      (by native_decide) (by native_decide)
  have hout_read_4 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1401 = (segment_000000_pm_final pmStore) 1401 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_multiref", ins := [1001, 1101, 1201, 1301, 1401], outs := [9001] } :: (segment_000000_pm_nodes.drop 2)) 1401
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 9001 = tensorSum [(segment_000000_pm_final pmStore) 1001, (segment_000000_pm_final pmStore) 1101, (segment_000000_pm_final pmStore) 1201, (segment_000000_pm_final pmStore) 1301, (segment_000000_pm_final pmStore) 1401] := by
    calc
      _ = tensorSum [((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1001, ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1101, ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1201, ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1301, ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1401] := hout_prefix
      _ = tensorSum [(segment_000000_pm_final pmStore) 1001, (segment_000000_pm_final pmStore) 1101, (segment_000000_pm_final pmStore) 1201, (segment_000000_pm_final pmStore) 1301, (segment_000000_pm_final pmStore) 1401] := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3, hout_read_4]
  exact hout

private theorem segment_000000_hPmWriter2 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 9002 = tensorSum [(segment_000000_pm_final pmStore) 1002, (segment_000000_pm_final pmStore) 1102, (segment_000000_pm_final pmStore) 1202, (segment_000000_pm_final pmStore) 1302, (segment_000000_pm_final pmStore) 1402] := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_multiref", ins := [1002, 1102, 1202, 1302, 1402], outs := [9002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 9002 = tensorSum [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1002, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1102, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1202, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1302, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1402] := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_multiref", ins := [1002, 1102, 1202, 1302, 1402], outs := [9002] } 9002
      (fun t => tensorSum [t 1002, t 1102, t 1202, t 1302, t 1402]) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        simpa only [List.map] using (applyNode_bw_multiref_out SyntheticBWMultiref.pmGraph t 2 [1002, 1102, 1202, 1302, 1402] 9002)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_multiref", ins := [1002, 1102, 1202, 1302, 1402], outs := [9002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1102 = (segment_000000_pm_final pmStore) 1102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_multiref", ins := [1002, 1102, 1202, 1302, 1402], outs := [9002] } :: (segment_000000_pm_nodes.drop 3)) 1102
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1202 = (segment_000000_pm_final pmStore) 1202 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_multiref", ins := [1002, 1102, 1202, 1302, 1402], outs := [9002] } :: (segment_000000_pm_nodes.drop 3)) 1202
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1302 = (segment_000000_pm_final pmStore) 1302 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_multiref", ins := [1002, 1102, 1202, 1302, 1402], outs := [9002] } :: (segment_000000_pm_nodes.drop 3)) 1302
      (by native_decide) (by native_decide)
  have hout_read_4 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1402 = (segment_000000_pm_final pmStore) 1402 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticBWMultiref.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_multiref", ins := [1002, 1102, 1202, 1302, 1402], outs := [9002] } :: (segment_000000_pm_nodes.drop 3)) 1402
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 9002 = tensorSum [(segment_000000_pm_final pmStore) 1002, (segment_000000_pm_final pmStore) 1102, (segment_000000_pm_final pmStore) 1202, (segment_000000_pm_final pmStore) 1302, (segment_000000_pm_final pmStore) 1402] := by
    calc
      _ = tensorSum [((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1002, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1102, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1202, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1302, ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticBWMultiref.pmGraph) pmStore 1402] := hout_prefix
      _ = tensorSum [(segment_000000_pm_final pmStore) 1002, (segment_000000_pm_final pmStore) 1102, (segment_000000_pm_final pmStore) 1202, (segment_000000_pm_final pmStore) 1302, (segment_000000_pm_final pmStore) 1402] := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3, hout_read_4]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
    let smFinal := segment_000000_sm_final smStore
    let pmFinal := segment_000000_pm_final pmStore
    have hframe : state_000000.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hi0 : fi0.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 1 [2, 9, 7] [2, 3, 7] at hi0
    have hv0 : smFinal 100 = allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002] := by
      simpa only [List.length_cons, List.length_nil] using hi0.full_value
    have hi1 : fi1.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 101) [pmFinal 1100, pmFinal 1101, pmFinal 1102] 1 [2, 9, 7] [2, 3, 7] at hi1
    have hv1 : smFinal 101 = allGatherPrimDimN 1 3 0 [pmFinal 1100, pmFinal 1101, pmFinal 1102] := by
      simpa only [List.length_cons, List.length_nil] using hi1.full_value
    have hi2 : fi2.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 102) [pmFinal 1200, pmFinal 1201, pmFinal 1202] 1 [2, 9, 7] [2, 3, 7] at hi2
    have hv2 : smFinal 102 = allGatherPrimDimN 1 3 0 [pmFinal 1200, pmFinal 1201, pmFinal 1202] := by
      simpa only [List.length_cons, List.length_nil] using hi2.full_value
    have hi3 : fi3.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 103) [pmFinal 1300, pmFinal 1301, pmFinal 1302] 1 [2, 9, 7] [2, 3, 7] at hi3
    have hv3 : smFinal 103 = allGatherPrimDimN 1 3 0 [pmFinal 1300, pmFinal 1301, pmFinal 1302] := by
      simpa only [List.length_cons, List.length_nil] using hi3.full_value
    have hi4 : fi4.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 104) [pmFinal 1400, pmFinal 1401, pmFinal 1402] 1 [2, 9, 7] [2, 3, 7] at hi4
    have hv4 : smFinal 104 = allGatherPrimDimN 1 3 0 [pmFinal 1400, pmFinal 1401, pmFinal 1402] := by
      simpa only [List.length_cons, List.length_nil] using hi4.full_value
    have hSmWriter : smFinal 300 = tensorSum [smFinal 100, smFinal 101, smFinal 102, smFinal 103, smFinal 104] :=
      segment_000000_hSmWriter smStore
    have hPmWriter0 : pmFinal 9000 = tensorSum [pmFinal 1000, pmFinal 1100, pmFinal 1200, pmFinal 1300, pmFinal 1400] :=
      segment_000000_hPmWriter0 pmStore
    have hOutShape0 : (pmFinal 9000).shape = [2, 3, 7] := by
      rw [hPmWriter0, tensorSum_shape]
      exact hi0.shard_shapes _ (by simp)
    have hPmWriter1 : pmFinal 9001 = tensorSum [pmFinal 1001, pmFinal 1101, pmFinal 1201, pmFinal 1301, pmFinal 1401] :=
      segment_000000_hPmWriter1 pmStore
    have hOutShape1 : (pmFinal 9001).shape = [2, 3, 7] := by
      rw [hPmWriter1, tensorSum_shape]
      exact hi0.shard_shapes _ (by simp)
    have hPmWriter2 : pmFinal 9002 = tensorSum [pmFinal 1002, pmFinal 1102, pmFinal 1202, pmFinal 1302, pmFinal 1402] :=
      segment_000000_hPmWriter2 pmStore
    have hOutShape2 : (pmFinal 9002).shape = [2, 3, 7] := by
      rw [hPmWriter2, tensorSum_shape]
      exact hi0.shard_shapes _ (by simp)
    have hcomm := TrainVerify.Denote.tensorSum_allGather_dim_K 1 3 [2, 3, 7] [[pmFinal 1000, pmFinal 1001, pmFinal 1002], [pmFinal 1100, pmFinal 1101, pmFinal 1102], [pmFinal 1200, pmFinal 1201, pmFinal 1202], [pmFinal 1300, pmFinal 1301, pmFinal 1302], [pmFinal 1400, pmFinal 1401, pmFinal 1402]]
      (by decide) (by simp) (by decide)
      (by
        intro xs hxs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxs
        rcases hxs with rfl | rfl | rfl | rfl | rfl <;> rfl)
      (by
        intro xs hxs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxs
        rcases hxs with rfl | rfl | rfl | rfl | rfl
        · exact hi0.shard_shapes
        · exact hi1.shard_shapes
        · exact hi2.shard_shapes
        · exact hi3.shard_shapes
        · exact hi4.shard_shapes)
    have hInputs : [smFinal 100, smFinal 101, smFinal 102, smFinal 103, smFinal 104] =
        [allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002], allGatherPrimDimN 1 3 0 [pmFinal 1100, pmFinal 1101, pmFinal 1102], allGatherPrimDimN 1 3 0 [pmFinal 1200, pmFinal 1201, pmFinal 1202], allGatherPrimDimN 1 3 0 [pmFinal 1300, pmFinal 1301, pmFinal 1302], allGatherPrimDimN 1 3 0 [pmFinal 1400, pmFinal 1401, pmFinal 1402]] :=
      (congrArg₂ List.cons hv0 (congrArg₂ List.cons hv1 (congrArg₂ List.cons hv2 (congrArg₂ List.cons hv3 (congrArg₂ List.cons hv4 rfl)))))
    have hOutValue : smFinal 300 = allGatherPrimDimN 1 3 0 [pmFinal 9000, pmFinal 9001, pmFinal 9002] := by
      rw [hSmWriter, hInputs]
      rw [hPmWriter0, hPmWriter1, hPmWriter2]
      simpa [tensorSumRanks, List.ofFn_succ] using hcomm
    have hOutValueList : smFinal 300 = allGatherPrimDimN 1 [pmFinal 9000, pmFinal 9001, pmFinal 9002].length 0 [pmFinal 9000, pmFinal 9001, pmFinal 9002] := by
      simpa only [List.length_cons, List.length_nil] using hOutValue
    have hFullShape : (smFinal 300).shape = [2, 9, 7] := by
      rw [hSmWriter, tensorSum_shape]
      exact hi0.full_shape
    have hout : fo.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 300) [pmFinal 9000, pmFinal 9001, pmFinal 9002] 1 [2, 9, 7] [2, 3, 7]
      refine {
        full_value := hOutValueList
        full_shape := hFullShape
        shards_nonempty := by simp
        gather_dim_lt := hi0.gather_dim_lt
        shard_shapes := ?_
        shape_contract := by
          simp only [List.length_cons, List.length_nil]
          native_decide
      }
      intro piece hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h0 | h1 | h2
      · subst piece
        exact hOutShape0
      · subst piece
        exact hOutShape1
      · subst piece
        exact hOutShape2
    intro fact hfact
    have covered : fact ∈ [fo] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fo] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticBWMultiref.smGraph SyntheticBWMultiref.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    exact segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end SyntheticBWMultiref
