import denote.RelationCompiler
import denote.KRankViewUnflatten
import denote.KRankLinearGather
set_option maxHeartbeats 500000
open TrainVerify.Denote
namespace UnflattenOutputK3N2M1Graph
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] }, { rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 15, 3, 7] }, { rank := 0, op := "OpName.FW_view", ins := [20000], outs := [20001], params := [2, 15, 3, 7] }] }
def pm : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] }, { rank := 0, op := "OpName.FW_view", ins := [20100], outs := [20200], params := [2, 5, 3, 7] }, { rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] }, { rank := 1, op := "OpName.FW_view", ins := [10101], outs := [10201], params := [2, 5, 3, 7] }, { rank := 1, op := "OpName.FW_view", ins := [20101], outs := [20201], params := [2, 5, 3, 7] }, { rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] }, { rank := 2, op := "OpName.FW_view", ins := [10102], outs := [10202], params := [2, 5, 3, 7] }, { rank := 2, op := "OpName.FW_view", ins := [20102], outs := [20202], params := [2, 5, 3, 7] }, { rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] }] }
end UnflattenOutputK3N2M1Graph
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.UnflattenOutputK3N2M1

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def x0 : RelationFact :=
  .sharded 10000 [10100, 10101, 10102] 1 [2, 15, 21] [2, 5, 21]

private def y0 : RelationFact :=
  .sharded 10001 [10200, 10201, 10202] 1 [2, 15, 3, 7] [2, 5, 3, 7]

private def x1 : RelationFact :=
  .sharded 20000 [20100, 20101, 20102] 1 [2, 15, 21] [2, 5, 21]

private def y1 : RelationFact :=
  .sharded 20001 [20200, 20201, 20202] 1 [2, 15, 3, 7] [2, 5, 3, 7]

private def x2 : RelationFact :=
  .joined 30000 30100 [2, 5, 7]

private def y2 : RelationFact :=
  .sharded 30001 [30200, 30201, 30202] 2 [2, 5, 9] [2, 5, 3]

private def w2 : RelationFact :=
  .sharded 30002 [30300, 30301, 30302] 0 [9, 7] [3, 7]

private def protected_pm : RelationFact :=
  .tensorShape .pm 998 [1]

private def anchor : RelationFact :=
  .tensorShape .sm 999 [1]

private def state_before : RelationState where
  facts := [anchor, protected_pm, x0, x1, x2, w2]
  nonempty := by decide

private def state_after : RelationState where
  facts := [anchor, protected_pm, x0, x1, x2, w2, y0, y1, y2]
  nonempty := by decide

private def segment_000000_smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] }, { rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 15, 3, 7] }, { rank := 0, op := "OpName.FW_view", ins := [20000], outs := [20001], params := [2, 15, 3, 7] }]
private def segment_000000_pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] }, { rank := 0, op := "OpName.FW_view", ins := [20100], outs := [20200], params := [2, 5, 3, 7] }, { rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] }, { rank := 1, op := "OpName.FW_view", ins := [10101], outs := [10201], params := [2, 5, 3, 7] }, { rank := 1, op := "OpName.FW_view", ins := [20101], outs := [20201], params := [2, 5, 3, 7] }, { rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] }, { rank := 2, op := "OpName.FW_view", ins := [10102], outs := [10202], params := [2, 5, 3, 7] }, { rank := 2, op := "OpName.FW_view", ins := [20102], outs := [20202], params := [2, 5, 3, 7] }, { rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] }]
@[irreducible] private def segment_000000_smFinal(z:Store):Store := segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) z
@[irreducible] private def segment_000000_pmFinal(z:Store):Store := segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) z
private theorem segment_000000_t0_smWriter (smStore : Store) :
    (segment_000000_smFinal smStore) 30001 = fw_linear ((segment_000000_smFinal smStore) 30000) ((segment_000000_smFinal smStore) 30002) := by
  have hfinal : (segment_000000_smFinal smStore) = segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore := by
    unfold segment_000000_smFinal
    rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] }] ++ (segment_000000_smNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 30001 = fw_linear (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 30000) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 30002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.sm smStore
      (segment_000000_smNodes.take 0) (segment_000000_smNodes.drop 1)
      { rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] } 30001
      (fun t => fw_linear (t 30000) (t 30002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK3N2M1Graph.sm t 0 30000 30002 30001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 30000 = (segment_000000_smFinal smStore) 30000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.sm smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] } :: (segment_000000_smNodes.drop 1)) 30000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 30002 = (segment_000000_smFinal smStore) 30002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.sm smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] } :: (segment_000000_smNodes.drop 1)) 30002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 30001 = fw_linear ((segment_000000_smFinal smStore) 30000) ((segment_000000_smFinal smStore) 30002) := by
    calc
      _ = fw_linear (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 30000) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 30002) := hout_prefix
      _ = fw_linear ((segment_000000_smFinal smStore) 30000) ((segment_000000_smFinal smStore) 30002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_pmWriter0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 30200 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30300) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 2) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] }] ++ (segment_000000_pmNodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 30200 = fw_linear (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30300) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 2) (segment_000000_pmNodes.drop 3)
      { rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] } 30200
      (fun t => fw_linear (t 30100) (t 30300)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK3N2M1Graph.pm t 0 30100 30300 30200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30100 = (segment_000000_pmFinal pmStore) 30100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] } :: (segment_000000_pmNodes.drop 3)) 30100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30300 = (segment_000000_pmFinal pmStore) 30300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] } :: (segment_000000_pmNodes.drop 3)) 30300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 30200 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30300) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30300) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30300) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_pmWriter1 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 30201 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30301) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 5) ++ [{ rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] }] ++ (segment_000000_pmNodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 30201 = fw_linear (((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30301) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 5) (segment_000000_pmNodes.drop 6)
      { rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] } 30201
      (fun t => fw_linear (t 30100) (t 30301)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK3N2M1Graph.pm t 1 30100 30301 30201
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30100 = (segment_000000_pmFinal pmStore) 30100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 5) ({ rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] } :: (segment_000000_pmNodes.drop 6)) 30100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30301 = (segment_000000_pmFinal pmStore) 30301 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 5) ({ rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] } :: (segment_000000_pmNodes.drop 6)) 30301
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 30201 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30301) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30301) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30301) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_pmWriter2 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 30202 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30302) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 8) ++ [{ rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] }] ++ (segment_000000_pmNodes.drop 9) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 30202 = fw_linear (((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30302) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 8) (segment_000000_pmNodes.drop 9)
      { rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] } 30202
      (fun t => fw_linear (t 30100) (t 30302)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK3N2M1Graph.pm t 2 30100 30302 30202
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30100 = (segment_000000_pmFinal pmStore) 30100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 8) ({ rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] } :: (segment_000000_pmNodes.drop 9)) 30100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30302 = (segment_000000_pmFinal pmStore) 30302 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 8) ({ rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] } :: (segment_000000_pmNodes.drop 9)) 30302
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 30202 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30302) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 30302) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30302) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_out (smStore pmStore : Store)
    (hActivation : x2.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore))
    (hWeight : w2.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)) :
    y2.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  change (segment_000000_smFinal smStore) 30000 = (segment_000000_pmFinal pmStore) 30100 ∧
    ((segment_000000_smFinal smStore) 30000).shape = [2, 5, 7] ∧
    ((segment_000000_pmFinal pmStore) 30100).shape = [2, 5, 7] at hActivation
  change ShardedRel ((segment_000000_smFinal smStore) 30002) [(segment_000000_pmFinal pmStore) 30300, (segment_000000_pmFinal pmStore) 30301, (segment_000000_pmFinal pmStore) 30302] 0 [9, 7] [3, 7] at hWeight
  have hSm := segment_000000_t0_smWriter smStore
  have hPm0 := segment_000000_t0_pmWriter0 pmStore
  have hPm1 := segment_000000_t0_pmWriter1 pmStore
  have hPm2 := segment_000000_t0_pmWriter2 pmStore
  have hComm := (TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm
    (K := [(segment_000000_pmFinal pmStore) 30300, (segment_000000_pmFinal pmStore) 30301, (segment_000000_pmFinal pmStore) 30302].length) (b := 2) (s := 5) (i := 7) (o := 3)
    (x := (segment_000000_pmFinal pmStore) 30100) (ws := [(segment_000000_pmFinal pmStore) 30300, (segment_000000_pmFinal pmStore) 30301, (segment_000000_pmFinal pmStore) 30302])
    (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by simp) hActivation.2.2 (fun w hw => hWeight.shard_shapes w hw))
  have hValue : (segment_000000_smFinal smStore) 30001 = allGatherPrimDimN 2 [(segment_000000_pmFinal pmStore) 30200, (segment_000000_pmFinal pmStore) 30201, (segment_000000_pmFinal pmStore) 30202].length 0 [(segment_000000_pmFinal pmStore) 30200, (segment_000000_pmFinal pmStore) 30201, (segment_000000_pmFinal pmStore) 30202] := by
    rw [hSm, hActivation.1, hWeight.full_value, hComm]
    simp only [List.map, List.length_cons, List.length_nil]
    rw [← hPm0, ← hPm1, ← hPm2]
  have hOutShape0 : ((segment_000000_pmFinal pmStore) 30200).shape = [2, 5, 3] := by
    rw [hPm0]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 30300) (by simp))
  have hOutShape1 : ((segment_000000_pmFinal pmStore) 30201).shape = [2, 5, 3] := by
    rw [hPm1]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 30301) (by simp))
  have hOutShape2 : ((segment_000000_pmFinal pmStore) 30202).shape = [2, 5, 3] := by
    rw [hPm2]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 30302) (by simp))
  unfold y2 RelationFact.Holds
  change ShardedRel ((segment_000000_smFinal smStore) 30001) [(segment_000000_pmFinal pmStore) 30200, (segment_000000_pmFinal pmStore) 30201, (segment_000000_pmFinal pmStore) 30202] 2 [2, 5, 9] [2, 5, 3]
  refine {
    full_value := hValue
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by native_decide
    shard_shapes := ?_
    shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
  }
  · rw [hValue]
    rw [allGatherPrimDimN_shape 2 [(segment_000000_pmFinal pmStore) 30200, (segment_000000_pmFinal pmStore) 30201, (segment_000000_pmFinal pmStore) 30202].length [(segment_000000_pmFinal pmStore) 30200, (segment_000000_pmFinal pmStore) 30201, (segment_000000_pmFinal pmStore) 30202] [2, 5, 3]]
    · simp only [List.length_cons, List.length_nil]
      native_decide
    · simp only [List.head?, Option.map, Option.getD]
      exact hOutShape0
  · intro shard hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hOutShape0
    · exact hOutShape1
    · exact hOutShape2

private theorem segment_000000_t1_hSmWriter(smStore:Store):(segment_000000_smFinal smStore) 10001=fw_view [2, 15, 3, 7] ((segment_000000_smFinal smStore) 10000):=by
  have hfinal:(segment_000000_smFinal smStore)=segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore:=by unfold segment_000000_smFinal;rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 1) ++ [{ rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 15, 3, 7] }] ++ (segment_000000_smNodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 10001 = fw_view [2, 15, 3, 7] (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 10000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.sm smStore
      (segment_000000_smNodes.take 1) (segment_000000_smNodes.drop 2)
      { rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 15, 3, 7] } 10001
      (fun t => fw_view [2, 15, 3, 7] (t 10000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK3N2M1Graph.sm t 0 2 [15, 3, 7] 10000 10001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 10000 = (segment_000000_smFinal smStore) 10000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.sm smStore
      (segment_000000_smNodes.take 1) ({ rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 15, 3, 7] } :: (segment_000000_smNodes.drop 2)) 10000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 10001 = fw_view [2, 15, 3, 7] ((segment_000000_smFinal smStore) 10000) := by
    calc
      _ = fw_view [2, 15, 3, 7] (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 10000) := hout_prefix
      _ = fw_view [2, 15, 3, 7] ((segment_000000_smFinal smStore) 10000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t1_hPmWriter0(pmStore:Store):(segment_000000_pmFinal pmStore) 10200=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10100):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 10200 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 10100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 0) (segment_000000_pmNodes.drop 1)
      { rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] } 10200
      (fun t => fw_view [2, 5, 3, 7] (t 10100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK3N2M1Graph.pm t 0 2 [5, 3, 7] 10100 10200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 10100 = (segment_000000_pmFinal pmStore) 10100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 1)) 10100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 10200 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10100) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 10100) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t1_hPmWriter1(pmStore:Store):(segment_000000_pmFinal pmStore) 10201=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10101):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 3) ++ [{ rank := 1, op := "OpName.FW_view", ins := [10101], outs := [10201], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 10201 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 10101) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 3) (segment_000000_pmNodes.drop 4)
      { rank := 1, op := "OpName.FW_view", ins := [10101], outs := [10201], params := [2, 5, 3, 7] } 10201
      (fun t => fw_view [2, 5, 3, 7] (t 10101)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK3N2M1Graph.pm t 1 2 [5, 3, 7] 10101 10201
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 10101 = (segment_000000_pmFinal pmStore) 10101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 3) ({ rank := 1, op := "OpName.FW_view", ins := [10101], outs := [10201], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 4)) 10101
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 10201 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10101) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 10101) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10101) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t1_hPmWriter2(pmStore:Store):(segment_000000_pmFinal pmStore) 10202=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10102):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 6) ++ [{ rank := 2, op := "OpName.FW_view", ins := [10102], outs := [10202], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 10202 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 6)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 10102) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 6) (segment_000000_pmNodes.drop 7)
      { rank := 2, op := "OpName.FW_view", ins := [10102], outs := [10202], params := [2, 5, 3, 7] } 10202
      (fun t => fw_view [2, 5, 3, 7] (t 10102)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK3N2M1Graph.pm t 2 2 [5, 3, 7] 10102 10202
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 6)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 10102 = (segment_000000_pmFinal pmStore) 10102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 6) ({ rank := 2, op := "OpName.FW_view", ins := [10102], outs := [10202], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 7)) 10102
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 10202 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10102) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 6)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 10102) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10102) := by rw [hout_read_0]
  exact hout
set_option maxHeartbeats 500000 in
private theorem segment_000000_t1_out(smStore pmStore:Store)(hframe:state_before.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)):
    y0.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore):=by
    let smFinal:=segment_000000_smFinal smStore
    let pmFinal:=segment_000000_pmFinal pmStore
    have hx:x0.Holds smFinal pmFinal:=hframe _ (by native_decide)
    change ShardedRel (smFinal 10000) [pmFinal 10100, pmFinal 10101, pmFinal 10102] 1 [2, 15, 21] [2, 5, 21] at hx
    have hxV:smFinal 10000=allGatherPrimDimN 1 3 0 [pmFinal 10100, pmFinal 10101, pmFinal 10102]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 10001=fw_view [2, 15, 3, 7] (smFinal 10000):=segment_000000_t1_hSmWriter smStore
    have hPm0:pmFinal 10200=fw_view [2, 5, 3, 7] (pmFinal 10100):=segment_000000_t1_hPmWriter0 pmStore
    have hPm1:pmFinal 10201=fw_view [2, 5, 3, 7] (pmFinal 10101):=segment_000000_t1_hPmWriter1 pmStore
    have hPm2:pmFinal 10202=fw_view [2, 5, 3, 7] (pmFinal 10102):=segment_000000_t1_hPmWriter2 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_unflatten_allGather_dim1_rank3 3 2 5 3 7 [pmFinal 10100, pmFinal 10101, pmFinal 10102]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 10001=allGatherPrimDimN 1 3 0 [pmFinal 10200, pmFinal 10201, pmFinal 10202]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1, ← hPm2]
    have hout:y0.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 10001) [pmFinal 10200, pmFinal 10201, pmFinal 10202] 1 [2, 15, 3, 7] [2, 5, 3, 7]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst piece; rw [hPm0]; rfl
        · subst piece; rw [hPm1]; rfl
        · subst piece; rw [hPm2]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    exact hout
private theorem segment_000000_t2_hSmWriter(smStore:Store):(segment_000000_smFinal smStore) 20001=fw_view [2, 15, 3, 7] ((segment_000000_smFinal smStore) 20000):=by
  have hfinal:(segment_000000_smFinal smStore)=segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore:=by unfold segment_000000_smFinal;rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 2) ++ [{ rank := 0, op := "OpName.FW_view", ins := [20000], outs := [20001], params := [2, 15, 3, 7] }] ++ (segment_000000_smNodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 20001 = fw_view [2, 15, 3, 7] (((segment_000000_smNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 20000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.sm smStore
      (segment_000000_smNodes.take 2) (segment_000000_smNodes.drop 3)
      { rank := 0, op := "OpName.FW_view", ins := [20000], outs := [20001], params := [2, 15, 3, 7] } 20001
      (fun t => fw_view [2, 15, 3, 7] (t 20000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK3N2M1Graph.sm t 0 2 [15, 3, 7] 20000 20001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 20000 = (segment_000000_smFinal smStore) 20000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.sm smStore
      (segment_000000_smNodes.take 2) ({ rank := 0, op := "OpName.FW_view", ins := [20000], outs := [20001], params := [2, 15, 3, 7] } :: (segment_000000_smNodes.drop 3)) 20000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 20001 = fw_view [2, 15, 3, 7] ((segment_000000_smFinal smStore) 20000) := by
    calc
      _ = fw_view [2, 15, 3, 7] (((segment_000000_smNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.sm) smStore 20000) := hout_prefix
      _ = fw_view [2, 15, 3, 7] ((segment_000000_smFinal smStore) 20000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t2_hPmWriter0(pmStore:Store):(segment_000000_pmFinal pmStore) 20200=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20100):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 1) ++ [{ rank := 0, op := "OpName.FW_view", ins := [20100], outs := [20200], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 20200 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 20100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 1) (segment_000000_pmNodes.drop 2)
      { rank := 0, op := "OpName.FW_view", ins := [20100], outs := [20200], params := [2, 5, 3, 7] } 20200
      (fun t => fw_view [2, 5, 3, 7] (t 20100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK3N2M1Graph.pm t 0 2 [5, 3, 7] 20100 20200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 20100 = (segment_000000_pmFinal pmStore) 20100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 0, op := "OpName.FW_view", ins := [20100], outs := [20200], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 2)) 20100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 20200 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20100) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 20100) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t2_hPmWriter1(pmStore:Store):(segment_000000_pmFinal pmStore) 20201=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20101):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 4) ++ [{ rank := 1, op := "OpName.FW_view", ins := [20101], outs := [20201], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 20201 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 20101) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 4) (segment_000000_pmNodes.drop 5)
      { rank := 1, op := "OpName.FW_view", ins := [20101], outs := [20201], params := [2, 5, 3, 7] } 20201
      (fun t => fw_view [2, 5, 3, 7] (t 20101)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK3N2M1Graph.pm t 1 2 [5, 3, 7] 20101 20201
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 20101 = (segment_000000_pmFinal pmStore) 20101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 4) ({ rank := 1, op := "OpName.FW_view", ins := [20101], outs := [20201], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 5)) 20101
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 20201 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20101) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 20101) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20101) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t2_hPmWriter2(pmStore:Store):(segment_000000_pmFinal pmStore) 20202=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20102):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 7) ++ [{ rank := 2, op := "OpName.FW_view", ins := [20102], outs := [20202], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 20202 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 7)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 20102) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 7) (segment_000000_pmNodes.drop 8)
      { rank := 2, op := "OpName.FW_view", ins := [20102], outs := [20202], params := [2, 5, 3, 7] } 20202
      (fun t => fw_view [2, 5, 3, 7] (t 20102)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK3N2M1Graph.pm t 2 2 [5, 3, 7] 20102 20202
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 7)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 20102 = (segment_000000_pmFinal pmStore) 20102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK3N2M1Graph.pm pmStore
      (segment_000000_pmNodes.take 7) ({ rank := 2, op := "OpName.FW_view", ins := [20102], outs := [20202], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 8)) 20102
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 20202 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20102) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 7)).foldl (applyNodeDistributedFaithful UnflattenOutputK3N2M1Graph.pm) pmStore 20102) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20102) := by rw [hout_read_0]
  exact hout
set_option maxHeartbeats 500000 in
private theorem segment_000000_t2_out(smStore pmStore:Store)(hframe:state_before.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)):
    y1.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore):=by
    let smFinal:=segment_000000_smFinal smStore
    let pmFinal:=segment_000000_pmFinal pmStore
    have hx:x1.Holds smFinal pmFinal:=hframe _ (by native_decide)
    change ShardedRel (smFinal 20000) [pmFinal 20100, pmFinal 20101, pmFinal 20102] 1 [2, 15, 21] [2, 5, 21] at hx
    have hxV:smFinal 20000=allGatherPrimDimN 1 3 0 [pmFinal 20100, pmFinal 20101, pmFinal 20102]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 20001=fw_view [2, 15, 3, 7] (smFinal 20000):=segment_000000_t2_hSmWriter smStore
    have hPm0:pmFinal 20200=fw_view [2, 5, 3, 7] (pmFinal 20100):=segment_000000_t2_hPmWriter0 pmStore
    have hPm1:pmFinal 20201=fw_view [2, 5, 3, 7] (pmFinal 20101):=segment_000000_t2_hPmWriter1 pmStore
    have hPm2:pmFinal 20202=fw_view [2, 5, 3, 7] (pmFinal 20102):=segment_000000_t2_hPmWriter2 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_unflatten_allGather_dim1_rank3 3 2 5 3 7 [pmFinal 20100, pmFinal 20101, pmFinal 20102]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 20001=allGatherPrimDimN 1 3 0 [pmFinal 20200, pmFinal 20201, pmFinal 20202]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1, ← hPm2]
    have hout:y1.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 20001) [pmFinal 20200, pmFinal 20201, pmFinal 20202] 1 [2, 15, 3, 7] [2, 5, 3, 7]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst piece; rw [hPm0]; rfl
        · subst piece; rw [hPm1]; rfl
        · subst piece; rw [hPm2]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    exact hout
private def segment_000000:ClosedDepSegmentCertificate UnflattenOutputK3N2M1Graph.sm UnflattenOutputK3N2M1Graph.pm state_before state_after where
  smNodes := segment_000000_smNodes
  pmNodes := segment_000000_pmNodes
  sound := by
    intro smStore pmStore hstate
    have hframe : state_before.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
      unfold segment_000000_smFinal segment_000000_pmFinal
      apply RelationState.Holds.fold_frame segment_000000_smNodes segment_000000_pmNodes smStore pmStore hstate <;> native_decide
    have h0 := segment_000000_t0_out smStore pmStore (hframe x2 (by native_decide)) (hframe w2 (by native_decide))
    have h1 := segment_000000_t1_out smStore pmStore hframe
    have h2 := segment_000000_t2_out smStore pmStore hframe
    have result : state_after.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
      intro fact hfact
      have covered : fact ∈ [y2, y0, y1] ++ state_before.facts :=
        (show state_after.facts ⊆ [y2, y0, y1] ++ state_before.facts by native_decide) hfact
      simp only [List.mem_append] at covered
      rcases covered with fresh | old
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
        rcases fresh with rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
      · exact hframe fact old
    simpa only [segment_000000_smFinal, segment_000000_pmFinal] using result

#print axioms segment_000000
end
end TrainVerify.Denote.UnflattenOutputK3N2M1
