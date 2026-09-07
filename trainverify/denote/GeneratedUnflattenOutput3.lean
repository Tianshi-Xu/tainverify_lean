import denote.RelationCompiler
import denote.KRankViewUnflatten
import denote.KRankLinearGather
set_option maxHeartbeats 500000
open TrainVerify.Denote
namespace UnflattenOutputK4N2M3Graph
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] }, { rank := 0, op := "OpName.FW_linear", ins := [40000, 40002], outs := [40001] }, { rank := 0, op := "OpName.FW_linear", ins := [50000, 50002], outs := [50001] }, { rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 20, 3, 7] }, { rank := 0, op := "OpName.FW_view", ins := [20000], outs := [20001], params := [2, 20, 3, 7] }] }
def pm : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] }, { rank := 0, op := "OpName.FW_view", ins := [20100], outs := [20200], params := [2, 5, 3, 7] }, { rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] }, { rank := 0, op := "OpName.FW_linear", ins := [40100, 40300], outs := [40200] }, { rank := 0, op := "OpName.FW_linear", ins := [50100, 50300], outs := [50200] }, { rank := 1, op := "OpName.FW_view", ins := [10101], outs := [10201], params := [2, 5, 3, 7] }, { rank := 1, op := "OpName.FW_view", ins := [20101], outs := [20201], params := [2, 5, 3, 7] }, { rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] }, { rank := 1, op := "OpName.FW_linear", ins := [40100, 40301], outs := [40201] }, { rank := 1, op := "OpName.FW_linear", ins := [50100, 50301], outs := [50201] }, { rank := 2, op := "OpName.FW_view", ins := [10102], outs := [10202], params := [2, 5, 3, 7] }, { rank := 2, op := "OpName.FW_view", ins := [20102], outs := [20202], params := [2, 5, 3, 7] }, { rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] }, { rank := 2, op := "OpName.FW_linear", ins := [40100, 40302], outs := [40202] }, { rank := 2, op := "OpName.FW_linear", ins := [50100, 50302], outs := [50202] }, { rank := 3, op := "OpName.FW_view", ins := [10103], outs := [10203], params := [2, 5, 3, 7] }, { rank := 3, op := "OpName.FW_view", ins := [20103], outs := [20203], params := [2, 5, 3, 7] }, { rank := 3, op := "OpName.FW_linear", ins := [30100, 30303], outs := [30203] }, { rank := 3, op := "OpName.FW_linear", ins := [40100, 40303], outs := [40203] }, { rank := 3, op := "OpName.FW_linear", ins := [50100, 50303], outs := [50203] }] }
end UnflattenOutputK4N2M3Graph
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.UnflattenOutputK4N2M3

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def x0 : RelationFact :=
  .sharded 10000 [10100, 10101, 10102, 10103] 1 [2, 20, 21] [2, 5, 21]

private def y0 : RelationFact :=
  .sharded 10001 [10200, 10201, 10202, 10203] 1 [2, 20, 3, 7] [2, 5, 3, 7]

private def x1 : RelationFact :=
  .sharded 20000 [20100, 20101, 20102, 20103] 1 [2, 20, 21] [2, 5, 21]

private def y1 : RelationFact :=
  .sharded 20001 [20200, 20201, 20202, 20203] 1 [2, 20, 3, 7] [2, 5, 3, 7]

private def x2 : RelationFact :=
  .joined 30000 30100 [2, 5, 7]

private def y2 : RelationFact :=
  .sharded 30001 [30200, 30201, 30202, 30203] 2 [2, 5, 12] [2, 5, 3]

private def w2 : RelationFact :=
  .sharded 30002 [30300, 30301, 30302, 30303] 0 [12, 7] [3, 7]

private def x3 : RelationFact :=
  .joined 40000 40100 [2, 5, 7]

private def y3 : RelationFact :=
  .sharded 40001 [40200, 40201, 40202, 40203] 2 [2, 5, 12] [2, 5, 3]

private def w3 : RelationFact :=
  .sharded 40002 [40300, 40301, 40302, 40303] 0 [12, 7] [3, 7]

private def x4 : RelationFact :=
  .joined 50000 50100 [2, 5, 7]

private def y4 : RelationFact :=
  .sharded 50001 [50200, 50201, 50202, 50203] 2 [2, 5, 12] [2, 5, 3]

private def w4 : RelationFact :=
  .sharded 50002 [50300, 50301, 50302, 50303] 0 [12, 7] [3, 7]

private def protected_pm : RelationFact :=
  .tensorShape .pm 998 [1]

private def anchor : RelationFact :=
  .tensorShape .sm 999 [1]

private def state_before : RelationState where
  facts := [anchor, protected_pm, x0, x1, x2, w2, x3, w3, x4, w4]
  nonempty := by decide

private def state_after : RelationState where
  facts := [anchor, protected_pm, x0, x1, x2, w2, x3, w3, x4, w4, y0, y1, y2, y3, y4]
  nonempty := by decide

private def segment_000000_smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] }, { rank := 0, op := "OpName.FW_linear", ins := [40000, 40002], outs := [40001] }, { rank := 0, op := "OpName.FW_linear", ins := [50000, 50002], outs := [50001] }, { rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 20, 3, 7] }, { rank := 0, op := "OpName.FW_view", ins := [20000], outs := [20001], params := [2, 20, 3, 7] }]
private def segment_000000_pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] }, { rank := 0, op := "OpName.FW_view", ins := [20100], outs := [20200], params := [2, 5, 3, 7] }, { rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] }, { rank := 0, op := "OpName.FW_linear", ins := [40100, 40300], outs := [40200] }, { rank := 0, op := "OpName.FW_linear", ins := [50100, 50300], outs := [50200] }, { rank := 1, op := "OpName.FW_view", ins := [10101], outs := [10201], params := [2, 5, 3, 7] }, { rank := 1, op := "OpName.FW_view", ins := [20101], outs := [20201], params := [2, 5, 3, 7] }, { rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] }, { rank := 1, op := "OpName.FW_linear", ins := [40100, 40301], outs := [40201] }, { rank := 1, op := "OpName.FW_linear", ins := [50100, 50301], outs := [50201] }, { rank := 2, op := "OpName.FW_view", ins := [10102], outs := [10202], params := [2, 5, 3, 7] }, { rank := 2, op := "OpName.FW_view", ins := [20102], outs := [20202], params := [2, 5, 3, 7] }, { rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] }, { rank := 2, op := "OpName.FW_linear", ins := [40100, 40302], outs := [40202] }, { rank := 2, op := "OpName.FW_linear", ins := [50100, 50302], outs := [50202] }, { rank := 3, op := "OpName.FW_view", ins := [10103], outs := [10203], params := [2, 5, 3, 7] }, { rank := 3, op := "OpName.FW_view", ins := [20103], outs := [20203], params := [2, 5, 3, 7] }, { rank := 3, op := "OpName.FW_linear", ins := [30100, 30303], outs := [30203] }, { rank := 3, op := "OpName.FW_linear", ins := [40100, 40303], outs := [40203] }, { rank := 3, op := "OpName.FW_linear", ins := [50100, 50303], outs := [50203] }]
@[irreducible] private def segment_000000_smFinal(z:Store):Store := segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) z
@[irreducible] private def segment_000000_pmFinal(z:Store):Store := segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) z
private theorem segment_000000_t0_smWriter (smStore : Store) :
    (segment_000000_smFinal smStore) 30001 = fw_linear ((segment_000000_smFinal smStore) 30000) ((segment_000000_smFinal smStore) 30002) := by
  have hfinal : (segment_000000_smFinal smStore) = segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore := by
    unfold segment_000000_smFinal
    rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] }] ++ (segment_000000_smNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 30001 = fw_linear (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 30000) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 30002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 0) (segment_000000_smNodes.drop 1)
      { rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] } 30001
      (fun t => fw_linear (t 30000) (t 30002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.sm t 0 30000 30002 30001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 30000 = (segment_000000_smFinal smStore) 30000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] } :: (segment_000000_smNodes.drop 1)) 30000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 30002 = (segment_000000_smFinal smStore) 30002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [30000, 30002], outs := [30001] } :: (segment_000000_smNodes.drop 1)) 30002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 30001 = fw_linear ((segment_000000_smFinal smStore) 30000) ((segment_000000_smFinal smStore) 30002) := by
    calc
      _ = fw_linear (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 30000) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 30002) := hout_prefix
      _ = fw_linear ((segment_000000_smFinal smStore) 30000) ((segment_000000_smFinal smStore) 30002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_pmWriter0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 30200 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30300) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 2) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] }] ++ (segment_000000_pmNodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 30200 = fw_linear (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30300) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 2) (segment_000000_pmNodes.drop 3)
      { rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] } 30200
      (fun t => fw_linear (t 30100) (t 30300)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 0 30100 30300 30200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100 = (segment_000000_pmFinal pmStore) 30100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] } :: (segment_000000_pmNodes.drop 3)) 30100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30300 = (segment_000000_pmFinal pmStore) 30300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 0, op := "OpName.FW_linear", ins := [30100, 30300], outs := [30200] } :: (segment_000000_pmNodes.drop 3)) 30300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 30200 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30300) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30300) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30300) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_pmWriter1 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 30201 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30301) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 7) ++ [{ rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] }] ++ (segment_000000_pmNodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 30201 = fw_linear (((segment_000000_pmNodes.take 7)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 7)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30301) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 7) (segment_000000_pmNodes.drop 8)
      { rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] } 30201
      (fun t => fw_linear (t 30100) (t 30301)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 1 30100 30301 30201
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 7)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100 = (segment_000000_pmFinal pmStore) 30100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 7) ({ rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] } :: (segment_000000_pmNodes.drop 8)) 30100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 7)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30301 = (segment_000000_pmFinal pmStore) 30301 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 7) ({ rank := 1, op := "OpName.FW_linear", ins := [30100, 30301], outs := [30201] } :: (segment_000000_pmNodes.drop 8)) 30301
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 30201 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30301) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 7)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 7)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30301) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30301) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_pmWriter2 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 30202 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30302) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 12) ++ [{ rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] }] ++ (segment_000000_pmNodes.drop 13) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 30202 = fw_linear (((segment_000000_pmNodes.take 12)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 12)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30302) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 12) (segment_000000_pmNodes.drop 13)
      { rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] } 30202
      (fun t => fw_linear (t 30100) (t 30302)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 2 30100 30302 30202
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 12)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100 = (segment_000000_pmFinal pmStore) 30100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 12) ({ rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] } :: (segment_000000_pmNodes.drop 13)) 30100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 12)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30302 = (segment_000000_pmFinal pmStore) 30302 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 12) ({ rank := 2, op := "OpName.FW_linear", ins := [30100, 30302], outs := [30202] } :: (segment_000000_pmNodes.drop 13)) 30302
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 30202 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30302) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 12)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 12)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30302) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30302) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_pmWriter3 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 30203 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30303) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 17) ++ [{ rank := 3, op := "OpName.FW_linear", ins := [30100, 30303], outs := [30203] }] ++ (segment_000000_pmNodes.drop 18) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 30203 = fw_linear (((segment_000000_pmNodes.take 17)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 17)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30303) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 17) (segment_000000_pmNodes.drop 18)
      { rank := 3, op := "OpName.FW_linear", ins := [30100, 30303], outs := [30203] } 30203
      (fun t => fw_linear (t 30100) (t 30303)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 3 30100 30303 30203
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 17)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100 = (segment_000000_pmFinal pmStore) 30100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 17) ({ rank := 3, op := "OpName.FW_linear", ins := [30100, 30303], outs := [30203] } :: (segment_000000_pmNodes.drop 18)) 30100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 17)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30303 = (segment_000000_pmFinal pmStore) 30303 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 17) ({ rank := 3, op := "OpName.FW_linear", ins := [30100, 30303], outs := [30203] } :: (segment_000000_pmNodes.drop 18)) 30303
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 30203 = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30303) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 17)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30100) (((segment_000000_pmNodes.take 17)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 30303) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 30100) ((segment_000000_pmFinal pmStore) 30303) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_out (smStore pmStore : Store)
    (hActivation : x2.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore))
    (hWeight : w2.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)) :
    y2.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  change (segment_000000_smFinal smStore) 30000 = (segment_000000_pmFinal pmStore) 30100 ∧
    ((segment_000000_smFinal smStore) 30000).shape = [2, 5, 7] ∧
    ((segment_000000_pmFinal pmStore) 30100).shape = [2, 5, 7] at hActivation
  change ShardedRel ((segment_000000_smFinal smStore) 30002) [(segment_000000_pmFinal pmStore) 30300, (segment_000000_pmFinal pmStore) 30301, (segment_000000_pmFinal pmStore) 30302, (segment_000000_pmFinal pmStore) 30303] 0 [12, 7] [3, 7] at hWeight
  have hSm := segment_000000_t0_smWriter smStore
  have hPm0 := segment_000000_t0_pmWriter0 pmStore
  have hPm1 := segment_000000_t0_pmWriter1 pmStore
  have hPm2 := segment_000000_t0_pmWriter2 pmStore
  have hPm3 := segment_000000_t0_pmWriter3 pmStore
  have hComm := (TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm
    (K := [(segment_000000_pmFinal pmStore) 30300, (segment_000000_pmFinal pmStore) 30301, (segment_000000_pmFinal pmStore) 30302, (segment_000000_pmFinal pmStore) 30303].length) (b := 2) (s := 5) (i := 7) (o := 3)
    (x := (segment_000000_pmFinal pmStore) 30100) (ws := [(segment_000000_pmFinal pmStore) 30300, (segment_000000_pmFinal pmStore) 30301, (segment_000000_pmFinal pmStore) 30302, (segment_000000_pmFinal pmStore) 30303])
    (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by simp) hActivation.2.2 (fun w hw => hWeight.shard_shapes w hw))
  have hValue : (segment_000000_smFinal smStore) 30001 = allGatherPrimDimN 2 [(segment_000000_pmFinal pmStore) 30200, (segment_000000_pmFinal pmStore) 30201, (segment_000000_pmFinal pmStore) 30202, (segment_000000_pmFinal pmStore) 30203].length 0 [(segment_000000_pmFinal pmStore) 30200, (segment_000000_pmFinal pmStore) 30201, (segment_000000_pmFinal pmStore) 30202, (segment_000000_pmFinal pmStore) 30203] := by
    rw [hSm, hActivation.1, hWeight.full_value, hComm]
    simp only [List.map, List.length_cons, List.length_nil]
    rw [← hPm0, ← hPm1, ← hPm2, ← hPm3]
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
  have hOutShape3 : ((segment_000000_pmFinal pmStore) 30203).shape = [2, 5, 3] := by
    rw [hPm3]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 30303) (by simp))
  unfold y2 RelationFact.Holds
  change ShardedRel ((segment_000000_smFinal smStore) 30001) [(segment_000000_pmFinal pmStore) 30200, (segment_000000_pmFinal pmStore) 30201, (segment_000000_pmFinal pmStore) 30202, (segment_000000_pmFinal pmStore) 30203] 2 [2, 5, 12] [2, 5, 3]
  refine {
    full_value := hValue
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by native_decide
    shard_shapes := ?_
    shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
  }
  · rw [hValue]
    rw [allGatherPrimDimN_shape 2 [(segment_000000_pmFinal pmStore) 30200, (segment_000000_pmFinal pmStore) 30201, (segment_000000_pmFinal pmStore) 30202, (segment_000000_pmFinal pmStore) 30203].length [(segment_000000_pmFinal pmStore) 30200, (segment_000000_pmFinal pmStore) 30201, (segment_000000_pmFinal pmStore) 30202, (segment_000000_pmFinal pmStore) 30203] [2, 5, 3]]
    · simp only [List.length_cons, List.length_nil]
      native_decide
    · simp only [List.head?, Option.map, Option.getD]
      exact hOutShape0
  · intro shard hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact hOutShape0
    · exact hOutShape1
    · exact hOutShape2
    · exact hOutShape3

private theorem segment_000000_t1_smWriter (smStore : Store) :
    (segment_000000_smFinal smStore) 40001 = fw_linear ((segment_000000_smFinal smStore) 40000) ((segment_000000_smFinal smStore) 40002) := by
  have hfinal : (segment_000000_smFinal smStore) = segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore := by
    unfold segment_000000_smFinal
    rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 1) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [40000, 40002], outs := [40001] }] ++ (segment_000000_smNodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 40001 = fw_linear (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 40000) (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 40002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 1) (segment_000000_smNodes.drop 2)
      { rank := 0, op := "OpName.FW_linear", ins := [40000, 40002], outs := [40001] } 40001
      (fun t => fw_linear (t 40000) (t 40002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.sm t 0 40000 40002 40001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 40000 = (segment_000000_smFinal smStore) 40000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 1) ({ rank := 0, op := "OpName.FW_linear", ins := [40000, 40002], outs := [40001] } :: (segment_000000_smNodes.drop 2)) 40000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 40002 = (segment_000000_smFinal smStore) 40002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 1) ({ rank := 0, op := "OpName.FW_linear", ins := [40000, 40002], outs := [40001] } :: (segment_000000_smNodes.drop 2)) 40002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 40001 = fw_linear ((segment_000000_smFinal smStore) 40000) ((segment_000000_smFinal smStore) 40002) := by
    calc
      _ = fw_linear (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 40000) (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 40002) := hout_prefix
      _ = fw_linear ((segment_000000_smFinal smStore) 40000) ((segment_000000_smFinal smStore) 40002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t1_pmWriter0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 40200 = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40300) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 3) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [40100, 40300], outs := [40200] }] ++ (segment_000000_pmNodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 40200 = fw_linear (((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100) (((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40300) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 3) (segment_000000_pmNodes.drop 4)
      { rank := 0, op := "OpName.FW_linear", ins := [40100, 40300], outs := [40200] } 40200
      (fun t => fw_linear (t 40100) (t 40300)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 0 40100 40300 40200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100 = (segment_000000_pmFinal pmStore) 40100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 3) ({ rank := 0, op := "OpName.FW_linear", ins := [40100, 40300], outs := [40200] } :: (segment_000000_pmNodes.drop 4)) 40100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40300 = (segment_000000_pmFinal pmStore) 40300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 3) ({ rank := 0, op := "OpName.FW_linear", ins := [40100, 40300], outs := [40200] } :: (segment_000000_pmNodes.drop 4)) 40300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 40200 = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40300) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100) (((segment_000000_pmNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40300) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40300) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t1_pmWriter1 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 40201 = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40301) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 8) ++ [{ rank := 1, op := "OpName.FW_linear", ins := [40100, 40301], outs := [40201] }] ++ (segment_000000_pmNodes.drop 9) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 40201 = fw_linear (((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100) (((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40301) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 8) (segment_000000_pmNodes.drop 9)
      { rank := 1, op := "OpName.FW_linear", ins := [40100, 40301], outs := [40201] } 40201
      (fun t => fw_linear (t 40100) (t 40301)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 1 40100 40301 40201
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100 = (segment_000000_pmFinal pmStore) 40100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 8) ({ rank := 1, op := "OpName.FW_linear", ins := [40100, 40301], outs := [40201] } :: (segment_000000_pmNodes.drop 9)) 40100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40301 = (segment_000000_pmFinal pmStore) 40301 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 8) ({ rank := 1, op := "OpName.FW_linear", ins := [40100, 40301], outs := [40201] } :: (segment_000000_pmNodes.drop 9)) 40301
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 40201 = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40301) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100) (((segment_000000_pmNodes.take 8)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40301) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40301) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t1_pmWriter2 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 40202 = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40302) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 13) ++ [{ rank := 2, op := "OpName.FW_linear", ins := [40100, 40302], outs := [40202] }] ++ (segment_000000_pmNodes.drop 14) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 40202 = fw_linear (((segment_000000_pmNodes.take 13)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100) (((segment_000000_pmNodes.take 13)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40302) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 13) (segment_000000_pmNodes.drop 14)
      { rank := 2, op := "OpName.FW_linear", ins := [40100, 40302], outs := [40202] } 40202
      (fun t => fw_linear (t 40100) (t 40302)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 2 40100 40302 40202
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 13)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100 = (segment_000000_pmFinal pmStore) 40100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 13) ({ rank := 2, op := "OpName.FW_linear", ins := [40100, 40302], outs := [40202] } :: (segment_000000_pmNodes.drop 14)) 40100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 13)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40302 = (segment_000000_pmFinal pmStore) 40302 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 13) ({ rank := 2, op := "OpName.FW_linear", ins := [40100, 40302], outs := [40202] } :: (segment_000000_pmNodes.drop 14)) 40302
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 40202 = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40302) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 13)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100) (((segment_000000_pmNodes.take 13)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40302) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40302) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t1_pmWriter3 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 40203 = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40303) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 18) ++ [{ rank := 3, op := "OpName.FW_linear", ins := [40100, 40303], outs := [40203] }] ++ (segment_000000_pmNodes.drop 19) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 40203 = fw_linear (((segment_000000_pmNodes.take 18)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100) (((segment_000000_pmNodes.take 18)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40303) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 18) (segment_000000_pmNodes.drop 19)
      { rank := 3, op := "OpName.FW_linear", ins := [40100, 40303], outs := [40203] } 40203
      (fun t => fw_linear (t 40100) (t 40303)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 3 40100 40303 40203
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 18)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100 = (segment_000000_pmFinal pmStore) 40100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 18) ({ rank := 3, op := "OpName.FW_linear", ins := [40100, 40303], outs := [40203] } :: (segment_000000_pmNodes.drop 19)) 40100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 18)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40303 = (segment_000000_pmFinal pmStore) 40303 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 18) ({ rank := 3, op := "OpName.FW_linear", ins := [40100, 40303], outs := [40203] } :: (segment_000000_pmNodes.drop 19)) 40303
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 40203 = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40303) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 18)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40100) (((segment_000000_pmNodes.take 18)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 40303) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 40100) ((segment_000000_pmFinal pmStore) 40303) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t1_out (smStore pmStore : Store)
    (hActivation : x3.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore))
    (hWeight : w3.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)) :
    y3.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  change (segment_000000_smFinal smStore) 40000 = (segment_000000_pmFinal pmStore) 40100 ∧
    ((segment_000000_smFinal smStore) 40000).shape = [2, 5, 7] ∧
    ((segment_000000_pmFinal pmStore) 40100).shape = [2, 5, 7] at hActivation
  change ShardedRel ((segment_000000_smFinal smStore) 40002) [(segment_000000_pmFinal pmStore) 40300, (segment_000000_pmFinal pmStore) 40301, (segment_000000_pmFinal pmStore) 40302, (segment_000000_pmFinal pmStore) 40303] 0 [12, 7] [3, 7] at hWeight
  have hSm := segment_000000_t1_smWriter smStore
  have hPm0 := segment_000000_t1_pmWriter0 pmStore
  have hPm1 := segment_000000_t1_pmWriter1 pmStore
  have hPm2 := segment_000000_t1_pmWriter2 pmStore
  have hPm3 := segment_000000_t1_pmWriter3 pmStore
  have hComm := (TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm
    (K := [(segment_000000_pmFinal pmStore) 40300, (segment_000000_pmFinal pmStore) 40301, (segment_000000_pmFinal pmStore) 40302, (segment_000000_pmFinal pmStore) 40303].length) (b := 2) (s := 5) (i := 7) (o := 3)
    (x := (segment_000000_pmFinal pmStore) 40100) (ws := [(segment_000000_pmFinal pmStore) 40300, (segment_000000_pmFinal pmStore) 40301, (segment_000000_pmFinal pmStore) 40302, (segment_000000_pmFinal pmStore) 40303])
    (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by simp) hActivation.2.2 (fun w hw => hWeight.shard_shapes w hw))
  have hValue : (segment_000000_smFinal smStore) 40001 = allGatherPrimDimN 2 [(segment_000000_pmFinal pmStore) 40200, (segment_000000_pmFinal pmStore) 40201, (segment_000000_pmFinal pmStore) 40202, (segment_000000_pmFinal pmStore) 40203].length 0 [(segment_000000_pmFinal pmStore) 40200, (segment_000000_pmFinal pmStore) 40201, (segment_000000_pmFinal pmStore) 40202, (segment_000000_pmFinal pmStore) 40203] := by
    rw [hSm, hActivation.1, hWeight.full_value, hComm]
    simp only [List.map, List.length_cons, List.length_nil]
    rw [← hPm0, ← hPm1, ← hPm2, ← hPm3]
  have hOutShape0 : ((segment_000000_pmFinal pmStore) 40200).shape = [2, 5, 3] := by
    rw [hPm0]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 40300) (by simp))
  have hOutShape1 : ((segment_000000_pmFinal pmStore) 40201).shape = [2, 5, 3] := by
    rw [hPm1]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 40301) (by simp))
  have hOutShape2 : ((segment_000000_pmFinal pmStore) 40202).shape = [2, 5, 3] := by
    rw [hPm2]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 40302) (by simp))
  have hOutShape3 : ((segment_000000_pmFinal pmStore) 40203).shape = [2, 5, 3] := by
    rw [hPm3]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 40303) (by simp))
  unfold y3 RelationFact.Holds
  change ShardedRel ((segment_000000_smFinal smStore) 40001) [(segment_000000_pmFinal pmStore) 40200, (segment_000000_pmFinal pmStore) 40201, (segment_000000_pmFinal pmStore) 40202, (segment_000000_pmFinal pmStore) 40203] 2 [2, 5, 12] [2, 5, 3]
  refine {
    full_value := hValue
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by native_decide
    shard_shapes := ?_
    shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
  }
  · rw [hValue]
    rw [allGatherPrimDimN_shape 2 [(segment_000000_pmFinal pmStore) 40200, (segment_000000_pmFinal pmStore) 40201, (segment_000000_pmFinal pmStore) 40202, (segment_000000_pmFinal pmStore) 40203].length [(segment_000000_pmFinal pmStore) 40200, (segment_000000_pmFinal pmStore) 40201, (segment_000000_pmFinal pmStore) 40202, (segment_000000_pmFinal pmStore) 40203] [2, 5, 3]]
    · simp only [List.length_cons, List.length_nil]
      native_decide
    · simp only [List.head?, Option.map, Option.getD]
      exact hOutShape0
  · intro shard hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact hOutShape0
    · exact hOutShape1
    · exact hOutShape2
    · exact hOutShape3

private theorem segment_000000_t2_smWriter (smStore : Store) :
    (segment_000000_smFinal smStore) 50001 = fw_linear ((segment_000000_smFinal smStore) 50000) ((segment_000000_smFinal smStore) 50002) := by
  have hfinal : (segment_000000_smFinal smStore) = segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore := by
    unfold segment_000000_smFinal
    rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 2) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [50000, 50002], outs := [50001] }] ++ (segment_000000_smNodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 50001 = fw_linear (((segment_000000_smNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 50000) (((segment_000000_smNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 50002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 2) (segment_000000_smNodes.drop 3)
      { rank := 0, op := "OpName.FW_linear", ins := [50000, 50002], outs := [50001] } 50001
      (fun t => fw_linear (t 50000) (t 50002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.sm t 0 50000 50002 50001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 50000 = (segment_000000_smFinal smStore) 50000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 2) ({ rank := 0, op := "OpName.FW_linear", ins := [50000, 50002], outs := [50001] } :: (segment_000000_smNodes.drop 3)) 50000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_smNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 50002 = (segment_000000_smFinal smStore) 50002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 2) ({ rank := 0, op := "OpName.FW_linear", ins := [50000, 50002], outs := [50001] } :: (segment_000000_smNodes.drop 3)) 50002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 50001 = fw_linear ((segment_000000_smFinal smStore) 50000) ((segment_000000_smFinal smStore) 50002) := by
    calc
      _ = fw_linear (((segment_000000_smNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 50000) (((segment_000000_smNodes.take 2)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 50002) := hout_prefix
      _ = fw_linear ((segment_000000_smFinal smStore) 50000) ((segment_000000_smFinal smStore) 50002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t2_pmWriter0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 50200 = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50300) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 4) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [50100, 50300], outs := [50200] }] ++ (segment_000000_pmNodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 50200 = fw_linear (((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100) (((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50300) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 4) (segment_000000_pmNodes.drop 5)
      { rank := 0, op := "OpName.FW_linear", ins := [50100, 50300], outs := [50200] } 50200
      (fun t => fw_linear (t 50100) (t 50300)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 0 50100 50300 50200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100 = (segment_000000_pmFinal pmStore) 50100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 4) ({ rank := 0, op := "OpName.FW_linear", ins := [50100, 50300], outs := [50200] } :: (segment_000000_pmNodes.drop 5)) 50100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50300 = (segment_000000_pmFinal pmStore) 50300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 4) ({ rank := 0, op := "OpName.FW_linear", ins := [50100, 50300], outs := [50200] } :: (segment_000000_pmNodes.drop 5)) 50300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 50200 = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50300) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100) (((segment_000000_pmNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50300) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50300) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t2_pmWriter1 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 50201 = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50301) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 9) ++ [{ rank := 1, op := "OpName.FW_linear", ins := [50100, 50301], outs := [50201] }] ++ (segment_000000_pmNodes.drop 10) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 50201 = fw_linear (((segment_000000_pmNodes.take 9)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100) (((segment_000000_pmNodes.take 9)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50301) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 9) (segment_000000_pmNodes.drop 10)
      { rank := 1, op := "OpName.FW_linear", ins := [50100, 50301], outs := [50201] } 50201
      (fun t => fw_linear (t 50100) (t 50301)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 1 50100 50301 50201
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 9)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100 = (segment_000000_pmFinal pmStore) 50100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 9) ({ rank := 1, op := "OpName.FW_linear", ins := [50100, 50301], outs := [50201] } :: (segment_000000_pmNodes.drop 10)) 50100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 9)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50301 = (segment_000000_pmFinal pmStore) 50301 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 9) ({ rank := 1, op := "OpName.FW_linear", ins := [50100, 50301], outs := [50201] } :: (segment_000000_pmNodes.drop 10)) 50301
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 50201 = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50301) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 9)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100) (((segment_000000_pmNodes.take 9)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50301) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50301) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t2_pmWriter2 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 50202 = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50302) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 14) ++ [{ rank := 2, op := "OpName.FW_linear", ins := [50100, 50302], outs := [50202] }] ++ (segment_000000_pmNodes.drop 15) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 50202 = fw_linear (((segment_000000_pmNodes.take 14)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100) (((segment_000000_pmNodes.take 14)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50302) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 14) (segment_000000_pmNodes.drop 15)
      { rank := 2, op := "OpName.FW_linear", ins := [50100, 50302], outs := [50202] } 50202
      (fun t => fw_linear (t 50100) (t 50302)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 2 50100 50302 50202
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 14)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100 = (segment_000000_pmFinal pmStore) 50100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 14) ({ rank := 2, op := "OpName.FW_linear", ins := [50100, 50302], outs := [50202] } :: (segment_000000_pmNodes.drop 15)) 50100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 14)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50302 = (segment_000000_pmFinal pmStore) 50302 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 14) ({ rank := 2, op := "OpName.FW_linear", ins := [50100, 50302], outs := [50202] } :: (segment_000000_pmNodes.drop 15)) 50302
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 50202 = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50302) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 14)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100) (((segment_000000_pmNodes.take 14)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50302) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50302) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t2_pmWriter3 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 50203 = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50303) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 19) ++ [{ rank := 3, op := "OpName.FW_linear", ins := [50100, 50303], outs := [50203] }] ++ (segment_000000_pmNodes.drop 20) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 50203 = fw_linear (((segment_000000_pmNodes.take 19)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100) (((segment_000000_pmNodes.take 19)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50303) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 19) (segment_000000_pmNodes.drop 20)
      { rank := 3, op := "OpName.FW_linear", ins := [50100, 50303], outs := [50203] } 50203
      (fun t => fw_linear (t 50100) (t 50303)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK4N2M3Graph.pm t 3 50100 50303 50203
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 19)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100 = (segment_000000_pmFinal pmStore) 50100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 19) ({ rank := 3, op := "OpName.FW_linear", ins := [50100, 50303], outs := [50203] } :: (segment_000000_pmNodes.drop 20)) 50100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 19)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50303 = (segment_000000_pmFinal pmStore) 50303 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 19) ({ rank := 3, op := "OpName.FW_linear", ins := [50100, 50303], outs := [50203] } :: (segment_000000_pmNodes.drop 20)) 50303
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 50203 = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50303) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 19)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50100) (((segment_000000_pmNodes.take 19)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 50303) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 50100) ((segment_000000_pmFinal pmStore) 50303) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t2_out (smStore pmStore : Store)
    (hActivation : x4.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore))
    (hWeight : w4.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)) :
    y4.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  change (segment_000000_smFinal smStore) 50000 = (segment_000000_pmFinal pmStore) 50100 ∧
    ((segment_000000_smFinal smStore) 50000).shape = [2, 5, 7] ∧
    ((segment_000000_pmFinal pmStore) 50100).shape = [2, 5, 7] at hActivation
  change ShardedRel ((segment_000000_smFinal smStore) 50002) [(segment_000000_pmFinal pmStore) 50300, (segment_000000_pmFinal pmStore) 50301, (segment_000000_pmFinal pmStore) 50302, (segment_000000_pmFinal pmStore) 50303] 0 [12, 7] [3, 7] at hWeight
  have hSm := segment_000000_t2_smWriter smStore
  have hPm0 := segment_000000_t2_pmWriter0 pmStore
  have hPm1 := segment_000000_t2_pmWriter1 pmStore
  have hPm2 := segment_000000_t2_pmWriter2 pmStore
  have hPm3 := segment_000000_t2_pmWriter3 pmStore
  have hComm := (TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm
    (K := [(segment_000000_pmFinal pmStore) 50300, (segment_000000_pmFinal pmStore) 50301, (segment_000000_pmFinal pmStore) 50302, (segment_000000_pmFinal pmStore) 50303].length) (b := 2) (s := 5) (i := 7) (o := 3)
    (x := (segment_000000_pmFinal pmStore) 50100) (ws := [(segment_000000_pmFinal pmStore) 50300, (segment_000000_pmFinal pmStore) 50301, (segment_000000_pmFinal pmStore) 50302, (segment_000000_pmFinal pmStore) 50303])
    (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by simp) hActivation.2.2 (fun w hw => hWeight.shard_shapes w hw))
  have hValue : (segment_000000_smFinal smStore) 50001 = allGatherPrimDimN 2 [(segment_000000_pmFinal pmStore) 50200, (segment_000000_pmFinal pmStore) 50201, (segment_000000_pmFinal pmStore) 50202, (segment_000000_pmFinal pmStore) 50203].length 0 [(segment_000000_pmFinal pmStore) 50200, (segment_000000_pmFinal pmStore) 50201, (segment_000000_pmFinal pmStore) 50202, (segment_000000_pmFinal pmStore) 50203] := by
    rw [hSm, hActivation.1, hWeight.full_value, hComm]
    simp only [List.map, List.length_cons, List.length_nil]
    rw [← hPm0, ← hPm1, ← hPm2, ← hPm3]
  have hOutShape0 : ((segment_000000_pmFinal pmStore) 50200).shape = [2, 5, 3] := by
    rw [hPm0]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 50300) (by simp))
  have hOutShape1 : ((segment_000000_pmFinal pmStore) 50201).shape = [2, 5, 3] := by
    rw [hPm1]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 50301) (by simp))
  have hOutShape2 : ((segment_000000_pmFinal pmStore) 50202).shape = [2, 5, 3] := by
    rw [hPm2]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 50302) (by simp))
  have hOutShape3 : ((segment_000000_pmFinal pmStore) 50203).shape = [2, 5, 3] := by
    rw [hPm3]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 50303) (by simp))
  unfold y4 RelationFact.Holds
  change ShardedRel ((segment_000000_smFinal smStore) 50001) [(segment_000000_pmFinal pmStore) 50200, (segment_000000_pmFinal pmStore) 50201, (segment_000000_pmFinal pmStore) 50202, (segment_000000_pmFinal pmStore) 50203] 2 [2, 5, 12] [2, 5, 3]
  refine {
    full_value := hValue
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by native_decide
    shard_shapes := ?_
    shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
  }
  · rw [hValue]
    rw [allGatherPrimDimN_shape 2 [(segment_000000_pmFinal pmStore) 50200, (segment_000000_pmFinal pmStore) 50201, (segment_000000_pmFinal pmStore) 50202, (segment_000000_pmFinal pmStore) 50203].length [(segment_000000_pmFinal pmStore) 50200, (segment_000000_pmFinal pmStore) 50201, (segment_000000_pmFinal pmStore) 50202, (segment_000000_pmFinal pmStore) 50203] [2, 5, 3]]
    · simp only [List.length_cons, List.length_nil]
      native_decide
    · simp only [List.head?, Option.map, Option.getD]
      exact hOutShape0
  · intro shard hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact hOutShape0
    · exact hOutShape1
    · exact hOutShape2
    · exact hOutShape3

private theorem segment_000000_t3_hSmWriter(smStore:Store):(segment_000000_smFinal smStore) 10001=fw_view [2, 20, 3, 7] ((segment_000000_smFinal smStore) 10000):=by
  have hfinal:(segment_000000_smFinal smStore)=segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore:=by unfold segment_000000_smFinal;rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 3) ++ [{ rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 20, 3, 7] }] ++ (segment_000000_smNodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 10001 = fw_view [2, 20, 3, 7] (((segment_000000_smNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 10000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 3) (segment_000000_smNodes.drop 4)
      { rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 20, 3, 7] } 10001
      (fun t => fw_view [2, 20, 3, 7] (t 10000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK4N2M3Graph.sm t 0 2 [20, 3, 7] 10000 10001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 10000 = (segment_000000_smFinal smStore) 10000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 3) ({ rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 20, 3, 7] } :: (segment_000000_smNodes.drop 4)) 10000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 10001 = fw_view [2, 20, 3, 7] ((segment_000000_smFinal smStore) 10000) := by
    calc
      _ = fw_view [2, 20, 3, 7] (((segment_000000_smNodes.take 3)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 10000) := hout_prefix
      _ = fw_view [2, 20, 3, 7] ((segment_000000_smFinal smStore) 10000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t3_hPmWriter0(pmStore:Store):(segment_000000_pmFinal pmStore) 10200=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10100):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 10200 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 0) (segment_000000_pmNodes.drop 1)
      { rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] } 10200
      (fun t => fw_view [2, 5, 3, 7] (t 10100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK4N2M3Graph.pm t 0 2 [5, 3, 7] 10100 10200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10100 = (segment_000000_pmFinal pmStore) 10100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 1)) 10100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 10200 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10100) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10100) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t3_hPmWriter1(pmStore:Store):(segment_000000_pmFinal pmStore) 10201=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10101):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 5) ++ [{ rank := 1, op := "OpName.FW_view", ins := [10101], outs := [10201], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 10201 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10101) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 5) (segment_000000_pmNodes.drop 6)
      { rank := 1, op := "OpName.FW_view", ins := [10101], outs := [10201], params := [2, 5, 3, 7] } 10201
      (fun t => fw_view [2, 5, 3, 7] (t 10101)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK4N2M3Graph.pm t 1 2 [5, 3, 7] 10101 10201
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10101 = (segment_000000_pmFinal pmStore) 10101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 5) ({ rank := 1, op := "OpName.FW_view", ins := [10101], outs := [10201], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 6)) 10101
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 10201 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10101) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 5)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10101) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10101) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t3_hPmWriter2(pmStore:Store):(segment_000000_pmFinal pmStore) 10202=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10102):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 10) ++ [{ rank := 2, op := "OpName.FW_view", ins := [10102], outs := [10202], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 11) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 10202 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 10)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10102) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 10) (segment_000000_pmNodes.drop 11)
      { rank := 2, op := "OpName.FW_view", ins := [10102], outs := [10202], params := [2, 5, 3, 7] } 10202
      (fun t => fw_view [2, 5, 3, 7] (t 10102)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK4N2M3Graph.pm t 2 2 [5, 3, 7] 10102 10202
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 10)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10102 = (segment_000000_pmFinal pmStore) 10102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 10) ({ rank := 2, op := "OpName.FW_view", ins := [10102], outs := [10202], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 11)) 10102
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 10202 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10102) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 10)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10102) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10102) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t3_hPmWriter3(pmStore:Store):(segment_000000_pmFinal pmStore) 10203=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10103):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 15) ++ [{ rank := 3, op := "OpName.FW_view", ins := [10103], outs := [10203], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 16) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 10203 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 15)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10103) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 15) (segment_000000_pmNodes.drop 16)
      { rank := 3, op := "OpName.FW_view", ins := [10103], outs := [10203], params := [2, 5, 3, 7] } 10203
      (fun t => fw_view [2, 5, 3, 7] (t 10103)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK4N2M3Graph.pm t 3 2 [5, 3, 7] 10103 10203
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 15)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10103 = (segment_000000_pmFinal pmStore) 10103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 15) ({ rank := 3, op := "OpName.FW_view", ins := [10103], outs := [10203], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 16)) 10103
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 10203 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10103) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 15)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 10103) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10103) := by rw [hout_read_0]
  exact hout
set_option maxHeartbeats 500000 in
private theorem segment_000000_t3_out(smStore pmStore:Store)(hframe:state_before.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)):
    y0.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore):=by
    let smFinal:=segment_000000_smFinal smStore
    let pmFinal:=segment_000000_pmFinal pmStore
    have hx:x0.Holds smFinal pmFinal:=hframe _ (by native_decide)
    change ShardedRel (smFinal 10000) [pmFinal 10100, pmFinal 10101, pmFinal 10102, pmFinal 10103] 1 [2, 20, 21] [2, 5, 21] at hx
    have hxV:smFinal 10000=allGatherPrimDimN 1 4 0 [pmFinal 10100, pmFinal 10101, pmFinal 10102, pmFinal 10103]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 10001=fw_view [2, 20, 3, 7] (smFinal 10000):=segment_000000_t3_hSmWriter smStore
    have hPm0:pmFinal 10200=fw_view [2, 5, 3, 7] (pmFinal 10100):=segment_000000_t3_hPmWriter0 pmStore
    have hPm1:pmFinal 10201=fw_view [2, 5, 3, 7] (pmFinal 10101):=segment_000000_t3_hPmWriter1 pmStore
    have hPm2:pmFinal 10202=fw_view [2, 5, 3, 7] (pmFinal 10102):=segment_000000_t3_hPmWriter2 pmStore
    have hPm3:pmFinal 10203=fw_view [2, 5, 3, 7] (pmFinal 10103):=segment_000000_t3_hPmWriter3 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_unflatten_allGather_dim1_rank3 4 2 5 3 7 [pmFinal 10100, pmFinal 10101, pmFinal 10102, pmFinal 10103]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 10001=allGatherPrimDimN 1 4 0 [pmFinal 10200, pmFinal 10201, pmFinal 10202, pmFinal 10203]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1, ← hPm2, ← hPm3]
    have hout:y0.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 10001) [pmFinal 10200, pmFinal 10201, pmFinal 10202, pmFinal 10203] 1 [2, 20, 3, 7] [2, 5, 3, 7]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0 | h1 | h2 | h3
        · subst piece; rw [hPm0]; rfl
        · subst piece; rw [hPm1]; rfl
        · subst piece; rw [hPm2]; rfl
        · subst piece; rw [hPm3]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    exact hout
private theorem segment_000000_t4_hSmWriter(smStore:Store):(segment_000000_smFinal smStore) 20001=fw_view [2, 20, 3, 7] ((segment_000000_smFinal smStore) 20000):=by
  have hfinal:(segment_000000_smFinal smStore)=segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore:=by unfold segment_000000_smFinal;rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 4) ++ [{ rank := 0, op := "OpName.FW_view", ins := [20000], outs := [20001], params := [2, 20, 3, 7] }] ++ (segment_000000_smNodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 20001 = fw_view [2, 20, 3, 7] (((segment_000000_smNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 20000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 4) (segment_000000_smNodes.drop 5)
      { rank := 0, op := "OpName.FW_view", ins := [20000], outs := [20001], params := [2, 20, 3, 7] } 20001
      (fun t => fw_view [2, 20, 3, 7] (t 20000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK4N2M3Graph.sm t 0 2 [20, 3, 7] 20000 20001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 20000 = (segment_000000_smFinal smStore) 20000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.sm smStore
      (segment_000000_smNodes.take 4) ({ rank := 0, op := "OpName.FW_view", ins := [20000], outs := [20001], params := [2, 20, 3, 7] } :: (segment_000000_smNodes.drop 5)) 20000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 20001 = fw_view [2, 20, 3, 7] ((segment_000000_smFinal smStore) 20000) := by
    calc
      _ = fw_view [2, 20, 3, 7] (((segment_000000_smNodes.take 4)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.sm) smStore 20000) := hout_prefix
      _ = fw_view [2, 20, 3, 7] ((segment_000000_smFinal smStore) 20000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t4_hPmWriter0(pmStore:Store):(segment_000000_pmFinal pmStore) 20200=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20100):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 1) ++ [{ rank := 0, op := "OpName.FW_view", ins := [20100], outs := [20200], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 20200 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 1) (segment_000000_pmNodes.drop 2)
      { rank := 0, op := "OpName.FW_view", ins := [20100], outs := [20200], params := [2, 5, 3, 7] } 20200
      (fun t => fw_view [2, 5, 3, 7] (t 20100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK4N2M3Graph.pm t 0 2 [5, 3, 7] 20100 20200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20100 = (segment_000000_pmFinal pmStore) 20100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 0, op := "OpName.FW_view", ins := [20100], outs := [20200], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 2)) 20100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 20200 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20100) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20100) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t4_hPmWriter1(pmStore:Store):(segment_000000_pmFinal pmStore) 20201=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20101):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 6) ++ [{ rank := 1, op := "OpName.FW_view", ins := [20101], outs := [20201], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 20201 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 6)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20101) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 6) (segment_000000_pmNodes.drop 7)
      { rank := 1, op := "OpName.FW_view", ins := [20101], outs := [20201], params := [2, 5, 3, 7] } 20201
      (fun t => fw_view [2, 5, 3, 7] (t 20101)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK4N2M3Graph.pm t 1 2 [5, 3, 7] 20101 20201
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 6)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20101 = (segment_000000_pmFinal pmStore) 20101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 6) ({ rank := 1, op := "OpName.FW_view", ins := [20101], outs := [20201], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 7)) 20101
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 20201 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20101) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 6)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20101) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20101) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t4_hPmWriter2(pmStore:Store):(segment_000000_pmFinal pmStore) 20202=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20102):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 11) ++ [{ rank := 2, op := "OpName.FW_view", ins := [20102], outs := [20202], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 12) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 20202 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 11)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20102) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 11) (segment_000000_pmNodes.drop 12)
      { rank := 2, op := "OpName.FW_view", ins := [20102], outs := [20202], params := [2, 5, 3, 7] } 20202
      (fun t => fw_view [2, 5, 3, 7] (t 20102)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK4N2M3Graph.pm t 2 2 [5, 3, 7] 20102 20202
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 11)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20102 = (segment_000000_pmFinal pmStore) 20102 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 11) ({ rank := 2, op := "OpName.FW_view", ins := [20102], outs := [20202], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 12)) 20102
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 20202 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20102) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 11)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20102) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20102) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t4_hPmWriter3(pmStore:Store):(segment_000000_pmFinal pmStore) 20203=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20103):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 16) ++ [{ rank := 3, op := "OpName.FW_view", ins := [20103], outs := [20203], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 17) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 20203 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 16)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20103) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 16) (segment_000000_pmNodes.drop 17)
      { rank := 3, op := "OpName.FW_view", ins := [20103], outs := [20203], params := [2, 5, 3, 7] } 20203
      (fun t => fw_view [2, 5, 3, 7] (t 20103)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK4N2M3Graph.pm t 3 2 [5, 3, 7] 20103 20203
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 16)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20103 = (segment_000000_pmFinal pmStore) 20103 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK4N2M3Graph.pm pmStore
      (segment_000000_pmNodes.take 16) ({ rank := 3, op := "OpName.FW_view", ins := [20103], outs := [20203], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 17)) 20103
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 20203 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20103) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 16)).foldl (applyNodeDistributedFaithful UnflattenOutputK4N2M3Graph.pm) pmStore 20103) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 20103) := by rw [hout_read_0]
  exact hout
set_option maxHeartbeats 500000 in
private theorem segment_000000_t4_out(smStore pmStore:Store)(hframe:state_before.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)):
    y1.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore):=by
    let smFinal:=segment_000000_smFinal smStore
    let pmFinal:=segment_000000_pmFinal pmStore
    have hx:x1.Holds smFinal pmFinal:=hframe _ (by native_decide)
    change ShardedRel (smFinal 20000) [pmFinal 20100, pmFinal 20101, pmFinal 20102, pmFinal 20103] 1 [2, 20, 21] [2, 5, 21] at hx
    have hxV:smFinal 20000=allGatherPrimDimN 1 4 0 [pmFinal 20100, pmFinal 20101, pmFinal 20102, pmFinal 20103]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 20001=fw_view [2, 20, 3, 7] (smFinal 20000):=segment_000000_t4_hSmWriter smStore
    have hPm0:pmFinal 20200=fw_view [2, 5, 3, 7] (pmFinal 20100):=segment_000000_t4_hPmWriter0 pmStore
    have hPm1:pmFinal 20201=fw_view [2, 5, 3, 7] (pmFinal 20101):=segment_000000_t4_hPmWriter1 pmStore
    have hPm2:pmFinal 20202=fw_view [2, 5, 3, 7] (pmFinal 20102):=segment_000000_t4_hPmWriter2 pmStore
    have hPm3:pmFinal 20203=fw_view [2, 5, 3, 7] (pmFinal 20103):=segment_000000_t4_hPmWriter3 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_unflatten_allGather_dim1_rank3 4 2 5 3 7 [pmFinal 20100, pmFinal 20101, pmFinal 20102, pmFinal 20103]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 20001=allGatherPrimDimN 1 4 0 [pmFinal 20200, pmFinal 20201, pmFinal 20202, pmFinal 20203]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1, ← hPm2, ← hPm3]
    have hout:y1.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 20001) [pmFinal 20200, pmFinal 20201, pmFinal 20202, pmFinal 20203] 1 [2, 20, 3, 7] [2, 5, 3, 7]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0 | h1 | h2 | h3
        · subst piece; rw [hPm0]; rfl
        · subst piece; rw [hPm1]; rfl
        · subst piece; rw [hPm2]; rfl
        · subst piece; rw [hPm3]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    exact hout
private def segment_000000:ClosedDepSegmentCertificate UnflattenOutputK4N2M3Graph.sm UnflattenOutputK4N2M3Graph.pm state_before state_after where
  smNodes := segment_000000_smNodes
  pmNodes := segment_000000_pmNodes
  sound := by
    intro smStore pmStore hstate
    have hframe : state_before.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
      unfold segment_000000_smFinal segment_000000_pmFinal
      apply RelationState.Holds.fold_frame segment_000000_smNodes segment_000000_pmNodes smStore pmStore hstate <;> native_decide
    have h0 := segment_000000_t0_out smStore pmStore (hframe x2 (by native_decide)) (hframe w2 (by native_decide))
    have h1 := segment_000000_t1_out smStore pmStore (hframe x3 (by native_decide)) (hframe w3 (by native_decide))
    have h2 := segment_000000_t2_out smStore pmStore (hframe x4 (by native_decide)) (hframe w4 (by native_decide))
    have h3 := segment_000000_t3_out smStore pmStore hframe
    have h4 := segment_000000_t4_out smStore pmStore hframe
    have result : state_after.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
      intro fact hfact
      have covered : fact ∈ [y2, y3, y4, y0, y1] ++ state_before.facts :=
        (show state_after.facts ⊆ [y2, y3, y4, y0, y1] ++ state_before.facts by native_decide) hfact
      simp only [List.mem_append] at covered
      rcases covered with fresh | old
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
        rcases fresh with rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h1
        · exact h2
        · exact h3
        · exact h4
      · exact hframe fact old
    simpa only [segment_000000_smFinal, segment_000000_pmFinal] using result

#print axioms segment_000000
end
end TrainVerify.Denote.UnflattenOutputK4N2M3
