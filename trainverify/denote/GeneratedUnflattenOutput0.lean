import denote.RelationCompiler
import denote.KRankViewUnflatten
import denote.KRankLinearGather
set_option maxHeartbeats 500000
open TrainVerify.Denote
namespace UnflattenOutputK1N1M1Graph
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [20000, 20002], outs := [20001] }, { rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 5, 3, 7] }] }
def pm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] }, { rank := 0, op := "OpName.FW_linear", ins := [20100, 20300], outs := [20200] }] }
end UnflattenOutputK1N1M1Graph
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.UnflattenOutputK1N1M1

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def x0 : RelationFact :=
  .sharded 10000 [10100] 1 [2, 5, 21] [2, 5, 21]

private def y0 : RelationFact :=
  .sharded 10001 [10200] 1 [2, 5, 3, 7] [2, 5, 3, 7]

private def x1 : RelationFact :=
  .joined 20000 20100 [2, 5, 7]

private def y1 : RelationFact :=
  .sharded 20001 [20200] 2 [2, 5, 3] [2, 5, 3]

private def w1 : RelationFact :=
  .sharded 20002 [20300] 0 [3, 7] [3, 7]

private def protected_pm : RelationFact :=
  .tensorShape .pm 998 [1]

private def anchor : RelationFact :=
  .tensorShape .sm 999 [1]

private def state_before : RelationState where
  facts := [anchor, protected_pm, x0, x1, w1]
  nonempty := by decide

private def state_after : RelationState where
  facts := [anchor, protected_pm, x0, x1, w1, y0, y1]
  nonempty := by decide

private def segment_000000_smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [20000, 20002], outs := [20001] }, { rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 5, 3, 7] }]
private def segment_000000_pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] }, { rank := 0, op := "OpName.FW_linear", ins := [20100, 20300], outs := [20200] }]
@[irreducible] private def segment_000000_smFinal(z:Store):Store := segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) z
@[irreducible] private def segment_000000_pmFinal(z:Store):Store := segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) z
private theorem segment_000000_t0_smWriter (smStore : Store) :
    (segment_000000_smFinal smStore) 20001 = fw_linear ((segment_000000_smFinal smStore) 20000) ((segment_000000_smFinal smStore) 20002) := by
  have hfinal : (segment_000000_smFinal smStore) = segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore := by
    unfold segment_000000_smFinal
    rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [20000, 20002], outs := [20001] }] ++ (segment_000000_smNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 20001 = fw_linear (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore 20000) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore 20002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK1N1M1Graph.sm smStore
      (segment_000000_smNodes.take 0) (segment_000000_smNodes.drop 1)
      { rank := 0, op := "OpName.FW_linear", ins := [20000, 20002], outs := [20001] } 20001
      (fun t => fw_linear (t 20000) (t 20002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK1N1M1Graph.sm t 0 20000 20002 20001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore 20000 = (segment_000000_smFinal smStore) 20000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK1N1M1Graph.sm smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [20000, 20002], outs := [20001] } :: (segment_000000_smNodes.drop 1)) 20000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore 20002 = (segment_000000_smFinal smStore) 20002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK1N1M1Graph.sm smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [20000, 20002], outs := [20001] } :: (segment_000000_smNodes.drop 1)) 20002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 20001 = fw_linear ((segment_000000_smFinal smStore) 20000) ((segment_000000_smFinal smStore) 20002) := by
    calc
      _ = fw_linear (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore 20000) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore 20002) := hout_prefix
      _ = fw_linear ((segment_000000_smFinal smStore) 20000) ((segment_000000_smFinal smStore) 20002) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_pmWriter0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 20200 = fw_linear ((segment_000000_pmFinal pmStore) 20100) ((segment_000000_pmFinal pmStore) 20300) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 1) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [20100, 20300], outs := [20200] }] ++ (segment_000000_pmNodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 20200 = fw_linear (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore 20100) (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore 20300) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK1N1M1Graph.pm pmStore
      (segment_000000_pmNodes.take 1) (segment_000000_pmNodes.drop 2)
      { rank := 0, op := "OpName.FW_linear", ins := [20100, 20300], outs := [20200] } 20200
      (fun t => fw_linear (t 20100) (t 20300)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out UnflattenOutputK1N1M1Graph.pm t 0 20100 20300 20200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore 20100 = (segment_000000_pmFinal pmStore) 20100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK1N1M1Graph.pm pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 0, op := "OpName.FW_linear", ins := [20100, 20300], outs := [20200] } :: (segment_000000_pmNodes.drop 2)) 20100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore 20300 = (segment_000000_pmFinal pmStore) 20300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK1N1M1Graph.pm pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 0, op := "OpName.FW_linear", ins := [20100, 20300], outs := [20200] } :: (segment_000000_pmNodes.drop 2)) 20300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 20200 = fw_linear ((segment_000000_pmFinal pmStore) 20100) ((segment_000000_pmFinal pmStore) 20300) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore 20100) (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore 20300) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 20100) ((segment_000000_pmFinal pmStore) 20300) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_t0_out (smStore pmStore : Store)
    (hActivation : x1.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore))
    (hWeight : w1.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)) :
    y1.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  change (segment_000000_smFinal smStore) 20000 = (segment_000000_pmFinal pmStore) 20100 ∧
    ((segment_000000_smFinal smStore) 20000).shape = [2, 5, 7] ∧
    ((segment_000000_pmFinal pmStore) 20100).shape = [2, 5, 7] at hActivation
  change ShardedRel ((segment_000000_smFinal smStore) 20002) [(segment_000000_pmFinal pmStore) 20300] 0 [3, 7] [3, 7] at hWeight
  have hSm := segment_000000_t0_smWriter smStore
  have hPm0 := segment_000000_t0_pmWriter0 pmStore
  have hComm := (TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm
    (K := [(segment_000000_pmFinal pmStore) 20300].length) (b := 2) (s := 5) (i := 7) (o := 3)
    (x := (segment_000000_pmFinal pmStore) 20100) (ws := [(segment_000000_pmFinal pmStore) 20300])
    (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by simp) hActivation.2.2 (fun w hw => hWeight.shard_shapes w hw))
  have hValue : (segment_000000_smFinal smStore) 20001 = allGatherPrimDimN 2 [(segment_000000_pmFinal pmStore) 20200].length 0 [(segment_000000_pmFinal pmStore) 20200] := by
    rw [hSm, hActivation.1, hWeight.full_value, hComm]
    simp only [List.map, List.length_cons, List.length_nil]
    rw [← hPm0]
  have hOutShape0 : ((segment_000000_pmFinal pmStore) 20200).shape = [2, 5, 3] := by
    rw [hPm0]
    exact fw_linear_3d_shape 2 5 7 3 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 20300) (by simp))
  unfold y1 RelationFact.Holds
  change ShardedRel ((segment_000000_smFinal smStore) 20001) [(segment_000000_pmFinal pmStore) 20200] 2 [2, 5, 3] [2, 5, 3]
  refine {
    full_value := hValue
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by native_decide
    shard_shapes := ?_
    shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
  }
  · rw [hValue]
    rw [allGatherPrimDimN_shape 2 [(segment_000000_pmFinal pmStore) 20200].length [(segment_000000_pmFinal pmStore) 20200] [2, 5, 3]]
    · simp only [List.length_cons, List.length_nil]
      native_decide
    · simp only [List.head?, Option.map, Option.getD]
      exact hOutShape0
  · intro shard hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl
    · exact hOutShape0

private theorem segment_000000_t1_hSmWriter(smStore:Store):(segment_000000_smFinal smStore) 10001=fw_view [2, 5, 3, 7] ((segment_000000_smFinal smStore) 10000):=by
  have hfinal:(segment_000000_smFinal smStore)=segment_000000_smNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore:=by unfold segment_000000_smFinal;rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 1) ++ [{ rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 5, 3, 7] }] ++ (segment_000000_smNodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 10001 = fw_view [2, 5, 3, 7] (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore 10000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK1N1M1Graph.sm smStore
      (segment_000000_smNodes.take 1) (segment_000000_smNodes.drop 2)
      { rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 5, 3, 7] } 10001
      (fun t => fw_view [2, 5, 3, 7] (t 10000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK1N1M1Graph.sm t 0 2 [5, 3, 7] 10000 10001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore 10000 = (segment_000000_smFinal smStore) 10000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK1N1M1Graph.sm smStore
      (segment_000000_smNodes.take 1) ({ rank := 0, op := "OpName.FW_view", ins := [10000], outs := [10001], params := [2, 5, 3, 7] } :: (segment_000000_smNodes.drop 2)) 10000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 10001 = fw_view [2, 5, 3, 7] ((segment_000000_smFinal smStore) 10000) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_smNodes.take 1)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.sm) smStore 10000) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_smFinal smStore) 10000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_t1_hPmWriter0(pmStore:Store):(segment_000000_pmFinal pmStore) 10200=fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10100):=by
  have hfinal:(segment_000000_pmFinal pmStore)=segment_000000_pmNodes.foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore:=by unfold segment_000000_pmFinal;rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] }] ++ (segment_000000_pmNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 10200 = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore 10100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer UnflattenOutputK1N1M1Graph.pm pmStore
      (segment_000000_pmNodes.take 0) (segment_000000_pmNodes.drop 1)
      { rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] } 10200
      (fun t => fw_view [2, 5, 3, 7] (t 10100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out UnflattenOutputK1N1M1Graph.pm t 0 2 [5, 3, 7] 10100 10200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore 10100 = (segment_000000_pmFinal pmStore) 10100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final UnflattenOutputK1N1M1Graph.pm pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_view", ins := [10100], outs := [10200], params := [2, 5, 3, 7] } :: (segment_000000_pmNodes.drop 1)) 10100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 10200 = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10100) := by
    calc
      _ = fw_view [2, 5, 3, 7] (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful UnflattenOutputK1N1M1Graph.pm) pmStore 10100) := hout_prefix
      _ = fw_view [2, 5, 3, 7] ((segment_000000_pmFinal pmStore) 10100) := by rw [hout_read_0]
  exact hout
set_option maxHeartbeats 500000 in
private theorem segment_000000_t1_out(smStore pmStore:Store)(hframe:state_before.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)):
    y0.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore):=by
    let smFinal:=segment_000000_smFinal smStore
    let pmFinal:=segment_000000_pmFinal pmStore
    have hx:x0.Holds smFinal pmFinal:=hframe _ (by native_decide)
    change ShardedRel (smFinal 10000) [pmFinal 10100] 1 [2, 5, 21] [2, 5, 21] at hx
    have hxV:smFinal 10000=allGatherPrimDimN 1 1 0 [pmFinal 10100]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 10001=fw_view [2, 5, 3, 7] (smFinal 10000):=segment_000000_t1_hSmWriter smStore
    have hPm0:pmFinal 10200=fw_view [2, 5, 3, 7] (pmFinal 10100):=segment_000000_t1_hPmWriter0 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_unflatten_allGather_dim1_rank3 1 2 5 3 7 [pmFinal 10100]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 10001=allGatherPrimDimN 1 1 0 [pmFinal 10200]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0]
    have hout:y0.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 10001) [pmFinal 10200] 1 [2, 5, 3, 7] [2, 5, 3, 7]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0
        · subst piece; rw [hPm0]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    exact hout
private def segment_000000:ClosedDepSegmentCertificate UnflattenOutputK1N1M1Graph.sm UnflattenOutputK1N1M1Graph.pm state_before state_after where
  smNodes := segment_000000_smNodes
  pmNodes := segment_000000_pmNodes
  sound := by
    intro smStore pmStore hstate
    have hframe : state_before.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
      unfold segment_000000_smFinal segment_000000_pmFinal
      apply RelationState.Holds.fold_frame segment_000000_smNodes segment_000000_pmNodes smStore pmStore hstate <;> native_decide
    have h0 := segment_000000_t0_out smStore pmStore (hframe x1 (by native_decide)) (hframe w1 (by native_decide))
    have h1 := segment_000000_t1_out smStore pmStore hframe
    have result : state_after.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
      intro fact hfact
      have covered : fact ∈ [y1, y0] ++ state_before.facts :=
        (show state_after.facts ⊆ [y1, y0] ++ state_before.facts by native_decide) hfact
      simp only [List.mem_append] at covered
      rcases covered with fresh | old
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
        rcases fresh with rfl | rfl
        · exact h0
        · exact h1
      · exact hframe fact old
    simpa only [segment_000000_smFinal, segment_000000_pmFinal] using result

#print axioms segment_000000
end
end TrainVerify.Denote.UnflattenOutputK1N1M1
