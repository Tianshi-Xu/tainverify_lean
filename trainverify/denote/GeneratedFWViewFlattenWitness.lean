import denote.RelationCompiler
import denote.KRankViewFlatten
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace FWViewFlattenAxis1
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [100], outs := [200], params := [2, 15, 21] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [1000], outs := [2000], params := [2, 5, 21] }, { rank := 1, op := "OpName.FW_view", ins := [1001], outs := [2001], params := [2, 5, 21] }, { rank := 2, op := "OpName.FW_view", ins := [1002], outs := [2002], params := [2, 5, 21] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002] 1 [2, 15, 3, 7] [2, 5, 3, 7]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002] 1 [2, 15, 21] [2, 5, 21]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [100], outs := [200], params := [2, 15, 21] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [1000], outs := [2000], params := [2, 5, 21] }, { rank := 1, op := "OpName.FW_view", ins := [1001], outs := [2001], params := [2, 5, 21] }, { rank := 2, op := "OpName.FW_view", ins := [1002], outs := [2002], params := [2, 5, 21] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [2, 15, 21] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.FW_view", ins := [100], outs := [200], params := [2, 15, 21] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [2, 15, 21] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FWViewFlattenAxis1.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.FW_view", ins := [100], outs := [200], params := [2, 15, 21] } 200
      (fun t => fw_view [2, 15, 21] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out FWViewFlattenAxis1.smGraph t 0 2 [15, 21] 100 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FWViewFlattenAxis1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.FW_view", ins := [100], outs := [200], params := [2, 15, 21] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [2, 15, 21] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [2, 15, 21] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.smGraph) smStore 100) := hout_prefix
      _ = fw_view [2, 15, 21] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.FW_view", ins := [1000], outs := [2000], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FWViewFlattenAxis1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.FW_view", ins := [1000], outs := [2000], params := [2, 5, 21] } 2000
      (fun t => fw_view [2, 5, 21] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out FWViewFlattenAxis1.pmGraph t 0 2 [5, 21] 1000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FWViewFlattenAxis1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.FW_view", ins := [1000], outs := [2000], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter1(pmStore:Store):(segment_000000_pm_final pmStore) 2001=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.FW_view", ins := [1001], outs := [2001], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FWViewFlattenAxis1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.FW_view", ins := [1001], outs := [2001], params := [2, 5, 21] } 2001
      (fun t => fw_view [2, 5, 21] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out FWViewFlattenAxis1.pmGraph t 1 2 [5, 21] 1001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FWViewFlattenAxis1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.FW_view", ins := [1001], outs := [2001], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore 1001) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter2(pmStore:Store):(segment_000000_pm_final pmStore) 2002=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1002):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.FW_view", ins := [1002], outs := [2002], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FWViewFlattenAxis1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.FW_view", ins := [1002], outs := [2002], params := [2, 5, 21] } 2002
      (fun t => fw_view [2, 5, 21] (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out FWViewFlattenAxis1.pmGraph t 2 2 [5, 21] 1002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FWViewFlattenAxis1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.FW_view", ins := [1002], outs := [2002], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis1.pmGraph) pmStore 1002) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1002) := by rw [hout_read_0]
  exact hout
set_option maxHeartbeats 500000 in
private theorem segment_000000_sound(smStore pmStore:Store)(hstate:state_000000.Holds smStore pmStore):
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore):=by
    let smFinal:=segment_000000_sm_final smStore
    let pmFinal:=segment_000000_pm_final pmStore
    have hframe:state_000000.Holds smFinal pmFinal:=by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
    have hx:fact_x.Holds smFinal pmFinal:=hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 1 [2, 15, 3, 7] [2, 5, 3, 7] at hx
    have hxV:smFinal 100=allGatherPrimDimN 1 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 200=fw_view [2, 15, 21] (smFinal 100):=segment_000000_hSmWriter smStore
    have hPm0:pmFinal 2000=fw_view [2, 5, 21] (pmFinal 1000):=segment_000000_hPmWriter0 pmStore
    have hPm1:pmFinal 2001=fw_view [2, 5, 21] (pmFinal 1001):=segment_000000_hPmWriter1 pmStore
    have hPm2:pmFinal 2002=fw_view [2, 5, 21] (pmFinal 1002):=segment_000000_hPmWriter2 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_allGatherPrimDimN_dim1_rank4_to_rank3 3 2 5 3 7 [pmFinal 1000, pmFinal 1001, pmFinal 1002]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 200=allGatherPrimDimN 1 3 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1, ← hPm2]
    have hout:fact_out.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002] 1 [2, 15, 21] [2, 5, 21]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst piece; rw [hPm0]; rfl
        · subst piece; rw [hPm1]; rfl
        · subst piece; rw [hPm2]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    intro fact hfact
    have covered:fact∈[fact_out]++state_000000.facts:=by
      exact (show state_000001.facts⊆[fact_out]++state_000000.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate FWViewFlattenAxis1.smGraph FWViewFlattenAxis1.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end FWViewFlattenAxis1
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace FWViewFlattenAxis2
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [100], outs := [200], params := [2, 5, 63] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_view", ins := [1000], outs := [2000], params := [2, 5, 21] }, { rank := 1, op := "OpName.FW_view", ins := [1001], outs := [2001], params := [2, 5, 21] }, { rank := 2, op := "OpName.FW_view", ins := [1002], outs := [2002], params := [2, 5, 21] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002] 2 [2, 5, 9, 7] [2, 5, 3, 7]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002] 2 [2, 5, 63] [2, 5, 21]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [100], outs := [200], params := [2, 5, 63] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.FW_view", ins := [1000], outs := [2000], params := [2, 5, 21] }, { rank := 1, op := "OpName.FW_view", ins := [1001], outs := [2001], params := [2, 5, 21] }, { rank := 2, op := "OpName.FW_view", ins := [1002], outs := [2002], params := [2, 5, 21] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [2, 5, 63] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.FW_view", ins := [100], outs := [200], params := [2, 5, 63] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [2, 5, 63] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FWViewFlattenAxis2.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.FW_view", ins := [100], outs := [200], params := [2, 5, 63] } 200
      (fun t => fw_view [2, 5, 63] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out FWViewFlattenAxis2.smGraph t 0 2 [5, 63] 100 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FWViewFlattenAxis2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.FW_view", ins := [100], outs := [200], params := [2, 5, 63] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [2, 5, 63] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [2, 5, 63] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.smGraph) smStore 100) := hout_prefix
      _ = fw_view [2, 5, 63] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.FW_view", ins := [1000], outs := [2000], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FWViewFlattenAxis2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.FW_view", ins := [1000], outs := [2000], params := [2, 5, 21] } 2000
      (fun t => fw_view [2, 5, 21] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out FWViewFlattenAxis2.pmGraph t 0 2 [5, 21] 1000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FWViewFlattenAxis2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.FW_view", ins := [1000], outs := [2000], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter1(pmStore:Store):(segment_000000_pm_final pmStore) 2001=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.FW_view", ins := [1001], outs := [2001], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FWViewFlattenAxis2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.FW_view", ins := [1001], outs := [2001], params := [2, 5, 21] } 2001
      (fun t => fw_view [2, 5, 21] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out FWViewFlattenAxis2.pmGraph t 1 2 [5, 21] 1001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FWViewFlattenAxis2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.FW_view", ins := [1001], outs := [2001], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore 1001) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter2(pmStore:Store):(segment_000000_pm_final pmStore) 2002=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1002):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.FW_view", ins := [1002], outs := [2002], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer FWViewFlattenAxis2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.FW_view", ins := [1002], outs := [2002], params := [2, 5, 21] } 2002
      (fun t => fw_view [2, 5, 21] (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_fw_view_out FWViewFlattenAxis2.pmGraph t 2 2 [5, 21] 1002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final FWViewFlattenAxis2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.FW_view", ins := [1002], outs := [2002], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful FWViewFlattenAxis2.pmGraph) pmStore 1002) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1002) := by rw [hout_read_0]
  exact hout
set_option maxHeartbeats 500000 in
private theorem segment_000000_sound(smStore pmStore:Store)(hstate:state_000000.Holds smStore pmStore):
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore):=by
    let smFinal:=segment_000000_sm_final smStore
    let pmFinal:=segment_000000_pm_final pmStore
    have hframe:state_000000.Holds smFinal pmFinal:=by
      unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
      apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
    have hx:fact_x.Holds smFinal pmFinal:=hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 2 [2, 5, 9, 7] [2, 5, 3, 7] at hx
    have hxV:smFinal 100=allGatherPrimDimN 2 3 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 200=fw_view [2, 5, 63] (smFinal 100):=segment_000000_hSmWriter smStore
    have hPm0:pmFinal 2000=fw_view [2, 5, 21] (pmFinal 1000):=segment_000000_hPmWriter0 pmStore
    have hPm1:pmFinal 2001=fw_view [2, 5, 21] (pmFinal 1001):=segment_000000_hPmWriter1 pmStore
    have hPm2:pmFinal 2002=fw_view [2, 5, 21] (pmFinal 1002):=segment_000000_hPmWriter2 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_allGatherPrimDimN_dim2_rank4_to_rank3 3 2 5 3 7 [pmFinal 1000, pmFinal 1001, pmFinal 1002]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 200=allGatherPrimDimN 2 3 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1, ← hPm2]
    have hout:fact_out.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002] 2 [2, 5, 63] [2, 5, 21]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst piece; rw [hPm0]; rfl
        · subst piece; rw [hPm1]; rfl
        · subst piece; rw [hPm2]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    intro fact hfact
    have covered:fact∈[fact_out]++state_000000.facts:=by
      exact (show state_000001.facts⊆[fact_out]++state_000000.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate FWViewFlattenAxis2.smGraph FWViewFlattenAxis2.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end FWViewFlattenAxis2
