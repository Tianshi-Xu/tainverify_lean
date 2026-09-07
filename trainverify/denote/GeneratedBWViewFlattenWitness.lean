import denote.RelationCompiler
import denote.KRankViewFlatten
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ViewFlattenA1Case0
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 16, 64] }] }
def pmGraph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 8, 64] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 8, 64] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001] 1 [1, 16, 4, 16] [1, 8, 4, 16]
def fact_out : RelationFact := .sharded 200 [2000, 2001] 1 [1, 16, 64] [1, 8, 64]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 16, 64] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 8, 64] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 8, 64] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [1, 16, 64] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 16, 64] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [1, 16, 64] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case0.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 16, 64] } 200
      (fun t => fw_view [1, 16, 64] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case0.smGraph t 0 1 [16, 64] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 16, 64] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [1, 16, 64] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [1, 16, 64] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.smGraph) smStore 100) := hout_prefix
      _ = fw_view [1, 16, 64] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 8, 64] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [1, 8, 64] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 8, 64] } 2000
      (fun t => fw_view [1, 8, 64] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case0.pmGraph t 0 1 [8, 64] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 8, 64] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [1, 8, 64] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter1(pmStore:Store):(segment_000000_pm_final pmStore) 2001=fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1001):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 8, 64] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = fw_view [1, 8, 64] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 8, 64] } 2001
      (fun t => fw_view [1, 8, 64] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case0.pmGraph t 1 1 [8, 64] 1001 8001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 8, 64] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = fw_view [1, 8, 64] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case0.pmGraph) pmStore 1001) := hout_prefix
      _ = fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
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
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001] 1 [1, 16, 4, 16] [1, 8, 4, 16] at hx
    have hxV:smFinal 100=allGatherPrimDimN 1 2 0 [pmFinal 1000, pmFinal 1001]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 200=fw_view [1, 16, 64] (smFinal 100):=segment_000000_hSmWriter smStore
    have hPm0:pmFinal 2000=fw_view [1, 8, 64] (pmFinal 1000):=segment_000000_hPmWriter0 pmStore
    have hPm1:pmFinal 2001=fw_view [1, 8, 64] (pmFinal 1001):=segment_000000_hPmWriter1 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_allGatherPrimDimN_dim1_rank4_to_rank3 2 1 8 4 16 [pmFinal 1000, pmFinal 1001]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 200=allGatherPrimDimN 1 2 0 [pmFinal 2000, pmFinal 2001]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1]
    have hout:fact_out.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001] 1 [1, 16, 64] [1, 8, 64]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0 | h1
        · subst piece; rw [hPm0]; rfl
        · subst piece; rw [hPm1]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    intro fact hfact
    have covered:fact∈[fact_out]++state_000000.facts:=by
      exact (show state_000001.facts⊆[fact_out]++state_000000.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate ViewFlattenA1Case0.smGraph ViewFlattenA1Case0.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end ViewFlattenA1Case0
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ViewFlattenA1Case1
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 16, 64] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 4, 64] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 4, 64] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [1, 4, 64] }, { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [1, 4, 64] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 1 [1, 16, 4, 16] [1, 4, 4, 16]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 1 [1, 16, 64] [1, 4, 64]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 16, 64] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 4, 64] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 4, 64] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [1, 4, 64] }, { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [1, 4, 64] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [1, 16, 64] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 16, 64] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [1, 16, 64] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case1.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 16, 64] } 200
      (fun t => fw_view [1, 16, 64] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case1.smGraph t 0 1 [16, 64] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 16, 64] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [1, 16, 64] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [1, 16, 64] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.smGraph) smStore 100) := hout_prefix
      _ = fw_view [1, 16, 64] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 4, 64] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 4, 64] } 2000
      (fun t => fw_view [1, 4, 64] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case1.pmGraph t 0 1 [4, 64] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 4, 64] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter1(pmStore:Store):(segment_000000_pm_final pmStore) 2001=fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1001):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 4, 64] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 4, 64] } 2001
      (fun t => fw_view [1, 4, 64] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case1.pmGraph t 1 1 [4, 64] 1001 8001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 4, 64] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1001) := hout_prefix
      _ = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter2(pmStore:Store):(segment_000000_pm_final pmStore) 2002=fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1002):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [1, 4, 64] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [1, 4, 64] } 2002
      (fun t => fw_view [1, 4, 64] (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case1.pmGraph t 2 1 [4, 64] 1002 8002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [1, 4, 64] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1002) := hout_prefix
      _ = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1002) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter3(pmStore:Store):(segment_000000_pm_final pmStore) 2003=fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1003):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [1, 4, 64] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2003 = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [1, 4, 64] } 2003
      (fun t => fw_view [1, 4, 64] (t 1003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case1.pmGraph t 3 1 [4, 64] 1003 8003 2003
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [1, 4, 64] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2003 = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1003) := by
    calc
      _ = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case1.pmGraph) pmStore 1003) := hout_prefix
      _ = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1003) := by rw [hout_read_0]
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
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 1 [1, 16, 4, 16] [1, 4, 4, 16] at hx
    have hxV:smFinal 100=allGatherPrimDimN 1 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 200=fw_view [1, 16, 64] (smFinal 100):=segment_000000_hSmWriter smStore
    have hPm0:pmFinal 2000=fw_view [1, 4, 64] (pmFinal 1000):=segment_000000_hPmWriter0 pmStore
    have hPm1:pmFinal 2001=fw_view [1, 4, 64] (pmFinal 1001):=segment_000000_hPmWriter1 pmStore
    have hPm2:pmFinal 2002=fw_view [1, 4, 64] (pmFinal 1002):=segment_000000_hPmWriter2 pmStore
    have hPm3:pmFinal 2003=fw_view [1, 4, 64] (pmFinal 1003):=segment_000000_hPmWriter3 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_allGatherPrimDimN_dim1_rank4_to_rank3 4 1 4 4 16 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 200=allGatherPrimDimN 1 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1, ← hPm2, ← hPm3]
    have hout:fact_out.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 1 [1, 16, 64] [1, 4, 64]
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
    intro fact hfact
    have covered:fact∈[fact_out]++state_000000.facts:=by
      exact (show state_000001.facts⊆[fact_out]++state_000000.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate ViewFlattenA1Case1.smGraph ViewFlattenA1Case1.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end ViewFlattenA1Case1
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ViewFlattenA1Case2
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 15, 21] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002] 1 [2, 15, 3, 7] [2, 5, 3, 7]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002] 1 [2, 15, 21] [2, 5, 21]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 15, 21] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [2, 15, 21] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 15, 21] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [2, 15, 21] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case2.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 15, 21] } 200
      (fun t => fw_view [2, 15, 21] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case2.smGraph t 0 2 [15, 21] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 15, 21] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [2, 15, 21] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [2, 15, 21] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.smGraph) smStore 100) := hout_prefix
      _ = fw_view [2, 15, 21] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] } 2000
      (fun t => fw_view [2, 5, 21] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case2.pmGraph t 0 2 [5, 21] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter1(pmStore:Store):(segment_000000_pm_final pmStore) 2001=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] } 2001
      (fun t => fw_view [2, 5, 21] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case2.pmGraph t 1 2 [5, 21] 1001 8001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore 1001) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter2(pmStore:Store):(segment_000000_pm_final pmStore) 2002=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1002):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] } 2002
      (fun t => fw_view [2, 5, 21] (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case2.pmGraph t 2 2 [5, 21] 1002 8002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case2.pmGraph) pmStore 1002) := hout_prefix
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
private def segment_000000:ClosedDepSegmentCertificate ViewFlattenA1Case2.smGraph ViewFlattenA1Case2.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end ViewFlattenA1Case2
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ViewFlattenA1Case3
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [3, 2, 4] }] }
def pmGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [3, 2, 4] }] }
def fact_x : RelationFact := .sharded 100 [1000] 1 [3, 2, 1, 4] [3, 2, 1, 4]
def fact_out : RelationFact := .sharded 200 [2000] 1 [3, 2, 4] [3, 2, 4]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [3, 2, 4] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [3, 2, 4] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case3.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case3.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [3, 2, 4] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case3.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [3, 2, 4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [3, 2, 4] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case3.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case3.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [3, 2, 4] } 200
      (fun t => fw_view [3, 2, 4] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case3.smGraph t 0 3 [2, 4] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case3.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [3, 2, 4] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [3, 2, 4] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [3, 2, 4] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case3.smGraph) smStore 100) := hout_prefix
      _ = fw_view [3, 2, 4] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [3, 2, 4] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case3.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [3, 2, 4] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [3, 2, 4] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case3.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [3, 2, 4] } 2000
      (fun t => fw_view [3, 2, 4] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case3.pmGraph t 0 3 [2, 4] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case3.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [3, 2, 4] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [3, 2, 4] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [3, 2, 4] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case3.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [3, 2, 4] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
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
    change ShardedRel (smFinal 100) [pmFinal 1000] 1 [3, 2, 1, 4] [3, 2, 1, 4] at hx
    have hxV:smFinal 100=allGatherPrimDimN 1 1 0 [pmFinal 1000]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 200=fw_view [3, 2, 4] (smFinal 100):=segment_000000_hSmWriter smStore
    have hPm0:pmFinal 2000=fw_view [3, 2, 4] (pmFinal 1000):=segment_000000_hPmWriter0 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_allGatherPrimDimN_dim1_rank4_to_rank3 1 3 2 1 4 [pmFinal 1000]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 200=allGatherPrimDimN 1 1 0 [pmFinal 2000]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0]
    have hout:fact_out.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 200) [pmFinal 2000] 1 [3, 2, 4] [3, 2, 4]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0
        · subst piece; rw [hPm0]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    intro fact hfact
    have covered:fact∈[fact_out]++state_000000.facts:=by
      exact (show state_000001.facts⊆[fact_out]++state_000000.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate ViewFlattenA1Case3.smGraph ViewFlattenA1Case3.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end ViewFlattenA1Case3
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ViewFlattenA1Case4
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 5, 6] }] }
def pmGraph : GraphDecl := { numRanks := 5, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 1, 6] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 1, 6] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 1, 6] }, { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [2, 1, 6] }, { rank := 4, op := "OpName.BW_view", ins := [1004, 8004], outs := [2004], params := [2, 1, 6] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002, 1003, 1004] 1 [2, 5, 2, 3] [2, 1, 2, 3]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002, 2003, 2004] 1 [2, 5, 6] [2, 1, 6]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 5, 6] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 1, 6] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 1, 6] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 1, 6] }, { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [2, 1, 6] }, { rank := 4, op := "OpName.BW_view", ins := [1004, 8004], outs := [2004], params := [2, 1, 6] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [2, 5, 6] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 5, 6] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [2, 5, 6] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case4.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 5, 6] } 200
      (fun t => fw_view [2, 5, 6] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case4.smGraph t 0 2 [5, 6] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 5, 6] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [2, 5, 6] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [2, 5, 6] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.smGraph) smStore 100) := hout_prefix
      _ = fw_view [2, 5, 6] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 1, 6] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 1, 6] } 2000
      (fun t => fw_view [2, 1, 6] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case4.pmGraph t 0 2 [1, 6] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 1, 6] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter1(pmStore:Store):(segment_000000_pm_final pmStore) 2001=fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1001):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 1, 6] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 1, 6] } 2001
      (fun t => fw_view [2, 1, 6] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case4.pmGraph t 1 2 [1, 6] 1001 8001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 1, 6] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1001) := hout_prefix
      _ = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter2(pmStore:Store):(segment_000000_pm_final pmStore) 2002=fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1002):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 1, 6] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 1, 6] } 2002
      (fun t => fw_view [2, 1, 6] (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case4.pmGraph t 2 2 [1, 6] 1002 8002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 1, 6] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1002) := hout_prefix
      _ = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1002) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter3(pmStore:Store):(segment_000000_pm_final pmStore) 2003=fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1003):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [2, 1, 6] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2003 = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [2, 1, 6] } 2003
      (fun t => fw_view [2, 1, 6] (t 1003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case4.pmGraph t 3 2 [1, 6] 1003 8003 2003
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [2, 1, 6] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2003 = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1003) := by
    calc
      _ = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1003) := hout_prefix
      _ = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1003) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter4(pmStore:Store):(segment_000000_pm_final pmStore) 2004=fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1004):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 4, op := "OpName.BW_view", ins := [1004, 8004], outs := [2004], params := [2, 1, 6] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2004 = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1004) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA1Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 4, op := "OpName.BW_view", ins := [1004, 8004], outs := [2004], params := [2, 1, 6] } 2004
      (fun t => fw_view [2, 1, 6] (t 1004)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA1Case4.pmGraph t 4 2 [1, 6] 1004 8004 2004
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1004 = (segment_000000_pm_final pmStore) 1004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA1Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_view", ins := [1004, 8004], outs := [2004], params := [2, 1, 6] } :: (segment_000000_pm_nodes.drop 5)) 1004
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2004 = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1004) := by
    calc
      _ = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ViewFlattenA1Case4.pmGraph) pmStore 1004) := hout_prefix
      _ = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1004) := by rw [hout_read_0]
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
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] 1 [2, 5, 2, 3] [2, 1, 2, 3] at hx
    have hxV:smFinal 100=allGatherPrimDimN 1 5 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 200=fw_view [2, 5, 6] (smFinal 100):=segment_000000_hSmWriter smStore
    have hPm0:pmFinal 2000=fw_view [2, 1, 6] (pmFinal 1000):=segment_000000_hPmWriter0 pmStore
    have hPm1:pmFinal 2001=fw_view [2, 1, 6] (pmFinal 1001):=segment_000000_hPmWriter1 pmStore
    have hPm2:pmFinal 2002=fw_view [2, 1, 6] (pmFinal 1002):=segment_000000_hPmWriter2 pmStore
    have hPm3:pmFinal 2003=fw_view [2, 1, 6] (pmFinal 1003):=segment_000000_hPmWriter3 pmStore
    have hPm4:pmFinal 2004=fw_view [2, 1, 6] (pmFinal 1004):=segment_000000_hPmWriter4 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_allGatherPrimDimN_dim1_rank4_to_rank3 5 2 1 2 3 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 200=allGatherPrimDimN 1 5 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1, ← hPm2, ← hPm3, ← hPm4]
    have hout:fact_out.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] 1 [2, 5, 6] [2, 1, 6]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0 | h1 | h2 | h3 | h4
        · subst piece; rw [hPm0]; rfl
        · subst piece; rw [hPm1]; rfl
        · subst piece; rw [hPm2]; rfl
        · subst piece; rw [hPm3]; rfl
        · subst piece; rw [hPm4]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    intro fact hfact
    have covered:fact∈[fact_out]++state_000000.facts:=by
      exact (show state_000001.facts⊆[fact_out]++state_000000.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate ViewFlattenA1Case4.smGraph ViewFlattenA1Case4.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end ViewFlattenA1Case4
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ViewFlattenA2Case0
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 8, 128] }] }
def pmGraph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 8, 64] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 8, 64] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001] 2 [1, 8, 8, 16] [1, 8, 4, 16]
def fact_out : RelationFact := .sharded 200 [2000, 2001] 2 [1, 8, 128] [1, 8, 64]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 8, 128] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 8, 64] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 8, 64] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [1, 8, 128] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 8, 128] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [1, 8, 128] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case0.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 8, 128] } 200
      (fun t => fw_view [1, 8, 128] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case0.smGraph t 0 1 [8, 128] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 8, 128] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [1, 8, 128] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [1, 8, 128] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.smGraph) smStore 100) := hout_prefix
      _ = fw_view [1, 8, 128] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 8, 64] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [1, 8, 64] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 8, 64] } 2000
      (fun t => fw_view [1, 8, 64] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case0.pmGraph t 0 1 [8, 64] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 8, 64] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [1, 8, 64] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter1(pmStore:Store):(segment_000000_pm_final pmStore) 2001=fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1001):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 8, 64] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = fw_view [1, 8, 64] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 8, 64] } 2001
      (fun t => fw_view [1, 8, 64] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case0.pmGraph t 1 1 [8, 64] 1001 8001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case0.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 8, 64] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = fw_view [1, 8, 64] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case0.pmGraph) pmStore 1001) := hout_prefix
      _ = fw_view [1, 8, 64] ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
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
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001] 2 [1, 8, 8, 16] [1, 8, 4, 16] at hx
    have hxV:smFinal 100=allGatherPrimDimN 2 2 0 [pmFinal 1000, pmFinal 1001]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 200=fw_view [1, 8, 128] (smFinal 100):=segment_000000_hSmWriter smStore
    have hPm0:pmFinal 2000=fw_view [1, 8, 64] (pmFinal 1000):=segment_000000_hPmWriter0 pmStore
    have hPm1:pmFinal 2001=fw_view [1, 8, 64] (pmFinal 1001):=segment_000000_hPmWriter1 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_allGatherPrimDimN_dim2_rank4_to_rank3 2 1 8 4 16 [pmFinal 1000, pmFinal 1001]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 200=allGatherPrimDimN 2 2 0 [pmFinal 2000, pmFinal 2001]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1]
    have hout:fact_out.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001] 2 [1, 8, 128] [1, 8, 64]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0 | h1
        · subst piece; rw [hPm0]; rfl
        · subst piece; rw [hPm1]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    intro fact hfact
    have covered:fact∈[fact_out]++state_000000.facts:=by
      exact (show state_000001.facts⊆[fact_out]++state_000000.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate ViewFlattenA2Case0.smGraph ViewFlattenA2Case0.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end ViewFlattenA2Case0
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ViewFlattenA2Case1
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 4, 256] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 4, 64] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 4, 64] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [1, 4, 64] }, { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [1, 4, 64] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 2 [1, 4, 16, 16] [1, 4, 4, 16]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 2 [1, 4, 256] [1, 4, 64]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 4, 256] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 4, 64] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 4, 64] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [1, 4, 64] }, { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [1, 4, 64] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [1, 4, 256] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 4, 256] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [1, 4, 256] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case1.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 4, 256] } 200
      (fun t => fw_view [1, 4, 256] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case1.smGraph t 0 1 [4, 256] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [1, 4, 256] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [1, 4, 256] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [1, 4, 256] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.smGraph) smStore 100) := hout_prefix
      _ = fw_view [1, 4, 256] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 4, 64] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 4, 64] } 2000
      (fun t => fw_view [1, 4, 64] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case1.pmGraph t 0 1 [4, 64] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [1, 4, 64] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter1(pmStore:Store):(segment_000000_pm_final pmStore) 2001=fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1001):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 4, 64] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 4, 64] } 2001
      (fun t => fw_view [1, 4, 64] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case1.pmGraph t 1 1 [4, 64] 1001 8001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [1, 4, 64] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1001) := hout_prefix
      _ = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter2(pmStore:Store):(segment_000000_pm_final pmStore) 2002=fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1002):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [1, 4, 64] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [1, 4, 64] } 2002
      (fun t => fw_view [1, 4, 64] (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case1.pmGraph t 2 1 [4, 64] 1002 8002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [1, 4, 64] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1002) := hout_prefix
      _ = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1002) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter3(pmStore:Store):(segment_000000_pm_final pmStore) 2003=fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1003):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [1, 4, 64] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2003 = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [1, 4, 64] } 2003
      (fun t => fw_view [1, 4, 64] (t 1003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case1.pmGraph t 3 1 [4, 64] 1003 8003 2003
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case1.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [1, 4, 64] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2003 = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1003) := by
    calc
      _ = fw_view [1, 4, 64] (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case1.pmGraph) pmStore 1003) := hout_prefix
      _ = fw_view [1, 4, 64] ((segment_000000_pm_final pmStore) 1003) := by rw [hout_read_0]
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
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 2 [1, 4, 16, 16] [1, 4, 4, 16] at hx
    have hxV:smFinal 100=allGatherPrimDimN 2 4 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 200=fw_view [1, 4, 256] (smFinal 100):=segment_000000_hSmWriter smStore
    have hPm0:pmFinal 2000=fw_view [1, 4, 64] (pmFinal 1000):=segment_000000_hPmWriter0 pmStore
    have hPm1:pmFinal 2001=fw_view [1, 4, 64] (pmFinal 1001):=segment_000000_hPmWriter1 pmStore
    have hPm2:pmFinal 2002=fw_view [1, 4, 64] (pmFinal 1002):=segment_000000_hPmWriter2 pmStore
    have hPm3:pmFinal 2003=fw_view [1, 4, 64] (pmFinal 1003):=segment_000000_hPmWriter3 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_allGatherPrimDimN_dim2_rank4_to_rank3 4 1 4 4 16 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 200=allGatherPrimDimN 2 4 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1, ← hPm2, ← hPm3]
    have hout:fact_out.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 2 [1, 4, 256] [1, 4, 64]
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
    intro fact hfact
    have covered:fact∈[fact_out]++state_000000.facts:=by
      exact (show state_000001.facts⊆[fact_out]++state_000000.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate ViewFlattenA2Case1.smGraph ViewFlattenA2Case1.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end ViewFlattenA2Case1
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ViewFlattenA2Case2
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 5, 63] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002] 2 [2, 5, 9, 7] [2, 5, 3, 7]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002] 2 [2, 5, 63] [2, 5, 21]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 5, 63] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [2, 5, 63] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 5, 63] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [2, 5, 63] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case2.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 5, 63] } 200
      (fun t => fw_view [2, 5, 63] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case2.smGraph t 0 2 [5, 63] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 5, 63] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [2, 5, 63] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [2, 5, 63] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.smGraph) smStore 100) := hout_prefix
      _ = fw_view [2, 5, 63] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] } 2000
      (fun t => fw_view [2, 5, 21] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case2.pmGraph t 0 2 [5, 21] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter1(pmStore:Store):(segment_000000_pm_final pmStore) 2001=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] } 2001
      (fun t => fw_view [2, 5, 21] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case2.pmGraph t 1 2 [5, 21] 1001 8001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore 1001) := hout_prefix
      _ = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter2(pmStore:Store):(segment_000000_pm_final pmStore) 2002=fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1002):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] } 2002
      (fun t => fw_view [2, 5, 21] (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case2.pmGraph t 2 2 [5, 21] 1002 8002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 5, 21] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 5, 21] ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = fw_view [2, 5, 21] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case2.pmGraph) pmStore 1002) := hout_prefix
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
private def segment_000000:ClosedDepSegmentCertificate ViewFlattenA2Case2.smGraph ViewFlattenA2Case2.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end ViewFlattenA2Case2
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ViewFlattenA2Case3
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [3, 2, 4] }] }
def pmGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [3, 2, 4] }] }
def fact_x : RelationFact := .sharded 100 [1000] 2 [3, 2, 1, 4] [3, 2, 1, 4]
def fact_out : RelationFact := .sharded 200 [2000] 2 [3, 2, 4] [3, 2, 4]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [3, 2, 4] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [3, 2, 4] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case3.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case3.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [3, 2, 4] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case3.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [3, 2, 4] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [3, 2, 4] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case3.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case3.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [3, 2, 4] } 200
      (fun t => fw_view [3, 2, 4] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case3.smGraph t 0 3 [2, 4] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case3.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [3, 2, 4] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [3, 2, 4] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [3, 2, 4] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case3.smGraph) smStore 100) := hout_prefix
      _ = fw_view [3, 2, 4] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [3, 2, 4] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case3.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [3, 2, 4] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [3, 2, 4] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case3.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [3, 2, 4] } 2000
      (fun t => fw_view [3, 2, 4] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case3.pmGraph t 0 3 [2, 4] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case3.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [3, 2, 4] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [3, 2, 4] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [3, 2, 4] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case3.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [3, 2, 4] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
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
    change ShardedRel (smFinal 100) [pmFinal 1000] 2 [3, 2, 1, 4] [3, 2, 1, 4] at hx
    have hxV:smFinal 100=allGatherPrimDimN 2 1 0 [pmFinal 1000]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 200=fw_view [3, 2, 4] (smFinal 100):=segment_000000_hSmWriter smStore
    have hPm0:pmFinal 2000=fw_view [3, 2, 4] (pmFinal 1000):=segment_000000_hPmWriter0 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_allGatherPrimDimN_dim2_rank4_to_rank3 1 3 2 1 4 [pmFinal 1000]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 200=allGatherPrimDimN 2 1 0 [pmFinal 2000]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0]
    have hout:fact_out.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 200) [pmFinal 2000] 2 [3, 2, 4] [3, 2, 4]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0
        · subst piece; rw [hPm0]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    intro fact hfact
    have covered:fact∈[fact_out]++state_000000.facts:=by
      exact (show state_000001.facts⊆[fact_out]++state_000000.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate ViewFlattenA2Case3.smGraph ViewFlattenA2Case3.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end ViewFlattenA2Case3
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace ViewFlattenA2Case4
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 1, 30] }] }
def pmGraph : GraphDecl := { numRanks := 5, nodes := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 1, 6] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 1, 6] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 1, 6] }, { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [2, 1, 6] }, { rank := 4, op := "OpName.BW_view", ins := [1004, 8004], outs := [2004], params := [2, 1, 6] }] }
def fact_x : RelationFact := .sharded 100 [1000, 1001, 1002, 1003, 1004] 2 [2, 1, 10, 3] [2, 1, 2, 3]
def fact_out : RelationFact := .sharded 200 [2000, 2001, 2002, 2003, 2004] 2 [2, 1, 30] [2, 1, 6]
def state_000000 : RelationState where
  facts := [fact_x]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_x, fact_out]
  nonempty := by decide
private def segment_000000_sm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 1, 30] }]
private def segment_000000_pm_nodes:List NodeDecl := [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 1, 6] }, { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 1, 6] }, { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 1, 6] }, { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [2, 1, 6] }, { rank := 4, op := "OpName.BW_view", ins := [1004, 8004], outs := [2004], params := [2, 1, 6] }]
@[irreducible] private def segment_000000_sm_final(z:Store):Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.smGraph) z
@[irreducible] private def segment_000000_pm_final(z:Store):Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) z
private theorem segment_000000_hSmWriter(smStore:Store):(segment_000000_sm_final smStore) 200=fw_view [2, 1, 30] ((segment_000000_sm_final smStore) 100):=by
  have hfinal:(segment_000000_sm_final smStore)=segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.smGraph) smStore:=by unfold segment_000000_sm_final;rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 1, 30] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 200 = fw_view [2, 1, 30] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.smGraph) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case4.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 1, 30] } 200
      (fun t => fw_view [2, 1, 30] (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case4.smGraph t 0 2 [1, 30] 100 800 200
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [100, 800], outs := [200], params := [2, 1, 30] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 200 = fw_view [2, 1, 30] ((segment_000000_sm_final smStore) 100) := by
    calc
      _ = fw_view [2, 1, 30] (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.smGraph) smStore 100) := hout_prefix
      _ = fw_view [2, 1, 30] ((segment_000000_sm_final smStore) 100) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter0(pmStore:Store):(segment_000000_pm_final pmStore) 2000=fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1000):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 1, 6] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 1, 6] } 2000
      (fun t => fw_view [2, 1, 6] (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case4.pmGraph t 0 2 [1, 6] 1000 8000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_view", ins := [1000, 8000], outs := [2000], params := [2, 1, 6] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter1(pmStore:Store):(segment_000000_pm_final pmStore) 2001=fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1001):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 1, 6] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1001) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 1, 6] } 2001
      (fun t => fw_view [2, 1, 6] (t 1001)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case4.pmGraph t 1 2 [1, 6] 1001 8001 2001
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_view", ins := [1001, 8001], outs := [2001], params := [2, 1, 6] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2001 = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1001) := by
    calc
      _ = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1001) := hout_prefix
      _ = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1001) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter2(pmStore:Store):(segment_000000_pm_final pmStore) 2002=fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1002):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 1, 6] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1002) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 1, 6] } 2002
      (fun t => fw_view [2, 1, 6] (t 1002)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case4.pmGraph t 2 2 [1, 6] 1002 8002 2002
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_view", ins := [1002, 8002], outs := [2002], params := [2, 1, 6] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2002 = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1002) := by
    calc
      _ = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1002) := hout_prefix
      _ = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1002) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter3(pmStore:Store):(segment_000000_pm_final pmStore) 2003=fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1003):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [2, 1, 6] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2003 = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1003) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [2, 1, 6] } 2003
      (fun t => fw_view [2, 1, 6] (t 1003)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case4.pmGraph t 3 2 [1, 6] 1003 8003 2003
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_view", ins := [1003, 8003], outs := [2003], params := [2, 1, 6] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2003 = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1003) := by
    calc
      _ = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1003) := hout_prefix
      _ = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1003) := by rw [hout_read_0]
  exact hout
private theorem segment_000000_hPmWriter4(pmStore:Store):(segment_000000_pm_final pmStore) 2004=fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1004):=by
  have hfinal:(segment_000000_pm_final pmStore)=segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore:=by unfold segment_000000_pm_final;rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 4, op := "OpName.BW_view", ins := [1004, 8004], outs := [2004], params := [2, 1, 6] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2004 = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1004) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer ViewFlattenA2Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 4, op := "OpName.BW_view", ins := [1004, 8004], outs := [2004], params := [2, 1, 6] } 2004
      (fun t => fw_view [2, 1, 6] (t 1004)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_view_out ViewFlattenA2Case4.pmGraph t 4 2 [1, 6] 1004 8004 2004
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1004 = (segment_000000_pm_final pmStore) 1004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final ViewFlattenA2Case4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_view", ins := [1004, 8004], outs := [2004], params := [2, 1, 6] } :: (segment_000000_pm_nodes.drop 5)) 1004
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2004 = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1004) := by
    calc
      _ = fw_view [2, 1, 6] (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful ViewFlattenA2Case4.pmGraph) pmStore 1004) := hout_prefix
      _ = fw_view [2, 1, 6] ((segment_000000_pm_final pmStore) 1004) := by rw [hout_read_0]
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
    change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] 2 [2, 1, 10, 3] [2, 1, 2, 3] at hx
    have hxV:smFinal 100=allGatherPrimDimN 2 5 0 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004]:=by simpa only [List.length_cons,List.length_nil] using hx.full_value
    have hSm:smFinal 200=fw_view [2, 1, 30] (smFinal 100):=segment_000000_hSmWriter smStore
    have hPm0:pmFinal 2000=fw_view [2, 1, 6] (pmFinal 1000):=segment_000000_hPmWriter0 pmStore
    have hPm1:pmFinal 2001=fw_view [2, 1, 6] (pmFinal 1001):=segment_000000_hPmWriter1 pmStore
    have hPm2:pmFinal 2002=fw_view [2, 1, 6] (pmFinal 1002):=segment_000000_hPmWriter2 pmStore
    have hPm3:pmFinal 2003=fw_view [2, 1, 6] (pmFinal 1003):=segment_000000_hPmWriter3 pmStore
    have hPm4:pmFinal 2004=fw_view [2, 1, 6] (pmFinal 1004):=segment_000000_hPmWriter4 pmStore
    have hcomm:=TrainVerify.Denote.fw_view_allGatherPrimDimN_dim2_rank4_to_rank3 5 2 1 2 3 [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004]
      (by decide) (by decide) (by decide) (by decide) (by decide) rfl hx.shard_shapes
    have hvalue:smFinal 200=allGatherPrimDimN 2 5 0 [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004]:=by
      rw [hSm,hxV,hcomm]
      simp only [List.map]
      rw [← hPm0, ← hPm1, ← hPm2, ← hPm3, ← hPm4]
    have hout:fact_out.Holds smFinal pmFinal:=by
      change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] 2 [2, 1, 30] [2, 1, 6]
      refine {full_value:=hvalue,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by decide,shard_shapes:=?_,shape_contract:=?_}
      · rw [hSm]; rfl
      · intro piece hmem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
        rcases hmem with h0 | h1 | h2 | h3 | h4
        · subst piece; rw [hPm0]; rfl
        · subst piece; rw [hPm1]; rfl
        · subst piece; rw [hPm2]; rfl
        · subst piece; rw [hPm3]; rfl
        · subst piece; rw [hPm4]; rfl
      · simp only [List.length_cons,List.length_nil]; native_decide
    intro fact hfact
    have covered:fact∈[fact_out]++state_000000.facts:=by
      exact (show state_000001.facts⊆[fact_out]++state_000000.facts by native_decide) hfact
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at covered
    rcases covered with rfl | old
    · exact hout
    · exact hframe fact old
private def segment_000000:ClosedDepSegmentCertificate ViewFlattenA2Case4.smGraph ViewFlattenA2Case4.pmGraph state_000000 state_000001 where
  smNodes:=segment_000000_sm_nodes
  pmNodes:=segment_000000_pm_nodes
  sound:=by intro smStore pmStore hstate; have h:=segment_000000_sound smStore pmStore hstate; unfold segment_000000_sm_final segment_000000_pm_final at h; exact h

#print axioms segment_000000
end
end ViewFlattenA2Case4
