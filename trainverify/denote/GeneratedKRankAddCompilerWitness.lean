import denote.KRankAddGather
import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticAdd
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_add", ins := [100, 110], outs := [120] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_add", ins := [200, 210], outs := [300] }, { rank := 1, op := "OpName.FW_add", ins := [201, 211], outs := [301] }, { rank := 2, op := "OpName.FW_add", ins := [202, 212], outs := [302] }] }

def fact_a : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 12, 5] [2, 4, 5]
def fact_b : RelationFact := .sharded 110 [210, 211, 212] 1 [2, 12, 5] [2, 4, 5]
def fact_out : RelationFact := .sharded 120 [300, 301, 302] 1 [2, 12, 5] [2, 4, 5]
def state_pre : RelationState where facts := [fact_a, fact_b]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

private def segment_000004_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_add", ins := [100, 110], outs := [120] }]
private def segment_000004_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_add", ins := [200, 210], outs := [300] }, { rank := 1, op := "OpName.FW_add", ins := [201, 211], outs := [301] }, { rank := 2, op := "OpName.FW_add", ins := [202, 212], outs := [302] }]
@[irreducible] private def segment_000004_sm_final (store : Store) : Store :=
  segment_000004_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticAdd.gSM) store
@[irreducible] private def segment_000004_pm_final (store : Store) : Store :=
  segment_000004_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) store

private theorem segment_000004_hSmWriter (smStore : Store) :
    (segment_000004_sm_final smStore) 120 = elemwiseAdd ((segment_000004_sm_final smStore) 100) ((segment_000004_sm_final smStore) 110) := by
  have hfinal : (segment_000004_sm_final smStore) = segment_000004_sm_nodes.foldl (applyNodeDistributedFaithful SyntheticAdd.gSM) smStore := by
    unfold segment_000004_sm_final
    rfl
  have hout_nodes : segment_000004_sm_nodes = (segment_000004_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.FW_add", ins := [100, 110], outs := [120] }] ++ (segment_000004_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000004_sm_final smStore) 120 = elemwiseAdd (((segment_000004_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gSM) smStore 100) (((segment_000004_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gSM) smStore 110) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticAdd.gSM smStore
      (segment_000004_sm_nodes.take 0) (segment_000004_sm_nodes.drop 1)
      { rank := 0, op := "OpName.FW_add", ins := [100, 110], outs := [120] } 120
      (fun t => elemwiseAdd (t 100) (t 110)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_add2_out SyntheticAdd.gSM t 0 100 110 120
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000004_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gSM) smStore 100 = (segment_000004_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticAdd.gSM smStore
      (segment_000004_sm_nodes.take 0) ({ rank := 0, op := "OpName.FW_add", ins := [100, 110], outs := [120] } :: (segment_000004_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000004_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gSM) smStore 110 = (segment_000004_sm_final smStore) 110 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticAdd.gSM smStore
      (segment_000004_sm_nodes.take 0) ({ rank := 0, op := "OpName.FW_add", ins := [100, 110], outs := [120] } :: (segment_000004_sm_nodes.drop 1)) 110
      (by native_decide) (by native_decide)
  have hout : (segment_000004_sm_final smStore) 120 = elemwiseAdd ((segment_000004_sm_final smStore) 100) ((segment_000004_sm_final smStore) 110) := by
    calc
      _ = elemwiseAdd (((segment_000004_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gSM) smStore 100) (((segment_000004_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gSM) smStore 110) := hout_prefix
      _ = elemwiseAdd ((segment_000004_sm_final smStore) 100) ((segment_000004_sm_final smStore) 110) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000004_hPmWriter0 (pmStore : Store) :
    (segment_000004_pm_final pmStore) 300 = elemwiseAdd ((segment_000004_pm_final pmStore) 200) ((segment_000004_pm_final pmStore) 210) := by
  have hfinal : (segment_000004_pm_final pmStore) = segment_000004_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore := by
    unfold segment_000004_pm_final
    rfl
  have hout_nodes : segment_000004_pm_nodes = (segment_000004_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.FW_add", ins := [200, 210], outs := [300] }] ++ (segment_000004_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000004_pm_final pmStore) 300 = elemwiseAdd (((segment_000004_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 200) (((segment_000004_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 210) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticAdd.gPM pmStore
      (segment_000004_pm_nodes.take 0) (segment_000004_pm_nodes.drop 1)
      { rank := 0, op := "OpName.FW_add", ins := [200, 210], outs := [300] } 300
      (fun t => elemwiseAdd (t 200) (t 210)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_add2_out SyntheticAdd.gPM t 0 200 210 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000004_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 200 = (segment_000004_pm_final pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticAdd.gPM pmStore
      (segment_000004_pm_nodes.take 0) ({ rank := 0, op := "OpName.FW_add", ins := [200, 210], outs := [300] } :: (segment_000004_pm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000004_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 210 = (segment_000004_pm_final pmStore) 210 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticAdd.gPM pmStore
      (segment_000004_pm_nodes.take 0) ({ rank := 0, op := "OpName.FW_add", ins := [200, 210], outs := [300] } :: (segment_000004_pm_nodes.drop 1)) 210
      (by native_decide) (by native_decide)
  have hout : (segment_000004_pm_final pmStore) 300 = elemwiseAdd ((segment_000004_pm_final pmStore) 200) ((segment_000004_pm_final pmStore) 210) := by
    calc
      _ = elemwiseAdd (((segment_000004_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 200) (((segment_000004_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 210) := hout_prefix
      _ = elemwiseAdd ((segment_000004_pm_final pmStore) 200) ((segment_000004_pm_final pmStore) 210) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000004_hPmWriter1 (pmStore : Store) :
    (segment_000004_pm_final pmStore) 301 = elemwiseAdd ((segment_000004_pm_final pmStore) 201) ((segment_000004_pm_final pmStore) 211) := by
  have hfinal : (segment_000004_pm_final pmStore) = segment_000004_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore := by
    unfold segment_000004_pm_final
    rfl
  have hout_nodes : segment_000004_pm_nodes = (segment_000004_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.FW_add", ins := [201, 211], outs := [301] }] ++ (segment_000004_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000004_pm_final pmStore) 301 = elemwiseAdd (((segment_000004_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 201) (((segment_000004_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 211) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticAdd.gPM pmStore
      (segment_000004_pm_nodes.take 1) (segment_000004_pm_nodes.drop 2)
      { rank := 1, op := "OpName.FW_add", ins := [201, 211], outs := [301] } 301
      (fun t => elemwiseAdd (t 201) (t 211)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_add2_out SyntheticAdd.gPM t 1 201 211 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000004_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 201 = (segment_000004_pm_final pmStore) 201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticAdd.gPM pmStore
      (segment_000004_pm_nodes.take 1) ({ rank := 1, op := "OpName.FW_add", ins := [201, 211], outs := [301] } :: (segment_000004_pm_nodes.drop 2)) 201
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000004_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 211 = (segment_000004_pm_final pmStore) 211 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticAdd.gPM pmStore
      (segment_000004_pm_nodes.take 1) ({ rank := 1, op := "OpName.FW_add", ins := [201, 211], outs := [301] } :: (segment_000004_pm_nodes.drop 2)) 211
      (by native_decide) (by native_decide)
  have hout : (segment_000004_pm_final pmStore) 301 = elemwiseAdd ((segment_000004_pm_final pmStore) 201) ((segment_000004_pm_final pmStore) 211) := by
    calc
      _ = elemwiseAdd (((segment_000004_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 201) (((segment_000004_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 211) := hout_prefix
      _ = elemwiseAdd ((segment_000004_pm_final pmStore) 201) ((segment_000004_pm_final pmStore) 211) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000004_hPmWriter2 (pmStore : Store) :
    (segment_000004_pm_final pmStore) 302 = elemwiseAdd ((segment_000004_pm_final pmStore) 202) ((segment_000004_pm_final pmStore) 212) := by
  have hfinal : (segment_000004_pm_final pmStore) = segment_000004_pm_nodes.foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore := by
    unfold segment_000004_pm_final
    rfl
  have hout_nodes : segment_000004_pm_nodes = (segment_000004_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.FW_add", ins := [202, 212], outs := [302] }] ++ (segment_000004_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000004_pm_final pmStore) 302 = elemwiseAdd (((segment_000004_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 202) (((segment_000004_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 212) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticAdd.gPM pmStore
      (segment_000004_pm_nodes.take 2) (segment_000004_pm_nodes.drop 3)
      { rank := 2, op := "OpName.FW_add", ins := [202, 212], outs := [302] } 302
      (fun t => elemwiseAdd (t 202) (t 212)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_add2_out SyntheticAdd.gPM t 2 202 212 302
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000004_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 202 = (segment_000004_pm_final pmStore) 202 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticAdd.gPM pmStore
      (segment_000004_pm_nodes.take 2) ({ rank := 2, op := "OpName.FW_add", ins := [202, 212], outs := [302] } :: (segment_000004_pm_nodes.drop 3)) 202
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000004_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 212 = (segment_000004_pm_final pmStore) 212 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticAdd.gPM pmStore
      (segment_000004_pm_nodes.take 2) ({ rank := 2, op := "OpName.FW_add", ins := [202, 212], outs := [302] } :: (segment_000004_pm_nodes.drop 3)) 212
      (by native_decide) (by native_decide)
  have hout : (segment_000004_pm_final pmStore) 302 = elemwiseAdd ((segment_000004_pm_final pmStore) 202) ((segment_000004_pm_final pmStore) 212) := by
    calc
      _ = elemwiseAdd (((segment_000004_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 202) (((segment_000004_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticAdd.gPM) pmStore 212) := hout_prefix
      _ = elemwiseAdd ((segment_000004_pm_final pmStore) 202) ((segment_000004_pm_final pmStore) 212) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000004_sound (smStore pmStore : Store)
    (hstate : state_pre.Holds smStore pmStore) :
    state_post.Holds (segment_000004_sm_final smStore) (segment_000004_pm_final pmStore) := by
    let smFinal := segment_000004_sm_final smStore
    let pmFinal := segment_000004_pm_final pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      unfold smFinal pmFinal segment_000004_sm_final segment_000004_pm_final
      apply RelationState.Holds.fold_frame segment_000004_sm_nodes segment_000004_pm_nodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have ha : fact_a.Holds smFinal pmFinal := hframe _ (by native_decide)
    have hb : fact_b.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 100) [pmFinal 200, pmFinal 201, pmFinal 202] 1 [2, 12, 5] [2, 4, 5] at ha
    change ShardedRel (smFinal 110) [pmFinal 210, pmFinal 211, pmFinal 212] 1 [2, 12, 5] [2, 4, 5] at hb
    have hSmWriter : smFinal 120 =
        elemwiseAdd (smFinal 100) (smFinal 110) := by
      exact segment_000004_hSmWriter smStore
    have hPmWriter0 : pmFinal 300 =
        elemwiseAdd (pmFinal 200) (pmFinal 210) := by
      exact segment_000004_hPmWriter0 pmStore
    have hPmWriter1 : pmFinal 301 =
        elemwiseAdd (pmFinal 201) (pmFinal 211) := by
      exact segment_000004_hPmWriter1 pmStore
    have hPmWriter2 : pmFinal 302 =
        elemwiseAdd (pmFinal 202) (pmFinal 212) := by
      exact segment_000004_hPmWriter2 pmStore
    have hcomm := fw_add_allGather_dim_K 1 [2, 4, 5] [pmFinal 200, pmFinal 201, pmFinal 202] [pmFinal 210, pmFinal 211, pmFinal 212]
      ha.shards_nonempty (by simp) ha.gather_dim_lt
      (fun r hr => ha.shard_shapes _ (List.get_mem _ ⟨r, hr⟩))
      (fun r hr => hb.shard_shapes _ (List.get_mem _ ⟨r, hr⟩))
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 120) [pmFinal 300, pmFinal 301, pmFinal 302] 1 [2, 12, 5] [2, 4, 5]
      constructor
      · rw [hSmWriter, ha.full_value, hb.full_value, hcomm]
        simp only [List.zipWith, List.length_cons, List.length_nil]
        rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
      · rw [hSmWriter]
        exact elemwiseAdd_shape_of_shapes _ _ [2, 12, 5] ha.full_shape hb.full_shape
      · simp
      · exact ha.gather_dim_lt
      · intro shard hmem
        have hAShape0 := ha.shard_shapes (pmFinal 200) (by simp)
        have hBShape0 := hb.shard_shapes (pmFinal 210) (by simp)
        have hAShape1 := ha.shard_shapes (pmFinal 201) (by simp)
        have hBShape1 := hb.shard_shapes (pmFinal 211) (by simp)
        have hAShape2 := ha.shard_shapes (pmFinal 202) (by simp)
        have hBShape2 := hb.shard_shapes (pmFinal 212) (by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h0 | h1 | h2
        · subst shard
          rw [hPmWriter0]
          exact elemwiseAdd_shape_of_shapes _ _ [2, 4, 5] hAShape0 hBShape0
        · subst shard
          rw [hPmWriter1]
          exact elemwiseAdd_shape_of_shapes _ _ [2, 4, 5] hAShape1 hBShape1
        · subst shard
          rw [hPmWriter2]
          exact elemwiseAdd_shape_of_shapes _ _ [2, 4, 5] hAShape2 hBShape2
      · exact ha.shape_contract
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_out] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

private def segment_000004 :
    ClosedDepSegmentCertificate SyntheticAdd.gSM SyntheticAdd.gPM state_pre state_post where
  smNodes := segment_000004_sm_nodes
  pmNodes := segment_000004_pm_nodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000004_sm_final, segment_000004_pm_final] using segment_000004_sound smStore pmStore hstate

#print axioms segment_000004
end
end SyntheticAdd
end TrainVerify.Denote
