import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticGelu
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_gelu", ins := [100], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_gelu", ins := [200], outs := [300] }, { rank := 1, op := "OpName.FW_gelu", ins := [201], outs := [301] }, { rank := 2, op := "OpName.FW_gelu", ins := [202], outs := [302] }] }

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 12, 5] [2, 4, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 12, 5] [2, 4, 5]
def state_pre : RelationState where facts := [fact_in]; nonempty := by decide
def state_post : RelationState where facts := [fact_out]; nonempty := by decide

private def segment_000051_smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_gelu", ins := [100], outs := [110] }]
private def segment_000051_pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_gelu", ins := [200], outs := [300] }, { rank := 1, op := "OpName.FW_gelu", ins := [201], outs := [301] }, { rank := 2, op := "OpName.FW_gelu", ins := [202], outs := [302] }]
@[irreducible] private def segment_000051_smFinal (s : Store) : Store :=
  segment_000051_smNodes.foldl (applyNodeDistributedFaithful SyntheticGelu.gSM) s
@[irreducible] private def segment_000051_pmFinal (s : Store) : Store :=
  segment_000051_pmNodes.foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) s

private theorem segment_000051_smWriter (smStore : Store) :
    (segment_000051_smFinal smStore) 110 = fw_gelu ((segment_000051_smFinal smStore) 100) := by
  have hfinal : (segment_000051_smFinal smStore) = segment_000051_smNodes.foldl (applyNodeDistributedFaithful SyntheticGelu.gSM) smStore := by
    unfold segment_000051_smFinal
    rfl
  have hout_nodes : segment_000051_smNodes = (segment_000051_smNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_gelu", ins := [100], outs := [110] }] ++ (segment_000051_smNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000051_smFinal smStore) 110 = fw_gelu (((segment_000051_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticGelu.gSM) smStore 100) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticGelu.gSM smStore
      (segment_000051_smNodes.take 0) (segment_000051_smNodes.drop 1)
      { rank := 0, op := "OpName.FW_gelu", ins := [100], outs := [110] } 110
      (fun t => fw_gelu (t 100)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_gelu_out SyntheticGelu.gSM t 0 100 110
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000051_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticGelu.gSM) smStore 100 = (segment_000051_smFinal smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticGelu.gSM smStore
      (segment_000051_smNodes.take 0) ({ rank := 0, op := "OpName.FW_gelu", ins := [100], outs := [110] } :: (segment_000051_smNodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout : (segment_000051_smFinal smStore) 110 = fw_gelu ((segment_000051_smFinal smStore) 100) := by
    calc
      _ = fw_gelu (((segment_000051_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticGelu.gSM) smStore 100) := hout_prefix
      _ = fw_gelu ((segment_000051_smFinal smStore) 100) := by rw [hout_read_0]
  exact hout

private theorem segment_000051_pmWriter0 (pmStore : Store) :
    (segment_000051_pmFinal pmStore) 300 = fw_gelu ((segment_000051_pmFinal pmStore) 200) := by
  have hfinal : (segment_000051_pmFinal pmStore) = segment_000051_pmNodes.foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore := by
    unfold segment_000051_pmFinal
    rfl
  have hout_nodes : segment_000051_pmNodes = (segment_000051_pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_gelu", ins := [200], outs := [300] }] ++ (segment_000051_pmNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000051_pmFinal pmStore) 300 = fw_gelu (((segment_000051_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore 200) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticGelu.gPM pmStore
      (segment_000051_pmNodes.take 0) (segment_000051_pmNodes.drop 1)
      { rank := 0, op := "OpName.FW_gelu", ins := [200], outs := [300] } 300
      (fun t => fw_gelu (t 200)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_gelu_out SyntheticGelu.gPM t 0 200 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000051_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore 200 = (segment_000051_pmFinal pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticGelu.gPM pmStore
      (segment_000051_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_gelu", ins := [200], outs := [300] } :: (segment_000051_pmNodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout : (segment_000051_pmFinal pmStore) 300 = fw_gelu ((segment_000051_pmFinal pmStore) 200) := by
    calc
      _ = fw_gelu (((segment_000051_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore 200) := hout_prefix
      _ = fw_gelu ((segment_000051_pmFinal pmStore) 200) := by rw [hout_read_0]
  exact hout

private theorem segment_000051_pmWriter1 (pmStore : Store) :
    (segment_000051_pmFinal pmStore) 301 = fw_gelu ((segment_000051_pmFinal pmStore) 201) := by
  have hfinal : (segment_000051_pmFinal pmStore) = segment_000051_pmNodes.foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore := by
    unfold segment_000051_pmFinal
    rfl
  have hout_nodes : segment_000051_pmNodes = (segment_000051_pmNodes.take 1) ++ [{ rank := 1, op := "OpName.FW_gelu", ins := [201], outs := [301] }] ++ (segment_000051_pmNodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000051_pmFinal pmStore) 301 = fw_gelu (((segment_000051_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore 201) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticGelu.gPM pmStore
      (segment_000051_pmNodes.take 1) (segment_000051_pmNodes.drop 2)
      { rank := 1, op := "OpName.FW_gelu", ins := [201], outs := [301] } 301
      (fun t => fw_gelu (t 201)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_gelu_out SyntheticGelu.gPM t 1 201 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000051_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore 201 = (segment_000051_pmFinal pmStore) 201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticGelu.gPM pmStore
      (segment_000051_pmNodes.take 1) ({ rank := 1, op := "OpName.FW_gelu", ins := [201], outs := [301] } :: (segment_000051_pmNodes.drop 2)) 201
      (by native_decide) (by native_decide)
  have hout : (segment_000051_pmFinal pmStore) 301 = fw_gelu ((segment_000051_pmFinal pmStore) 201) := by
    calc
      _ = fw_gelu (((segment_000051_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore 201) := hout_prefix
      _ = fw_gelu ((segment_000051_pmFinal pmStore) 201) := by rw [hout_read_0]
  exact hout

private theorem segment_000051_pmWriter2 (pmStore : Store) :
    (segment_000051_pmFinal pmStore) 302 = fw_gelu ((segment_000051_pmFinal pmStore) 202) := by
  have hfinal : (segment_000051_pmFinal pmStore) = segment_000051_pmNodes.foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore := by
    unfold segment_000051_pmFinal
    rfl
  have hout_nodes : segment_000051_pmNodes = (segment_000051_pmNodes.take 2) ++ [{ rank := 2, op := "OpName.FW_gelu", ins := [202], outs := [302] }] ++ (segment_000051_pmNodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000051_pmFinal pmStore) 302 = fw_gelu (((segment_000051_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore 202) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticGelu.gPM pmStore
      (segment_000051_pmNodes.take 2) (segment_000051_pmNodes.drop 3)
      { rank := 2, op := "OpName.FW_gelu", ins := [202], outs := [302] } 302
      (fun t => fw_gelu (t 202)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_gelu_out SyntheticGelu.gPM t 2 202 302
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000051_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore 202 = (segment_000051_pmFinal pmStore) 202 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticGelu.gPM pmStore
      (segment_000051_pmNodes.take 2) ({ rank := 2, op := "OpName.FW_gelu", ins := [202], outs := [302] } :: (segment_000051_pmNodes.drop 3)) 202
      (by native_decide) (by native_decide)
  have hout : (segment_000051_pmFinal pmStore) 302 = fw_gelu ((segment_000051_pmFinal pmStore) 202) := by
    calc
      _ = fw_gelu (((segment_000051_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticGelu.gPM) pmStore 202) := hout_prefix
      _ = fw_gelu ((segment_000051_pmFinal pmStore) 202) := by rw [hout_read_0]
  exact hout

private theorem segment_000051_out (smStore pmStore : Store)
    (hin : fact_in.Holds (segment_000051_smFinal smStore) (segment_000051_pmFinal pmStore)) :
    fact_out.Holds (segment_000051_smFinal smStore) (segment_000051_pmFinal pmStore) := by
  change ShardedRel ((segment_000051_smFinal smStore) 100) [(segment_000051_pmFinal pmStore) 200, (segment_000051_pmFinal pmStore) 201, (segment_000051_pmFinal pmStore) 202] 1 [2, 12, 5] [2, 4, 5] at hin
  have hSm := segment_000051_smWriter smStore
  have hPm0 := segment_000051_pmWriter0 pmStore
  have hPm1 := segment_000051_pmWriter1 pmStore
  have hPm2 := segment_000051_pmWriter2 pmStore
  have hcomm := TrainVerify.Denote.fw_gelu_allGatherPrimDimN_eq 1 [(segment_000051_pmFinal pmStore) 200, (segment_000051_pmFinal pmStore) 201, (segment_000051_pmFinal pmStore) 202].length [(segment_000051_pmFinal pmStore) 200, (segment_000051_pmFinal pmStore) 201, (segment_000051_pmFinal pmStore) 202] [2, 4, 5]
    (by simp) rfl
    (by simp only [List.head?, Option.map, Option.getD]; exact hin.shard_shapes _ (by simp))
    (by intro i hi; exact hin.shard_shapes _ (List.get_mem _ ⟨i, hi⟩))
  unfold fact_out RelationFact.Holds
  change ShardedRel ((segment_000051_smFinal smStore) 110) [(segment_000051_pmFinal pmStore) 300, (segment_000051_pmFinal pmStore) 301, (segment_000051_pmFinal pmStore) 302] 1 [2, 12, 5] [2, 4, 5]
  constructor
  · rw [hSm, hin.full_value, hcomm]
    simp only [List.map, List.length_cons, List.length_nil]
    rw [← hPm0, ← hPm1, ← hPm2]
  · rw [hSm, fw_gelu_shape]
    exact hin.full_shape
  · simp
  · exact hin.gather_dim_lt
  · intro shard hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h0 | h1 | h2
    · subst shard
      rw [hPm0, fw_gelu_shape]
      exact hin.shard_shapes ((segment_000051_pmFinal pmStore) 200) (by simp)
    · subst shard
      rw [hPm1, fw_gelu_shape]
      exact hin.shard_shapes ((segment_000051_pmFinal pmStore) 201) (by simp)
    · subst shard
      rw [hPm2, fw_gelu_shape]
      exact hin.shard_shapes ((segment_000051_pmFinal pmStore) 202) (by simp)
  · exact hin.shape_contract

private theorem segment_000051_sound (smStore pmStore : Store) (hstate : state_pre.Holds smStore pmStore) :
    state_post.Holds (segment_000051_smFinal smStore) (segment_000051_pmFinal pmStore) := by
  have hframe : state_pre.Holds (segment_000051_smFinal smStore) (segment_000051_pmFinal pmStore) := by
    unfold segment_000051_smFinal segment_000051_pmFinal
    apply RelationState.Holds.fold_frame segment_000051_smNodes segment_000051_pmNodes smStore pmStore hstate
    · native_decide
    · native_decide
    · native_decide
    · native_decide
  have hin := hframe fact_in (by native_decide)
  have hout := segment_000051_out smStore pmStore hin
  intro fact hfact
  have covered : fact ∈ [fact_out] ++ state_pre.facts := by
    exact (show state_post.facts ⊆ [fact_out] ++ state_pre.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000051 : ClosedDepSegmentCertificate SyntheticGelu.gSM SyntheticGelu.gPM state_pre state_post where
  smNodes := segment_000051_smNodes
  pmNodes := segment_000051_pmNodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000051_smFinal, segment_000051_pmFinal] using segment_000051_sound smStore pmStore hstate

#print axioms segment_000051
end
end SyntheticGelu
end TrainVerify.Denote
