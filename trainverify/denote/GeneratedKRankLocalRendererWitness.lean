import denote.RelationCompiler
import denote.KRankLinearGather
import denote.KRankLayernormGather

namespace TrainVerify.Denote
open RelationCompiler

namespace SyntheticLinear
noncomputable section

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 90], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 90], outs := [300] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 90], outs := [301] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 90], outs := [302] }] }

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 9, 5] [2, 3, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 9, 7] [2, 3, 7]
def external_eq_90 : RelationFact := .tensorEq .sm 90 .pm 90
def external_shape_90 : RelationFact := .tensorShape .pm 90 [7, 5]

def state_pre : RelationState where
  facts := [fact_in, external_eq_90, external_shape_90]
  nonempty := by decide

def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

private def segment_000000_smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 90], outs := [110] }]
private def segment_000000_pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 90], outs := [300] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 90], outs := [301] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 90], outs := [302] }]
@[irreducible] private def segment_000000_smFinal (s : Store) : Store :=
  segment_000000_smNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gSM) s
@[irreducible] private def segment_000000_pmFinal (s : Store) : Store :=
  segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) s

private theorem segment_000000_smWriter (smStore : Store) :
    (segment_000000_smFinal smStore) 110 = fw_linear ((segment_000000_smFinal smStore) 100) ((segment_000000_smFinal smStore) 90) := by
  have hfinal : (segment_000000_smFinal smStore) = segment_000000_smNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gSM) smStore := by
    unfold segment_000000_smFinal
    rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 90], outs := [110] }] ++ (segment_000000_smNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 110 = fw_linear (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gSM) smStore 100) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gSM) smStore 90) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLinear.gSM smStore
      (segment_000000_smNodes.take 0) (segment_000000_smNodes.drop 1)
      { rank := 0, op := "OpName.FW_linear", ins := [100, 90], outs := [110] } 110
      (fun t => fw_linear (t 100) (t 90)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out SyntheticLinear.gSM t 0 100 90 110
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gSM) smStore 100 = (segment_000000_smFinal smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinear.gSM smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [100, 90], outs := [110] } :: (segment_000000_smNodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gSM) smStore 90 = (segment_000000_smFinal smStore) 90 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinear.gSM smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [100, 90], outs := [110] } :: (segment_000000_smNodes.drop 1)) 90
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 110 = fw_linear ((segment_000000_smFinal smStore) 100) ((segment_000000_smFinal smStore) 90) := by
    calc
      _ = fw_linear (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gSM) smStore 100) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gSM) smStore 90) := hout_prefix
      _ = fw_linear ((segment_000000_smFinal smStore) 100) ((segment_000000_smFinal smStore) 90) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_pmWriter0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 300 = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 90) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [200, 90], outs := [300] }] ++ (segment_000000_pmNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 300 = fw_linear (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 200) (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 90) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLinear.gPM pmStore
      (segment_000000_pmNodes.take 0) (segment_000000_pmNodes.drop 1)
      { rank := 0, op := "OpName.FW_linear", ins := [200, 90], outs := [300] } 300
      (fun t => fw_linear (t 200) (t 90)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out SyntheticLinear.gPM t 0 200 90 300
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 200 = (segment_000000_pmFinal pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinear.gPM pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [200, 90], outs := [300] } :: (segment_000000_pmNodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 90 = (segment_000000_pmFinal pmStore) 90 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinear.gPM pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [200, 90], outs := [300] } :: (segment_000000_pmNodes.drop 1)) 90
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 300 = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 90) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 200) (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 90) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 90) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_pmWriter1 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 301 = fw_linear ((segment_000000_pmFinal pmStore) 201) ((segment_000000_pmFinal pmStore) 90) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 1) ++ [{ rank := 1, op := "OpName.FW_linear", ins := [201, 90], outs := [301] }] ++ (segment_000000_pmNodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 301 = fw_linear (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 201) (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 90) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLinear.gPM pmStore
      (segment_000000_pmNodes.take 1) (segment_000000_pmNodes.drop 2)
      { rank := 1, op := "OpName.FW_linear", ins := [201, 90], outs := [301] } 301
      (fun t => fw_linear (t 201) (t 90)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out SyntheticLinear.gPM t 1 201 90 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 201 = (segment_000000_pmFinal pmStore) 201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinear.gPM pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 1, op := "OpName.FW_linear", ins := [201, 90], outs := [301] } :: (segment_000000_pmNodes.drop 2)) 201
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 90 = (segment_000000_pmFinal pmStore) 90 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinear.gPM pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 1, op := "OpName.FW_linear", ins := [201, 90], outs := [301] } :: (segment_000000_pmNodes.drop 2)) 90
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 301 = fw_linear ((segment_000000_pmFinal pmStore) 201) ((segment_000000_pmFinal pmStore) 90) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 201) (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 90) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 201) ((segment_000000_pmFinal pmStore) 90) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_pmWriter2 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 302 = fw_linear ((segment_000000_pmFinal pmStore) 202) ((segment_000000_pmFinal pmStore) 90) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 2) ++ [{ rank := 2, op := "OpName.FW_linear", ins := [202, 90], outs := [302] }] ++ (segment_000000_pmNodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 302 = fw_linear (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 202) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 90) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLinear.gPM pmStore
      (segment_000000_pmNodes.take 2) (segment_000000_pmNodes.drop 3)
      { rank := 2, op := "OpName.FW_linear", ins := [202, 90], outs := [302] } 302
      (fun t => fw_linear (t 202) (t 90)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out SyntheticLinear.gPM t 2 202 90 302
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 202 = (segment_000000_pmFinal pmStore) 202 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinear.gPM pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 2, op := "OpName.FW_linear", ins := [202, 90], outs := [302] } :: (segment_000000_pmNodes.drop 3)) 202
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 90 = (segment_000000_pmFinal pmStore) 90 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinear.gPM pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 2, op := "OpName.FW_linear", ins := [202, 90], outs := [302] } :: (segment_000000_pmNodes.drop 3)) 90
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 302 = fw_linear ((segment_000000_pmFinal pmStore) 202) ((segment_000000_pmFinal pmStore) 90) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 202) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore 90) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 202) ((segment_000000_pmFinal pmStore) 90) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_out (smStore pmStore : Store)
    (hin : fact_in.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore))
    (heq : external_eq_90.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore))
    (hshape : external_shape_90.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)) :
    fact_out.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  change ShardedRel ((segment_000000_smFinal smStore) 100) [(segment_000000_pmFinal pmStore) 200, (segment_000000_pmFinal pmStore) 201, (segment_000000_pmFinal pmStore) 202] 1 [2, 9, 5] [2, 3, 5] at hin
  change (segment_000000_smFinal smStore) 90 = (segment_000000_pmFinal pmStore) 90 at heq
  change ((segment_000000_pmFinal pmStore) 90).shape = [7, 5] at hshape
  have hSm := segment_000000_smWriter smStore
  have hPm0 := segment_000000_pmWriter0 pmStore
  have hPm1 := segment_000000_pmWriter1 pmStore
  have hPm2 := segment_000000_pmWriter2 pmStore
  have hComm := TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [(segment_000000_pmFinal pmStore) 200, (segment_000000_pmFinal pmStore) 201, (segment_000000_pmFinal pmStore) 202].length) (b := 2) (s := 3) (i := 5) (o := 7)
    (xs := [(segment_000000_pmFinal pmStore) 200, (segment_000000_pmFinal pmStore) 201, (segment_000000_pmFinal pmStore) 202]) (w := (segment_000000_pmFinal pmStore) 90)
    (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hin.shard_shapes x hx) hshape
  have hValue : (segment_000000_smFinal smStore) 110 = allGatherPrimDimN 1 [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302].length 0 [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302] := by
    rw [hSm, heq, hin.full_value, hComm]
    simp only [List.map, List.length_cons, List.length_nil]
    rw [← hPm0, ← hPm1, ← hPm2]
  have hOutShape0 : ((segment_000000_pmFinal pmStore) 300).shape = [2, 3, 7] := by
    rw [hPm0]
    exact fw_linear_3d_shape 2 3 5 7 _ _
      (hin.shard_shapes ((segment_000000_pmFinal pmStore) 200) (by simp)) hshape
  have hOutShape1 : ((segment_000000_pmFinal pmStore) 301).shape = [2, 3, 7] := by
    rw [hPm1]
    exact fw_linear_3d_shape 2 3 5 7 _ _
      (hin.shard_shapes ((segment_000000_pmFinal pmStore) 201) (by simp)) hshape
  have hOutShape2 : ((segment_000000_pmFinal pmStore) 302).shape = [2, 3, 7] := by
    rw [hPm2]
    exact fw_linear_3d_shape 2 3 5 7 _ _
      (hin.shard_shapes ((segment_000000_pmFinal pmStore) 202) (by simp)) hshape
  unfold fact_out RelationFact.Holds
  change ShardedRel ((segment_000000_smFinal smStore) 110) [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302] 1 [2, 9, 7] [2, 3, 7]
  refine {
    full_value := hValue
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  · rw [hValue]
    rw [allGatherPrimDimN_shape 1 [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302].length [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302] [2, 3, 7]]
    · norm_num [List.set, List.getD]
    · simp only [List.head?, Option.map, Option.getD]; exact hOutShape0
  · intro shard hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hOutShape0
    · exact hOutShape1
    · exact hOutShape2

private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_pre.Holds smStore pmStore) :
    state_post.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  have hframe : state_pre.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
    unfold segment_000000_smFinal segment_000000_pmFinal
    apply RelationState.Holds.fold_frame segment_000000_smNodes segment_000000_pmNodes smStore pmStore hstate
    · native_decide
    · native_decide
    · native_decide
    · native_decide
  have hin := hframe fact_in (by native_decide)
  have heq := hframe external_eq_90 (by native_decide)
  have hshape := hframe external_shape_90 (by native_decide)
  have hout := segment_000000_out smStore pmStore hin heq hshape
  intro fact hfact
  have covered : fact ∈ [fact_out] ++ state_pre.facts := by
    exact (show state_post.facts ⊆ [fact_out] ++ state_pre.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SyntheticLinear.gSM SyntheticLinear.gPM state_pre state_post where
  smNodes := segment_000000_smNodes
  pmNodes := segment_000000_pmNodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000000_smFinal, segment_000000_pmFinal] using segment_000000_sound smStore pmStore hstate

#check segment_000000
end
end SyntheticLinear

namespace SyntheticLayernorm
noncomputable section

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] }, { rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] }, { rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] }] }

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 9, 5] [2, 3, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 9, 5] [2, 3, 5]
def external_eq_91 : RelationFact := .tensorEq .sm 91 .pm 91
def external_shape_91 : RelationFact := .tensorShape .pm 91 [5]
def external_eq_92 : RelationFact := .tensorEq .sm 92 .pm 92
def external_shape_92 : RelationFact := .tensorShape .pm 92 [5]

def state_pre : RelationState where
  facts := [fact_in, external_eq_91, external_shape_91, external_eq_92, external_shape_92]
  nonempty := by decide

def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

private def segment_000000_smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] }]
private def segment_000000_pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] }, { rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] }, { rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] }]
@[irreducible] private def segment_000000_smFinal (s : Store) : Store :=
  segment_000000_smNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) s
@[irreducible] private def segment_000000_pmFinal (s : Store) : Store :=
  segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) s

private theorem segment_000000_smWriter (smStore : Store) :
    (segment_000000_smFinal smStore) 110 = fw_layernorm ((segment_000000_smFinal smStore) 100) ((segment_000000_smFinal smStore) 91) ((segment_000000_smFinal smStore) 92) := by
  have hfinal : (segment_000000_smFinal smStore) = segment_000000_smNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore := by
    unfold segment_000000_smFinal
    rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] }] ++ (segment_000000_smNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 110 = fw_layernorm (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore 100) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore 91) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore 92) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLayernorm.gSM smStore
      (segment_000000_smNodes.take 0) (segment_000000_smNodes.drop 1)
      { rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] } 110
      (fun t => fw_layernorm (t 100) (t 91) (t 92)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_layernorm_out SyntheticLayernorm.gSM t 0 100 91 92 110 []
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore 100 = (segment_000000_smFinal smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gSM smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] } :: (segment_000000_smNodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore 91 = (segment_000000_smFinal smStore) 91 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gSM smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] } :: (segment_000000_smNodes.drop 1)) 91
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore 92 = (segment_000000_smFinal smStore) 92 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gSM smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] } :: (segment_000000_smNodes.drop 1)) 92
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 110 = fw_layernorm ((segment_000000_smFinal smStore) 100) ((segment_000000_smFinal smStore) 91) ((segment_000000_smFinal smStore) 92) := by
    calc
      _ = fw_layernorm (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore 100) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore 91) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore 92) := hout_prefix
      _ = fw_layernorm ((segment_000000_smFinal smStore) 100) ((segment_000000_smFinal smStore) 91) ((segment_000000_smFinal smStore) 92) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_pmWriter0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 300 = fw_layernorm ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 91) ((segment_000000_pmFinal pmStore) 92) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] }] ++ (segment_000000_pmNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 300 = fw_layernorm (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 200) (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 91) (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 92) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 0) (segment_000000_pmNodes.drop 1)
      { rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] } 300
      (fun t => fw_layernorm (t 200) (t 91) (t 92)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_layernorm_out SyntheticLayernorm.gPM t 0 200 91 92 300 []
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 200 = (segment_000000_pmFinal pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] } :: (segment_000000_pmNodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 91 = (segment_000000_pmFinal pmStore) 91 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] } :: (segment_000000_pmNodes.drop 1)) 91
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 92 = (segment_000000_pmFinal pmStore) 92 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] } :: (segment_000000_pmNodes.drop 1)) 92
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 300 = fw_layernorm ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 91) ((segment_000000_pmFinal pmStore) 92) := by
    calc
      _ = fw_layernorm (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 200) (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 91) (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 92) := hout_prefix
      _ = fw_layernorm ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 91) ((segment_000000_pmFinal pmStore) 92) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_pmWriter1 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 301 = fw_layernorm ((segment_000000_pmFinal pmStore) 201) ((segment_000000_pmFinal pmStore) 91) ((segment_000000_pmFinal pmStore) 92) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 1) ++ [{ rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] }] ++ (segment_000000_pmNodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 301 = fw_layernorm (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 201) (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 91) (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 92) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 1) (segment_000000_pmNodes.drop 2)
      { rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] } 301
      (fun t => fw_layernorm (t 201) (t 91) (t 92)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_layernorm_out SyntheticLayernorm.gPM t 1 201 91 92 301 []
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 201 = (segment_000000_pmFinal pmStore) 201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] } :: (segment_000000_pmNodes.drop 2)) 201
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 91 = (segment_000000_pmFinal pmStore) 91 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] } :: (segment_000000_pmNodes.drop 2)) 91
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 92 = (segment_000000_pmFinal pmStore) 92 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] } :: (segment_000000_pmNodes.drop 2)) 92
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 301 = fw_layernorm ((segment_000000_pmFinal pmStore) 201) ((segment_000000_pmFinal pmStore) 91) ((segment_000000_pmFinal pmStore) 92) := by
    calc
      _ = fw_layernorm (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 201) (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 91) (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 92) := hout_prefix
      _ = fw_layernorm ((segment_000000_pmFinal pmStore) 201) ((segment_000000_pmFinal pmStore) 91) ((segment_000000_pmFinal pmStore) 92) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_pmWriter2 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 302 = fw_layernorm ((segment_000000_pmFinal pmStore) 202) ((segment_000000_pmFinal pmStore) 91) ((segment_000000_pmFinal pmStore) 92) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 2) ++ [{ rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] }] ++ (segment_000000_pmNodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 302 = fw_layernorm (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 202) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 91) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 92) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 2) (segment_000000_pmNodes.drop 3)
      { rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] } 302
      (fun t => fw_layernorm (t 202) (t 91) (t 92)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_layernorm_out SyntheticLayernorm.gPM t 2 202 91 92 302 []
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 202 = (segment_000000_pmFinal pmStore) 202 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] } :: (segment_000000_pmNodes.drop 3)) 202
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 91 = (segment_000000_pmFinal pmStore) 91 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] } :: (segment_000000_pmNodes.drop 3)) 91
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 92 = (segment_000000_pmFinal pmStore) 92 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLayernorm.gPM pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] } :: (segment_000000_pmNodes.drop 3)) 92
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 302 = fw_layernorm ((segment_000000_pmFinal pmStore) 202) ((segment_000000_pmFinal pmStore) 91) ((segment_000000_pmFinal pmStore) 92) := by
    calc
      _ = fw_layernorm (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 202) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 91) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore 92) := hout_prefix
      _ = fw_layernorm ((segment_000000_pmFinal pmStore) 202) ((segment_000000_pmFinal pmStore) 91) ((segment_000000_pmFinal pmStore) 92) := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_out (smStore pmStore : Store)
    (hin : fact_in.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore))
    (heq0 : (segment_000000_smFinal smStore) 91 = (segment_000000_pmFinal pmStore) 91)
    (hshape0 : ((segment_000000_pmFinal pmStore) 91).shape = [5])
    (heq1 : (segment_000000_smFinal smStore) 92 = (segment_000000_pmFinal pmStore) 92)
    (hshape1 : ((segment_000000_pmFinal pmStore) 92).shape = [5])
    : fact_out.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  change ShardedRel ((segment_000000_smFinal smStore) 100) [(segment_000000_pmFinal pmStore) 200, (segment_000000_pmFinal pmStore) 201, (segment_000000_pmFinal pmStore) 202] 1 [2, 9, 5] [2, 3, 5] at hin
  have hSm := segment_000000_smWriter smStore
  have hPm0 := segment_000000_pmWriter0 pmStore
  have hPm1 := segment_000000_pmWriter1 pmStore
  have hPm2 := segment_000000_pmWriter2 pmStore
  have hComm := TrainVerify.Denote.fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d (K := [(segment_000000_pmFinal pmStore) 200, (segment_000000_pmFinal pmStore) 201, (segment_000000_pmFinal pmStore) 202].length) (b := 2) (s := 3) (d := 5)
    (xs := [(segment_000000_pmFinal pmStore) 200, (segment_000000_pmFinal pmStore) 201, (segment_000000_pmFinal pmStore) 202]) (gamma := (segment_000000_pmFinal pmStore) 91)
    (beta := (segment_000000_pmFinal pmStore) 92) (by simp) (by omega) (by omega) (by omega)
    rfl (fun x hx => hin.shard_shapes x hx) hshape0 hshape1
  have hValue : (segment_000000_smFinal smStore) 110 = allGatherPrimDimN 1 [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302].length 0 [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302] := by
    rw [hSm]
    rw [heq0, heq1, hin.full_value, hComm]
    simp only [List.map, List.length_cons, List.length_nil]
    rw [← hPm0, ← hPm1, ← hPm2]
  have hOutShape0 : ((segment_000000_pmFinal pmStore) 300).shape = [2, 3, 5] := by
    rw [hPm0]
    unfold fw_layernorm
    rw [hin.shard_shapes ((segment_000000_pmFinal pmStore) 200) (by simp)]
    rfl
  have hOutShape1 : ((segment_000000_pmFinal pmStore) 301).shape = [2, 3, 5] := by
    rw [hPm1]
    unfold fw_layernorm
    rw [hin.shard_shapes ((segment_000000_pmFinal pmStore) 201) (by simp)]
    rfl
  have hOutShape2 : ((segment_000000_pmFinal pmStore) 302).shape = [2, 3, 5] := by
    rw [hPm2]
    unfold fw_layernorm
    rw [hin.shard_shapes ((segment_000000_pmFinal pmStore) 202) (by simp)]
    rfl
  unfold fact_out RelationFact.Holds
  change ShardedRel ((segment_000000_smFinal smStore) 110) [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302] 1 [2, 9, 5] [2, 3, 5]
  refine {
    full_value := hValue
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by native_decide
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  · rw [hValue]
    rw [allGatherPrimDimN_shape 1 [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302].length [(segment_000000_pmFinal pmStore) 300, (segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302] [2, 3, 5]]
    · norm_num [List.set, List.getD]
    · simp only [List.head?, Option.map, Option.getD]; exact hOutShape0
  · intro shard hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hOutShape0
    · exact hOutShape1
    · exact hOutShape2

private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_pre.Holds smStore pmStore) :
    state_post.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  have hframe : state_pre.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
    unfold segment_000000_smFinal segment_000000_pmFinal
    apply RelationState.Holds.fold_frame segment_000000_smNodes segment_000000_pmNodes smStore pmStore hstate
    · native_decide
    · native_decide
    · native_decide
    · native_decide
  have hin := hframe fact_in (by native_decide)
  have heq0 := hframe external_eq_91 (by native_decide)
  unfold external_eq_91 RelationFact.Holds at heq0
  have hshape0 := hframe external_shape_91 (by native_decide)
  unfold external_shape_91 RelationFact.Holds at hshape0
  have heq1 := hframe external_eq_92 (by native_decide)
  unfold external_eq_92 RelationFact.Holds at heq1
  have hshape1 := hframe external_shape_92 (by native_decide)
  unfold external_shape_92 RelationFact.Holds at hshape1
  have hout := segment_000000_out smStore pmStore hin heq0 hshape0 heq1 hshape1
  intro fact hfact
  have covered : fact ∈ [fact_out] ++ state_pre.facts := by
    exact (show state_post.facts ⊆ [fact_out] ++ state_pre.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SyntheticLayernorm.gSM SyntheticLayernorm.gPM state_pre state_post where
  smNodes := segment_000000_smNodes
  pmNodes := segment_000000_pmNodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000000_smFinal, segment_000000_pmFinal] using segment_000000_sound smStore pmStore hstate

#check segment_000000
end
end SyntheticLayernorm

end TrainVerify.Denote
