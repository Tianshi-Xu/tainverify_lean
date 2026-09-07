import denote.GraphGears
import denote.RelationCompiler
import denote.KRankBWLayernormParam
open TrainVerify.Denote
namespace BWLayernormParamGraphK1B2S3D7Dgamma
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_layernorm", ins := [1, 2, 3, 4], outs := [10, 11, 12] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }] }
def pm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [105], outs := [106] }, { rank := 0, op := "OpName.BW_layernorm", ins := [100, 101, 3, 4], outs := [102, 103, 104] }, { rank := 0, op := "OpName.FW_float", ins := [105], outs := [107] }] }
end BWLayernormParamGraphK1B2S3D7Dgamma
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWLayernormParamK1B2S3D7Dgamma

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100] 1 [2, 3, 7] [2, 3, 7]

private def fact_x : RelationFact :=
  .sharded 2 [101] 1 [2, 3, 7] [2, 3, 7]

private def fact_gamma : RelationFact :=
  .sharded 3 [3] 0 [7] [7]

private def fact_beta : RelationFact :=
  .sharded 4 [4] 0 [7] [7]

private def fact_dgamma : RelationFact :=
  .reduction 11 [103] [7]

private def public_anchor : RelationFact :=
  .tensorShape .sm 3 [7]

private def state_before : RelationState where
  facts := [fact_g, fact_x, fact_gamma, fact_beta, public_anchor]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_x, fact_gamma, fact_beta, fact_dgamma, public_anchor]
  nonempty := by decide

set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_layernorm", ins := [1, 2, 3, 4], outs := [10, 11, 12] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [105], outs := [106] }, { rank := 0, op := "OpName.BW_layernorm", ins := [100, 101, 3, 4], outs := [102, 103, 104] }, { rank := 0, op := "OpName.FW_float", ins := [105], outs := [107] }]
@[irreducible] private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK1B2S3D7Dgamma.sm) store
@[irreducible] private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK1B2S3D7Dgamma.pm) store

set_option maxHeartbeats 500000 in
private theorem segment_000000_four_input_middle_writer
    (g : GraphDecl) (fullnodes before after : List NodeDecl)
    (initialStore finalStore : Store) (target : NodeDecl)
    (in0 in1 in2 in3 output : Tid)
    (f : Tensor → Tensor → Tensor → Tensor → Tensor)
    (hnodes : fullnodes = before ++ [target] ++ after)
    (hfinal : finalStore = fullnodes.foldl (applyNodeDistributedFaithful g) initialStore)
    (happly : ∀ t, applyNodeDistributedFaithful g t target output =
      f (t in0) (t in1) (t in2) (t in3))
    (hAfterNil : ∀ n ∈ after, n.outs ≠ [])
    (hAfterOutput : ∀ n ∈ after, output ∉ n.outs)
    (h0nil : ∀ n ∈ target :: after, n.outs ≠ [])
    (h0 : ∀ n ∈ target :: after, in0 ∉ n.outs)
    (h1nil : ∀ n ∈ target :: after, n.outs ≠ [])
    (h1 : ∀ n ∈ target :: after, in1 ∉ n.outs)
    (h2nil : ∀ n ∈ target :: after, n.outs ≠ [])
    (h2 : ∀ n ∈ target :: after, in2 ∉ n.outs)
    (h3nil : ∀ n ∈ target :: after, n.outs ≠ [])
    (h3 : ∀ n ∈ target :: after, in3 ∉ n.outs) :
    finalStore output = f (finalStore in0) (finalStore in1)
      (finalStore in2) (finalStore in3) := by
  have hfold : finalStore = (before ++ [target] ++ after).foldl
      (applyNodeDistributedFaithful g) initialStore :=
    hfinal.trans (congrArg (fun ns : List NodeDecl =>
      ns.foldl (applyNodeDistributedFaithful g) initialStore) hnodes)
  have hwriter := foldl_faithful_middle_writer g initialStore before after target output
    (fun t => f (t in0) (t in1) (t in2) (t in3)) happly hAfterNil hAfterOutput
  have hprefix : finalStore output = f
      ((before.foldl (applyNodeDistributedFaithful g) initialStore) in0)
      ((before.foldl (applyNodeDistributedFaithful g) initialStore) in1)
      ((before.foldl (applyNodeDistributedFaithful g) initialStore) in2)
      ((before.foldl (applyNodeDistributedFaithful g) initialStore) in3) :=
    (congrArg (fun st : Store => st output) hfold).trans hwriter
  have hread (tid : Tid) (hnil : ∀ n ∈ target :: after, n.outs ≠ [])
      (hnot : ∀ n ∈ target :: after, tid ∉ n.outs) :
      (before.foldl (applyNodeDistributedFaithful g) initialStore) tid = finalStore tid := by
    have hp : (before.foldl (applyNodeDistributedFaithful g) initialStore) tid =
        ((before ++ [target] ++ after).foldl (applyNodeDistributedFaithful g) initialStore) tid := by
      simpa only [List.append_assoc, List.singleton_append] using
        foldl_faithful_prefix_read_eq_final g initialStore before (target :: after) tid hnil hnot
    exact hp.trans (congrArg (fun st : Store => st tid) hfold).symm
  exact hprefix.trans (congrArg
    (fun v : Tensor × Tensor × Tensor × Tensor => f v.1 v.2.1 v.2.2.1 v.2.2.2)
    (congrArg₂ Prod.mk (hread in0 h0nil h0)
      (congrArg₂ Prod.mk (hread in1 h1nil h1)
        (congrArg₂ Prod.mk (hread in2 h2nil h2) (hread in3 h3nil h3)))))

private theorem segment_000000_hSmdgamma (store : Store) :
    (segment_000000_sm_final store) 11 = (bw_layernorm ((segment_000000_sm_final store) 1) ((segment_000000_sm_final store) 2) ((segment_000000_sm_final store) 3) ((segment_000000_sm_final store) 4)).2.1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK1B2S3D7Dgamma.sm) store := by
    unfold segment_000000_sm_final
    rfl
  have hnodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_layernorm", ins := [1, 2, 3, 4], outs := [10, 11, 12] }] ++ (segment_000000_sm_nodes.drop 2) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK1B2S3D7Dgamma.sm
    segment_000000_sm_nodes (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
    store (segment_000000_sm_final store) { rank := 0, op := "OpName.BW_layernorm", ins := [1, 2, 3, 4], outs := [10, 11, 12] }
    1 2 3 4 11 (fun a b c d => (bw_layernorm a b c d).2.1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dw_out BWLayernormParamGraphK1B2S3D7Dgamma.sm t 0 1 2 3 4 10 11 12 (by native_decide)
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdgamma0 (store : Store) :
    (segment_000000_pm_final store) 103 = (bw_layernorm ((segment_000000_pm_final store) 100) ((segment_000000_pm_final store) 101) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).2.1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK1B2S3D7Dgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_layernorm", ins := [100, 101, 3, 4], outs := [102, 103, 104] }] ++ (segment_000000_pm_nodes.drop 2) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK1B2S3D7Dgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
    store (segment_000000_pm_final store) { rank := 0, op := "OpName.BW_layernorm", ins := [100, 101, 3, 4], outs := [102, 103, 104] }
    100 101 3 4 103 (fun a b c d => (bw_layernorm a b c d).2.1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dw_out BWLayernormParamGraphK1B2S3D7Dgamma.pm t 0 100 101 3 4 102 103 104 (by native_decide)
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

set_option maxHeartbeats 500000 in
private theorem segment_000000_dgamma_semantic (smFinal pmFinal : Store)
    (hg : ShardedRel (smFinal 1) [pmFinal 100] 1 [2, 3, 7] [2, 3, 7])
    (hx : ShardedRel (smFinal 2) [pmFinal 101] 1 [2, 3, 7] [2, 3, 7])
    (hgamma : ShardedRel (smFinal 3) [pmFinal 3] 0 [7] [7])
    (hbeta : ShardedRel (smFinal 4) [pmFinal 4] 0 [7] [7])
    (hSm : smFinal 11 = (bw_layernorm (smFinal 1) (smFinal 2) (smFinal 3) (smFinal 4)).2.1)
    (hPm0 : pmFinal 103 = (bw_layernorm (pmFinal 100) (pmFinal 101) (pmFinal 3) (pmFinal 4)).2.1)
    : fact_dgamma.Holds smFinal pmFinal := by
  have hgValue : smFinal 1 = allGatherPrimDimN 1 1 0 [pmFinal 100] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hxValue : smFinal 2 = allGatherPrimDimN 1 1 0 [pmFinal 101] := by
    simpa only [List.length_cons, List.length_nil] using hx.full_value
  have hgammaShape : (pmFinal 3).shape = [7] := hgamma.shard_shapes _ (by simp)
  have hgammaValue : smFinal 3 = pmFinal 3 := by
    rw [hgamma.full_value]
    simpa only [List.length_cons, List.length_nil] using
      (allGatherPrimDimN_singleton_eq 0 (pmFinal 3) (by
        rw [hgamma.shard_shapes _ (by simp)]; decide))
  have hbetaShape : (pmFinal 4).shape = [7] := hbeta.shard_shapes _ (by simp)
  have hbetaValue : smFinal 4 = pmFinal 4 := by
    rw [hbeta.full_value]
    simpa only [List.length_cons, List.length_nil] using
      (allGatherPrimDimN_singleton_eq 0 (pmFinal 4) (by
        rw [hbeta.shard_shapes _ (by simp)]; decide))
  have hComm := TrainVerify.Denote.bw_layernorm_dgamma_sequence_reduction_rank3 1 2 3 7
    [pmFinal 100] [pmFinal 101] (pmFinal 3) (pmFinal 4)
    (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes
    hgammaShape hbetaShape
  have hValue : smFinal 11 = tensorSum [pmFinal 103] := by
    rw [hSm, hgValue, hxValue, hgammaValue, hbetaValue, hComm]
    simp only [List.zipWith]
    rw [← hPm0]
  have hShape0 : (pmFinal 103).shape = [7] := by
    rw [hPm0, bw_layernorm_dw_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hgammaShape
  have hFull : (smFinal 11).shape = [7] := by
    rw [hSm, bw_layernorm_dw_shape _ _ _ _ 7 [3, 2] (by rw [hx.full_shape]; rfl)]
    exact hgamma.full_shape
  have hReduce : smFinal 11 = allReducePrim [pmFinal 103].length 0 [pmFinal 103] := by
    rw [hValue]
    rfl
  change ReductionRel (smFinal 11) [pmFinal 103] [7]
  refine { full_value := hReduce, full_shape := hFull, contributions_nonempty := by simp, contribution_shapes := ?_, reduced_shape := ?_ }
  · simp only [List.forall_mem_cons]
    exact ⟨hShape0, List.forall_mem_nil _⟩
  · rw [← hReduce]
    exact hFull

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 1) [pmFinal 100] 1 [2, 3, 7] [2, 3, 7] at hg
  have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 101] 1 [2, 3, 7] [2, 3, 7] at hx
  have hgamma : fact_gamma.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 3] 0 [7] [7] at hgamma
  have hbeta : fact_beta.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 4) [pmFinal 4] 0 [7] [7] at hbeta
  have hout1 := segment_000000_dgamma_semantic smFinal pmFinal hg hx hgamma hbeta
    (segment_000000_hSmdgamma smStore) (segment_000000_hPmdgamma0 pmStore)
  intro fact hfact
  have covered : fact ∈ [fact_dgamma] ++ state_before.facts :=
    (show state_after.facts ⊆ [fact_dgamma] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    subst fact
    exact hout1
  · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 : ClosedDepSegmentCertificate BWLayernormParamGraphK1B2S3D7Dgamma.sm BWLayernormParamGraphK1B2S3D7Dgamma.pm state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    have h := segment_000000_sound smStore pmStore hstate
    unfold segment_000000_sm_final segment_000000_pm_final at h
    exact h

#print axioms segment_000000_sound
#print axioms segment_000000
end
end TrainVerify.Denote.GeneratedBWLayernormParamK1B2S3D7Dgamma
