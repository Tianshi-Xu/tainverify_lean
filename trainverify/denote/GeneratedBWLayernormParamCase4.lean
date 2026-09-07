import denote.GraphGears
import denote.RelationCompiler
import denote.KRankBWLayernormParam
import denote.KRankBWLayernorm
open TrainVerify.Denote
namespace BWLayernormParamGraphK5B2S3D7DxDgamma
def sm : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_layernorm", ins := [1, 2, 3, 4], outs := [10, 11, 12] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }] }
def pm : GraphDecl := { numRanks := 5, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [125], outs := [126] }, { rank := 0, op := "OpName.BW_layernorm", ins := [100, 105, 3, 4], outs := [110, 115, 120] }, { rank := 1, op := "OpName.FW_float", ins := [125], outs := [127] }, { rank := 1, op := "OpName.BW_layernorm", ins := [101, 106, 3, 4], outs := [111, 116, 121] }, { rank := 2, op := "OpName.FW_float", ins := [125], outs := [128] }, { rank := 2, op := "OpName.BW_layernorm", ins := [102, 107, 3, 4], outs := [112, 117, 122] }, { rank := 3, op := "OpName.FW_float", ins := [125], outs := [129] }, { rank := 3, op := "OpName.BW_layernorm", ins := [103, 108, 3, 4], outs := [113, 118, 123] }, { rank := 4, op := "OpName.FW_float", ins := [125], outs := [130] }, { rank := 4, op := "OpName.BW_layernorm", ins := [104, 109, 3, 4], outs := [114, 119, 124] }, { rank := 0, op := "OpName.FW_float", ins := [125], outs := [131] }] }
end BWLayernormParamGraphK5B2S3D7DxDgamma
/- AUTO-GENERATED closed relation state universe. -/

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedBWLayernormParamK5B2S3D7DxDgamma

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_g : RelationFact :=
  .sharded 1 [100, 101, 102, 103, 104] 1 [2, 15, 7] [2, 3, 7]

private def fact_x : RelationFact :=
  .sharded 2 [105, 106, 107, 108, 109] 1 [2, 15, 7] [2, 3, 7]

private def fact_gamma : RelationFact :=
  .sharded 3 [3] 0 [7] [7]

private def fact_beta : RelationFact :=
  .sharded 4 [4] 0 [7] [7]

private def fact_dx : RelationFact :=
  .sharded 10 [110, 111, 112, 113, 114] 1 [2, 15, 7] [2, 3, 7]

private def fact_dgamma : RelationFact :=
  .reduction 11 [115, 116, 117, 118, 119] [7]

private def public_anchor : RelationFact :=
  .tensorShape .sm 3 [7]

private def state_before : RelationState where
  facts := [fact_g, fact_x, fact_gamma, fact_beta, public_anchor]
  nonempty := by decide

private def state_after : RelationState where
  facts := [fact_g, fact_x, fact_gamma, fact_beta, fact_dx, fact_dgamma, public_anchor]
  nonempty := by decide

set_option maxHeartbeats 500000 in
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [80], outs := [81] }, { rank := 0, op := "OpName.BW_layernorm", ins := [1, 2, 3, 4], outs := [10, 11, 12] }, { rank := 0, op := "OpName.FW_float", ins := [81], outs := [82] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_float", ins := [125], outs := [126] }, { rank := 0, op := "OpName.BW_layernorm", ins := [100, 105, 3, 4], outs := [110, 115, 120] }, { rank := 1, op := "OpName.FW_float", ins := [125], outs := [127] }, { rank := 1, op := "OpName.BW_layernorm", ins := [101, 106, 3, 4], outs := [111, 116, 121] }, { rank := 2, op := "OpName.FW_float", ins := [125], outs := [128] }, { rank := 2, op := "OpName.BW_layernorm", ins := [102, 107, 3, 4], outs := [112, 117, 122] }, { rank := 3, op := "OpName.FW_float", ins := [125], outs := [129] }, { rank := 3, op := "OpName.BW_layernorm", ins := [103, 108, 3, 4], outs := [113, 118, 123] }, { rank := 4, op := "OpName.FW_float", ins := [125], outs := [130] }, { rank := 4, op := "OpName.BW_layernorm", ins := [104, 109, 3, 4], outs := [114, 119, 124] }, { rank := 0, op := "OpName.FW_float", ins := [125], outs := [131] }]
@[irreducible] private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.sm) store
@[irreducible] private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store

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

private theorem segment_000000_hSmdx (store : Store) :
    (segment_000000_sm_final store) 10 = (bw_layernorm ((segment_000000_sm_final store) 1) ((segment_000000_sm_final store) 2) ((segment_000000_sm_final store) 3) ((segment_000000_sm_final store) 4)).1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.sm) store := by
    unfold segment_000000_sm_final
    rfl
  have hnodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_layernorm", ins := [1, 2, 3, 4], outs := [10, 11, 12] }] ++ (segment_000000_sm_nodes.drop 2) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.sm
    segment_000000_sm_nodes (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
    store (segment_000000_sm_final store) { rank := 0, op := "OpName.BW_layernorm", ins := [1, 2, 3, 4], outs := [10, 11, 12] }
    1 2 3 4 10 (fun a b c d => (bw_layernorm a b c d).1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dx_out BWLayernormParamGraphK5B2S3D7DxDgamma.sm t 0 1 2 3 4 10 11 12
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdx0 (store : Store) :
    (segment_000000_pm_final store) 110 = (bw_layernorm ((segment_000000_pm_final store) 100) ((segment_000000_pm_final store) 105) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_layernorm", ins := [100, 105, 3, 4], outs := [110, 115, 120] }] ++ (segment_000000_pm_nodes.drop 2) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
    store (segment_000000_pm_final store) { rank := 0, op := "OpName.BW_layernorm", ins := [100, 105, 3, 4], outs := [110, 115, 120] }
    100 105 3 4 110 (fun a b c d => (bw_layernorm a b c d).1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dx_out BWLayernormParamGraphK5B2S3D7DxDgamma.pm t 0 100 105 3 4 110 115 120
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdx1 (store : Store) :
    (segment_000000_pm_final store) 111 = (bw_layernorm ((segment_000000_pm_final store) 101) ((segment_000000_pm_final store) 106) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_layernorm", ins := [101, 106, 3, 4], outs := [111, 116, 121] }] ++ (segment_000000_pm_nodes.drop 4) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
    store (segment_000000_pm_final store) { rank := 1, op := "OpName.BW_layernorm", ins := [101, 106, 3, 4], outs := [111, 116, 121] }
    101 106 3 4 111 (fun a b c d => (bw_layernorm a b c d).1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dx_out BWLayernormParamGraphK5B2S3D7DxDgamma.pm t 1 101 106 3 4 111 116 121
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdx2 (store : Store) :
    (segment_000000_pm_final store) 112 = (bw_layernorm ((segment_000000_pm_final store) 102) ((segment_000000_pm_final store) 107) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_layernorm", ins := [102, 107, 3, 4], outs := [112, 117, 122] }] ++ (segment_000000_pm_nodes.drop 6) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
    store (segment_000000_pm_final store) { rank := 2, op := "OpName.BW_layernorm", ins := [102, 107, 3, 4], outs := [112, 117, 122] }
    102 107 3 4 112 (fun a b c d => (bw_layernorm a b c d).1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dx_out BWLayernormParamGraphK5B2S3D7DxDgamma.pm t 2 102 107 3 4 112 117 122
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdx3 (store : Store) :
    (segment_000000_pm_final store) 113 = (bw_layernorm ((segment_000000_pm_final store) 103) ((segment_000000_pm_final store) 108) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_layernorm", ins := [103, 108, 3, 4], outs := [113, 118, 123] }] ++ (segment_000000_pm_nodes.drop 8) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
    store (segment_000000_pm_final store) { rank := 3, op := "OpName.BW_layernorm", ins := [103, 108, 3, 4], outs := [113, 118, 123] }
    103 108 3 4 113 (fun a b c d => (bw_layernorm a b c d).1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dx_out BWLayernormParamGraphK5B2S3D7DxDgamma.pm t 3 103 108 3 4 113 118 123
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdx4 (store : Store) :
    (segment_000000_pm_final store) 114 = (bw_layernorm ((segment_000000_pm_final store) 104) ((segment_000000_pm_final store) 109) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 9) ++ [{ rank := 4, op := "OpName.BW_layernorm", ins := [104, 109, 3, 4], outs := [114, 119, 124] }] ++ (segment_000000_pm_nodes.drop 10) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 9) (segment_000000_pm_nodes.drop 10)
    store (segment_000000_pm_final store) { rank := 4, op := "OpName.BW_layernorm", ins := [104, 109, 3, 4], outs := [114, 119, 124] }
    104 109 3 4 114 (fun a b c d => (bw_layernorm a b c d).1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dx_out BWLayernormParamGraphK5B2S3D7DxDgamma.pm t 4 104 109 3 4 114 119 124
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hSmdgamma (store : Store) :
    (segment_000000_sm_final store) 11 = (bw_layernorm ((segment_000000_sm_final store) 1) ((segment_000000_sm_final store) 2) ((segment_000000_sm_final store) 3) ((segment_000000_sm_final store) 4)).2.1 := by
  have hfinal : (segment_000000_sm_final store) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.sm) store := by
    unfold segment_000000_sm_final
    rfl
  have hnodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_layernorm", ins := [1, 2, 3, 4], outs := [10, 11, 12] }] ++ (segment_000000_sm_nodes.drop 2) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.sm
    segment_000000_sm_nodes (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
    store (segment_000000_sm_final store) { rank := 0, op := "OpName.BW_layernorm", ins := [1, 2, 3, 4], outs := [10, 11, 12] }
    1 2 3 4 11 (fun a b c d => (bw_layernorm a b c d).2.1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dw_out BWLayernormParamGraphK5B2S3D7DxDgamma.sm t 0 1 2 3 4 10 11 12 (by native_decide)
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdgamma0 (store : Store) :
    (segment_000000_pm_final store) 115 = (bw_layernorm ((segment_000000_pm_final store) 100) ((segment_000000_pm_final store) 105) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).2.1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_layernorm", ins := [100, 105, 3, 4], outs := [110, 115, 120] }] ++ (segment_000000_pm_nodes.drop 2) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
    store (segment_000000_pm_final store) { rank := 0, op := "OpName.BW_layernorm", ins := [100, 105, 3, 4], outs := [110, 115, 120] }
    100 105 3 4 115 (fun a b c d => (bw_layernorm a b c d).2.1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dw_out BWLayernormParamGraphK5B2S3D7DxDgamma.pm t 0 100 105 3 4 110 115 120 (by native_decide)
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdgamma1 (store : Store) :
    (segment_000000_pm_final store) 116 = (bw_layernorm ((segment_000000_pm_final store) 101) ((segment_000000_pm_final store) 106) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).2.1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_layernorm", ins := [101, 106, 3, 4], outs := [111, 116, 121] }] ++ (segment_000000_pm_nodes.drop 4) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
    store (segment_000000_pm_final store) { rank := 1, op := "OpName.BW_layernorm", ins := [101, 106, 3, 4], outs := [111, 116, 121] }
    101 106 3 4 116 (fun a b c d => (bw_layernorm a b c d).2.1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dw_out BWLayernormParamGraphK5B2S3D7DxDgamma.pm t 1 101 106 3 4 111 116 121 (by native_decide)
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdgamma2 (store : Store) :
    (segment_000000_pm_final store) 117 = (bw_layernorm ((segment_000000_pm_final store) 102) ((segment_000000_pm_final store) 107) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).2.1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 5) ++ [{ rank := 2, op := "OpName.BW_layernorm", ins := [102, 107, 3, 4], outs := [112, 117, 122] }] ++ (segment_000000_pm_nodes.drop 6) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 5) (segment_000000_pm_nodes.drop 6)
    store (segment_000000_pm_final store) { rank := 2, op := "OpName.BW_layernorm", ins := [102, 107, 3, 4], outs := [112, 117, 122] }
    102 107 3 4 117 (fun a b c d => (bw_layernorm a b c d).2.1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dw_out BWLayernormParamGraphK5B2S3D7DxDgamma.pm t 2 102 107 3 4 112 117 122 (by native_decide)
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdgamma3 (store : Store) :
    (segment_000000_pm_final store) 118 = (bw_layernorm ((segment_000000_pm_final store) 103) ((segment_000000_pm_final store) 108) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).2.1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_layernorm", ins := [103, 108, 3, 4], outs := [113, 118, 123] }] ++ (segment_000000_pm_nodes.drop 8) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 7) (segment_000000_pm_nodes.drop 8)
    store (segment_000000_pm_final store) { rank := 3, op := "OpName.BW_layernorm", ins := [103, 108, 3, 4], outs := [113, 118, 123] }
    103 108 3 4 118 (fun a b c d => (bw_layernorm a b c d).2.1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dw_out BWLayernormParamGraphK5B2S3D7DxDgamma.pm t 3 103 108 3 4 113 118 123 (by native_decide)
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

private theorem segment_000000_hPmdgamma4 (store : Store) :
    (segment_000000_pm_final store) 119 = (bw_layernorm ((segment_000000_pm_final store) 104) ((segment_000000_pm_final store) 109) ((segment_000000_pm_final store) 3) ((segment_000000_pm_final store) 4)).2.1 := by
  have hfinal : (segment_000000_pm_final store) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful BWLayernormParamGraphK5B2S3D7DxDgamma.pm) store := by
    unfold segment_000000_pm_final
    rfl
  have hnodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 9) ++ [{ rank := 4, op := "OpName.BW_layernorm", ins := [104, 109, 3, 4], outs := [114, 119, 124] }] ++ (segment_000000_pm_nodes.drop 10) := by native_decide
  exact segment_000000_four_input_middle_writer BWLayernormParamGraphK5B2S3D7DxDgamma.pm
    segment_000000_pm_nodes (segment_000000_pm_nodes.take 9) (segment_000000_pm_nodes.drop 10)
    store (segment_000000_pm_final store) { rank := 4, op := "OpName.BW_layernorm", ins := [104, 109, 3, 4], outs := [114, 119, 124] }
    104 109 3 4 119 (fun a b c d => (bw_layernorm a b c d).2.1)
    hnodes hfinal (by
      intro t
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
      simp [applyNodeDistributed, applyNodeRingAttn]
      exact applyNode_bw_layernorm_dw_out BWLayernormParamGraphK5B2S3D7DxDgamma.pm t 4 104 109 3 4 114 119 124 (by native_decide)
    ) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

set_option maxHeartbeats 500000 in
private theorem segment_000000_dx_semantic (smFinal pmFinal : Store)
    (hg : ShardedRel (smFinal 1) [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103, pmFinal 104] 1 [2, 15, 7] [2, 3, 7])
    (hx : ShardedRel (smFinal 2) [pmFinal 105, pmFinal 106, pmFinal 107, pmFinal 108, pmFinal 109] 1 [2, 15, 7] [2, 3, 7])
    (hgamma : ShardedRel (smFinal 3) [pmFinal 3] 0 [7] [7])
    (hbeta : ShardedRel (smFinal 4) [pmFinal 4] 0 [7] [7])
    (hSm : smFinal 10 = (bw_layernorm (smFinal 1) (smFinal 2) (smFinal 3) (smFinal 4)).1)
    (hPm0 : pmFinal 110 = (bw_layernorm (pmFinal 100) (pmFinal 105) (pmFinal 3) (pmFinal 4)).1)
    (hPm1 : pmFinal 111 = (bw_layernorm (pmFinal 101) (pmFinal 106) (pmFinal 3) (pmFinal 4)).1)
    (hPm2 : pmFinal 112 = (bw_layernorm (pmFinal 102) (pmFinal 107) (pmFinal 3) (pmFinal 4)).1)
    (hPm3 : pmFinal 113 = (bw_layernorm (pmFinal 103) (pmFinal 108) (pmFinal 3) (pmFinal 4)).1)
    (hPm4 : pmFinal 114 = (bw_layernorm (pmFinal 104) (pmFinal 109) (pmFinal 3) (pmFinal 4)).1)
    : fact_dx.Holds smFinal pmFinal := by
  have hgValue : smFinal 1 = allGatherPrimDimN 1 5 0 [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103, pmFinal 104] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hxValue : smFinal 2 = allGatherPrimDimN 1 5 0 [pmFinal 105, pmFinal 106, pmFinal 107, pmFinal 108, pmFinal 109] := by
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
  have hComm := TrainVerify.Denote.bw_layernorm_dx_allGatherPrimDimN_dim1_3d 5 2 3 7
    [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103, pmFinal 104] [pmFinal 105, pmFinal 106, pmFinal 107, pmFinal 108, pmFinal 109] (pmFinal 3) (pmFinal 4)
    (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes
  have hValue : smFinal 10 = allGatherPrimDimN 1 5 0 [pmFinal 110, pmFinal 111, pmFinal 112, pmFinal 113, pmFinal 114] := by
    rw [hSm, hgValue, hxValue, hgammaValue, hbetaValue, hComm]
    simp only [List.zipWith]
    rw [← hPm0, ← hPm1, ← hPm2, ← hPm3, ← hPm4]
  have hShape0 : (pmFinal 110).shape = [2, 3, 7] := by
    rw [hPm0, bw_layernorm_dx_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hx.shard_shapes _ (by simp)
  have hShape1 : (pmFinal 111).shape = [2, 3, 7] := by
    rw [hPm1, bw_layernorm_dx_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hx.shard_shapes _ (by simp)
  have hShape2 : (pmFinal 112).shape = [2, 3, 7] := by
    rw [hPm2, bw_layernorm_dx_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hx.shard_shapes _ (by simp)
  have hShape3 : (pmFinal 113).shape = [2, 3, 7] := by
    rw [hPm3, bw_layernorm_dx_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hx.shard_shapes _ (by simp)
  have hShape4 : (pmFinal 114).shape = [2, 3, 7] := by
    rw [hPm4, bw_layernorm_dx_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hx.shard_shapes _ (by simp)
  have hFull : (smFinal 10).shape = [2, 15, 7] := by
    rw [hSm, bw_layernorm_dx_shape _ _ _ _ 7 [15, 2] (by rw [hx.full_shape]; rfl)]
    exact hx.full_shape
  change ShardedRel (smFinal 10) [pmFinal 110, pmFinal 111, pmFinal 112, pmFinal 113, pmFinal 114] 1 [2, 15, 7] [2, 3, 7]
  refine { full_value := ?_, full_shape := hFull, shards_nonempty := by simp, gather_dim_lt := by decide, shard_shapes := ?_, shape_contract := ?_ }
  · simpa only [List.length_cons, List.length_nil] using hValue
  · simp only [List.forall_mem_cons]
    exact ⟨hShape0, hShape1, hShape2, hShape3, hShape4, List.forall_mem_nil _⟩
  · simp only [List.length_cons, List.length_nil]
    decide

set_option maxHeartbeats 500000 in
private theorem segment_000000_dgamma_semantic (smFinal pmFinal : Store)
    (hg : ShardedRel (smFinal 1) [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103, pmFinal 104] 1 [2, 15, 7] [2, 3, 7])
    (hx : ShardedRel (smFinal 2) [pmFinal 105, pmFinal 106, pmFinal 107, pmFinal 108, pmFinal 109] 1 [2, 15, 7] [2, 3, 7])
    (hgamma : ShardedRel (smFinal 3) [pmFinal 3] 0 [7] [7])
    (hbeta : ShardedRel (smFinal 4) [pmFinal 4] 0 [7] [7])
    (hSm : smFinal 11 = (bw_layernorm (smFinal 1) (smFinal 2) (smFinal 3) (smFinal 4)).2.1)
    (hPm0 : pmFinal 115 = (bw_layernorm (pmFinal 100) (pmFinal 105) (pmFinal 3) (pmFinal 4)).2.1)
    (hPm1 : pmFinal 116 = (bw_layernorm (pmFinal 101) (pmFinal 106) (pmFinal 3) (pmFinal 4)).2.1)
    (hPm2 : pmFinal 117 = (bw_layernorm (pmFinal 102) (pmFinal 107) (pmFinal 3) (pmFinal 4)).2.1)
    (hPm3 : pmFinal 118 = (bw_layernorm (pmFinal 103) (pmFinal 108) (pmFinal 3) (pmFinal 4)).2.1)
    (hPm4 : pmFinal 119 = (bw_layernorm (pmFinal 104) (pmFinal 109) (pmFinal 3) (pmFinal 4)).2.1)
    : fact_dgamma.Holds smFinal pmFinal := by
  have hgValue : smFinal 1 = allGatherPrimDimN 1 5 0 [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103, pmFinal 104] := by
    simpa only [List.length_cons, List.length_nil] using hg.full_value
  have hxValue : smFinal 2 = allGatherPrimDimN 1 5 0 [pmFinal 105, pmFinal 106, pmFinal 107, pmFinal 108, pmFinal 109] := by
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
  have hComm := TrainVerify.Denote.bw_layernorm_dgamma_sequence_reduction_rank3 5 2 3 7
    [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103, pmFinal 104] [pmFinal 105, pmFinal 106, pmFinal 107, pmFinal 108, pmFinal 109] (pmFinal 3) (pmFinal 4)
    (by decide) (by decide) (by decide) (by decide) rfl rfl hg.shard_shapes hx.shard_shapes
    hgammaShape hbetaShape
  have hValue : smFinal 11 = tensorSum [pmFinal 115, pmFinal 116, pmFinal 117, pmFinal 118, pmFinal 119] := by
    rw [hSm, hgValue, hxValue, hgammaValue, hbetaValue, hComm]
    simp only [List.zipWith]
    rw [← hPm0, ← hPm1, ← hPm2, ← hPm3, ← hPm4]
  have hShape0 : (pmFinal 115).shape = [7] := by
    rw [hPm0, bw_layernorm_dw_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hgammaShape
  have hShape1 : (pmFinal 116).shape = [7] := by
    rw [hPm1, bw_layernorm_dw_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hgammaShape
  have hShape2 : (pmFinal 117).shape = [7] := by
    rw [hPm2, bw_layernorm_dw_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hgammaShape
  have hShape3 : (pmFinal 118).shape = [7] := by
    rw [hPm3, bw_layernorm_dw_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hgammaShape
  have hShape4 : (pmFinal 119).shape = [7] := by
    rw [hPm4, bw_layernorm_dw_shape _ _ _ _ 7 [3, 2] (by rw [hx.shard_shapes _ (by simp)]; rfl)]
    exact hgammaShape
  have hFull : (smFinal 11).shape = [7] := by
    rw [hSm, bw_layernorm_dw_shape _ _ _ _ 7 [15, 2] (by rw [hx.full_shape]; rfl)]
    exact hgamma.full_shape
  have hReduce : smFinal 11 = allReducePrim [pmFinal 115, pmFinal 116, pmFinal 117, pmFinal 118, pmFinal 119].length 0 [pmFinal 115, pmFinal 116, pmFinal 117, pmFinal 118, pmFinal 119] := by
    rw [hValue]
    rfl
  change ReductionRel (smFinal 11) [pmFinal 115, pmFinal 116, pmFinal 117, pmFinal 118, pmFinal 119] [7]
  refine { full_value := hReduce, full_shape := hFull, contributions_nonempty := by simp, contribution_shapes := ?_, reduced_shape := ?_ }
  · simp only [List.forall_mem_cons]
    exact ⟨hShape0, hShape1, hShape2, hShape3, hShape4, List.forall_mem_nil _⟩
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
  change ShardedRel (smFinal 1) [pmFinal 100, pmFinal 101, pmFinal 102, pmFinal 103, pmFinal 104] 1 [2, 15, 7] [2, 3, 7] at hg
  have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 2) [pmFinal 105, pmFinal 106, pmFinal 107, pmFinal 108, pmFinal 109] 1 [2, 15, 7] [2, 3, 7] at hx
  have hgamma : fact_gamma.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 3) [pmFinal 3] 0 [7] [7] at hgamma
  have hbeta : fact_beta.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 4) [pmFinal 4] 0 [7] [7] at hbeta
  have hout0 := segment_000000_dx_semantic smFinal pmFinal hg hx hgamma hbeta
    (segment_000000_hSmdx smStore) (segment_000000_hPmdx0 pmStore) (segment_000000_hPmdx1 pmStore) (segment_000000_hPmdx2 pmStore) (segment_000000_hPmdx3 pmStore) (segment_000000_hPmdx4 pmStore)
  have hout1 := segment_000000_dgamma_semantic smFinal pmFinal hg hx hgamma hbeta
    (segment_000000_hSmdgamma smStore) (segment_000000_hPmdgamma0 pmStore) (segment_000000_hPmdgamma1 pmStore) (segment_000000_hPmdgamma2 pmStore) (segment_000000_hPmdgamma3 pmStore) (segment_000000_hPmdgamma4 pmStore)
  intro fact hfact
  have covered : fact ∈ [fact_dx, fact_dgamma] ++ state_before.facts :=
    (show state_after.facts ⊆ [fact_dx, fact_dgamma] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl
    · exact hout0
    · exact hout1
  · exact hframe fact old

set_option maxRecDepth 8192 in
private def segment_000000 : ClosedDepSegmentCertificate BWLayernormParamGraphK5B2S3D7DxDgamma.sm BWLayernormParamGraphK5B2S3D7DxDgamma.pm state_before state_after where
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
end TrainVerify.Denote.GeneratedBWLayernormParamK5B2S3D7DxDgamma
