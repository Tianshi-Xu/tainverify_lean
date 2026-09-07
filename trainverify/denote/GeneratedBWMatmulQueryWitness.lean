import denote.RelationCompiler
import denote.KRankBWMatmulQuery
import denote.KRankMatmulQueryAxis
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace MatmulQueryCase0
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] }
def fact_g : RelationFact := .sharded 100 [1000] 2 [2, 3, 5, 11] [2, 3, 5, 11]
def fact_x : RelationFact := .sharded 200 [2000] 2 [2, 3, 5, 7] [2, 3, 5, 7]
def fact_y : RelationFact := .joined 300 3000 [2, 3, 7, 11]
def fact_out0 : RelationFact := .sharded 400 [4000] 2 [2, 3, 5, 7] [2, 3, 5, 7]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_y]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_out0]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) s

private theorem segment_000000_hSm0 (smStore : Store) : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase0.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase0.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase0.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase0.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase0.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_transpose_shape (t : Tensor) (a b c d : Nat)
    (ht : t.shape = [a,b,c,d]) : (transpose2d t).shape = [a,b,d,c] := by
  simp only [transpose2d, ht, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Tensor.mkShape]

private theorem segment_000000_semantic_fst (g x y py : Tensor) (gs xs : List Tensor)
    (hg : ShardedRel g gs 2 [2, 3, 5, 11] [2, 3, 5, 11]) (hx : ShardedRel x xs 2 [2, 3, 5, 7] [2, 3, 5, 7])
    (hy : y = py ∧ y.shape = [2, 3, 7, 11] ∧ py.shape = [2, 3, 7, 11])
    (hgl : gs.length = 1) (hxl : xs.length = 1) :
    ShardedRel (bw_matmul g x y).1 (gs.map (fun z => (bw_matmul z x py).1)) 2 [2, 3, 5, 7] [2, 3, 5, 7] := by
  have hyT : transpose2d y = transpose2d py ∧ (transpose2d y).shape = [2, 3, 11, 7] ∧ (transpose2d py).shape = [2, 3, 11, 7] :=
    ⟨congrArg transpose2d hy.1, segment_000000_transpose_shape y 2 3 7 11 hy.2.1, segment_000000_transpose_shape py 2 3 7 11 hy.2.2⟩
  exact TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4 (K := 1) (b := 2) (h := 3) (q := 5) (k := 11) (m := 7) hg hyT (by decide) (by decide) (by decide) (by decide) hgl

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_000000.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000] 2 [2, 3, 5, 11] [2, 3, 5, 11] at hg
  have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000] 2 [2, 3, 5, 7] [2, 3, 5, 7] at hx
  have hy : fact_y.Holds smFinal pmFinal := hframe _ (by native_decide)
  change smFinal 300 = pmFinal 3000 ∧ (smFinal 300).shape = [2, 3, 7, 11] ∧ (pmFinal 3000).shape = [2, 3, 7, 11] at hy
  have hS0 := segment_000000_hSm0 smStore
  change smFinal 400 = (bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).1 at hS0
  have hP0_0 := segment_000000_hPm0_0 pmStore
  change pmFinal 4000 = (bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1 at hP0_0
  have hC0 := segment_000000_semantic_fst (smFinal 100) (smFinal 200) (smFinal 300) (pmFinal 3000) [pmFinal 1000] [pmFinal 2000] hg hx hy (by rfl) (by rfl)
  have hout0 : fact_out0.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 400) [pmFinal 4000] 2 [2, 3, 5, 7] [2, 3, 5, 7]
    rw [hS0, hP0_0]
    simpa only [List.map, bw_matmul, batchedMatmulBwd] using hC0
  intro fact hfact
  have hc : fact ∈ [fact_out0] ++ state_000000.facts := (show state_000001.facts ⊆ [fact_out0] ++ state_000000.facts by native_decide) hfact
  simp only [List.mem_append] at hc
  rcases hc with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    subst fact
    exact hout0
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate MatmulQueryCase0.smGraph MatmulQueryCase0.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by intro smStore pmStore h; have h' := segment_000000_sound smStore pmStore h; unfold segment_000000_sm_final segment_000000_pm_final at h'; exact h'

#print axioms segment_000000
end
end MatmulQueryCase0
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace MatmulQueryCase1
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001] 2 [2, 3, 10, 11] [2, 3, 5, 11]
def fact_x : RelationFact := .sharded 200 [2000, 2001] 2 [2, 3, 10, 7] [2, 3, 5, 7]
def fact_y : RelationFact := .joined 300 3000 [2, 3, 7, 11]
def fact_out1 : RelationFact := .reduction 401 [5000, 5001] [2, 3, 7, 11]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_y]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_out1]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) s

private theorem segment_000000_hSm1 (smStore : Store) : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase1.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase1.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase1.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } 5001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase1.pmGraph t 1 1001 2001 3000 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase1.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase1.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_transpose_shape (t : Tensor) (a b c d : Nat)
    (ht : t.shape = [a,b,c,d]) : (transpose2d t).shape = [a,b,d,c] := by
  simp only [transpose2d, ht, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Tensor.mkShape]

private theorem segment_000000_semantic_snd (g x y py : Tensor) (gs xs : List Tensor)
    (hg : ShardedRel g gs 2 [2, 3, 10, 11] [2, 3, 5, 11]) (hx : ShardedRel x xs 2 [2, 3, 10, 7] [2, 3, 5, 7])
    (hy : y = py ∧ y.shape = [2, 3, 7, 11] ∧ py.shape = [2, 3, 7, 11])
    (hgl : gs.length = 2) (hxl : xs.length = 2) :
    (bw_matmul g x y).2 = tensorSum (List.zipWith (fun a z => (bw_matmul a z py).2) gs xs) := by
  rw [hg.full_value, hx.full_value, hgl, hxl, hy.1]
  exact TrainVerify.Denote.bw_matmul_snd_query_reduction_rank4 2 2 3 5 7 11 gs xs py (by decide) (by decide) (by decide) (by decide) (by decide) hgl hxl hg.shard_shapes hx.shard_shapes

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_000000.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001] 2 [2, 3, 10, 11] [2, 3, 5, 11] at hg
  have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001] 2 [2, 3, 10, 7] [2, 3, 5, 7] at hx
  have hy : fact_y.Holds smFinal pmFinal := hframe _ (by native_decide)
  change smFinal 300 = pmFinal 3000 ∧ (smFinal 300).shape = [2, 3, 7, 11] ∧ (pmFinal 3000).shape = [2, 3, 7, 11] at hy
  have hS1 := segment_000000_hSm1 smStore
  change smFinal 401 = (bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).2 at hS1
  have hP1_0 := segment_000000_hPm1_0 pmStore
  change pmFinal 5000 = (bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2 at hP1_0
  have hP1_1 := segment_000000_hPm1_1 pmStore
  change pmFinal 5001 = (bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3000)).2 at hP1_1
  have hC1 := segment_000000_semantic_snd (smFinal 100) (smFinal 200) (smFinal 300) (pmFinal 3000) [pmFinal 1000, pmFinal 1001] [pmFinal 2000, pmFinal 2001] hg hx hy (by rfl) (by rfl)
  simp only [List.zipWith] at hC1
  rw [←hS1, ←hP1_0, ←hP1_1] at hC1
  have hRV : smFinal 401 = allReducePrim [pmFinal 5000, pmFinal 5001].length 0 [pmFinal 5000, pmFinal 5001] := hC1
  have hFull : (smFinal 401).shape = [2, 3, 7, 11] := by
    rw [hS1]
    exact fw_matmul_rank4_shape _ _ 2 3 7 10 11 (segment_000000_transpose_shape _ 2 3 10 7 hx.full_shape) hg.full_shape
  have hShape0 : (pmFinal 5000).shape = [2, 3, 7, 11] := by
    rw [hP1_0]
    exact fw_matmul_rank4_shape _ _ 2 3 7 5 11 (segment_000000_transpose_shape _ 2 3 5 7 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShape1 : (pmFinal 5001).shape = [2, 3, 7, 11] := by
    rw [hP1_1]
    exact fw_matmul_rank4_shape _ _ 2 3 7 5 11 (segment_000000_transpose_shape _ 2 3 5 7 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShapes : ∀ z ∈ [pmFinal 5000, pmFinal 5001], z.shape = [2, 3, 7, 11] := by
    simp only [List.forall_mem_cons]
    exact ⟨hShape0, hShape1, List.forall_mem_nil _⟩
  have hout1 : fact_out1.Holds smFinal pmFinal := by
    exact {
      full_value := hRV
      full_shape := hFull
      contributions_nonempty := List.cons_ne_nil _ _
      contribution_shapes := hShapes
      reduced_shape := by simp only [List.map]; rw [←hRV]; exact hFull }
  intro fact hfact
  have hc : fact ∈ [fact_out1] ++ state_000000.facts := (show state_000001.facts ⊆ [fact_out1] ++ state_000000.facts by native_decide) hfact
  simp only [List.mem_append] at hc
  rcases hc with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    subst fact
    exact hout1
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate MatmulQueryCase1.smGraph MatmulQueryCase1.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by intro smStore pmStore h; have h' := segment_000000_sound smStore pmStore h; unfold segment_000000_sm_final segment_000000_pm_final at h'; exact h'

#print axioms segment_000000
end
end MatmulQueryCase1
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace MatmulQueryCase2
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002] 2 [2, 3, 15, 11] [2, 3, 5, 11]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002] 2 [2, 3, 15, 7] [2, 3, 5, 7]
def fact_y : RelationFact := .joined 300 3000 [2, 3, 7, 11]
def fact_out0 : RelationFact := .sharded 400 [4000, 4001, 4002] 2 [2, 3, 15, 7] [2, 3, 5, 7]
def fact_out1 : RelationFact := .reduction 401 [5000, 5001, 5002] [2, 3, 7, 11]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_y]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_out0, fact_out1]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) s

private theorem segment_000000_hSm0 (smStore : Store) : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase2.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase2.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 4001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } 4001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase2.pmGraph t 1 1001 2001 3000 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_2 (pmStore : Store) : (segment_000000_pm_final pmStore) 4002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } 4002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase2.pmGraph t 2 1002 2002 3000 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hSm1 (smStore : Store) : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase2.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase2.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } 5001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase2.pmGraph t 1 1001 2001 3000 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_2 (pmStore : Store) : (segment_000000_pm_final pmStore) 5002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } 5002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase2.pmGraph t 2 1002 2002 3000 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase2.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase2.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_transpose_shape (t : Tensor) (a b c d : Nat)
    (ht : t.shape = [a,b,c,d]) : (transpose2d t).shape = [a,b,d,c] := by
  simp only [transpose2d, ht, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Tensor.mkShape]

private theorem segment_000000_semantic_fst (g x y py : Tensor) (gs xs : List Tensor)
    (hg : ShardedRel g gs 2 [2, 3, 15, 11] [2, 3, 5, 11]) (hx : ShardedRel x xs 2 [2, 3, 15, 7] [2, 3, 5, 7])
    (hy : y = py ∧ y.shape = [2, 3, 7, 11] ∧ py.shape = [2, 3, 7, 11])
    (hgl : gs.length = 3) (hxl : xs.length = 3) :
    ShardedRel (bw_matmul g x y).1 (gs.map (fun z => (bw_matmul z x py).1)) 2 [2, 3, 15, 7] [2, 3, 5, 7] := by
  have hyT : transpose2d y = transpose2d py ∧ (transpose2d y).shape = [2, 3, 11, 7] ∧ (transpose2d py).shape = [2, 3, 11, 7] :=
    ⟨congrArg transpose2d hy.1, segment_000000_transpose_shape y 2 3 7 11 hy.2.1, segment_000000_transpose_shape py 2 3 7 11 hy.2.2⟩
  exact TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4 (K := 3) (b := 2) (h := 3) (q := 5) (k := 11) (m := 7) hg hyT (by decide) (by decide) (by decide) (by decide) hgl

private theorem segment_000000_semantic_snd (g x y py : Tensor) (gs xs : List Tensor)
    (hg : ShardedRel g gs 2 [2, 3, 15, 11] [2, 3, 5, 11]) (hx : ShardedRel x xs 2 [2, 3, 15, 7] [2, 3, 5, 7])
    (hy : y = py ∧ y.shape = [2, 3, 7, 11] ∧ py.shape = [2, 3, 7, 11])
    (hgl : gs.length = 3) (hxl : xs.length = 3) :
    (bw_matmul g x y).2 = tensorSum (List.zipWith (fun a z => (bw_matmul a z py).2) gs xs) := by
  rw [hg.full_value, hx.full_value, hgl, hxl, hy.1]
  exact TrainVerify.Denote.bw_matmul_snd_query_reduction_rank4 3 2 3 5 7 11 gs xs py (by decide) (by decide) (by decide) (by decide) (by decide) hgl hxl hg.shard_shapes hx.shard_shapes

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_000000.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002] 2 [2, 3, 15, 11] [2, 3, 5, 11] at hg
  have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002] 2 [2, 3, 15, 7] [2, 3, 5, 7] at hx
  have hy : fact_y.Holds smFinal pmFinal := hframe _ (by native_decide)
  change smFinal 300 = pmFinal 3000 ∧ (smFinal 300).shape = [2, 3, 7, 11] ∧ (pmFinal 3000).shape = [2, 3, 7, 11] at hy
  have hS0 := segment_000000_hSm0 smStore
  change smFinal 400 = (bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).1 at hS0
  have hP0_0 := segment_000000_hPm0_0 pmStore
  change pmFinal 4000 = (bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1 at hP0_0
  have hP0_1 := segment_000000_hPm0_1 pmStore
  change pmFinal 4001 = (bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3000)).1 at hP0_1
  have hP0_2 := segment_000000_hPm0_2 pmStore
  change pmFinal 4002 = (bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3000)).1 at hP0_2
  have hC0 := segment_000000_semantic_fst (smFinal 100) (smFinal 200) (smFinal 300) (pmFinal 3000) [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 2000, pmFinal 2001, pmFinal 2002] hg hx hy (by rfl) (by rfl)
  have hout0 : fact_out0.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002] 2 [2, 3, 15, 7] [2, 3, 5, 7]
    rw [hS0, hP0_0, hP0_1, hP0_2]
    simpa only [List.map, bw_matmul, batchedMatmulBwd] using hC0
  have hS1 := segment_000000_hSm1 smStore
  change smFinal 401 = (bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).2 at hS1
  have hP1_0 := segment_000000_hPm1_0 pmStore
  change pmFinal 5000 = (bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2 at hP1_0
  have hP1_1 := segment_000000_hPm1_1 pmStore
  change pmFinal 5001 = (bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3000)).2 at hP1_1
  have hP1_2 := segment_000000_hPm1_2 pmStore
  change pmFinal 5002 = (bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3000)).2 at hP1_2
  have hC1 := segment_000000_semantic_snd (smFinal 100) (smFinal 200) (smFinal 300) (pmFinal 3000) [pmFinal 1000, pmFinal 1001, pmFinal 1002] [pmFinal 2000, pmFinal 2001, pmFinal 2002] hg hx hy (by rfl) (by rfl)
  simp only [List.zipWith] at hC1
  rw [←hS1, ←hP1_0, ←hP1_1, ←hP1_2] at hC1
  have hRV : smFinal 401 = allReducePrim [pmFinal 5000, pmFinal 5001, pmFinal 5002].length 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002] := hC1
  have hFull : (smFinal 401).shape = [2, 3, 7, 11] := by
    rw [hS1]
    exact fw_matmul_rank4_shape _ _ 2 3 7 15 11 (segment_000000_transpose_shape _ 2 3 15 7 hx.full_shape) hg.full_shape
  have hShape0 : (pmFinal 5000).shape = [2, 3, 7, 11] := by
    rw [hP1_0]
    exact fw_matmul_rank4_shape _ _ 2 3 7 5 11 (segment_000000_transpose_shape _ 2 3 5 7 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShape1 : (pmFinal 5001).shape = [2, 3, 7, 11] := by
    rw [hP1_1]
    exact fw_matmul_rank4_shape _ _ 2 3 7 5 11 (segment_000000_transpose_shape _ 2 3 5 7 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShape2 : (pmFinal 5002).shape = [2, 3, 7, 11] := by
    rw [hP1_2]
    exact fw_matmul_rank4_shape _ _ 2 3 7 5 11 (segment_000000_transpose_shape _ 2 3 5 7 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShapes : ∀ z ∈ [pmFinal 5000, pmFinal 5001, pmFinal 5002], z.shape = [2, 3, 7, 11] := by
    simp only [List.forall_mem_cons]
    exact ⟨hShape0, hShape1, hShape2, List.forall_mem_nil _⟩
  have hout1 : fact_out1.Holds smFinal pmFinal := by
    exact {
      full_value := hRV
      full_shape := hFull
      contributions_nonempty := List.cons_ne_nil _ _
      contribution_shapes := hShapes
      reduced_shape := by simp only [List.map]; rw [←hRV]; exact hFull }
  intro fact hfact
  have hc : fact ∈ [fact_out0, fact_out1] ++ state_000000.facts := (show state_000001.facts ⊆ [fact_out0, fact_out1] ++ state_000000.facts by native_decide) hfact
  simp only [List.mem_append] at hc
  rcases hc with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl
    · exact hout0
    · exact hout1
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate MatmulQueryCase2.smGraph MatmulQueryCase2.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by intro smStore pmStore h; have h' := segment_000000_sound smStore pmStore h; unfold segment_000000_sm_final segment_000000_pm_final at h'; exact h'

#print axioms segment_000000
end
end MatmulQueryCase2
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace MatmulQueryCase3
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] }
def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003] 2 [1, 4, 16, 16] [1, 4, 4, 16]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003] 2 [1, 4, 16, 16] [1, 4, 4, 16]
def fact_y : RelationFact := .joined 300 3000 [1, 4, 16, 16]
def fact_out0 : RelationFact := .sharded 400 [4000, 4001, 4002, 4003] 2 [1, 4, 16, 16] [1, 4, 4, 16]
def fact_out1 : RelationFact := .reduction 401 [5000, 5001, 5002, 5003] [1, 4, 16, 16]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_y]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_out0, fact_out1]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) s

private theorem segment_000000_hSm0 (smStore : Store) : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase3.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase3.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 4001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } 4001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase3.pmGraph t 1 1001 2001 3000 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_2 (pmStore : Store) : (segment_000000_pm_final pmStore) 4002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } 4002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase3.pmGraph t 2 1002 2002 3000 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_3 (pmStore : Store) : (segment_000000_pm_final pmStore) 4003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4003 = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } 4003
      (fun t => (bw_matmul (t 1003) (t 2003) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase3.pmGraph t 3 1003 2003 3000 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hSm1 (smStore : Store) : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase3.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase3.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } 5001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase3.pmGraph t 1 1001 2001 3000 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_2 (pmStore : Store) : (segment_000000_pm_final pmStore) 5002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } 5002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase3.pmGraph t 2 1002 2002 3000 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_3 (pmStore : Store) : (segment_000000_pm_final pmStore) 5003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5003 = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } 5003
      (fun t => (bw_matmul (t 1003) (t 2003) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase3.pmGraph t 3 1003 2003 3000 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase3.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase3.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_transpose_shape (t : Tensor) (a b c d : Nat)
    (ht : t.shape = [a,b,c,d]) : (transpose2d t).shape = [a,b,d,c] := by
  simp only [transpose2d, ht, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Tensor.mkShape]

private theorem segment_000000_semantic_fst (g x y py : Tensor) (gs xs : List Tensor)
    (hg : ShardedRel g gs 2 [1, 4, 16, 16] [1, 4, 4, 16]) (hx : ShardedRel x xs 2 [1, 4, 16, 16] [1, 4, 4, 16])
    (hy : y = py ∧ y.shape = [1, 4, 16, 16] ∧ py.shape = [1, 4, 16, 16])
    (hgl : gs.length = 4) (hxl : xs.length = 4) :
    ShardedRel (bw_matmul g x y).1 (gs.map (fun z => (bw_matmul z x py).1)) 2 [1, 4, 16, 16] [1, 4, 4, 16] := by
  have hyT : transpose2d y = transpose2d py ∧ (transpose2d y).shape = [1, 4, 16, 16] ∧ (transpose2d py).shape = [1, 4, 16, 16] :=
    ⟨congrArg transpose2d hy.1, segment_000000_transpose_shape y 1 4 16 16 hy.2.1, segment_000000_transpose_shape py 1 4 16 16 hy.2.2⟩
  exact TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4 (K := 4) (b := 1) (h := 4) (q := 4) (k := 16) (m := 16) hg hyT (by decide) (by decide) (by decide) (by decide) hgl

private theorem segment_000000_semantic_snd (g x y py : Tensor) (gs xs : List Tensor)
    (hg : ShardedRel g gs 2 [1, 4, 16, 16] [1, 4, 4, 16]) (hx : ShardedRel x xs 2 [1, 4, 16, 16] [1, 4, 4, 16])
    (hy : y = py ∧ y.shape = [1, 4, 16, 16] ∧ py.shape = [1, 4, 16, 16])
    (hgl : gs.length = 4) (hxl : xs.length = 4) :
    (bw_matmul g x y).2 = tensorSum (List.zipWith (fun a z => (bw_matmul a z py).2) gs xs) := by
  rw [hg.full_value, hx.full_value, hgl, hxl, hy.1]
  exact TrainVerify.Denote.bw_matmul_snd_query_reduction_rank4 4 1 4 4 16 16 gs xs py (by decide) (by decide) (by decide) (by decide) (by decide) hgl hxl hg.shard_shapes hx.shard_shapes

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_000000.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] 2 [1, 4, 16, 16] [1, 4, 4, 16] at hg
  have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] 2 [1, 4, 16, 16] [1, 4, 4, 16] at hx
  have hy : fact_y.Holds smFinal pmFinal := hframe _ (by native_decide)
  change smFinal 300 = pmFinal 3000 ∧ (smFinal 300).shape = [1, 4, 16, 16] ∧ (pmFinal 3000).shape = [1, 4, 16, 16] at hy
  have hS0 := segment_000000_hSm0 smStore
  change smFinal 400 = (bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).1 at hS0
  have hP0_0 := segment_000000_hPm0_0 pmStore
  change pmFinal 4000 = (bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1 at hP0_0
  have hP0_1 := segment_000000_hPm0_1 pmStore
  change pmFinal 4001 = (bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3000)).1 at hP0_1
  have hP0_2 := segment_000000_hPm0_2 pmStore
  change pmFinal 4002 = (bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3000)).1 at hP0_2
  have hP0_3 := segment_000000_hPm0_3 pmStore
  change pmFinal 4003 = (bw_matmul (pmFinal 1003) (pmFinal 2003) (pmFinal 3000)).1 at hP0_3
  have hC0 := segment_000000_semantic_fst (smFinal 100) (smFinal 200) (smFinal 300) (pmFinal 3000) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] hg hx hy (by rfl) (by rfl)
  have hout0 : fact_out0.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003] 2 [1, 4, 16, 16] [1, 4, 4, 16]
    rw [hS0, hP0_0, hP0_1, hP0_2, hP0_3]
    simpa only [List.map, bw_matmul, batchedMatmulBwd] using hC0
  have hS1 := segment_000000_hSm1 smStore
  change smFinal 401 = (bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).2 at hS1
  have hP1_0 := segment_000000_hPm1_0 pmStore
  change pmFinal 5000 = (bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2 at hP1_0
  have hP1_1 := segment_000000_hPm1_1 pmStore
  change pmFinal 5001 = (bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3000)).2 at hP1_1
  have hP1_2 := segment_000000_hPm1_2 pmStore
  change pmFinal 5002 = (bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3000)).2 at hP1_2
  have hP1_3 := segment_000000_hPm1_3 pmStore
  change pmFinal 5003 = (bw_matmul (pmFinal 1003) (pmFinal 2003) (pmFinal 3000)).2 at hP1_3
  have hC1 := segment_000000_semantic_snd (smFinal 100) (smFinal 200) (smFinal 300) (pmFinal 3000) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003] hg hx hy (by rfl) (by rfl)
  simp only [List.zipWith] at hC1
  rw [←hS1, ←hP1_0, ←hP1_1, ←hP1_2, ←hP1_3] at hC1
  have hRV : smFinal 401 = allReducePrim [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003].length 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003] := hC1
  have hFull : (smFinal 401).shape = [1, 4, 16, 16] := by
    rw [hS1]
    exact fw_matmul_rank4_shape _ _ 1 4 16 16 16 (segment_000000_transpose_shape _ 1 4 16 16 hx.full_shape) hg.full_shape
  have hShape0 : (pmFinal 5000).shape = [1, 4, 16, 16] := by
    rw [hP1_0]
    exact fw_matmul_rank4_shape _ _ 1 4 16 4 16 (segment_000000_transpose_shape _ 1 4 4 16 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShape1 : (pmFinal 5001).shape = [1, 4, 16, 16] := by
    rw [hP1_1]
    exact fw_matmul_rank4_shape _ _ 1 4 16 4 16 (segment_000000_transpose_shape _ 1 4 4 16 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShape2 : (pmFinal 5002).shape = [1, 4, 16, 16] := by
    rw [hP1_2]
    exact fw_matmul_rank4_shape _ _ 1 4 16 4 16 (segment_000000_transpose_shape _ 1 4 4 16 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShape3 : (pmFinal 5003).shape = [1, 4, 16, 16] := by
    rw [hP1_3]
    exact fw_matmul_rank4_shape _ _ 1 4 16 4 16 (segment_000000_transpose_shape _ 1 4 4 16 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShapes : ∀ z ∈ [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003], z.shape = [1, 4, 16, 16] := by
    simp only [List.forall_mem_cons]
    exact ⟨hShape0, hShape1, hShape2, hShape3, List.forall_mem_nil _⟩
  have hout1 : fact_out1.Holds smFinal pmFinal := by
    exact {
      full_value := hRV
      full_shape := hFull
      contributions_nonempty := List.cons_ne_nil _ _
      contribution_shapes := hShapes
      reduced_shape := by simp only [List.map]; rw [←hRV]; exact hFull }
  intro fact hfact
  have hc : fact ∈ [fact_out0, fact_out1] ++ state_000000.facts := (show state_000001.facts ⊆ [fact_out0, fact_out1] ++ state_000000.facts by native_decide) hfact
  simp only [List.mem_append] at hc
  rcases hc with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl
    · exact hout0
    · exact hout1
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate MatmulQueryCase3.smGraph MatmulQueryCase3.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by intro smStore pmStore h; have h' := segment_000000_sound smStore pmStore h; unfold segment_000000_sm_final segment_000000_pm_final at h'; exact h'

#print axioms segment_000000
end
end MatmulQueryCase3
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace MatmulQueryCase4
noncomputable section
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }, { rank := 0, op := "OpName.BW_view", ins := [600, 601], outs := [700], params := [2, 3, 77] }] }
def pmGraph : GraphDecl := { numRanks := 5, nodes := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] }, { rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] }, { rank := 0, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }, { rank := 1, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }, { rank := 2, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }, { rank := 3, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }, { rank := 4, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }] }
def fact_g : RelationFact := .sharded 100 [1000, 1001, 1002, 1003, 1004] 2 [2, 3, 25, 11] [2, 3, 5, 11]
def fact_x : RelationFact := .sharded 200 [2000, 2001, 2002, 2003, 2004] 2 [2, 3, 25, 7] [2, 3, 5, 7]
def fact_y : RelationFact := .joined 300 3000 [2, 3, 7, 11]
def fact_out0 : RelationFact := .sharded 400 [4000, 4001, 4002, 4003, 4004] 2 [2, 3, 25, 7] [2, 3, 5, 7]
def fact_out1 : RelationFact := .reduction 401 [5000, 5001, 5002, 5003, 5004] [2, 3, 7, 11]
def fact_vi : RelationFact := .joined 600 6000 [2, 3, 7, 11]
def fact_vo : RelationFact := .joined 700 7000 [2, 3, 77]
def state_000000 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_vi]
  nonempty := by decide
def state_000001 : RelationState where
  facts := [fact_g, fact_x, fact_y, fact_vi, fact_out0, fact_out1, fact_vo]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }, { rank := 0, op := "OpName.BW_view", ins := [600, 601], outs := [700], params := [2, 3, 77] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }, { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }, { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }, { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] }, { rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] }, { rank := 0, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }, { rank := 1, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }, { rank := 2, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }, { rank := 3, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }, { rank := 4, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }]
@[irreducible] private def segment_000000_sm_final (s : Store) : Store := segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) s
@[irreducible] private def segment_000000_pm_final (s : Store) : Store := segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) s

private theorem segment_000000_hSm0 (smStore : Store) : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 400 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 300)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 400
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase4.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 400 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 300)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 4000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase4.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 4001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } 4001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase4.pmGraph t 1 1001 2001 3000 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_2 (pmStore : Store) : (segment_000000_pm_final pmStore) 4002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } 4002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase4.pmGraph t 2 1002 2002 3000 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_3 (pmStore : Store) : (segment_000000_pm_final pmStore) 4003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4003 = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } 4003
      (fun t => (bw_matmul (t 1003) (t 2003) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase4.pmGraph t 3 1003 2003 3000 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm0_4 (pmStore : Store) : (segment_000000_pm_final pmStore) 4004 = (bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3000)).1 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 4004 = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] } 4004
      (fun t => (bw_matmul (t 1004) (t 2004) (t 3000)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out MatmulQueryCase4.pmGraph t 4 1004 2004 3000 4004 5004 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1004 = (segment_000000_pm_final pmStore) 1004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 1004
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2004 = (segment_000000_pm_final pmStore) 2004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 2004
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 4004 = (bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3000)).1 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).1 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3000)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hSm1 (smStore : Store) : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 401 = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 300)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } 401
      (fun t => (bw_matmul (t 100) (t 200) (t 300)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase4.smGraph t 0 100 200 300 400 401 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 100 = (segment_000000_sm_final smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 200 = (segment_000000_sm_final smStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 300 = (segment_000000_sm_final smStore) 300 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [100, 200, 300], outs := [400, 401] } :: (segment_000000_sm_nodes.drop 1)) 300
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 401 = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 100) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 200) (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 300)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_sm_final smStore) 100) ((segment_000000_sm_final smStore) 200) ((segment_000000_sm_final smStore) 300)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_0 (pmStore : Store) : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5000 = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } 5000
      (fun t => (bw_matmul (t 1000) (t 2000) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase4.pmGraph t 0 1000 2000 3000 4000 5000 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2000 = (segment_000000_pm_final pmStore) 2000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 2000
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [1000, 2000, 3000], outs := [4000, 5000] } :: (segment_000000_pm_nodes.drop 1)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5000 = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2000) (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1000) ((segment_000000_pm_final pmStore) 2000) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_1 (pmStore : Store) : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5001 = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } 5001
      (fun t => (bw_matmul (t 1001) (t 2001) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase4.pmGraph t 1 1001 2001 3000 4001 5001 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1001 = (segment_000000_pm_final pmStore) 1001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 1001
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2001 = (segment_000000_pm_final pmStore) 2001 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 2001
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_matmul", ins := [1001, 2001, 3000], outs := [4001, 5001] } :: (segment_000000_pm_nodes.drop 2)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5001 = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2001) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1001) ((segment_000000_pm_final pmStore) 2001) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_2 (pmStore : Store) : (segment_000000_pm_final pmStore) 5002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5002 = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } 5002
      (fun t => (bw_matmul (t 1002) (t 2002) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase4.pmGraph t 2 1002 2002 3000 4002 5002 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1002 = (segment_000000_pm_final pmStore) 1002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 1002
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2002 = (segment_000000_pm_final pmStore) 2002 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 2002
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_matmul", ins := [1002, 2002, 3000], outs := [4002, 5002] } :: (segment_000000_pm_nodes.drop 3)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5002 = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2002) (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1002) ((segment_000000_pm_final pmStore) 2002) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_3 (pmStore : Store) : (segment_000000_pm_final pmStore) 5003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5003 = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } 5003
      (fun t => (bw_matmul (t 1003) (t 2003) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase4.pmGraph t 3 1003 2003 3000 4003 5003 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1003 = (segment_000000_pm_final pmStore) 1003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 1003
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2003 = (segment_000000_pm_final pmStore) 2003 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 2003
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_matmul", ins := [1003, 2003, 3000], outs := [4003, 5003] } :: (segment_000000_pm_nodes.drop 4)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5003 = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2003) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1003) ((segment_000000_pm_final pmStore) 2003) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hPm1_4 (pmStore : Store) : (segment_000000_pm_final pmStore) 5004 = (bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3000)).2 := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 4) ++ [{ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] }] ++ (segment_000000_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 5004 = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) (segment_000000_pm_nodes.drop 5)
      { rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] } 5004
      (fun t => (bw_matmul (t 1004) (t 2004) (t 3000)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out MatmulQueryCase4.pmGraph t 4 1004 2004 3000 4004 5004 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1004 = (segment_000000_pm_final pmStore) 1004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 1004
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2004 = (segment_000000_pm_final pmStore) 2004 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 2004
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000 = (segment_000000_pm_final pmStore) 3000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 4) ({ rank := 4, op := "OpName.BW_matmul", ins := [1004, 2004, 3000], outs := [4004, 5004] } :: (segment_000000_pm_nodes.drop 5)) 3000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 5004 = (bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3000)).2 := by
    calc
      _ = (bw_matmul (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 1004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 2004) (((segment_000000_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 3000)).2 := hout_prefix
      _ = (bw_matmul ((segment_000000_pm_final pmStore) 1004) ((segment_000000_pm_final pmStore) 2004) ((segment_000000_pm_final pmStore) 3000)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000000_hViewSm (smStore : Store) : (segment_000000_sm_final smStore) 700 = fw_view [2, 3, 77] ((segment_000000_sm_final smStore) 600) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore := by unfold segment_000000_sm_final; rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_view", ins := [600, 601], outs := [700], params := [2, 3, 77] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 700 = fw_view [2, 3, 77] (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 600) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_view", ins := [600, 601], outs := [700], params := [2, 3, 77] } 700
      (fun t => fw_view [2, 3, 77] (t 600)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_view_out MatmulQueryCase4.smGraph t 0 2 [3, 77] 600 601 700
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 600 = (segment_000000_sm_final smStore) 600 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_view", ins := [600, 601], outs := [700], params := [2, 3, 77] } :: (segment_000000_sm_nodes.drop 2)) 600
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 700 = fw_view [2, 3, 77] ((segment_000000_sm_final smStore) 600) := by
    calc
      _ = fw_view [2, 3, 77] (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.smGraph) smStore 600) := hout_prefix
      _ = fw_view [2, 3, 77] ((segment_000000_sm_final smStore) 600) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_hViewPm (pmStore : Store) : (segment_000000_pm_final pmStore) 7000 = fw_view [2, 3, 77] ((segment_000000_pm_final pmStore) 6000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore := by unfold segment_000000_pm_final; rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 9) ++ [{ rank := 4, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] }] ++ (segment_000000_pm_nodes.drop 10) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 7000 = fw_view [2, 3, 77] (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 6000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 9) (segment_000000_pm_nodes.drop 10)
      { rank := 4, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] } 7000
      (fun t => fw_view [2, 3, 77] (t 6000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_view_out MatmulQueryCase4.pmGraph t 4 2 [3, 77] 6000 6001 7000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 6000 = (segment_000000_pm_final pmStore) 6000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final MatmulQueryCase4.pmGraph pmStore
      (segment_000000_pm_nodes.take 9) ({ rank := 4, op := "OpName.BW_view", ins := [6000, 6001], outs := [7000], params := [2, 3, 77] } :: (segment_000000_pm_nodes.drop 10)) 6000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 7000 = fw_view [2, 3, 77] ((segment_000000_pm_final pmStore) 6000) := by
    calc
      _ = fw_view [2, 3, 77] (((segment_000000_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful MatmulQueryCase4.pmGraph) pmStore 6000) := hout_prefix
      _ = fw_view [2, 3, 77] ((segment_000000_pm_final pmStore) 6000) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_transpose_shape (t : Tensor) (a b c d : Nat)
    (ht : t.shape = [a,b,c,d]) : (transpose2d t).shape = [a,b,d,c] := by
  simp only [transpose2d, ht, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, Tensor.mkShape]

private theorem segment_000000_semantic_fst (g x y py : Tensor) (gs xs : List Tensor)
    (hg : ShardedRel g gs 2 [2, 3, 25, 11] [2, 3, 5, 11]) (hx : ShardedRel x xs 2 [2, 3, 25, 7] [2, 3, 5, 7])
    (hy : y = py ∧ y.shape = [2, 3, 7, 11] ∧ py.shape = [2, 3, 7, 11])
    (hgl : gs.length = 5) (hxl : xs.length = 5) :
    ShardedRel (bw_matmul g x y).1 (gs.map (fun z => (bw_matmul z x py).1)) 2 [2, 3, 25, 7] [2, 3, 5, 7] := by
  have hyT : transpose2d y = transpose2d py ∧ (transpose2d y).shape = [2, 3, 11, 7] ∧ (transpose2d py).shape = [2, 3, 11, 7] :=
    ⟨congrArg transpose2d hy.1, segment_000000_transpose_shape y 2 3 7 11 hy.2.1, segment_000000_transpose_shape py 2 3 7 11 hy.2.2⟩
  exact TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4 (K := 5) (b := 2) (h := 3) (q := 5) (k := 11) (m := 7) hg hyT (by decide) (by decide) (by decide) (by decide) hgl

private theorem segment_000000_semantic_snd (g x y py : Tensor) (gs xs : List Tensor)
    (hg : ShardedRel g gs 2 [2, 3, 25, 11] [2, 3, 5, 11]) (hx : ShardedRel x xs 2 [2, 3, 25, 7] [2, 3, 5, 7])
    (hy : y = py ∧ y.shape = [2, 3, 7, 11] ∧ py.shape = [2, 3, 7, 11])
    (hgl : gs.length = 5) (hxl : xs.length = 5) :
    (bw_matmul g x y).2 = tensorSum (List.zipWith (fun a z => (bw_matmul a z py).2) gs xs) := by
  rw [hg.full_value, hx.full_value, hgl, hxl, hy.1]
  exact TrainVerify.Denote.bw_matmul_snd_query_reduction_rank4 5 2 3 5 7 11 gs xs py (by decide) (by decide) (by decide) (by decide) (by decide) hgl hxl hg.shard_shapes hx.shard_shapes

set_option maxHeartbeats 500000 in
private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_000000.Holds smStore pmStore) :
    state_000001.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_000000.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate <;> native_decide
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 100) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] 2 [2, 3, 25, 11] [2, 3, 5, 11] at hg
  have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 200) [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] 2 [2, 3, 25, 7] [2, 3, 5, 7] at hx
  have hy : fact_y.Holds smFinal pmFinal := hframe _ (by native_decide)
  change smFinal 300 = pmFinal 3000 ∧ (smFinal 300).shape = [2, 3, 7, 11] ∧ (pmFinal 3000).shape = [2, 3, 7, 11] at hy
  have hS0 := segment_000000_hSm0 smStore
  change smFinal 400 = (bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).1 at hS0
  have hP0_0 := segment_000000_hPm0_0 pmStore
  change pmFinal 4000 = (bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).1 at hP0_0
  have hP0_1 := segment_000000_hPm0_1 pmStore
  change pmFinal 4001 = (bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3000)).1 at hP0_1
  have hP0_2 := segment_000000_hPm0_2 pmStore
  change pmFinal 4002 = (bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3000)).1 at hP0_2
  have hP0_3 := segment_000000_hPm0_3 pmStore
  change pmFinal 4003 = (bw_matmul (pmFinal 1003) (pmFinal 2003) (pmFinal 3000)).1 at hP0_3
  have hP0_4 := segment_000000_hPm0_4 pmStore
  change pmFinal 4004 = (bw_matmul (pmFinal 1004) (pmFinal 2004) (pmFinal 3000)).1 at hP0_4
  have hC0 := segment_000000_semantic_fst (smFinal 100) (smFinal 200) (smFinal 300) (pmFinal 3000) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] hg hx hy (by rfl) (by rfl)
  have hout0 : fact_out0.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 400) [pmFinal 4000, pmFinal 4001, pmFinal 4002, pmFinal 4003, pmFinal 4004] 2 [2, 3, 25, 7] [2, 3, 5, 7]
    rw [hS0, hP0_0, hP0_1, hP0_2, hP0_3, hP0_4]
    simpa only [List.map, bw_matmul, batchedMatmulBwd] using hC0
  have hS1 := segment_000000_hSm1 smStore
  change smFinal 401 = (bw_matmul (smFinal 100) (smFinal 200) (smFinal 300)).2 at hS1
  have hP1_0 := segment_000000_hPm1_0 pmStore
  change pmFinal 5000 = (bw_matmul (pmFinal 1000) (pmFinal 2000) (pmFinal 3000)).2 at hP1_0
  have hP1_1 := segment_000000_hPm1_1 pmStore
  change pmFinal 5001 = (bw_matmul (pmFinal 1001) (pmFinal 2001) (pmFinal 3000)).2 at hP1_1
  have hP1_2 := segment_000000_hPm1_2 pmStore
  change pmFinal 5002 = (bw_matmul (pmFinal 1002) (pmFinal 2002) (pmFinal 3000)).2 at hP1_2
  have hP1_3 := segment_000000_hPm1_3 pmStore
  change pmFinal 5003 = (bw_matmul (pmFinal 1003) (pmFinal 2003) (pmFinal 3000)).2 at hP1_3
  have hP1_4 := segment_000000_hPm1_4 pmStore
  change pmFinal 5004 = (bw_matmul (pmFinal 1004) (pmFinal 2004) (pmFinal 3000)).2 at hP1_4
  have hC1 := segment_000000_semantic_snd (smFinal 100) (smFinal 200) (smFinal 300) (pmFinal 3000) [pmFinal 1000, pmFinal 1001, pmFinal 1002, pmFinal 1003, pmFinal 1004] [pmFinal 2000, pmFinal 2001, pmFinal 2002, pmFinal 2003, pmFinal 2004] hg hx hy (by rfl) (by rfl)
  simp only [List.zipWith] at hC1
  rw [←hS1, ←hP1_0, ←hP1_1, ←hP1_2, ←hP1_3, ←hP1_4] at hC1
  have hRV : smFinal 401 = allReducePrim [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003, pmFinal 5004].length 0 [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003, pmFinal 5004] := hC1
  have hFull : (smFinal 401).shape = [2, 3, 7, 11] := by
    rw [hS1]
    exact fw_matmul_rank4_shape _ _ 2 3 7 25 11 (segment_000000_transpose_shape _ 2 3 25 7 hx.full_shape) hg.full_shape
  have hShape0 : (pmFinal 5000).shape = [2, 3, 7, 11] := by
    rw [hP1_0]
    exact fw_matmul_rank4_shape _ _ 2 3 7 5 11 (segment_000000_transpose_shape _ 2 3 5 7 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShape1 : (pmFinal 5001).shape = [2, 3, 7, 11] := by
    rw [hP1_1]
    exact fw_matmul_rank4_shape _ _ 2 3 7 5 11 (segment_000000_transpose_shape _ 2 3 5 7 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShape2 : (pmFinal 5002).shape = [2, 3, 7, 11] := by
    rw [hP1_2]
    exact fw_matmul_rank4_shape _ _ 2 3 7 5 11 (segment_000000_transpose_shape _ 2 3 5 7 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShape3 : (pmFinal 5003).shape = [2, 3, 7, 11] := by
    rw [hP1_3]
    exact fw_matmul_rank4_shape _ _ 2 3 7 5 11 (segment_000000_transpose_shape _ 2 3 5 7 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShape4 : (pmFinal 5004).shape = [2, 3, 7, 11] := by
    rw [hP1_4]
    exact fw_matmul_rank4_shape _ _ 2 3 7 5 11 (segment_000000_transpose_shape _ 2 3 5 7 (hx.shard_shapes _ (by simp))) (hg.shard_shapes _ (by simp))
  have hShapes : ∀ z ∈ [pmFinal 5000, pmFinal 5001, pmFinal 5002, pmFinal 5003, pmFinal 5004], z.shape = [2, 3, 7, 11] := by
    simp only [List.forall_mem_cons]
    exact ⟨hShape0, hShape1, hShape2, hShape3, hShape4, List.forall_mem_nil _⟩
  have hout1 : fact_out1.Holds smFinal pmFinal := by
    exact {
      full_value := hRV
      full_shape := hFull
      contributions_nonempty := List.cons_ne_nil _ _
      contribution_shapes := hShapes
      reduced_shape := by simp only [List.map]; rw [←hRV]; exact hFull }
  have hvi : fact_vi.Holds smFinal pmFinal := hframe _ (by native_decide)
  have hVS := segment_000000_hViewSm smStore
  have hVP := segment_000000_hViewPm pmStore
  change smFinal 700 = fw_view [2, 3, 77] (smFinal 600) at hVS
  change pmFinal 7000 = fw_view [2, 3, 77] (pmFinal 6000) at hVP
  have houtV : fact_vo.Holds smFinal pmFinal := by
    change smFinal 700 = pmFinal 7000 ∧ _ ∧ _
    rw [hVS, hVP]
    exact JoinedRel.fw_view [2, 3, 77] [2, 3, 7, 11] hvi
  intro fact hfact
  have hc : fact ∈ [fact_out0, fact_out1, fact_vo] ++ state_000000.facts := (show state_000001.facts ⊆ [fact_out0, fact_out1, fact_vo] ++ state_000000.facts by native_decide) hfact
  simp only [List.mem_append] at hc
  rcases hc with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl | rfl
    · exact hout0
    · exact hout1
    · exact houtV
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate MatmulQueryCase4.smGraph MatmulQueryCase4.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by intro smStore pmStore h; have h' := segment_000000_sound smStore pmStore h; unfold segment_000000_sm_final segment_000000_pm_final at h'; exact h'

#print axioms segment_000000
end
end MatmulQueryCase4
