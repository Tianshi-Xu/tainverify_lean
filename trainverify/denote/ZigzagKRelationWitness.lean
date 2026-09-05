import denote.RelationCompiler

open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
open TrainVerify.Denote.ZigzagCollective

namespace TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness
noncomputable section

#check RelationFact.zigzagK
#check ZigzagKRel
#check ZigzagKRel.of_sharded

/-- Distinct rank and local-position values; no constant/zero tensor shortcut. -/
def source (rank : Nat) : Tensor :=
  Tensor.mkShape [4, 2] (fun i => ((100 * rank + i.val + 1 : Nat) : Scalar))
def sources : List Tensor := [source 0, source 1, source 2]
def full : Tensor := allGatherPrimDimN 0 3 0 sources
def cu : Tensor := Tensor.mkShape [2] (fun i => if i.val = 0 then 0 else 12)
def out (rank : Nat) : Tensor :=
  fw_maybe_shuffle_collective sources (decodeCuSeqlens cu) 3 rank

theorem decode_cu : decodeCuSeqlens cu = [0, 12] := by
  unfold decodeCuSeqlens cu
  change (List.range 2).map _ = _
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.map_append]
  simp only [valAt, Tensor.mkShape, prodShape]
  norm_num [scalarToNat]

theorem metadata_shape : cu.shape = [2] := rfl

theorem sharded_input : ShardedRel full sources 0 [12, 2] [4, 2] := by
  refine ⟨rfl, ?_, by simp [sources], by decide, ?_, rfl⟩
  · unfold full
    rw [allGatherPrimDimN_shape 0 3 sources [4, 2] rfl]
    rfl
  · intro x hx
    simp only [sources, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rfl

theorem cu_wf : ZigzagCuWF (decodeCuSeqlens cu) sources sources.length := by
  rw [decode_cu]
  refine ⟨by decide, rfl, rfl, by decide, ?_, ?_, ?_, ?_, rfl⟩
  · intro s hs
    have : s = 0 := by simp only [List.length_cons, List.length_nil] at hs; omega
    subst s
    decide
  · intro s hs
    have : s = 0 := by simp only [List.length_cons, List.length_nil] at hs; omega
    subst s
    decide
  · intro x hx
    simp only [sources, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> decide
  · intro x hx
    simp only [sources, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rfl

/-- All entry hypotheses are inhabited by the concrete, nonzero CP3 tensors. -/
theorem entry : ZigzagKRel full [out 0, out 1, out 2] cu [12, 2] [4, 2] := by
  exact ZigzagKRel.of_sharded sharded_input cu_wf

/-- Entire asymmetric token permutation, including the final rank. -/
theorem positions :
    (List.range 3).map (fun r => (List.range 4).map (zigzagPos [0, 12] 3 r)) =
      [[0, 1, 10, 11], [2, 3, 8, 9], [4, 5, 6, 7]] := by
  decide

/-- Actual collective values from both halves and every rank, not just shapes. -/
theorem values :
    [valAt (out 0) 0, valAt (out 0) 4,
     valAt (out 1) 0, valAt (out 1) 4,
     valAt (out 2) 0, valAt (out 2) 4] =
      ([1, 205, 5, 201, 101, 105] : List Scalar) := by
  unfold out
  rw [decode_cu]
  change [((1 : Nat) : Scalar), ((205 : Nat) : Scalar),
    ((5 : Nat) : Scalar), ((201 : Nat) : Scalar),
    ((101 : Nat) : Scalar), ((105 : Nat) : Scalar)] = _
  norm_num

def fact : RelationFact := .zigzagK 100 [200, 201, 202] 900 [12, 2] [4, 2]
def sm : Store := fun _ => full
def pm : Store := fun tid =>
  if tid = 200 then out 0 else if tid = 201 then out 1
  else if tid = 202 then out 2 else cu

theorem holds : fact.Holds sm pm := by
  change ZigzagKRel full [out 0, out 1, out 2] cu [12, 2] [4, 2]
  exact entry

theorem dependencies : fact.smTids = [100] ∧ fact.pmTids = [200, 201, 202, 900] :=
  ⟨rfl, rfl⟩

theorem last_rank_dependency : 202 ∈ fact.pmTids := by decide
theorem metadata_dependency : 900 ∈ fact.pmTids := by decide

/-- Changes outside the complete footprint preserve this inhabited boundary. -/
theorem framed (sm' pm' : Store)
    (hsm : sm' 100 = full)
    (hpm : ∀ tid ∈ [200, 201, 202, 900], pm' tid = pm tid) :
    fact.Holds sm' pm' := by
  apply RelationFact.Holds.frame holds
  · intro tid htid
    have : tid = 100 := List.mem_singleton.mp htid
    subst tid
    exact hsm
  · exact hpm

end
end TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness
