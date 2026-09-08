import denote.GroupScopedEval
namespace TrainVerify.Denote.GroupScopedEval.Witness
set_option maxHeartbeats 500000
noncomputable section
def x : Tensor := Tensor.mkShape [2, 12] (fun i => ((i.val*i.val+3*i.val+7 : Nat) : Scalar))
def s : Store := fun _ => x
def g : GraphDecl := {numRanks := 4, nodes := []}
def node (rank : Nat) : NodeDecl := {rank := rank, op := "OpName.ChunkPrim", ins := [10], outs := [20], params := [1]}
theorem rank2_resolved : resolve 4 2 (some [2, 3]) = some ([2, 3], 0) := by decide
theorem rank2_input : ChunkInput [2, 3] 1 x := by change 1 < 2 ∧ 0 < 12 ∧ 2 ∣ 12; decide
theorem rank2_step : step g (.group (some [2, 3])) s (node 2) = some (localStep [2, 3] s (node 2)) :=
  step_scoped g s (node 2) [2, 3] (by decide) (by rfl)
theorem rank2_shape : (localStep [2, 3] s (node 2) 20).shape = [2, 6] := by rfl
theorem rank2_value_0 : valAt (localStep [2, 3] s (node 2) 20) 0 = 7 := by
  change ((7 : Nat) : Scalar) = 7; norm_num
#print axioms rank2_value_0
theorem rank2_value_1 : valAt (localStep [2, 3] s (node 2) 20) 1 = 11 := by
  change ((11 : Nat) : Scalar) = 11; norm_num
#print axioms rank2_value_1
theorem rank2_value_2 : valAt (localStep [2, 3] s (node 2) 20) 2 = 17 := by
  change ((17 : Nat) : Scalar) = 17; norm_num
#print axioms rank2_value_2
theorem rank2_value_3 : valAt (localStep [2, 3] s (node 2) 20) 3 = 25 := by
  change ((25 : Nat) : Scalar) = 25; norm_num
#print axioms rank2_value_3
theorem rank2_value_4 : valAt (localStep [2, 3] s (node 2) 20) 4 = 35 := by
  change ((35 : Nat) : Scalar) = 35; norm_num
#print axioms rank2_value_4
theorem rank2_value_5 : valAt (localStep [2, 3] s (node 2) 20) 5 = 47 := by
  change ((47 : Nat) : Scalar) = 47; norm_num
#print axioms rank2_value_5
theorem rank2_value_6 : valAt (localStep [2, 3] s (node 2) 20) 6 = 187 := by
  change ((187 : Nat) : Scalar) = 187; norm_num
#print axioms rank2_value_6
theorem rank2_value_7 : valAt (localStep [2, 3] s (node 2) 20) 7 = 215 := by
  change ((215 : Nat) : Scalar) = 215; norm_num
#print axioms rank2_value_7
theorem rank2_value_8 : valAt (localStep [2, 3] s (node 2) 20) 8 = 245 := by
  change ((245 : Nat) : Scalar) = 245; norm_num
#print axioms rank2_value_8
theorem rank2_value_9 : valAt (localStep [2, 3] s (node 2) 20) 9 = 277 := by
  change ((277 : Nat) : Scalar) = 277; norm_num
#print axioms rank2_value_9
theorem rank2_value_10 : valAt (localStep [2, 3] s (node 2) 20) 10 = 311 := by
  change ((311 : Nat) : Scalar) = 311; norm_num
#print axioms rank2_value_10
theorem rank2_value_11 : valAt (localStep [2, 3] s (node 2) 20) 11 = 347 := by
  change ((347 : Nat) : Scalar) = 347; norm_num
#print axioms rank2_value_11
#print axioms rank2_step
theorem rank3_resolved : resolve 4 3 (some [2, 3]) = some ([2, 3], 1) := by decide
theorem rank3_input : ChunkInput [2, 3] 1 x := by change 1 < 2 ∧ 0 < 12 ∧ 2 ∣ 12; decide
theorem rank3_step : step g (.group (some [2, 3])) s (node 3) = some (localStep [2, 3] s (node 3)) :=
  step_scoped g s (node 3) [2, 3] (by decide) (by rfl)
theorem rank3_shape : (localStep [2, 3] s (node 3) 20).shape = [2, 6] := by rfl
theorem rank3_value_0 : valAt (localStep [2, 3] s (node 3) 20) 0 = 61 := by
  change ((61 : Nat) : Scalar) = 61; norm_num
#print axioms rank3_value_0
theorem rank3_value_1 : valAt (localStep [2, 3] s (node 3) 20) 1 = 77 := by
  change ((77 : Nat) : Scalar) = 77; norm_num
#print axioms rank3_value_1
theorem rank3_value_2 : valAt (localStep [2, 3] s (node 3) 20) 2 = 95 := by
  change ((95 : Nat) : Scalar) = 95; norm_num
#print axioms rank3_value_2
theorem rank3_value_3 : valAt (localStep [2, 3] s (node 3) 20) 3 = 115 := by
  change ((115 : Nat) : Scalar) = 115; norm_num
#print axioms rank3_value_3
theorem rank3_value_4 : valAt (localStep [2, 3] s (node 3) 20) 4 = 137 := by
  change ((137 : Nat) : Scalar) = 137; norm_num
#print axioms rank3_value_4
theorem rank3_value_5 : valAt (localStep [2, 3] s (node 3) 20) 5 = 161 := by
  change ((161 : Nat) : Scalar) = 161; norm_num
#print axioms rank3_value_5
theorem rank3_value_6 : valAt (localStep [2, 3] s (node 3) 20) 6 = 385 := by
  change ((385 : Nat) : Scalar) = 385; norm_num
#print axioms rank3_value_6
theorem rank3_value_7 : valAt (localStep [2, 3] s (node 3) 20) 7 = 425 := by
  change ((425 : Nat) : Scalar) = 425; norm_num
#print axioms rank3_value_7
theorem rank3_value_8 : valAt (localStep [2, 3] s (node 3) 20) 8 = 467 := by
  change ((467 : Nat) : Scalar) = 467; norm_num
#print axioms rank3_value_8
theorem rank3_value_9 : valAt (localStep [2, 3] s (node 3) 20) 9 = 511 := by
  change ((511 : Nat) : Scalar) = 511; norm_num
#print axioms rank3_value_9
theorem rank3_value_10 : valAt (localStep [2, 3] s (node 3) 20) 10 = 557 := by
  change ((557 : Nat) : Scalar) = 557; norm_num
#print axioms rank3_value_10
theorem rank3_value_11 : valAt (localStep [2, 3] s (node 3) 20) 11 = 605 := by
  change ((605 : Nat) : Scalar) = 605; norm_num
#print axioms rank3_value_11
#print axioms rank3_step
theorem noncontiguous_resolved : resolve 4 2 (some [0, 2]) = some ([0, 2], 1) := by decide
theorem noncontiguous_input : ChunkInput [0, 2] 1 x := by change 1 < 2 ∧ 0 < 12 ∧ 2 ∣ 12; decide
theorem noncontiguous_step : step g (.group (some [0, 2])) s (node 2) = some (localStep [0, 2] s (node 2)) :=
  step_scoped g s (node 2) [0, 2] (by decide) (by rfl)
theorem noncontiguous_shape : (localStep [0, 2] s (node 2) 20).shape = [2, 6] := by rfl
theorem noncontiguous_value_0 : valAt (localStep [0, 2] s (node 2) 20) 0 = 61 := by
  change ((61 : Nat) : Scalar) = 61; norm_num
#print axioms noncontiguous_value_0
theorem noncontiguous_value_1 : valAt (localStep [0, 2] s (node 2) 20) 1 = 77 := by
  change ((77 : Nat) : Scalar) = 77; norm_num
#print axioms noncontiguous_value_1
theorem noncontiguous_value_2 : valAt (localStep [0, 2] s (node 2) 20) 2 = 95 := by
  change ((95 : Nat) : Scalar) = 95; norm_num
#print axioms noncontiguous_value_2
theorem noncontiguous_value_3 : valAt (localStep [0, 2] s (node 2) 20) 3 = 115 := by
  change ((115 : Nat) : Scalar) = 115; norm_num
#print axioms noncontiguous_value_3
theorem noncontiguous_value_4 : valAt (localStep [0, 2] s (node 2) 20) 4 = 137 := by
  change ((137 : Nat) : Scalar) = 137; norm_num
#print axioms noncontiguous_value_4
theorem noncontiguous_value_5 : valAt (localStep [0, 2] s (node 2) 20) 5 = 161 := by
  change ((161 : Nat) : Scalar) = 161; norm_num
#print axioms noncontiguous_value_5
theorem noncontiguous_value_6 : valAt (localStep [0, 2] s (node 2) 20) 6 = 385 := by
  change ((385 : Nat) : Scalar) = 385; norm_num
#print axioms noncontiguous_value_6
theorem noncontiguous_value_7 : valAt (localStep [0, 2] s (node 2) 20) 7 = 425 := by
  change ((425 : Nat) : Scalar) = 425; norm_num
#print axioms noncontiguous_value_7
theorem noncontiguous_value_8 : valAt (localStep [0, 2] s (node 2) 20) 8 = 467 := by
  change ((467 : Nat) : Scalar) = 467; norm_num
#print axioms noncontiguous_value_8
theorem noncontiguous_value_9 : valAt (localStep [0, 2] s (node 2) 20) 9 = 511 := by
  change ((511 : Nat) : Scalar) = 511; norm_num
#print axioms noncontiguous_value_9
theorem noncontiguous_value_10 : valAt (localStep [0, 2] s (node 2) 20) 10 = 557 := by
  change ((557 : Nat) : Scalar) = 557; norm_num
#print axioms noncontiguous_value_10
theorem noncontiguous_value_11 : valAt (localStep [0, 2] s (node 2) 20) 11 = 605 := by
  change ((605 : Nat) : Scalar) = 605; norm_num
#print axioms noncontiguous_value_11
#print axioms noncontiguous_step
theorem k1_resolved : resolve 4 3 (some [3]) = some ([3], 0) := by decide
theorem k1_input : ChunkInput [3] 1 x := by change 1 < 2 ∧ 0 < 12 ∧ 1 ∣ 12; decide
theorem k1_step : step g (.group (some [3])) s (node 3) = some (localStep [3] s (node 3)) :=
  step_scoped g s (node 3) [3] (by decide) (by rfl)
theorem k1_shape : (localStep [3] s (node 3) 20).shape = [2, 12] := by rfl
theorem k1_value_0 : valAt (localStep [3] s (node 3) 20) 0 = 7 := by
  change ((7 : Nat) : Scalar) = 7; norm_num
#print axioms k1_value_0
theorem k1_value_1 : valAt (localStep [3] s (node 3) 20) 1 = 11 := by
  change ((11 : Nat) : Scalar) = 11; norm_num
#print axioms k1_value_1
theorem k1_value_2 : valAt (localStep [3] s (node 3) 20) 2 = 17 := by
  change ((17 : Nat) : Scalar) = 17; norm_num
#print axioms k1_value_2
theorem k1_value_3 : valAt (localStep [3] s (node 3) 20) 3 = 25 := by
  change ((25 : Nat) : Scalar) = 25; norm_num
#print axioms k1_value_3
theorem k1_value_4 : valAt (localStep [3] s (node 3) 20) 4 = 35 := by
  change ((35 : Nat) : Scalar) = 35; norm_num
#print axioms k1_value_4
theorem k1_value_5 : valAt (localStep [3] s (node 3) 20) 5 = 47 := by
  change ((47 : Nat) : Scalar) = 47; norm_num
#print axioms k1_value_5
theorem k1_value_6 : valAt (localStep [3] s (node 3) 20) 6 = 61 := by
  change ((61 : Nat) : Scalar) = 61; norm_num
#print axioms k1_value_6
theorem k1_value_7 : valAt (localStep [3] s (node 3) 20) 7 = 77 := by
  change ((77 : Nat) : Scalar) = 77; norm_num
#print axioms k1_value_7
theorem k1_value_8 : valAt (localStep [3] s (node 3) 20) 8 = 95 := by
  change ((95 : Nat) : Scalar) = 95; norm_num
#print axioms k1_value_8
theorem k1_value_9 : valAt (localStep [3] s (node 3) 20) 9 = 115 := by
  change ((115 : Nat) : Scalar) = 115; norm_num
#print axioms k1_value_9
theorem k1_value_10 : valAt (localStep [3] s (node 3) 20) 10 = 137 := by
  change ((137 : Nat) : Scalar) = 137; norm_num
#print axioms k1_value_10
theorem k1_value_11 : valAt (localStep [3] s (node 3) 20) 11 = 161 := by
  change ((161 : Nat) : Scalar) = 161; norm_num
#print axioms k1_value_11
theorem k1_value_12 : valAt (localStep [3] s (node 3) 20) 12 = 187 := by
  change ((187 : Nat) : Scalar) = 187; norm_num
#print axioms k1_value_12
theorem k1_value_13 : valAt (localStep [3] s (node 3) 20) 13 = 215 := by
  change ((215 : Nat) : Scalar) = 215; norm_num
#print axioms k1_value_13
theorem k1_value_14 : valAt (localStep [3] s (node 3) 20) 14 = 245 := by
  change ((245 : Nat) : Scalar) = 245; norm_num
#print axioms k1_value_14
theorem k1_value_15 : valAt (localStep [3] s (node 3) 20) 15 = 277 := by
  change ((277 : Nat) : Scalar) = 277; norm_num
#print axioms k1_value_15
theorem k1_value_16 : valAt (localStep [3] s (node 3) 20) 16 = 311 := by
  change ((311 : Nat) : Scalar) = 311; norm_num
#print axioms k1_value_16
theorem k1_value_17 : valAt (localStep [3] s (node 3) 20) 17 = 347 := by
  change ((347 : Nat) : Scalar) = 347; norm_num
#print axioms k1_value_17
theorem k1_value_18 : valAt (localStep [3] s (node 3) 20) 18 = 385 := by
  change ((385 : Nat) : Scalar) = 385; norm_num
#print axioms k1_value_18
theorem k1_value_19 : valAt (localStep [3] s (node 3) 20) 19 = 425 := by
  change ((425 : Nat) : Scalar) = 425; norm_num
#print axioms k1_value_19
theorem k1_value_20 : valAt (localStep [3] s (node 3) 20) 20 = 467 := by
  change ((467 : Nat) : Scalar) = 467; norm_num
#print axioms k1_value_20
theorem k1_value_21 : valAt (localStep [3] s (node 3) 20) 21 = 511 := by
  change ((511 : Nat) : Scalar) = 511; norm_num
#print axioms k1_value_21
theorem k1_value_22 : valAt (localStep [3] s (node 3) 20) 22 = 557 := by
  change ((557 : Nat) : Scalar) = 557; norm_num
#print axioms k1_value_22
theorem k1_value_23 : valAt (localStep [3] s (node 3) 20) 23 = 605 := by
  change ((605 : Nat) : Scalar) = 605; norm_num
#print axioms k1_value_23
#print axioms k1_step
theorem k3_resolved : resolve 4 3 (some [0, 1, 3]) = some ([0, 1, 3], 2) := by decide
theorem k3_input : ChunkInput [0, 1, 3] 1 x := by change 1 < 2 ∧ 0 < 12 ∧ 3 ∣ 12; decide
theorem k3_step : step g (.group (some [0, 1, 3])) s (node 3) = some (localStep [0, 1, 3] s (node 3)) :=
  step_scoped g s (node 3) [0, 1, 3] (by decide) (by rfl)
theorem k3_shape : (localStep [0, 1, 3] s (node 3) 20).shape = [2, 4] := by rfl
theorem k3_value_0 : valAt (localStep [0, 1, 3] s (node 3) 20) 0 = 95 := by
  change ((95 : Nat) : Scalar) = 95; norm_num
#print axioms k3_value_0
theorem k3_value_1 : valAt (localStep [0, 1, 3] s (node 3) 20) 1 = 115 := by
  change ((115 : Nat) : Scalar) = 115; norm_num
#print axioms k3_value_1
theorem k3_value_2 : valAt (localStep [0, 1, 3] s (node 3) 20) 2 = 137 := by
  change ((137 : Nat) : Scalar) = 137; norm_num
#print axioms k3_value_2
theorem k3_value_3 : valAt (localStep [0, 1, 3] s (node 3) 20) 3 = 161 := by
  change ((161 : Nat) : Scalar) = 161; norm_num
#print axioms k3_value_3
theorem k3_value_4 : valAt (localStep [0, 1, 3] s (node 3) 20) 4 = 467 := by
  change ((467 : Nat) : Scalar) = 467; norm_num
#print axioms k3_value_4
theorem k3_value_5 : valAt (localStep [0, 1, 3] s (node 3) 20) 5 = 511 := by
  change ((511 : Nat) : Scalar) = 511; norm_num
#print axioms k3_value_5
theorem k3_value_6 : valAt (localStep [0, 1, 3] s (node 3) 20) 6 = 557 := by
  change ((557 : Nat) : Scalar) = 557; norm_num
#print axioms k3_value_6
theorem k3_value_7 : valAt (localStep [0, 1, 3] s (node 3) 20) 7 = 605 := by
  change ((605 : Nat) : Scalar) = 605; norm_num
#print axioms k3_value_7
#print axioms k3_step
theorem old_world_value : valAt (applyNode g s (node 2) 20) 0 = 61 := by
  change ((61 : Nat) : Scalar) = 61; norm_num
theorem old_world_differs : localStep [2,3] s (node 2) 20 ≠ applyNode g s (node 2) 20 := by
  intro h
  have he := congrArg (fun t => valAt t 0) h
  rw [rank2_value_0, old_world_value] at he
  norm_num at he
#print axioms old_world_differs
theorem reject_empty : resolve 4 2 (some []) = none := by decide
#print axioms reject_empty
theorem reject_duplicate : resolve 4 2 (some [2, 2]) = none := by decide
#print axioms reject_duplicate
theorem reject_nonmember : resolve 4 2 (some [0, 1]) = none := by decide
#print axioms reject_nonmember
theorem reject_out_of_world : resolve 4 2 (some [2, 4]) = none := by decide
#print axioms reject_out_of_world
theorem reject_missing : resolve 4 2 none = none := rfl
theorem membership_no_alias : resolve 4 2 (some [2,3]) ≠ resolve 4 2 (some [0,1]) := by decide
theorem ordered_membership_no_alias : resolve 4 2 (some [2,3]) ≠ resolve 4 2 (some [0,2]) := by decide
#print axioms membership_no_alias
#print axioms ordered_membership_no_alias
#print axioms rank2_resolved
#print axioms rank2_input
#print axioms rank2_shape
#print axioms rank3_resolved
#print axioms rank3_input
#print axioms rank3_shape
#print axioms noncontiguous_resolved
#print axioms noncontiguous_input
#print axioms noncontiguous_shape
#print axioms k1_resolved
#print axioms k1_input
#print axioms k1_shape
#print axioms k3_resolved
#print axioms k3_input
#print axioms k3_shape
#print axioms old_world_value
#print axioms reject_missing
end
end TrainVerify.Denote.GroupScopedEval.Witness
