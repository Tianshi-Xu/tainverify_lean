import denote.AllToAllSourceFaithful
namespace TrainVerify.Denote.AllToAllSourceFaithful.Witness
set_option maxHeartbeats 500000
noncomputable section
-- Generated CPU derived-source-flow replay; no GPU/collective invocation.
def sample (sh : Shape) (base : Nat) : Tensor :=
  Tensor.mkShape sh (fun j => ((base + j.val : Nat) : Scalar))
def xs_k1_i0_o0_d0 : List Tensor := [sample [1, 2] 200]
theorem shape_k1_i0_o0_d0 : (tensor 1 0 0 0 xs_k1_i0_o0_d0).shape = [1, 2] := by
  rfl
theorem value_k1_i0_o0_d0_0 : valAt (tensor 1 0 0 0 xs_k1_i0_o0_d0) 0 = (200 : Scalar) := by
  rfl
theorem value_k1_i0_o0_d0_1 : valAt (tensor 1 0 0 0 xs_k1_i0_o0_d0) 1 = (201 : Scalar) := by
  rfl
def store_k1_i0_o0_d0 : Store := fun tid => sample [1, 2] (100 * tid)
def node_k1_i0_o0_d0 : NodeDecl := {rank := 2, op := "OpName.AllToAllPrim", ins := [2], outs := [99], params := [0, 0]}
theorem contract_k1_i0_o0_d0 : NodeContract [2] id store_k1_i0_o0_d0 node_k1_i0_o0_d0 0 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [1, 2], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [1, 2] 200] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl
  all_goals rfl
theorem step_k1_i0_o0_d0 : step {numRanks := 6, nodes := []} (some [2]) id store_k1_i0_o0_d0 node_k1_i0_o0_d0 = .ok (localStep [2] store_k1_i0_o0_d0 node_k1_i0_o0_d0 0 0) := by
  exact step_valid _ _ _ _ _ 0 0 99 (by decide) contract_k1_i0_o0_d0
def xs_k1_i1_o1_d0 : List Tensor := [sample [1, 2] 200]
theorem shape_k1_i1_o1_d0 : (tensor 1 0 1 1 xs_k1_i1_o1_d0).shape = [1, 2] := by
  rfl
theorem value_k1_i1_o1_d0_0 : valAt (tensor 1 0 1 1 xs_k1_i1_o1_d0) 0 = (200 : Scalar) := by
  rfl
theorem value_k1_i1_o1_d0_1 : valAt (tensor 1 0 1 1 xs_k1_i1_o1_d0) 1 = (201 : Scalar) := by
  rfl
def store_k1_i1_o1_d0 : Store := fun tid => sample [1, 2] (100 * tid)
def node_k1_i1_o1_d0 : NodeDecl := {rank := 2, op := "OpName.AllToAllPrim", ins := [2], outs := [99], params := [1, 1]}
theorem contract_k1_i1_o1_d0 : NodeContract [2] id store_k1_i1_o1_d0 node_k1_i1_o1_d0 1 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [1, 2], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [1, 2] 200] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl
  all_goals rfl
theorem step_k1_i1_o1_d0 : step {numRanks := 6, nodes := []} (some [2]) id store_k1_i1_o1_d0 node_k1_i1_o1_d0 = .ok (localStep [2] store_k1_i1_o1_d0 node_k1_i1_o1_d0 1 1) := by
  exact step_valid _ _ _ _ _ 1 1 99 (by decide) contract_k1_i1_o1_d0
def xs_k1_i0_o1_d0 : List Tensor := [sample [1, 2] 200]
theorem shape_k1_i0_o1_d0 : (tensor 1 0 0 1 xs_k1_i0_o1_d0).shape = [1, 2] := by
  rfl
theorem value_k1_i0_o1_d0_0 : valAt (tensor 1 0 0 1 xs_k1_i0_o1_d0) 0 = (200 : Scalar) := by
  rfl
theorem value_k1_i0_o1_d0_1 : valAt (tensor 1 0 0 1 xs_k1_i0_o1_d0) 1 = (201 : Scalar) := by
  rfl
def store_k1_i0_o1_d0 : Store := fun tid => sample [1, 2] (100 * tid)
def node_k1_i0_o1_d0 : NodeDecl := {rank := 2, op := "OpName.AllToAllPrim", ins := [2], outs := [99], params := [0, 1]}
theorem contract_k1_i0_o1_d0 : NodeContract [2] id store_k1_i0_o1_d0 node_k1_i0_o1_d0 0 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [1, 2], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [1, 2] 200] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl
  all_goals rfl
theorem step_k1_i0_o1_d0 : step {numRanks := 6, nodes := []} (some [2]) id store_k1_i0_o1_d0 node_k1_i0_o1_d0 = .ok (localStep [2] store_k1_i0_o1_d0 node_k1_i0_o1_d0 0 1) := by
  exact step_valid _ _ _ _ _ 0 1 99 (by decide) contract_k1_i0_o1_d0
def xs_k1_i1_o0_d0 : List Tensor := [sample [1, 2] 200]
theorem shape_k1_i1_o0_d0 : (tensor 1 0 1 0 xs_k1_i1_o0_d0).shape = [1, 2] := by
  rfl
theorem value_k1_i1_o0_d0_0 : valAt (tensor 1 0 1 0 xs_k1_i1_o0_d0) 0 = (200 : Scalar) := by
  rfl
theorem value_k1_i1_o0_d0_1 : valAt (tensor 1 0 1 0 xs_k1_i1_o0_d0) 1 = (201 : Scalar) := by
  rfl
def store_k1_i1_o0_d0 : Store := fun tid => sample [1, 2] (100 * tid)
def node_k1_i1_o0_d0 : NodeDecl := {rank := 2, op := "OpName.AllToAllPrim", ins := [2], outs := [99], params := [1, 0]}
theorem contract_k1_i1_o0_d0 : NodeContract [2] id store_k1_i1_o0_d0 node_k1_i1_o0_d0 1 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [1, 2], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [1, 2] 200] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl
  all_goals rfl
theorem step_k1_i1_o0_d0 : step {numRanks := 6, nodes := []} (some [2]) id store_k1_i1_o0_d0 node_k1_i1_o0_d0 = .ok (localStep [2] store_k1_i1_o0_d0 node_k1_i1_o0_d0 1 0) := by
  exact step_valid _ _ _ _ _ 1 0 99 (by decide) contract_k1_i1_o0_d0
def xs_k2_i0_o0_d0 : List Tensor := [sample [2, 4] 100, sample [2, 4] 300]
theorem shape_k2_i0_o0_d0 : (tensor 2 0 0 0 xs_k2_i0_o0_d0).shape = [2, 4] := by
  rfl
theorem value_k2_i0_o0_d0_0 : valAt (tensor 2 0 0 0 xs_k2_i0_o0_d0) 0 = (100 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d0_1 : valAt (tensor 2 0 0 0 xs_k2_i0_o0_d0) 1 = (101 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d0_2 : valAt (tensor 2 0 0 0 xs_k2_i0_o0_d0) 2 = (102 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d0_3 : valAt (tensor 2 0 0 0 xs_k2_i0_o0_d0) 3 = (103 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d0_4 : valAt (tensor 2 0 0 0 xs_k2_i0_o0_d0) 4 = (300 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d0_5 : valAt (tensor 2 0 0 0 xs_k2_i0_o0_d0) 5 = (301 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d0_6 : valAt (tensor 2 0 0 0 xs_k2_i0_o0_d0) 6 = (302 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d0_7 : valAt (tensor 2 0 0 0 xs_k2_i0_o0_d0) 7 = (303 : Scalar) := by
  rfl
def store_k2_i0_o0_d0 : Store := fun tid => sample [2, 4] (100 * tid)
def node_k2_i0_o0_d0 : NodeDecl := {rank := 1, op := "OpName.AllToAllPrim", ins := [1, 3], outs := [99], params := [0, 0]}
theorem contract_k2_i0_o0_d0 : NodeContract [1, 3] id store_k2_i0_o0_d0 node_k2_i0_o0_d0 0 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [2, 4], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [2, 4] 100, sample [2, 4] 300] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  all_goals rfl
theorem step_k2_i0_o0_d0 : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i0_o0_d0 node_k2_i0_o0_d0 = .ok (localStep [1, 3] store_k2_i0_o0_d0 node_k2_i0_o0_d0 0 0) := by
  exact step_valid _ _ _ _ _ 0 0 99 (by decide) contract_k2_i0_o0_d0
def xs_k2_i0_o0_d1 : List Tensor := [sample [2, 4] 100, sample [2, 4] 300]
theorem shape_k2_i0_o0_d1 : (tensor 2 1 0 0 xs_k2_i0_o0_d1).shape = [2, 4] := by
  rfl
theorem value_k2_i0_o0_d1_0 : valAt (tensor 2 1 0 0 xs_k2_i0_o0_d1) 0 = (104 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d1_1 : valAt (tensor 2 1 0 0 xs_k2_i0_o0_d1) 1 = (105 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d1_2 : valAt (tensor 2 1 0 0 xs_k2_i0_o0_d1) 2 = (106 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d1_3 : valAt (tensor 2 1 0 0 xs_k2_i0_o0_d1) 3 = (107 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d1_4 : valAt (tensor 2 1 0 0 xs_k2_i0_o0_d1) 4 = (304 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d1_5 : valAt (tensor 2 1 0 0 xs_k2_i0_o0_d1) 5 = (305 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d1_6 : valAt (tensor 2 1 0 0 xs_k2_i0_o0_d1) 6 = (306 : Scalar) := by
  rfl
theorem value_k2_i0_o0_d1_7 : valAt (tensor 2 1 0 0 xs_k2_i0_o0_d1) 7 = (307 : Scalar) := by
  rfl
def store_k2_i0_o0_d1 : Store := fun tid => sample [2, 4] (100 * tid)
def node_k2_i0_o0_d1 : NodeDecl := {rank := 3, op := "OpName.AllToAllPrim", ins := [1, 3], outs := [99], params := [0, 0]}
theorem contract_k2_i0_o0_d1 : NodeContract [1, 3] id store_k2_i0_o0_d1 node_k2_i0_o0_d1 0 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [2, 4], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [2, 4] 100, sample [2, 4] 300] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  all_goals rfl
theorem step_k2_i0_o0_d1 : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i0_o0_d1 node_k2_i0_o0_d1 = .ok (localStep [1, 3] store_k2_i0_o0_d1 node_k2_i0_o0_d1 0 0) := by
  exact step_valid _ _ _ _ _ 0 0 99 (by decide) contract_k2_i0_o0_d1
def xs_k2_i1_o1_d0 : List Tensor := [sample [2, 4] 100, sample [2, 4] 300]
theorem shape_k2_i1_o1_d0 : (tensor 2 0 1 1 xs_k2_i1_o1_d0).shape = [2, 4] := by
  rfl
theorem value_k2_i1_o1_d0_0 : valAt (tensor 2 0 1 1 xs_k2_i1_o1_d0) 0 = (100 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d0_1 : valAt (tensor 2 0 1 1 xs_k2_i1_o1_d0) 1 = (101 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d0_2 : valAt (tensor 2 0 1 1 xs_k2_i1_o1_d0) 2 = (300 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d0_3 : valAt (tensor 2 0 1 1 xs_k2_i1_o1_d0) 3 = (301 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d0_4 : valAt (tensor 2 0 1 1 xs_k2_i1_o1_d0) 4 = (104 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d0_5 : valAt (tensor 2 0 1 1 xs_k2_i1_o1_d0) 5 = (105 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d0_6 : valAt (tensor 2 0 1 1 xs_k2_i1_o1_d0) 6 = (304 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d0_7 : valAt (tensor 2 0 1 1 xs_k2_i1_o1_d0) 7 = (305 : Scalar) := by
  rfl
def store_k2_i1_o1_d0 : Store := fun tid => sample [2, 4] (100 * tid)
def node_k2_i1_o1_d0 : NodeDecl := {rank := 1, op := "OpName.AllToAllPrim", ins := [1, 3], outs := [99], params := [1, 1]}
theorem contract_k2_i1_o1_d0 : NodeContract [1, 3] id store_k2_i1_o1_d0 node_k2_i1_o1_d0 1 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [2, 4], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [2, 4] 100, sample [2, 4] 300] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  all_goals rfl
theorem step_k2_i1_o1_d0 : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i1_o1_d0 node_k2_i1_o1_d0 = .ok (localStep [1, 3] store_k2_i1_o1_d0 node_k2_i1_o1_d0 1 1) := by
  exact step_valid _ _ _ _ _ 1 1 99 (by decide) contract_k2_i1_o1_d0
def xs_k2_i1_o1_d1 : List Tensor := [sample [2, 4] 100, sample [2, 4] 300]
theorem shape_k2_i1_o1_d1 : (tensor 2 1 1 1 xs_k2_i1_o1_d1).shape = [2, 4] := by
  rfl
theorem value_k2_i1_o1_d1_0 : valAt (tensor 2 1 1 1 xs_k2_i1_o1_d1) 0 = (102 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d1_1 : valAt (tensor 2 1 1 1 xs_k2_i1_o1_d1) 1 = (103 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d1_2 : valAt (tensor 2 1 1 1 xs_k2_i1_o1_d1) 2 = (302 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d1_3 : valAt (tensor 2 1 1 1 xs_k2_i1_o1_d1) 3 = (303 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d1_4 : valAt (tensor 2 1 1 1 xs_k2_i1_o1_d1) 4 = (106 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d1_5 : valAt (tensor 2 1 1 1 xs_k2_i1_o1_d1) 5 = (107 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d1_6 : valAt (tensor 2 1 1 1 xs_k2_i1_o1_d1) 6 = (306 : Scalar) := by
  rfl
theorem value_k2_i1_o1_d1_7 : valAt (tensor 2 1 1 1 xs_k2_i1_o1_d1) 7 = (307 : Scalar) := by
  rfl
def store_k2_i1_o1_d1 : Store := fun tid => sample [2, 4] (100 * tid)
def node_k2_i1_o1_d1 : NodeDecl := {rank := 3, op := "OpName.AllToAllPrim", ins := [1, 3], outs := [99], params := [1, 1]}
theorem contract_k2_i1_o1_d1 : NodeContract [1, 3] id store_k2_i1_o1_d1 node_k2_i1_o1_d1 1 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [2, 4], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [2, 4] 100, sample [2, 4] 300] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  all_goals rfl
theorem step_k2_i1_o1_d1 : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i1_o1_d1 node_k2_i1_o1_d1 = .ok (localStep [1, 3] store_k2_i1_o1_d1 node_k2_i1_o1_d1 1 1) := by
  exact step_valid _ _ _ _ _ 1 1 99 (by decide) contract_k2_i1_o1_d1
def xs_k2_i0_o1_d0 : List Tensor := [sample [2, 4] 100, sample [2, 4] 300]
theorem shape_k2_i0_o1_d0 : (tensor 2 0 0 1 xs_k2_i0_o1_d0).shape = [4, 2] := by
  rfl
theorem value_k2_i0_o1_d0_0 : valAt (tensor 2 0 0 1 xs_k2_i0_o1_d0) 0 = (100 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d0_1 : valAt (tensor 2 0 0 1 xs_k2_i0_o1_d0) 1 = (101 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d0_2 : valAt (tensor 2 0 0 1 xs_k2_i0_o1_d0) 2 = (104 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d0_3 : valAt (tensor 2 0 0 1 xs_k2_i0_o1_d0) 3 = (105 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d0_4 : valAt (tensor 2 0 0 1 xs_k2_i0_o1_d0) 4 = (300 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d0_5 : valAt (tensor 2 0 0 1 xs_k2_i0_o1_d0) 5 = (301 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d0_6 : valAt (tensor 2 0 0 1 xs_k2_i0_o1_d0) 6 = (304 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d0_7 : valAt (tensor 2 0 0 1 xs_k2_i0_o1_d0) 7 = (305 : Scalar) := by
  rfl
def store_k2_i0_o1_d0 : Store := fun tid => sample [2, 4] (100 * tid)
def node_k2_i0_o1_d0 : NodeDecl := {rank := 1, op := "OpName.AllToAllPrim", ins := [1, 3], outs := [99], params := [0, 1]}
theorem contract_k2_i0_o1_d0 : NodeContract [1, 3] id store_k2_i0_o1_d0 node_k2_i0_o1_d0 0 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [2, 4], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [2, 4] 100, sample [2, 4] 300] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  all_goals rfl
theorem step_k2_i0_o1_d0 : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i0_o1_d0 node_k2_i0_o1_d0 = .ok (localStep [1, 3] store_k2_i0_o1_d0 node_k2_i0_o1_d0 0 1) := by
  exact step_valid _ _ _ _ _ 0 1 99 (by decide) contract_k2_i0_o1_d0
def xs_k2_i0_o1_d1 : List Tensor := [sample [2, 4] 100, sample [2, 4] 300]
theorem shape_k2_i0_o1_d1 : (tensor 2 1 0 1 xs_k2_i0_o1_d1).shape = [4, 2] := by
  rfl
theorem value_k2_i0_o1_d1_0 : valAt (tensor 2 1 0 1 xs_k2_i0_o1_d1) 0 = (102 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d1_1 : valAt (tensor 2 1 0 1 xs_k2_i0_o1_d1) 1 = (103 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d1_2 : valAt (tensor 2 1 0 1 xs_k2_i0_o1_d1) 2 = (106 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d1_3 : valAt (tensor 2 1 0 1 xs_k2_i0_o1_d1) 3 = (107 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d1_4 : valAt (tensor 2 1 0 1 xs_k2_i0_o1_d1) 4 = (302 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d1_5 : valAt (tensor 2 1 0 1 xs_k2_i0_o1_d1) 5 = (303 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d1_6 : valAt (tensor 2 1 0 1 xs_k2_i0_o1_d1) 6 = (306 : Scalar) := by
  rfl
theorem value_k2_i0_o1_d1_7 : valAt (tensor 2 1 0 1 xs_k2_i0_o1_d1) 7 = (307 : Scalar) := by
  rfl
def store_k2_i0_o1_d1 : Store := fun tid => sample [2, 4] (100 * tid)
def node_k2_i0_o1_d1 : NodeDecl := {rank := 3, op := "OpName.AllToAllPrim", ins := [1, 3], outs := [99], params := [0, 1]}
theorem contract_k2_i0_o1_d1 : NodeContract [1, 3] id store_k2_i0_o1_d1 node_k2_i0_o1_d1 0 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [2, 4], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [2, 4] 100, sample [2, 4] 300] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  all_goals rfl
theorem step_k2_i0_o1_d1 : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i0_o1_d1 node_k2_i0_o1_d1 = .ok (localStep [1, 3] store_k2_i0_o1_d1 node_k2_i0_o1_d1 0 1) := by
  exact step_valid _ _ _ _ _ 0 1 99 (by decide) contract_k2_i0_o1_d1
def xs_k2_i1_o0_d0 : List Tensor := [sample [2, 4] 100, sample [2, 4] 300]
theorem shape_k2_i1_o0_d0 : (tensor 2 0 1 0 xs_k2_i1_o0_d0).shape = [1, 8] := by
  rfl
theorem value_k2_i1_o0_d0_0 : valAt (tensor 2 0 1 0 xs_k2_i1_o0_d0) 0 = (100 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d0_1 : valAt (tensor 2 0 1 0 xs_k2_i1_o0_d0) 1 = (101 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d0_2 : valAt (tensor 2 0 1 0 xs_k2_i1_o0_d0) 2 = (102 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d0_3 : valAt (tensor 2 0 1 0 xs_k2_i1_o0_d0) 3 = (103 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d0_4 : valAt (tensor 2 0 1 0 xs_k2_i1_o0_d0) 4 = (300 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d0_5 : valAt (tensor 2 0 1 0 xs_k2_i1_o0_d0) 5 = (301 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d0_6 : valAt (tensor 2 0 1 0 xs_k2_i1_o0_d0) 6 = (302 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d0_7 : valAt (tensor 2 0 1 0 xs_k2_i1_o0_d0) 7 = (303 : Scalar) := by
  rfl
def store_k2_i1_o0_d0 : Store := fun tid => sample [2, 4] (100 * tid)
def node_k2_i1_o0_d0 : NodeDecl := {rank := 1, op := "OpName.AllToAllPrim", ins := [1, 3], outs := [99], params := [1, 0]}
theorem contract_k2_i1_o0_d0 : NodeContract [1, 3] id store_k2_i1_o0_d0 node_k2_i1_o0_d0 1 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [2, 4], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [2, 4] 100, sample [2, 4] 300] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  all_goals rfl
theorem step_k2_i1_o0_d0 : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i1_o0_d0 node_k2_i1_o0_d0 = .ok (localStep [1, 3] store_k2_i1_o0_d0 node_k2_i1_o0_d0 1 0) := by
  exact step_valid _ _ _ _ _ 1 0 99 (by decide) contract_k2_i1_o0_d0
def xs_k2_i1_o0_d1 : List Tensor := [sample [2, 4] 100, sample [2, 4] 300]
theorem shape_k2_i1_o0_d1 : (tensor 2 1 1 0 xs_k2_i1_o0_d1).shape = [1, 8] := by
  rfl
theorem value_k2_i1_o0_d1_0 : valAt (tensor 2 1 1 0 xs_k2_i1_o0_d1) 0 = (104 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d1_1 : valAt (tensor 2 1 1 0 xs_k2_i1_o0_d1) 1 = (105 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d1_2 : valAt (tensor 2 1 1 0 xs_k2_i1_o0_d1) 2 = (106 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d1_3 : valAt (tensor 2 1 1 0 xs_k2_i1_o0_d1) 3 = (107 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d1_4 : valAt (tensor 2 1 1 0 xs_k2_i1_o0_d1) 4 = (304 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d1_5 : valAt (tensor 2 1 1 0 xs_k2_i1_o0_d1) 5 = (305 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d1_6 : valAt (tensor 2 1 1 0 xs_k2_i1_o0_d1) 6 = (306 : Scalar) := by
  rfl
theorem value_k2_i1_o0_d1_7 : valAt (tensor 2 1 1 0 xs_k2_i1_o0_d1) 7 = (307 : Scalar) := by
  rfl
def store_k2_i1_o0_d1 : Store := fun tid => sample [2, 4] (100 * tid)
def node_k2_i1_o0_d1 : NodeDecl := {rank := 3, op := "OpName.AllToAllPrim", ins := [1, 3], outs := [99], params := [1, 0]}
theorem contract_k2_i1_o0_d1 : NodeContract [1, 3] id store_k2_i1_o0_d1 node_k2_i1_o0_d1 1 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [2, 4], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [2, 4] 100, sample [2, 4] 300] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  all_goals rfl
theorem step_k2_i1_o0_d1 : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i1_o0_d1 node_k2_i1_o0_d1 = .ok (localStep [1, 3] store_k2_i1_o0_d1 node_k2_i1_o0_d1 1 0) := by
  exact step_valid _ _ _ _ _ 1 0 99 (by decide) contract_k2_i1_o0_d1
def xs_k3_i0_o0_d0 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i0_o0_d0 : (tensor 3 0 0 0 xs_k3_i0_o0_d0).shape = [3, 6] := by
  rfl
theorem value_k3_i0_o0_d0_0 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 0 = (0 : Scalar) := by
  change ((0 : Nat) : Scalar) = 0
  norm_num
theorem value_k3_i0_o0_d0_1 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 1 = (1 : Scalar) := by
  change ((1 : Nat) : Scalar) = 1
  norm_num
theorem value_k3_i0_o0_d0_2 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 2 = (2 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_3 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 3 = (3 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_4 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 4 = (4 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_5 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 5 = (5 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_6 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 6 = (200 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_7 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 7 = (201 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_8 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 8 = (202 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_9 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 9 = (203 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_10 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 10 = (204 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_11 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 11 = (205 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_12 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 12 = (500 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_13 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 13 = (501 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_14 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 14 = (502 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_15 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 15 = (503 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_16 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 16 = (504 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d0_17 : valAt (tensor 3 0 0 0 xs_k3_i0_o0_d0) 17 = (505 : Scalar) := by
  rfl
def store_k3_i0_o0_d0 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i0_o0_d0 : NodeDecl := {rank := 0, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [0, 0]}
theorem contract_k3_i0_o0_d0 : NodeContract [0, 2, 5] id store_k3_i0_o0_d0 node_k3_i0_o0_d0 0 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i0_o0_d0 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i0_o0_d0 node_k3_i0_o0_d0 = .ok (localStep [0, 2, 5] store_k3_i0_o0_d0 node_k3_i0_o0_d0 0 0) := by
  exact step_valid _ _ _ _ _ 0 0 99 (by decide) contract_k3_i0_o0_d0
def xs_k3_i0_o0_d1 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i0_o0_d1 : (tensor 3 1 0 0 xs_k3_i0_o0_d1).shape = [3, 6] := by
  rfl
theorem value_k3_i0_o0_d1_0 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 0 = (6 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_1 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 1 = (7 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_2 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 2 = (8 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_3 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 3 = (9 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_4 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 4 = (10 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_5 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 5 = (11 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_6 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 6 = (206 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_7 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 7 = (207 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_8 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 8 = (208 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_9 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 9 = (209 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_10 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 10 = (210 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_11 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 11 = (211 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_12 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 12 = (506 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_13 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 13 = (507 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_14 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 14 = (508 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_15 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 15 = (509 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_16 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 16 = (510 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d1_17 : valAt (tensor 3 1 0 0 xs_k3_i0_o0_d1) 17 = (511 : Scalar) := by
  rfl
def store_k3_i0_o0_d1 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i0_o0_d1 : NodeDecl := {rank := 2, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [0, 0]}
theorem contract_k3_i0_o0_d1 : NodeContract [0, 2, 5] id store_k3_i0_o0_d1 node_k3_i0_o0_d1 0 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i0_o0_d1 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i0_o0_d1 node_k3_i0_o0_d1 = .ok (localStep [0, 2, 5] store_k3_i0_o0_d1 node_k3_i0_o0_d1 0 0) := by
  exact step_valid _ _ _ _ _ 0 0 99 (by decide) contract_k3_i0_o0_d1
def xs_k3_i0_o0_d2 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i0_o0_d2 : (tensor 3 2 0 0 xs_k3_i0_o0_d2).shape = [3, 6] := by
  rfl
theorem value_k3_i0_o0_d2_0 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 0 = (12 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_1 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 1 = (13 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_2 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 2 = (14 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_3 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 3 = (15 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_4 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 4 = (16 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_5 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 5 = (17 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_6 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 6 = (212 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_7 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 7 = (213 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_8 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 8 = (214 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_9 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 9 = (215 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_10 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 10 = (216 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_11 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 11 = (217 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_12 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 12 = (512 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_13 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 13 = (513 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_14 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 14 = (514 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_15 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 15 = (515 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_16 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 16 = (516 : Scalar) := by
  rfl
theorem value_k3_i0_o0_d2_17 : valAt (tensor 3 2 0 0 xs_k3_i0_o0_d2) 17 = (517 : Scalar) := by
  rfl
def store_k3_i0_o0_d2 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i0_o0_d2 : NodeDecl := {rank := 5, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [0, 0]}
theorem contract_k3_i0_o0_d2 : NodeContract [0, 2, 5] id store_k3_i0_o0_d2 node_k3_i0_o0_d2 0 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i0_o0_d2 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i0_o0_d2 node_k3_i0_o0_d2 = .ok (localStep [0, 2, 5] store_k3_i0_o0_d2 node_k3_i0_o0_d2 0 0) := by
  exact step_valid _ _ _ _ _ 0 0 99 (by decide) contract_k3_i0_o0_d2
def xs_k3_i1_o1_d0 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i1_o1_d0 : (tensor 3 0 1 1 xs_k3_i1_o1_d0).shape = [3, 6] := by
  rfl
theorem value_k3_i1_o1_d0_0 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 0 = (0 : Scalar) := by
  change ((0 : Nat) : Scalar) = 0
  norm_num
theorem value_k3_i1_o1_d0_1 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 1 = (1 : Scalar) := by
  change ((1 : Nat) : Scalar) = 1
  norm_num
theorem value_k3_i1_o1_d0_2 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 2 = (200 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_3 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 3 = (201 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_4 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 4 = (500 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_5 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 5 = (501 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_6 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 6 = (6 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_7 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 7 = (7 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_8 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 8 = (206 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_9 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 9 = (207 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_10 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 10 = (506 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_11 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 11 = (507 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_12 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 12 = (12 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_13 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 13 = (13 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_14 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 14 = (212 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_15 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 15 = (213 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_16 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 16 = (512 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d0_17 : valAt (tensor 3 0 1 1 xs_k3_i1_o1_d0) 17 = (513 : Scalar) := by
  rfl
def store_k3_i1_o1_d0 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i1_o1_d0 : NodeDecl := {rank := 0, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [1, 1]}
theorem contract_k3_i1_o1_d0 : NodeContract [0, 2, 5] id store_k3_i1_o1_d0 node_k3_i1_o1_d0 1 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i1_o1_d0 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i1_o1_d0 node_k3_i1_o1_d0 = .ok (localStep [0, 2, 5] store_k3_i1_o1_d0 node_k3_i1_o1_d0 1 1) := by
  exact step_valid _ _ _ _ _ 1 1 99 (by decide) contract_k3_i1_o1_d0
def xs_k3_i1_o1_d1 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i1_o1_d1 : (tensor 3 1 1 1 xs_k3_i1_o1_d1).shape = [3, 6] := by
  rfl
theorem value_k3_i1_o1_d1_0 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 0 = (2 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_1 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 1 = (3 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_2 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 2 = (202 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_3 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 3 = (203 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_4 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 4 = (502 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_5 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 5 = (503 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_6 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 6 = (8 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_7 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 7 = (9 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_8 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 8 = (208 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_9 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 9 = (209 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_10 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 10 = (508 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_11 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 11 = (509 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_12 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 12 = (14 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_13 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 13 = (15 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_14 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 14 = (214 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_15 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 15 = (215 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_16 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 16 = (514 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d1_17 : valAt (tensor 3 1 1 1 xs_k3_i1_o1_d1) 17 = (515 : Scalar) := by
  rfl
def store_k3_i1_o1_d1 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i1_o1_d1 : NodeDecl := {rank := 2, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [1, 1]}
theorem contract_k3_i1_o1_d1 : NodeContract [0, 2, 5] id store_k3_i1_o1_d1 node_k3_i1_o1_d1 1 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i1_o1_d1 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i1_o1_d1 node_k3_i1_o1_d1 = .ok (localStep [0, 2, 5] store_k3_i1_o1_d1 node_k3_i1_o1_d1 1 1) := by
  exact step_valid _ _ _ _ _ 1 1 99 (by decide) contract_k3_i1_o1_d1
def xs_k3_i1_o1_d2 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i1_o1_d2 : (tensor 3 2 1 1 xs_k3_i1_o1_d2).shape = [3, 6] := by
  rfl
theorem value_k3_i1_o1_d2_0 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 0 = (4 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_1 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 1 = (5 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_2 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 2 = (204 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_3 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 3 = (205 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_4 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 4 = (504 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_5 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 5 = (505 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_6 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 6 = (10 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_7 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 7 = (11 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_8 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 8 = (210 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_9 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 9 = (211 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_10 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 10 = (510 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_11 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 11 = (511 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_12 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 12 = (16 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_13 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 13 = (17 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_14 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 14 = (216 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_15 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 15 = (217 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_16 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 16 = (516 : Scalar) := by
  rfl
theorem value_k3_i1_o1_d2_17 : valAt (tensor 3 2 1 1 xs_k3_i1_o1_d2) 17 = (517 : Scalar) := by
  rfl
def store_k3_i1_o1_d2 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i1_o1_d2 : NodeDecl := {rank := 5, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [1, 1]}
theorem contract_k3_i1_o1_d2 : NodeContract [0, 2, 5] id store_k3_i1_o1_d2 node_k3_i1_o1_d2 1 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i1_o1_d2 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i1_o1_d2 node_k3_i1_o1_d2 = .ok (localStep [0, 2, 5] store_k3_i1_o1_d2 node_k3_i1_o1_d2 1 1) := by
  exact step_valid _ _ _ _ _ 1 1 99 (by decide) contract_k3_i1_o1_d2
def xs_k3_i0_o1_d0 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i0_o1_d0 : (tensor 3 0 0 1 xs_k3_i0_o1_d0).shape = [9, 2] := by
  rfl
theorem value_k3_i0_o1_d0_0 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 0 = (0 : Scalar) := by
  change ((0 : Nat) : Scalar) = 0
  norm_num
theorem value_k3_i0_o1_d0_1 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 1 = (1 : Scalar) := by
  change ((1 : Nat) : Scalar) = 1
  norm_num
theorem value_k3_i0_o1_d0_2 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 2 = (6 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_3 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 3 = (7 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_4 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 4 = (12 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_5 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 5 = (13 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_6 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 6 = (200 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_7 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 7 = (201 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_8 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 8 = (206 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_9 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 9 = (207 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_10 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 10 = (212 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_11 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 11 = (213 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_12 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 12 = (500 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_13 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 13 = (501 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_14 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 14 = (506 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_15 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 15 = (507 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_16 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 16 = (512 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d0_17 : valAt (tensor 3 0 0 1 xs_k3_i0_o1_d0) 17 = (513 : Scalar) := by
  rfl
def store_k3_i0_o1_d0 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i0_o1_d0 : NodeDecl := {rank := 0, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [0, 1]}
theorem contract_k3_i0_o1_d0 : NodeContract [0, 2, 5] id store_k3_i0_o1_d0 node_k3_i0_o1_d0 0 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i0_o1_d0 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i0_o1_d0 node_k3_i0_o1_d0 = .ok (localStep [0, 2, 5] store_k3_i0_o1_d0 node_k3_i0_o1_d0 0 1) := by
  exact step_valid _ _ _ _ _ 0 1 99 (by decide) contract_k3_i0_o1_d0
def xs_k3_i0_o1_d1 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i0_o1_d1 : (tensor 3 1 0 1 xs_k3_i0_o1_d1).shape = [9, 2] := by
  rfl
theorem value_k3_i0_o1_d1_0 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 0 = (2 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_1 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 1 = (3 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_2 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 2 = (8 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_3 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 3 = (9 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_4 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 4 = (14 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_5 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 5 = (15 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_6 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 6 = (202 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_7 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 7 = (203 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_8 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 8 = (208 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_9 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 9 = (209 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_10 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 10 = (214 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_11 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 11 = (215 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_12 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 12 = (502 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_13 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 13 = (503 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_14 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 14 = (508 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_15 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 15 = (509 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_16 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 16 = (514 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d1_17 : valAt (tensor 3 1 0 1 xs_k3_i0_o1_d1) 17 = (515 : Scalar) := by
  rfl
def store_k3_i0_o1_d1 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i0_o1_d1 : NodeDecl := {rank := 2, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [0, 1]}
theorem contract_k3_i0_o1_d1 : NodeContract [0, 2, 5] id store_k3_i0_o1_d1 node_k3_i0_o1_d1 0 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i0_o1_d1 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i0_o1_d1 node_k3_i0_o1_d1 = .ok (localStep [0, 2, 5] store_k3_i0_o1_d1 node_k3_i0_o1_d1 0 1) := by
  exact step_valid _ _ _ _ _ 0 1 99 (by decide) contract_k3_i0_o1_d1
def xs_k3_i0_o1_d2 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i0_o1_d2 : (tensor 3 2 0 1 xs_k3_i0_o1_d2).shape = [9, 2] := by
  rfl
theorem value_k3_i0_o1_d2_0 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 0 = (4 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_1 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 1 = (5 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_2 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 2 = (10 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_3 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 3 = (11 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_4 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 4 = (16 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_5 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 5 = (17 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_6 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 6 = (204 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_7 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 7 = (205 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_8 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 8 = (210 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_9 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 9 = (211 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_10 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 10 = (216 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_11 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 11 = (217 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_12 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 12 = (504 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_13 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 13 = (505 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_14 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 14 = (510 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_15 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 15 = (511 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_16 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 16 = (516 : Scalar) := by
  rfl
theorem value_k3_i0_o1_d2_17 : valAt (tensor 3 2 0 1 xs_k3_i0_o1_d2) 17 = (517 : Scalar) := by
  rfl
def store_k3_i0_o1_d2 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i0_o1_d2 : NodeDecl := {rank := 5, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [0, 1]}
theorem contract_k3_i0_o1_d2 : NodeContract [0, 2, 5] id store_k3_i0_o1_d2 node_k3_i0_o1_d2 0 1 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i0_o1_d2 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i0_o1_d2 node_k3_i0_o1_d2 = .ok (localStep [0, 2, 5] store_k3_i0_o1_d2 node_k3_i0_o1_d2 0 1) := by
  exact step_valid _ _ _ _ _ 0 1 99 (by decide) contract_k3_i0_o1_d2
def xs_k3_i1_o0_d0 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i1_o0_d0 : (tensor 3 0 1 0 xs_k3_i1_o0_d0).shape = [1, 18] := by
  rfl
theorem value_k3_i1_o0_d0_0 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 0 = (0 : Scalar) := by
  change ((0 : Nat) : Scalar) = 0
  norm_num
theorem value_k3_i1_o0_d0_1 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 1 = (1 : Scalar) := by
  change ((1 : Nat) : Scalar) = 1
  norm_num
theorem value_k3_i1_o0_d0_2 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 2 = (2 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_3 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 3 = (3 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_4 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 4 = (4 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_5 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 5 = (5 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_6 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 6 = (200 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_7 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 7 = (201 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_8 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 8 = (202 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_9 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 9 = (203 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_10 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 10 = (204 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_11 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 11 = (205 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_12 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 12 = (500 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_13 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 13 = (501 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_14 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 14 = (502 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_15 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 15 = (503 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_16 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 16 = (504 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d0_17 : valAt (tensor 3 0 1 0 xs_k3_i1_o0_d0) 17 = (505 : Scalar) := by
  rfl
def store_k3_i1_o0_d0 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i1_o0_d0 : NodeDecl := {rank := 0, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [1, 0]}
theorem contract_k3_i1_o0_d0 : NodeContract [0, 2, 5] id store_k3_i1_o0_d0 node_k3_i1_o0_d0 1 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i1_o0_d0 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i1_o0_d0 node_k3_i1_o0_d0 = .ok (localStep [0, 2, 5] store_k3_i1_o0_d0 node_k3_i1_o0_d0 1 0) := by
  exact step_valid _ _ _ _ _ 1 0 99 (by decide) contract_k3_i1_o0_d0
def xs_k3_i1_o0_d1 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i1_o0_d1 : (tensor 3 1 1 0 xs_k3_i1_o0_d1).shape = [1, 18] := by
  rfl
theorem value_k3_i1_o0_d1_0 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 0 = (6 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_1 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 1 = (7 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_2 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 2 = (8 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_3 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 3 = (9 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_4 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 4 = (10 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_5 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 5 = (11 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_6 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 6 = (206 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_7 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 7 = (207 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_8 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 8 = (208 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_9 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 9 = (209 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_10 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 10 = (210 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_11 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 11 = (211 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_12 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 12 = (506 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_13 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 13 = (507 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_14 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 14 = (508 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_15 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 15 = (509 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_16 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 16 = (510 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d1_17 : valAt (tensor 3 1 1 0 xs_k3_i1_o0_d1) 17 = (511 : Scalar) := by
  rfl
def store_k3_i1_o0_d1 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i1_o0_d1 : NodeDecl := {rank := 2, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [1, 0]}
theorem contract_k3_i1_o0_d1 : NodeContract [0, 2, 5] id store_k3_i1_o0_d1 node_k3_i1_o0_d1 1 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i1_o0_d1 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i1_o0_d1 node_k3_i1_o0_d1 = .ok (localStep [0, 2, 5] store_k3_i1_o0_d1 node_k3_i1_o0_d1 1 0) := by
  exact step_valid _ _ _ _ _ 1 0 99 (by decide) contract_k3_i1_o0_d1
def xs_k3_i1_o0_d2 : List Tensor := [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500]
theorem shape_k3_i1_o0_d2 : (tensor 3 2 1 0 xs_k3_i1_o0_d2).shape = [1, 18] := by
  rfl
theorem value_k3_i1_o0_d2_0 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 0 = (12 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_1 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 1 = (13 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_2 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 2 = (14 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_3 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 3 = (15 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_4 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 4 = (16 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_5 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 5 = (17 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_6 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 6 = (212 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_7 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 7 = (213 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_8 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 8 = (214 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_9 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 9 = (215 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_10 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 10 = (216 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_11 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 11 = (217 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_12 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 12 = (512 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_13 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 13 = (513 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_14 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 14 = (514 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_15 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 15 = (515 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_16 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 16 = (516 : Scalar) := by
  rfl
theorem value_k3_i1_o0_d2_17 : valAt (tensor 3 2 1 0 xs_k3_i1_o0_d2) 17 = (517 : Scalar) := by
  rfl
def store_k3_i1_o0_d2 : Store := fun tid => sample [3, 6] (100 * tid)
def node_k3_i1_o0_d2 : NodeDecl := {rank := 5, op := "OpName.AllToAllPrim", ins := [0, 2, 5], outs := [99], params := [1, 0]}
theorem contract_k3_i1_o0_d2 : NodeContract [0, 2, 5] id store_k3_i1_o0_d2 node_k3_i1_o0_d2 1 0 99 := by
  refine ⟨rfl, rfl, rfl, rfl, by decide, rfl, [3, 6], ?_, by decide, by decide, by decide, by decide⟩
  intro x hx
  change x ∈ [sample [3, 6] 0, sample [3, 6] 200, sample [3, 6] 500] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals rfl
theorem step_k3_i1_o0_d2 : step {numRanks := 6, nodes := []} (some [0, 2, 5]) id store_k3_i1_o0_d2 node_k3_i1_o0_d2 = .ok (localStep [0, 2, 5] store_k3_i1_o0_d2 node_k3_i1_o0_d2 1 0) := by
  exact step_valid _ _ _ _ _ 1 0 99 (by decide) contract_k3_i1_o0_d2
theorem legacy_sameaxis_counterexample : valAt (allToAllPrimWithDims 2 0 xs_k2_i1_o1_d0 1 1) 2 ≠ valAt (tensor 2 0 1 1 xs_k2_i1_o1_d0) 2 := by
  change (102 : Scalar) ≠ 300
  norm_num
theorem missing_scope : step {numRanks := 6, nodes := []} none id store_k2_i1_o1_d0 node_k2_i1_o1_d0 = .error .missingScope := by
  rfl
theorem wrong_world_rejected : step {numRanks := 2, nodes := []} (some [1, 3]) id store_k2_i1_o1_d0 node_k2_i1_o1_d0 = .error .rejectedScope := by
  exact step_rejected _ _ _ _ _ (by decide)
theorem legacy_distinct_axis_control : valAt (allToAllPrimWithDims 2 0 xs_k2_i0_o1_d0 0 1) 4 = (300 : Scalar) := by
  rfl
theorem duplicate_group_rejected : step {numRanks := 6, nodes := []} (some [1, 1]) id store_k2_i1_o1_d0 node_k2_i1_o1_d0 = .error .rejectedScope := by
  exact step_rejected _ _ _ _ _ (by decide)
theorem invalid_op : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i1_o1_d0 {node_k2_i1_o1_d0 with op := "bad"} = .error .invalidNode := by
  apply step_invalid _ _ _ _ _ 1 1 99 (by decide) rfl rfl
  intro hc
  have h := hc.1
  contradiction
theorem invalid_order : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i1_o1_d0 {node_k2_i1_o1_d0 with ins := [3, 1]} = .error .invalidNode := by
  apply step_invalid _ _ _ _ _ 1 1 99 (by decide) rfl rfl
  intro hc
  have h := hc.2.2.1
  contradiction
theorem invalid_arity : step {numRanks := 6, nodes := []} (some [1, 3]) id store_k2_i1_o1_d0 {node_k2_i1_o1_d0 with ins := [1]} = .error .invalidNode := by
  apply step_invalid _ _ _ _ _ 1 1 99 (by decide) rfl rfl
  intro hc
  have h := hc.2.2.1
  contradiction
#print axioms shape_k1_i0_o0_d0
#print axioms value_k1_i0_o0_d0_0
#print axioms value_k1_i0_o0_d0_1
#print axioms contract_k1_i0_o0_d0
#print axioms step_k1_i0_o0_d0
#print axioms shape_k1_i1_o1_d0
#print axioms value_k1_i1_o1_d0_0
#print axioms value_k1_i1_o1_d0_1
#print axioms contract_k1_i1_o1_d0
#print axioms step_k1_i1_o1_d0
#print axioms shape_k1_i0_o1_d0
#print axioms value_k1_i0_o1_d0_0
#print axioms value_k1_i0_o1_d0_1
#print axioms contract_k1_i0_o1_d0
#print axioms step_k1_i0_o1_d0
#print axioms shape_k1_i1_o0_d0
#print axioms value_k1_i1_o0_d0_0
#print axioms value_k1_i1_o0_d0_1
#print axioms contract_k1_i1_o0_d0
#print axioms step_k1_i1_o0_d0
#print axioms shape_k2_i0_o0_d0
#print axioms value_k2_i0_o0_d0_0
#print axioms value_k2_i0_o0_d0_1
#print axioms value_k2_i0_o0_d0_2
#print axioms value_k2_i0_o0_d0_3
#print axioms value_k2_i0_o0_d0_4
#print axioms value_k2_i0_o0_d0_5
#print axioms value_k2_i0_o0_d0_6
#print axioms value_k2_i0_o0_d0_7
#print axioms contract_k2_i0_o0_d0
#print axioms step_k2_i0_o0_d0
#print axioms shape_k2_i0_o0_d1
#print axioms value_k2_i0_o0_d1_0
#print axioms value_k2_i0_o0_d1_1
#print axioms value_k2_i0_o0_d1_2
#print axioms value_k2_i0_o0_d1_3
#print axioms value_k2_i0_o0_d1_4
#print axioms value_k2_i0_o0_d1_5
#print axioms value_k2_i0_o0_d1_6
#print axioms value_k2_i0_o0_d1_7
#print axioms contract_k2_i0_o0_d1
#print axioms step_k2_i0_o0_d1
#print axioms shape_k2_i1_o1_d0
#print axioms value_k2_i1_o1_d0_0
#print axioms value_k2_i1_o1_d0_1
#print axioms value_k2_i1_o1_d0_2
#print axioms value_k2_i1_o1_d0_3
#print axioms value_k2_i1_o1_d0_4
#print axioms value_k2_i1_o1_d0_5
#print axioms value_k2_i1_o1_d0_6
#print axioms value_k2_i1_o1_d0_7
#print axioms contract_k2_i1_o1_d0
#print axioms step_k2_i1_o1_d0
#print axioms shape_k2_i1_o1_d1
#print axioms value_k2_i1_o1_d1_0
#print axioms value_k2_i1_o1_d1_1
#print axioms value_k2_i1_o1_d1_2
#print axioms value_k2_i1_o1_d1_3
#print axioms value_k2_i1_o1_d1_4
#print axioms value_k2_i1_o1_d1_5
#print axioms value_k2_i1_o1_d1_6
#print axioms value_k2_i1_o1_d1_7
#print axioms contract_k2_i1_o1_d1
#print axioms step_k2_i1_o1_d1
#print axioms shape_k2_i0_o1_d0
#print axioms value_k2_i0_o1_d0_0
#print axioms value_k2_i0_o1_d0_1
#print axioms value_k2_i0_o1_d0_2
#print axioms value_k2_i0_o1_d0_3
#print axioms value_k2_i0_o1_d0_4
#print axioms value_k2_i0_o1_d0_5
#print axioms value_k2_i0_o1_d0_6
#print axioms value_k2_i0_o1_d0_7
#print axioms contract_k2_i0_o1_d0
#print axioms step_k2_i0_o1_d0
#print axioms shape_k2_i0_o1_d1
#print axioms value_k2_i0_o1_d1_0
#print axioms value_k2_i0_o1_d1_1
#print axioms value_k2_i0_o1_d1_2
#print axioms value_k2_i0_o1_d1_3
#print axioms value_k2_i0_o1_d1_4
#print axioms value_k2_i0_o1_d1_5
#print axioms value_k2_i0_o1_d1_6
#print axioms value_k2_i0_o1_d1_7
#print axioms contract_k2_i0_o1_d1
#print axioms step_k2_i0_o1_d1
#print axioms shape_k2_i1_o0_d0
#print axioms value_k2_i1_o0_d0_0
#print axioms value_k2_i1_o0_d0_1
#print axioms value_k2_i1_o0_d0_2
#print axioms value_k2_i1_o0_d0_3
#print axioms value_k2_i1_o0_d0_4
#print axioms value_k2_i1_o0_d0_5
#print axioms value_k2_i1_o0_d0_6
#print axioms value_k2_i1_o0_d0_7
#print axioms contract_k2_i1_o0_d0
#print axioms step_k2_i1_o0_d0
#print axioms shape_k2_i1_o0_d1
#print axioms value_k2_i1_o0_d1_0
#print axioms value_k2_i1_o0_d1_1
#print axioms value_k2_i1_o0_d1_2
#print axioms value_k2_i1_o0_d1_3
#print axioms value_k2_i1_o0_d1_4
#print axioms value_k2_i1_o0_d1_5
#print axioms value_k2_i1_o0_d1_6
#print axioms value_k2_i1_o0_d1_7
#print axioms contract_k2_i1_o0_d1
#print axioms step_k2_i1_o0_d1
#print axioms shape_k3_i0_o0_d0
#print axioms value_k3_i0_o0_d0_0
#print axioms value_k3_i0_o0_d0_1
#print axioms value_k3_i0_o0_d0_2
#print axioms value_k3_i0_o0_d0_3
#print axioms value_k3_i0_o0_d0_4
#print axioms value_k3_i0_o0_d0_5
#print axioms value_k3_i0_o0_d0_6
#print axioms value_k3_i0_o0_d0_7
#print axioms value_k3_i0_o0_d0_8
#print axioms value_k3_i0_o0_d0_9
#print axioms value_k3_i0_o0_d0_10
#print axioms value_k3_i0_o0_d0_11
#print axioms value_k3_i0_o0_d0_12
#print axioms value_k3_i0_o0_d0_13
#print axioms value_k3_i0_o0_d0_14
#print axioms value_k3_i0_o0_d0_15
#print axioms value_k3_i0_o0_d0_16
#print axioms value_k3_i0_o0_d0_17
#print axioms contract_k3_i0_o0_d0
#print axioms step_k3_i0_o0_d0
#print axioms shape_k3_i0_o0_d1
#print axioms value_k3_i0_o0_d1_0
#print axioms value_k3_i0_o0_d1_1
#print axioms value_k3_i0_o0_d1_2
#print axioms value_k3_i0_o0_d1_3
#print axioms value_k3_i0_o0_d1_4
#print axioms value_k3_i0_o0_d1_5
#print axioms value_k3_i0_o0_d1_6
#print axioms value_k3_i0_o0_d1_7
#print axioms value_k3_i0_o0_d1_8
#print axioms value_k3_i0_o0_d1_9
#print axioms value_k3_i0_o0_d1_10
#print axioms value_k3_i0_o0_d1_11
#print axioms value_k3_i0_o0_d1_12
#print axioms value_k3_i0_o0_d1_13
#print axioms value_k3_i0_o0_d1_14
#print axioms value_k3_i0_o0_d1_15
#print axioms value_k3_i0_o0_d1_16
#print axioms value_k3_i0_o0_d1_17
#print axioms contract_k3_i0_o0_d1
#print axioms step_k3_i0_o0_d1
#print axioms shape_k3_i0_o0_d2
#print axioms value_k3_i0_o0_d2_0
#print axioms value_k3_i0_o0_d2_1
#print axioms value_k3_i0_o0_d2_2
#print axioms value_k3_i0_o0_d2_3
#print axioms value_k3_i0_o0_d2_4
#print axioms value_k3_i0_o0_d2_5
#print axioms value_k3_i0_o0_d2_6
#print axioms value_k3_i0_o0_d2_7
#print axioms value_k3_i0_o0_d2_8
#print axioms value_k3_i0_o0_d2_9
#print axioms value_k3_i0_o0_d2_10
#print axioms value_k3_i0_o0_d2_11
#print axioms value_k3_i0_o0_d2_12
#print axioms value_k3_i0_o0_d2_13
#print axioms value_k3_i0_o0_d2_14
#print axioms value_k3_i0_o0_d2_15
#print axioms value_k3_i0_o0_d2_16
#print axioms value_k3_i0_o0_d2_17
#print axioms contract_k3_i0_o0_d2
#print axioms step_k3_i0_o0_d2
#print axioms shape_k3_i1_o1_d0
#print axioms value_k3_i1_o1_d0_0
#print axioms value_k3_i1_o1_d0_1
#print axioms value_k3_i1_o1_d0_2
#print axioms value_k3_i1_o1_d0_3
#print axioms value_k3_i1_o1_d0_4
#print axioms value_k3_i1_o1_d0_5
#print axioms value_k3_i1_o1_d0_6
#print axioms value_k3_i1_o1_d0_7
#print axioms value_k3_i1_o1_d0_8
#print axioms value_k3_i1_o1_d0_9
#print axioms value_k3_i1_o1_d0_10
#print axioms value_k3_i1_o1_d0_11
#print axioms value_k3_i1_o1_d0_12
#print axioms value_k3_i1_o1_d0_13
#print axioms value_k3_i1_o1_d0_14
#print axioms value_k3_i1_o1_d0_15
#print axioms value_k3_i1_o1_d0_16
#print axioms value_k3_i1_o1_d0_17
#print axioms contract_k3_i1_o1_d0
#print axioms step_k3_i1_o1_d0
#print axioms shape_k3_i1_o1_d1
#print axioms value_k3_i1_o1_d1_0
#print axioms value_k3_i1_o1_d1_1
#print axioms value_k3_i1_o1_d1_2
#print axioms value_k3_i1_o1_d1_3
#print axioms value_k3_i1_o1_d1_4
#print axioms value_k3_i1_o1_d1_5
#print axioms value_k3_i1_o1_d1_6
#print axioms value_k3_i1_o1_d1_7
#print axioms value_k3_i1_o1_d1_8
#print axioms value_k3_i1_o1_d1_9
#print axioms value_k3_i1_o1_d1_10
#print axioms value_k3_i1_o1_d1_11
#print axioms value_k3_i1_o1_d1_12
#print axioms value_k3_i1_o1_d1_13
#print axioms value_k3_i1_o1_d1_14
#print axioms value_k3_i1_o1_d1_15
#print axioms value_k3_i1_o1_d1_16
#print axioms value_k3_i1_o1_d1_17
#print axioms contract_k3_i1_o1_d1
#print axioms step_k3_i1_o1_d1
#print axioms shape_k3_i1_o1_d2
#print axioms value_k3_i1_o1_d2_0
#print axioms value_k3_i1_o1_d2_1
#print axioms value_k3_i1_o1_d2_2
#print axioms value_k3_i1_o1_d2_3
#print axioms value_k3_i1_o1_d2_4
#print axioms value_k3_i1_o1_d2_5
#print axioms value_k3_i1_o1_d2_6
#print axioms value_k3_i1_o1_d2_7
#print axioms value_k3_i1_o1_d2_8
#print axioms value_k3_i1_o1_d2_9
#print axioms value_k3_i1_o1_d2_10
#print axioms value_k3_i1_o1_d2_11
#print axioms value_k3_i1_o1_d2_12
#print axioms value_k3_i1_o1_d2_13
#print axioms value_k3_i1_o1_d2_14
#print axioms value_k3_i1_o1_d2_15
#print axioms value_k3_i1_o1_d2_16
#print axioms value_k3_i1_o1_d2_17
#print axioms contract_k3_i1_o1_d2
#print axioms step_k3_i1_o1_d2
#print axioms shape_k3_i0_o1_d0
#print axioms value_k3_i0_o1_d0_0
#print axioms value_k3_i0_o1_d0_1
#print axioms value_k3_i0_o1_d0_2
#print axioms value_k3_i0_o1_d0_3
#print axioms value_k3_i0_o1_d0_4
#print axioms value_k3_i0_o1_d0_5
#print axioms value_k3_i0_o1_d0_6
#print axioms value_k3_i0_o1_d0_7
#print axioms value_k3_i0_o1_d0_8
#print axioms value_k3_i0_o1_d0_9
#print axioms value_k3_i0_o1_d0_10
#print axioms value_k3_i0_o1_d0_11
#print axioms value_k3_i0_o1_d0_12
#print axioms value_k3_i0_o1_d0_13
#print axioms value_k3_i0_o1_d0_14
#print axioms value_k3_i0_o1_d0_15
#print axioms value_k3_i0_o1_d0_16
#print axioms value_k3_i0_o1_d0_17
#print axioms contract_k3_i0_o1_d0
#print axioms step_k3_i0_o1_d0
#print axioms shape_k3_i0_o1_d1
#print axioms value_k3_i0_o1_d1_0
#print axioms value_k3_i0_o1_d1_1
#print axioms value_k3_i0_o1_d1_2
#print axioms value_k3_i0_o1_d1_3
#print axioms value_k3_i0_o1_d1_4
#print axioms value_k3_i0_o1_d1_5
#print axioms value_k3_i0_o1_d1_6
#print axioms value_k3_i0_o1_d1_7
#print axioms value_k3_i0_o1_d1_8
#print axioms value_k3_i0_o1_d1_9
#print axioms value_k3_i0_o1_d1_10
#print axioms value_k3_i0_o1_d1_11
#print axioms value_k3_i0_o1_d1_12
#print axioms value_k3_i0_o1_d1_13
#print axioms value_k3_i0_o1_d1_14
#print axioms value_k3_i0_o1_d1_15
#print axioms value_k3_i0_o1_d1_16
#print axioms value_k3_i0_o1_d1_17
#print axioms contract_k3_i0_o1_d1
#print axioms step_k3_i0_o1_d1
#print axioms shape_k3_i0_o1_d2
#print axioms value_k3_i0_o1_d2_0
#print axioms value_k3_i0_o1_d2_1
#print axioms value_k3_i0_o1_d2_2
#print axioms value_k3_i0_o1_d2_3
#print axioms value_k3_i0_o1_d2_4
#print axioms value_k3_i0_o1_d2_5
#print axioms value_k3_i0_o1_d2_6
#print axioms value_k3_i0_o1_d2_7
#print axioms value_k3_i0_o1_d2_8
#print axioms value_k3_i0_o1_d2_9
#print axioms value_k3_i0_o1_d2_10
#print axioms value_k3_i0_o1_d2_11
#print axioms value_k3_i0_o1_d2_12
#print axioms value_k3_i0_o1_d2_13
#print axioms value_k3_i0_o1_d2_14
#print axioms value_k3_i0_o1_d2_15
#print axioms value_k3_i0_o1_d2_16
#print axioms value_k3_i0_o1_d2_17
#print axioms contract_k3_i0_o1_d2
#print axioms step_k3_i0_o1_d2
#print axioms shape_k3_i1_o0_d0
#print axioms value_k3_i1_o0_d0_0
#print axioms value_k3_i1_o0_d0_1
#print axioms value_k3_i1_o0_d0_2
#print axioms value_k3_i1_o0_d0_3
#print axioms value_k3_i1_o0_d0_4
#print axioms value_k3_i1_o0_d0_5
#print axioms value_k3_i1_o0_d0_6
#print axioms value_k3_i1_o0_d0_7
#print axioms value_k3_i1_o0_d0_8
#print axioms value_k3_i1_o0_d0_9
#print axioms value_k3_i1_o0_d0_10
#print axioms value_k3_i1_o0_d0_11
#print axioms value_k3_i1_o0_d0_12
#print axioms value_k3_i1_o0_d0_13
#print axioms value_k3_i1_o0_d0_14
#print axioms value_k3_i1_o0_d0_15
#print axioms value_k3_i1_o0_d0_16
#print axioms value_k3_i1_o0_d0_17
#print axioms contract_k3_i1_o0_d0
#print axioms step_k3_i1_o0_d0
#print axioms shape_k3_i1_o0_d1
#print axioms value_k3_i1_o0_d1_0
#print axioms value_k3_i1_o0_d1_1
#print axioms value_k3_i1_o0_d1_2
#print axioms value_k3_i1_o0_d1_3
#print axioms value_k3_i1_o0_d1_4
#print axioms value_k3_i1_o0_d1_5
#print axioms value_k3_i1_o0_d1_6
#print axioms value_k3_i1_o0_d1_7
#print axioms value_k3_i1_o0_d1_8
#print axioms value_k3_i1_o0_d1_9
#print axioms value_k3_i1_o0_d1_10
#print axioms value_k3_i1_o0_d1_11
#print axioms value_k3_i1_o0_d1_12
#print axioms value_k3_i1_o0_d1_13
#print axioms value_k3_i1_o0_d1_14
#print axioms value_k3_i1_o0_d1_15
#print axioms value_k3_i1_o0_d1_16
#print axioms value_k3_i1_o0_d1_17
#print axioms contract_k3_i1_o0_d1
#print axioms step_k3_i1_o0_d1
#print axioms shape_k3_i1_o0_d2
#print axioms value_k3_i1_o0_d2_0
#print axioms value_k3_i1_o0_d2_1
#print axioms value_k3_i1_o0_d2_2
#print axioms value_k3_i1_o0_d2_3
#print axioms value_k3_i1_o0_d2_4
#print axioms value_k3_i1_o0_d2_5
#print axioms value_k3_i1_o0_d2_6
#print axioms value_k3_i1_o0_d2_7
#print axioms value_k3_i1_o0_d2_8
#print axioms value_k3_i1_o0_d2_9
#print axioms value_k3_i1_o0_d2_10
#print axioms value_k3_i1_o0_d2_11
#print axioms value_k3_i1_o0_d2_12
#print axioms value_k3_i1_o0_d2_13
#print axioms value_k3_i1_o0_d2_14
#print axioms value_k3_i1_o0_d2_15
#print axioms value_k3_i1_o0_d2_16
#print axioms value_k3_i1_o0_d2_17
#print axioms contract_k3_i1_o0_d2
#print axioms step_k3_i1_o0_d2
#print axioms legacy_sameaxis_counterexample
#print axioms missing_scope
#print axioms wrong_world_rejected
#print axioms legacy_distinct_axis_control
#print axioms duplicate_group_rejected
#print axioms invalid_op
#print axioms invalid_order
#print axioms invalid_arity
end
end TrainVerify.Denote.AllToAllSourceFaithful.Witness
