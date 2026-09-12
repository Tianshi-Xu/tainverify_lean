import denote.SourceBWLayernormDxUnit

/-!
Nondegenerate, satisfiable source-input fixture:
D=2, T=3, B=2, S=3, H=5, all DP units and all TP ranks.
G/X are distinct nonconstant position-dependent tensors; gamma is nonzero
on every hidden coordinate. X has row-dependent hidden-coordinate variation,
not merely a rowwise additive shift. These are actual saved-X input values.
No zeroTensor witness, output-equality premise, sorry, or new axiom is used.
The zeroTensor appearing in list getD is only an unreachable fallback.
Edit-only candidate: parent runs Lean and the printed axiom audit.
-/
namespace TrainVerify.Denote.LayernormDxUnitWitness
noncomputable section
set_option maxHeartbeats 800000

 def g : Tensor := Tensor.mkShape [4, 9, 5]
  (fun i => ((i.1 * i.1 + 3 * i.1 + 1 : Nat) : Scalar))
 def x : Tensor := Tensor.mkShape [4, 9, 5]
  (fun i => (((i.1 % 5 + 1) * (i.1 / 5 + 1) +
    (i.1 % 5) * (i.1 % 5) + 2 : Nat) : Scalar))
 def gamma : Tensor := Tensor.mkShape [5] (fun i => ((i.1 + 1 : Nat) : Scalar))
 def beta : Tensor := Tensor.mkShape [5] (fun i => ((i.1 : Nat) : Scalar) - 2)

 def shards (y : Tensor) (u : Fin 2) : List Tensor :=
  List.ofFn (fun r : Fin 3 => chunkPrimDimN 1 3 r.1 (chunkPrimDimN 0 2 u.1 y))

 theorem shards_length (y : Tensor) (u : Fin 2) : (shards y u).length = 3 :=
  List.length_ofFn

 theorem shards_shape (y : Tensor) (hy : y.shape = [4, 9, 5]) (u : Fin 2) :
    ∀ z ∈ shards y u, z.shape = [2, 3, 5] := by
  intro z hz
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hz
  exact source_dx_chunk1_shape 3 r.1 2 3 5 _ (by decide)
    (source_dx_chunk0_shape 2 u.1 2 9 5 y (by decide) hy)

 theorem input_relation (y : Tensor) (hy : y.shape = [4, 9, 5]) (u : Fin 2) :
    chunkPrimDimN 0 2 u.1 y = allGatherPrimDimN 1 3 0 (shards y u) := by
  have hc := source_dx_chunk0_shape 2 u.1 2 9 5 y (by decide) hy
  exact (allGatherPrimDimN_chunks_ofFn 1 3 (chunkPrimDimN 0 2 u.1 y)
    (by decide) (by rw [hc]; decide) (by rw [hc]; decide)).symm

/-- The entire joint input contract is inhabited for every DP unit. -/
theorem inputs_satisfiable (u : Fin 2) :
    g.shape = [4, 9, 5] ∧ x.shape = [4, 9, 5] ∧
    gamma.shape = [5] ∧ beta.shape = [5] ∧
    (shards g u).length = 3 ∧ (shards x u).length = 3 ∧
    (∀ z ∈ shards g u, z.shape = [2, 3, 5]) ∧
    (∀ z ∈ shards x u, z.shape = [2, 3, 5]) ∧
    chunkPrimDimN 0 2 u.1 g = allGatherPrimDimN 1 3 0 (shards g u) ∧
    chunkPrimDimN 0 2 u.1 x = allGatherPrimDimN 1 3 0 (shards x u) :=
  ⟨rfl, rfl, rfl, rfl, shards_length g u, shards_length x u,
    shards_shape g rfl u, shards_shape x rfl u,
    input_relation g rfl u, input_relation x rfl u⟩

 def localDx (u : Fin 2) (r : Fin 3) : Tensor :=
  (bw_layernorm ((shards g u).getD r.1 (zeroTensor [2, 3, 5]))
    ((shards x u).getD r.1 (zeroTensor [2, 3, 5])) gamma beta).1

/-- Genuine theorem application, not equality postulated in a witness record. -/
theorem all_units_all_ranks (u : Fin 2) (r : Fin 3) :
    localDx u r = chunkPrimDimN 1 3 r.1
      (chunkPrimDimN 0 2 u.1 (bw_layernorm g x gamma beta).1) := by
  exact source_bw_layernorm_dx_unit_local 2 3 2 3 5 u.1 g x gamma beta
    (shards g u) (shards x u) (by decide) (by decide) (by decide)
    (by decide) (by decide) u.2 rfl rfl (shards_length g u) (shards_length x u)
    (shards_shape g rfl u) (shards_shape x rfl u) rfl rfl
    (input_relation g rfl u) (input_relation x rfl u) r

 theorem global_shape : (bw_layernorm g x gamma beta).1.shape = [4, 9, 5] :=
  bw_layernorm_dx_shape g x gamma beta 5 [9, 4] rfl

/-- Both sides have the intended nonempty [B,S,H] shape. -/
theorem output_shapes (u : Fin 2) (r : Fin 3) :
    (localDx u r).shape = [2, 3, 5] ∧
    (chunkPrimDimN 1 3 r.1 (chunkPrimDimN 0 2 u.1
      (bw_layernorm g x gamma beta).1)).shape = [2, 3, 5] := by
  have hs := source_dx_chunk1_shape 3 r.1 2 3 5 _ (by decide)
    (source_dx_chunk0_shape 2 u.1 2 9 5 _ (by decide) global_shape)
  exact ⟨(congrArg Tensor.shape (all_units_all_ranks u r)).trans hs, hs⟩

 theorem g_nonconstant : valAt g 0 ≠ valAt g 1 := by
  change ((1 : Nat) : Scalar) ≠ ((5 : Nat) : Scalar)
  norm_num
 theorem x_nonconstant : valAt x 0 ≠ valAt x 1 := by
  change ((3 : Nat) : Scalar) ≠ ((5 : Nat) : Scalar)
  norm_num
 theorem inputs_distinct : valAt g 0 ≠ valAt x 0 := by
  change ((1 : Nat) : Scalar) ≠ ((3 : Nat) : Scalar)
  norm_num
 theorem gamma_nonzero (j : Nat) (hj : j < 5) : valAt gamma j ≠ 0 := by
  rw [valAt_of_lt _ _ (by exact hj)]
  change (((j + 1 : Nat) : Scalar)) ≠ 0
  positivity

#print axioms shards_length
#print axioms shards_shape
#print axioms input_relation
#print axioms global_shape
#print axioms inputs_distinct
#print axioms inputs_satisfiable
#print axioms all_units_all_ranks
#print axioms output_shapes
#print axioms g_nonconstant
#print axioms x_nonconstant
#print axioms gamma_nonzero
end
end TrainVerify.Denote.LayernormDxUnitWitness
