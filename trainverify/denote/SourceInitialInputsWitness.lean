import denote.SourceInitialInputs

/-! Uncompiled P2 nonvacuity probe. This is a mathematical witness, not a
replacement for the actual runtime feed or an assertion about saved captures. -/
namespace TrainVerify.Denote.SourceInitialInputsWitness
open SourceScopedEval SourceInitialInputs RelationCompiler
noncomputable section
set_option maxHeartbeats 500000

private def full : Tensor :=
  { shape := [2, 1], val := fun i => (i.val : Scalar) }
private def unit0 : Tensor := chunkPrimDimN 0 2 0 full
private def unit1 : Tensor := chunkPrimDimN 0 2 1 full

/-- Positive shape, unequal DP samples and exact TP copies inhabit all four
caller equations. An equal-valued/zero-only witness could hide a row swap. -/
theorem candidate_nonvacuous :
    ∃ x a b c d : Tensor,
      x.shape = [2, 1] ∧
      a = chunkPrimDimN 0 2 0 x ∧ b = chunkPrimDimN 0 2 0 x ∧
      c = chunkPrimDimN 0 2 1 x ∧ d = chunkPrimDimN 0 2 1 x ∧
      valAt a 0 ≠ valAt c 0 ∧
      ChunkedRel x [a, c] 0 [2, 1] [1, 1] ∧
      ChunkedRel x [b, d] 0 [2, 1] [1, 1] ∧
      ReplicatedRel a [a, b] [1, 1] ∧ ReplicatedRel c [c, d] [1, 1] := by
  have h0 : valAt unit0 0 = valAt full 0 :=
    batch_row_coordinate full unit0 2 0 1 1 rfl rfl
      (by decide) (by decide) (by decide) 0 0 (by decide) (by decide)
  have h1 : valAt unit1 0 = valAt full 1 :=
    batch_row_coordinate full unit1 2 1 1 1 rfl rfl
      (by decide) (by decide) (by decide) 0 0 (by decide) (by decide)
  refine ⟨full, unit0, unit0, unit1, unit1, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rw [h0, h1]
    rw [valAt_of_lt full 0 (by decide), valAt_of_lt full 1 (by decide)]
    dsimp [full]
    norm_num
  · exact batchSplit_tpCopies_two full unit0 unit0 unit1 unit1 1 1 rfl rfl rfl rfl rfl

/-- Intentionally descending port IDs: graph order, not numerical sort order,
is authoritative. Both value-bearing ports have a valid checked loader. -/
private def loader : NodeDecl :=
  { rank := 0, op := "OpName.DATALOADER", ins := [], outs := [9, 4], params := [] }
private def feed : PortFeed := [(9, unit0), (4, unit1)]

theorem ordered_feed_contract : InputContract loader feed := by decide

theorem ordered_feed_values (s : Store) :
    storeSet s feed 9 = unit0 ∧ storeSet s feed 4 = unit1 := by
  have hs := checkedInputStep_valid s loader feed ordered_feed_contract
  refine ⟨?_, ?_⟩
  · exact checkedInputStep_value s (storeSet s feed) loader feed 9 unit0
      (List.mem_cons_self) hs
  · exact checkedInputStep_value s (storeSet s feed) loader feed 4 unit1
      (List.mem_cons_of_mem _ List.mem_cons_self) hs

#print axioms candidate_nonvacuous
#print axioms ordered_feed_contract
#print axioms ordered_feed_values
end
end TrainVerify.Denote.SourceInitialInputsWitness
