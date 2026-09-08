import denote.SourceScopedEval

namespace TrainVerify.Denote.SourceScopedPrefix
open SourceScopedEval
set_option maxHeartbeats 500000
noncomputable section

/-- Shape projection avoids traversing normalization's value arithmetic. -/
theorem layernorm_shape (x w b : Tensor) : (fw_layernorm x w b).shape = x.shape := by
  unfold fw_layernorm
  split <;> rfl

/-- The 2D analogue of Denote's existing generic 3D shape theorem. -/
theorem linear_shape_2d (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  simp only [fw_linear, hx, hw, Tensor.mkShape]

#print axioms layernorm_shape
#print axioms linear_shape_2d

/-- Composition of the existing shared engine, without another graph or evaluator. -/
theorem runUsing_append {α : Type} (advance : α → Store → Option Store)
    (xs ys : List α) (s : Option Store) :
    runUsing advance (xs ++ ys) s = runUsing advance ys (runUsing advance xs s) := by
  exact List.foldl_append

/-- A successful complete-request prefix feeds the canonical remaining requests. -/
theorem continuation {α : Type} (advance : α → Store → Option Store)
    (requests : List α) (k : Nat) (s t : Store)
    (h : runUsing advance (requests.take k) (some s) = some t) :
    runUsing advance requests (some s) = runUsing advance (requests.drop k) (some t) := by
  conv_lhs => rw [← List.take_append_drop k requests]
  rw [runUsing_append, h]

/-- Frame includes every request in the prefix, not just collective operands. -/
theorem frame (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (requests : List InputRequest) (s t : Store)
    (tid : Tid) (ht : ∀ row ∈ requests, tid ∉ row.1.outs)
    (h : runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
      requests (some s) = some t) : t tid = s tid := by
  apply runUsing_frame _ requests s t tid _ h
  intro row hr a b hb
  exact stepWithInputs_skip g (scope row.1) (peer row.1) a b row.1 row.2 tid (ht row hr) hb

#print axioms runUsing_append
#print axioms continuation
#print axioms frame
end
end TrainVerify.Denote.SourceScopedPrefix
