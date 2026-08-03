import denote.Denote

/-!
# Graph-parameterized denotation gears

Small structural lemmas shared by bridge families.  They are parameterized by
the graph rather than duplicated once for every generated SM/PM namespace.
-/

namespace TrainVerify.Denote

/-- Evaluate a tid written at node `k` by exposing that node, provided the
remaining suffix does not overwrite the tid. -/
theorem denoteGraph_val_at_node (g : GraphDecl) (init : Store) (k : Nat)
    (out : Tid) (hk : k < g.nodes.length)
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), out ∉ n.outs) :
    denoteGraph g init out =
      applyNode g (denoteGraph { g with nodes := g.nodes.take k } init)
        g.nodes[k] out := by
  have e1 : denoteGraph g init out =
      denoteGraph { g with nodes := g.nodes.take (k + 1) } init out :=
    denoteGraph_tid_eq_of_suffix_no_writes g init out
      (g.nodes.take (k + 1)) (g.nodes.drop (k + 1))
      (List.take_append_drop (k + 1) g.nodes).symm hdrop
  have hfn : applyNode { g with nodes := g.nodes.take (k + 1) } = applyNode g :=
    applyNode_congr_numRanks _ _ rfl
  have hfn' : applyNode { g with nodes := g.nodes.take k } = applyNode g :=
    applyNode_congr_numRanks _ _ rfl
  rw [e1]
  simp only [denoteGraph, hfn, hfn']
  exact congrFun (foldl_take_succ (applyNode g) g.nodes init k hk) out

/-- Expose one graph step at node `k`. -/
theorem denoteGraph_step (g : GraphDecl) (init : Store) (k : Nat)
    (hk : k < g.nodes.length) :
    denoteGraph { g with nodes := g.nodes.take (k + 1) } init =
      applyNode g (denoteGraph { g with nodes := g.nodes.take k } init) g.nodes[k] := by
  have hfn : applyNode { g with nodes := g.nodes.take (k + 1) } = applyNode g :=
    applyNode_congr_numRanks _ _ rfl
  have hfn' : applyNode { g with nodes := g.nodes.take k } = applyNode g :=
    applyNode_congr_numRanks _ _ rfl
  simp only [denoteGraph, hfn, hfn']
  exact foldl_take_succ (applyNode g) g.nodes init k hk

/-- A prefix and the full graph agree at a tid not written by the suffix. -/
theorem denoteGraph_prefix_eq (g : GraphDecl) (init : Store) (k : Nat)
    (tid : Tid) (hdrop : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    denoteGraph { g with nodes := g.nodes.take k } init tid =
      denoteGraph g init tid :=
  (denoteGraph_tid_eq_of_suffix_no_writes g init tid
    (g.nodes.take k) (g.nodes.drop k)
    (List.take_append_drop k g.nodes).symm hdrop).symm

/-- Initial lineage goals remain true after evaluating graphs that never write
any SM/PM tid observed by those goals. -/
theorem initGoals_preserved_of_not_written
    (sm pm : GraphDecl) (goals : List LineageGoal) (initSM initPM : Store)
    (hSM : ∀ gl ∈ goals, ∀ n ∈ sm.nodes, gl.ts ∉ n.outs)
    (hPM : ∀ gl ∈ goals, ∀ tp ∈ gl.tps, ∀ n ∈ pm.nodes, tp.tid ∉ n.outs)
    (hInit : InitGoalsHold pm.numRanks goals initSM initPM) :
    InitGoalsHold pm.numRanks goals (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  intro gl hgl
  have h0 := hInit gl hgl
  have hts : denoteGraph sm initSM gl.ts = initSM gl.ts := by
    exact denoteGraph_tid_eq_of_forall_not_mem_outs sm sm.nodes initSM gl.ts
      (hSM gl hgl)
  have htps : ∀ tp ∈ gl.tps, denoteGraph pm initPM tp.tid = initPM tp.tid := by
    intro tp htp
    exact denoteGraph_tid_eq_of_forall_not_mem_outs pm pm.nodes initPM tp.tid
      (hPM gl hgl tp htp)
  dsimp only [InitGoalHolds] at h0 ⊢
  rw [hts, List.map_congr_left (fun tp htp => htps tp htp)]
  exact h0

/-- Successful lookup in `shapeEnvOfList` comes from a list member. -/
theorem shapeEnvOfList_mem_of_eq_some {xs : List (Tid × Shape)} {tid sh}
    (h : shapeEnvOfList xs tid = some sh) : (tid, sh) ∈ xs := by
  unfold shapeEnvOfList at h
  cases hf : xs.find? (fun p => p.1 = tid) with
  | none => rw [hf] at h; simp at h
  | some pair =>
    rw [hf] at h
    obtain ⟨t, s⟩ := pair
    simp only [Option.some.injEq] at h
    subst h
    have hmem := List.mem_of_find?_eq_some hf
    have hpred := List.find?_some hf
    simp only [decide_eq_true_eq] at hpred
    subst hpred
    exact hmem

/-- Restrict `StoreShapesHold` to a shape environment whose entries resolve in
the larger environment. -/
theorem storeShapesHold_weaken {init : Store} {small big : List (Tid × Shape)}
    (hsub : ∀ p ∈ small, shapeEnvOfList big p.1 = some p.2)
    (hbig : StoreShapesHold init (shapeEnvOfList big)) :
    StoreShapesHold init (shapeEnvOfList small) := by
  intro tid sh hsh
  have hmem : (tid, sh) ∈ small := shapeEnvOfList_mem_of_eq_some hsh
  exact hbig tid sh (hsub (tid, sh) hmem)

end TrainVerify.Denote
