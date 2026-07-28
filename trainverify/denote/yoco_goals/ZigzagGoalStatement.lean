/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagLayoutRel

/-!
# Zigzag-aware lineage goals: the statement layer

`LineageGoal` (in `denote/Denote.lean`) states reconstruction as
`reconstructForGoal`: either an ordinary `reconstructWithDim` gather or a
replicated "pick one". Both are **false** for a context-parallel tensor whose
shards are in NNScaler's zigzag layout — under cp=2 rank 0 owns global positions
`[0, 3]`, not the contiguous `[0, 1]`.

The shard *shapes* are identical either way, which is why shape-based layout
inference in the goal emitter could not distinguish them.
`ZigzagGoalRefutation.gatheredZigzag_ne_full` machine-checks the disagreement on
a concrete cp=2 fixture.

This module carries only the goal **structure** and its `Prop`, deliberately kept
free of any dependency on generated graphs so that
`denote/GeneratedYOCOMoE.lean` can import it and emit `ZigzagLineageGoal`
definitions directly. The bridges to `Gather2Rel` and the non-vacuity witness
live in `denote/yoco_goals/ZigzagLineageGoal.lean`, which sits above the
generated module.

`LineageGoal` itself is untouched, so none of the already-proven goals move.
-/

set_option linter.style.longLine false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-- A lineage goal for a tensor whose parallel shards are in CP zigzag layout.

Mirrors `LineageGoal`, with two differences:

* `cuTid` names the cu_seqlens tensor that pins the zigzag layout. Ownership is
  not recoverable from shapes, so it must be carried explicitly.
* `cpSize` is the context-parallel width. Only `cpSize = 2` is supported by the
  discharge rule, matching the collectives in `ZigzagCollective`.

There is no `gatherDim`/`replicated`: a zigzag tensor is sharded along the
sequence axis by construction, and it is never a replicated copy. -/
structure ZigzagLineageGoal where
  ts : Tid
  tsShape : Shape
  tps : List Piece
  tpShapes : List Shape
  cuTid : Tid
  cpSize : Nat := 2
  deriving Repr, DecidableEq

/-- The obligation carried by a `ZigzagLineageGoal`, stated over two arbitrary
stores (in practice the SM and PM denotations).

Shapes are asserted exactly as for an ordinary goal; the *value* claim is
`Zigzag2Rel` rather than `reconstructForGoal`. `Zigzag2Rel` says the full tensor
is the ordinary dim-0 gather of hidden contiguous **source** shards, while each
exposed shard is the zigzag shuffle of those sources — which is precisely the
relation an ordinary gather goal gets wrong. -/
def ZigzagGoalHolds (g : ZigzagLineageGoal) (smStore pmStore : Store) : Prop :=
  g.cpSize = 2 ∧
  ∃ (t0 t1 : Tid),
    g.tps = [{ rank := 0, tid := t0 }, { rank := 1, tid := t1 }] ∧
    g.tpShapes = [(smStore g.ts).shape.headD 0 / 2 :: g.tsShape.tail,
                  (smStore g.ts).shape.headD 0 / 2 :: g.tsShape.tail] ∧
    (smStore g.ts).shape = g.tsShape ∧
    Zigzag2Rel (smStore g.ts) (pmStore t0) (pmStore t1) (pmStore g.cuTid)
      g.tsShape ((smStore g.ts).shape.headD 0 / 2 :: g.tsShape.tail)

/-- Build a `ZigzagGoalHolds` from a `Zigzag2Rel` in the standard two-rank form.

This is what lets the ~502 existing `recon_zigzagGoal_N_faithful` theorems
satisfy the new goal form without being reproved. -/
theorem ZigzagGoalHolds.of_zigzag2Rel
    (g : ZigzagLineageGoal) (smStore pmStore : Store)
    (t0 t1 : Tid) (lDim : Nat) (rest : Shape)
    (hcp : g.cpSize = 2)
    (htps : g.tps = [{ rank := 0, tid := t0 }, { rank := 1, tid := t1 }])
    (hts : g.tsShape = lDim * 2 :: rest)
    (htpShapes : g.tpShapes = [lDim :: rest, lDim :: rest])
    (hfullShape : (smStore g.ts).shape = lDim * 2 :: rest)
    (hrel : Zigzag2Rel (smStore g.ts) (pmStore t0) (pmStore t1) (pmStore g.cuTid)
      (lDim * 2 :: rest) (lDim :: rest)) :
    ZigzagGoalHolds g smStore pmStore := by
  have hhead : (smStore g.ts).shape.headD 0 / 2 = lDim := by
    rw [hfullShape]
    simp only [List.headD_cons]
    omega
  refine ⟨hcp, t0, t1, htps, ?_, ?_, ?_⟩
  · rw [htpShapes, hhead, hts]; simp
  · rw [hfullShape, hts]
  · rw [hhead, hts]; simpa using hrel

/-- Recover the underlying `Zigzag2Rel`. -/
theorem ZigzagGoalHolds.zigzag2Rel
    {g : ZigzagLineageGoal} {smStore pmStore : Store}
    (h : ZigzagGoalHolds g smStore pmStore) :
    ∃ (t0 t1 : Tid),
      g.tps = [{ rank := 0, tid := t0 }, { rank := 1, tid := t1 }] ∧
      Zigzag2Rel (smStore g.ts) (pmStore t0) (pmStore t1) (pmStore g.cuTid)
        g.tsShape ((smStore g.ts).shape.headD 0 / 2 :: g.tsShape.tail) := by
  obtain ⟨_, t0, t1, htps, _, _, hrel⟩ := h
  exact ⟨t0, t1, htps, hrel⟩

end

end TrainVerify.Denote.GeneratedPatterns
