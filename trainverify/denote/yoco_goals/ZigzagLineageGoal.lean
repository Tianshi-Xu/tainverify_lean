/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagExitGear
import denote.yoco_goals.ZigzagLayoutRelRegression

/-!
# Zigzag-aware lineage goals

`LineageGoal` states reconstruction as `reconstructForGoal`, i.e. either an
ordinary `reconstructWithDim` gather or a replicated "pick one". Both are wrong
for a context-parallel tensor whose shards are in NNScaler's **zigzag** layout:
under cp=2 rank 0 owns global positions `[0, 3]`, not the contiguous `[0, 1]`.

The shard *shapes* are identical either way, which is why the goal emitter could
not distinguish them and (before `Verdict/graph_to_lean.py` grew an ownership
oracle) emitted plain gather goals that were simply false.

This module adds the missing statement form. It is deliberately **additive**:
`LineageGoal` is untouched, so none of the ~1135 already-proven goals move.

## The shape of the fix

`ZigzagLineageGoal` carries the same identifying data as a `LineageGoal` plus the
cu-metadata tid that pins the CP layout. `ZigzagGoalHolds` discharges it against
`Zigzag2Rel` rather than `reconstructWithDim`.

Two bridges make it usable:

* `ZigzagGoalHolds.to_gather_after_unshuffle` — once the graph's
  `FW_maybe_unshuffle` has run, a zigzag goal becomes an ordinary `Gather2Rel`,
  which is exactly what the existing machinery consumes.
* `ZigzagGoalHolds.of_zigzag2Rel` / `.zigzag2Rel` — pack and unpack, so the ~502
  existing `recon_zigzagGoal_N_faithful` theorems satisfy the new form directly
  without being reproved.
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
  discharge rule below, matching the collectives in `ZigzagCollective`.

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

/-! ### Pack / unpack against the existing `Zigzag2Rel` theorems

The ~502 `recon_zigzagGoal_N_faithful` results in this repository already have
exactly the `Zigzag2Rel` shape. These two lemmas let them satisfy
`ZigzagGoalHolds` without being reproved. -/

/-- Build a `ZigzagGoalHolds` from a `Zigzag2Rel` in the standard two-rank form. -/
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

/-! ### The bridge back to ordinary reconstruction

This is what makes the new form *useful* rather than merely honest: applying the
graph's `FW_maybe_unshuffle` to a zigzag goal's two shards yields an ordinary
`Gather2Rel`, so every downstream lemma that already consumes `Gather2Rel` keeps
working unchanged. -/

/-- After unshuffling, a zigzag goal is an ordinary two-rank dim-0 gather. -/
theorem ZigzagGoalHolds.to_gather_after_unshuffle
    {g : ZigzagLineageGoal} {smStore pmStore : Store}
    (lDim hM : Nat)
    (h : ZigzagGoalHolds g smStore pmStore)
    (hts : g.tsShape = lDim * 2 :: [hM])
    (hl : 0 < lDim) (heven : lDim % 2 = 0) (hns : [lDim, hM] ≠ [1])
    (hdecoded : decodeCuSeqlens (pmStore g.cuTid) = [0, 2 * lDim]) :
    ∃ (t0 t1 : Tid),
      g.tps = [{ rank := 0, tid := t0 }, { rank := 1, tid := t1 }] ∧
      Gather2Rel (smStore g.ts)
        (fw_maybe_unshuffle_collective [pmStore t0, pmStore t1]
          (decodeCuSeqlens (pmStore g.cuTid)) 2 0)
        (fw_maybe_unshuffle_collective [pmStore t0, pmStore t1]
          (decodeCuSeqlens (pmStore g.cuTid)) 2 1)
        [lDim * 2, hM] [lDim, hM] := by
  obtain ⟨t0, t1, htps, hrel⟩ := h.zigzag2Rel
  refine ⟨t0, t1, htps, ?_⟩
  have hshape : (smStore g.ts).shape = lDim * 2 :: [hM] := by
    obtain ⟨_, _, _, _, _, hfs, _⟩ := h
    rw [hfs, hts]
  have hhead : (smStore g.ts).shape.headD 0 / 2 = lDim := by
    rw [hshape]
    simp only [List.headD_cons]
    omega
  rw [hts, hhead] at hrel
  exact Zigzag2Rel.to_gather2_unshuffle lDim hM (by simpa using hrel)
    hl heven hns hdecoded

/-! ### Non-vacuity

`ZigzagGoalHolds` must not be accidentally unsatisfiable — a goal form that
nothing can satisfy would make every downstream theorem vacuous (AGENTS #29,
vacuity trap 2). The witness below exhibits a concrete satisfying pair of
stores, so the predicate is genuinely inhabited. -/

theorem ZigzagGoalHolds.satisfiable :
    ∃ (g : ZigzagLineageGoal) (smStore pmStore : Store),
      ZigzagGoalHolds g smStore pmStore := by
  classical
  -- Reuse the concrete cp=2 fixture from `ZigzagLayoutRelRegression`: a genuine
  -- `[8, 1]` tensor whose two `[4, 1]` shards are in real zigzag layout (rank 0
  -- owning global positions [0, 3], not [0, 1]). Using a real fixture rather
  -- than a zero tensor matters: a degenerate witness could satisfy the relation
  -- for the wrong reason and would not rule out vacuity.
  refine ⟨{ ts := 10, tsShape := [8, 1],
            tps := [{ rank := 0, tid := 11 }, { rank := 1, tid := 12 }],
            tpShapes := [[4, 1], [4, 1]], cuTid := 13, cpSize := 2 },
          fun _ => ZigzagLayoutRelRegression.full,
          fun t =>
            if t = 11 then ZigzagLayoutRelRegression.z0
            else if t = 12 then ZigzagLayoutRelRegression.z1
            else ZigzagLayoutRelRegression.cu,
          ?_⟩
  refine ZigzagGoalHolds.of_zigzag2Rel _ _ _ 11 12 4 [1] rfl rfl rfl rfl
    ZigzagLayoutRelRegression.full_shape ?_
  simpa using ZigzagLayoutRelRegression.concrete_zigzag2Rel

end

end TrainVerify.Denote.GeneratedPatterns
