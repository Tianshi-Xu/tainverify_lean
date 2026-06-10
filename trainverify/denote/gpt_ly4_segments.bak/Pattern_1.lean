/- Auto-generated pattern proof file.
   Pattern: 1
   Hash: 5ce1449adbcdff14
   Goals: 1
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_19

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_1_goalIds : List Nat := [1]
inductive pattern_1_target : Prop → Prop
  | goal_1 : pattern_1_target goal_1_stmt

def pattern_1_stmt : Prop :=
  ∀ {target : Prop}, pattern_1_target target → target

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

/-! ## Node literals (singleton output nodes we will rewrite via `applyNode_*_out`). -/

@[reducible] private def sm_n117 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sum", ins := [712], outs := [562] }

@[reducible] private def pm_n771 : NodeDecl :=
  { rank := 0, op := "OpName.FW_sum", ins := [3373], outs := [3397] }
@[reducible] private def pm_n773 : NodeDecl :=
  { rank := 1, op := "OpName.FW_sum", ins := [3374], outs := [3398] }
@[reducible] private def pm_n775 : NodeDecl :=
  { rank := 2, op := "OpName.FW_sum", ins := [3375], outs := [3399] }
@[reducible] private def pm_n777 : NodeDecl :=
  { rank := 3, op := "OpName.FW_sum", ins := [3376], outs := [3400] }
@[reducible] private def pm_n782 : NodeDecl :=
  { rank := 0, op := "OpName.AllReducePrim",
    ins := ((List.range 4).map (fun r => 3397 + r)),
    outs := [562] }

/-! ## A reusable helper that traces `denoteGraph g initStore tid` to
`fw_sum (denoteGraph g initStore srcTid)` whenever the unique writer
of `tid` is a `FW_sum` node at index `K` and the unique writer of
`srcTid` is at some index `< K`. -/

private theorem denote_fw_sum_step (g : GraphDecl) (initStore : Store)
    (K : Nat) (srcTid outTid : Tid) (rk : Nat)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.FW_sum",
                      ins := [srcTid], outs := [outTid] })
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (hsuf_out : ∀ n ∈ g.nodes.drop (K+1), outTid ∉ n.outs)
    (hsuf_src : ∀ n ∈ g.nodes.drop K, srcTid ∉ n.outs) :
    denoteGraph g initStore outTid = fw_sum (denoteGraph g initStore srcTid) := by
  -- Drop nodes beyond index K (none write outTid).
  have h1 : denoteGraph g initStore outTid =
      denoteGraph { g with nodes := g.nodes.take (K+1) } initStore outTid :=
    denoteGraph_tid_eq_of_suffix_no_writes g initStore outTid
      (g.nodes.take (K+1)) (g.nodes.drop (K+1))
      (List.take_append_drop (K+1) _).symm hsuf_out
  rw [h1]
  -- take (K+1) = take K ++ [node] using the abstract list lemma + the index equality.
  have htake : g.nodes.take (K+1) = g.nodes.take K ++ [node] := by
    rw [list_take_succ_eq_take_append_get g.nodes K hKlt, hidx]
  have hg_eq : ({ g with nodes := g.nodes.take (K+1) } : GraphDecl) =
      { g with nodes := g.nodes.take K ++ [node] } := by
    cases g; congr 1
  rw [hg_eq, denoteGraph_nodes_append]
  -- denoteGraph [node] s = applyNode g s node.
  have hsing : ({ g with nodes := [node] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := node :: [] } := by cases g; rfl
  rw [hsing, denoteGraph_cons_eq g node []]
  change applyNode g (denoteGraph { g with nodes := g.nodes.take K } initStore) node outTid = _
  rw [hnode, applyNode_fw_sum_out g _ rk srcTid outTid]
  -- Replace (denoteGraph (take K)) srcTid by (denoteGraph g) srcTid.
  have hsrc : (denoteGraph { g with nodes := g.nodes.take K } initStore) srcTid =
      denoteGraph g initStore srcTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore srcTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_src).symm
  rw [hsrc]

/-- Same shape, for `AllReducePrim` with an arbitrary list of input tids. -/
private theorem denote_allReduce_step (g : GraphDecl) (initStore : Store)
    (K : Nat) (ins : List Tid) (outTid : Tid) (rk : Nat)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.AllReducePrim",
                      ins := ins, outs := [outTid] })
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (hsuf_out : ∀ n ∈ g.nodes.drop (K+1), outTid ∉ n.outs)
    (hsuf_ins : ∀ tid ∈ ins, ∀ n ∈ g.nodes.drop K, tid ∉ n.outs) :
    denoteGraph g initStore outTid =
      allReducePrim g.numRanks rk (ins.map (denoteGraph g initStore)) := by
  have h1 : denoteGraph g initStore outTid =
      denoteGraph { g with nodes := g.nodes.take (K+1) } initStore outTid :=
    denoteGraph_tid_eq_of_suffix_no_writes g initStore outTid
      (g.nodes.take (K+1)) (g.nodes.drop (K+1))
      (List.take_append_drop (K+1) _).symm hsuf_out
  rw [h1]
  have htake : g.nodes.take (K+1) = g.nodes.take K ++ [node] := by
    rw [list_take_succ_eq_take_append_get g.nodes K hKlt, hidx]
  have hg_eq : ({ g with nodes := g.nodes.take (K+1) } : GraphDecl) =
      { g with nodes := g.nodes.take K ++ [node] } := by
    cases g; congr 1
  rw [hg_eq, denoteGraph_nodes_append]
  have hsing : ({ g with nodes := [node] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := node :: [] } := by cases g; rfl
  rw [hsing, denoteGraph_cons_eq g node []]
  change applyNode g (denoteGraph { g with nodes := g.nodes.take K } initStore) node outTid = _
  rw [hnode, applyNode_allReducePrim_out g _ rk ins outTid]
  -- Convert ins.map (denoteGraph (take K)) to ins.map (denoteGraph g) via List.map_congr.
  congr 1
  apply List.map_congr_left
  intro tid htid
  exact (denoteGraph_tid_eq_of_suffix_no_writes g initStore tid
    (g.nodes.take K) (g.nodes.drop K)
    (List.take_append_drop K _).symm (hsuf_ins tid htid)).symm

/-! ## SM-side evaluation: `denoteGraph sm initSM 562 = fw_sum (... 712)`. -/

private theorem sm_eval_562 (initSM : Store) :
    denoteGraph sm initSM 562 = fw_sum (denoteGraph sm initSM 712) := by
  apply denote_fw_sum_step sm initSM 117 712 562 0 sm_n117 rfl
    (by decide) (by decide) (by decide) (by decide)

/-! ## PM-side evaluations: each `3397 + r` is `fw_sum (... 3373 + r)`. -/

private theorem pm_eval_3397 (initPM : Store) :
    denoteGraph pm initPM 3397 = fw_sum (denoteGraph pm initPM 3373) := by
  apply denote_fw_sum_step pm initPM 771 3373 3397 0 pm_n771 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3398 (initPM : Store) :
    denoteGraph pm initPM 3398 = fw_sum (denoteGraph pm initPM 3374) := by
  apply denote_fw_sum_step pm initPM 773 3374 3398 1 pm_n773 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3399 (initPM : Store) :
    denoteGraph pm initPM 3399 = fw_sum (denoteGraph pm initPM 3375) := by
  apply denote_fw_sum_step pm initPM 775 3375 3399 2 pm_n775 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3400 (initPM : Store) :
    denoteGraph pm initPM 3400 = fw_sum (denoteGraph pm initPM 3376) := by
  apply denote_fw_sum_step pm initPM 777 3376 3400 3 pm_n777 rfl
    (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_562 (initPM : Store) :
    denoteGraph pm initPM 562 =
      allReducePrim 4 0
        [ fw_sum (denoteGraph pm initPM 3373),
          fw_sum (denoteGraph pm initPM 3374),
          fw_sum (denoteGraph pm initPM 3375),
          fw_sum (denoteGraph pm initPM 3376) ] := by
  have hAR := denote_allReduce_step pm initPM 782
      ((List.range 4).map (fun r => 3397 + r)) 562 0 pm_n782 rfl
      (by decide) (by decide) (by decide)
      (by
        intro tid htid
        -- Reduce membership to one of 4 cases.
        have hrange : ((List.range 4).map (fun r => 3397 + r)) = [3397, 3398, 3399, 3400] := by
          decide
        rw [hrange] at htid
        cases htid with
        | head => decide
        | tail _ h => cases h with
          | head => decide
          | tail _ h => cases h with
            | head => decide
            | tail _ h => cases h with
              | head => decide
              | tail _ h => exact (nomatch h))
  -- pm.numRanks = 4
  have hnr : pm.numRanks = 4 := rfl
  rw [hnr] at hAR
  rw [hAR]
  -- Convert ((List.range 4).map (3397+·)).map (denoteGraph pm initPM) to the explicit list.
  have hrange : ((List.range 4).map (fun r => 3397 + r)) = [3397, 3398, 3399, 3400] := by
    decide
  rw [hrange]
  simp only [List.map_cons, List.map_nil]
  rw [pm_eval_3397, pm_eval_3398, pm_eval_3399, pm_eval_3400]

/-! ## Bridge lemma applied to abstract tensors. -/

private theorem bridge_4 (t0 t1 t2 t3 : Tensor)
    (h0 : t0.shape = [1, 8, 32])
    (h1 : t1.shape = [1, 8, 32])
    (h2 : t2.shape = [1, 8, 32])
    (h3 : t3.shape = [1, 8, 32]) :
    fw_sum (allGatherPrimDimN 2 4 0 [t0, t1, t2, t3]) =
      allReducePrim 4 0 [fw_sum t0, fw_sum t1, fw_sum t2, fw_sum t3] := by
  have hb := fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum
      (gatherDim := 2) (numParts := 4) (xs := [t0, t1, t2, t3])
      (shardShape := [1, 8, 32])
      (hlen := by simp)
      (hparts := by decide)
      (hhead := by simp [h0])
      (hshape := by
        intro x hx
        cases hx with
        | head => exact h0
        | tail _ hx => cases hx with
          | head => exact h1
          | tail _ hx => cases hx with
            | head => exact h2
            | tail _ hx => cases hx with
              | head => exact h3
              | tail _ hx => exact (nomatch hx))
      (hgatherDim := by decide)
      (hdimPos := by decide)
      (hpostPos := by decide)
  simpa [List.map_cons, List.map_nil] using hb

/-! ## Main theorem.

We obtain the lineage of `712` (i.e., `goal_106`) from `prove_pattern_19`,
combine with `sm_eval_562`, `pm_eval_562`, and the bridging lemma
`fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum`. -/

theorem prove_pattern_1 : pattern_1_stmt := by
  intro target h
  cases h
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- Obtain goal_106 (lineage of tid 712).
  have hGoal106 := prove_pattern_19 (target := goal_106_stmt) pattern_19_target.goal_106
  have h106 := hGoal106 initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨_h712_sh, hpm_shapes, h712_rec⟩ := h106
  simp only [goal_106, List.map_cons, List.map_nil] at hpm_shapes h712_rec
  -- Per-shard shapes.
  have h3373_sh : (denoteGraph pm initPM 3373).shape = [1, 8, 32] := by
    have := hpm_shapes; simp only [List.cons.injEq] at this; exact this.1
  have h3374_sh : (denoteGraph pm initPM 3374).shape = [1, 8, 32] := by
    have := hpm_shapes; simp only [List.cons.injEq] at this; exact this.2.1
  have h3375_sh : (denoteGraph pm initPM 3375).shape = [1, 8, 32] := by
    have := hpm_shapes; simp only [List.cons.injEq] at this; exact this.2.2.1
  have h3376_sh : (denoteGraph pm initPM 3376).shape = [1, 8, 32] := by
    have := hpm_shapes; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  -- Reconstruction → allGatherPrimDimN (head shape ≠ [1]).
  have h712_dimN : denoteGraph sm initSM 712 = allGatherPrimDimN 2 pm.numRanks 0
      [ denoteGraph pm initPM 3373, denoteGraph pm initPM 3374,
        denoteGraph pm initPM 3375, denoteGraph pm initPM 3376 ] := by
    rw [h712_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [h3373_sh]; intro hc; cases hc
  -- Bridge lemma applied to the four pm shards.
  have hbridge :=
    bridge_4 (denoteGraph pm initPM 3373) (denoteGraph pm initPM 3374)
      (denoteGraph pm initPM 3375) (denoteGraph pm initPM 3376)
      h3373_sh h3374_sh h3375_sh h3376_sh
  refine ⟨?_, ?_, ?_⟩
  · -- (denoteGraph sm initSM 562).shape = [1]
    show (denoteGraph sm initSM 562).shape = [1]
    rw [sm_eval_562]; exact fw_sum_shape _
  · -- [(denoteGraph pm initPM 562).shape] = [[1]]
    show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 562 } : Piece)].map (fun p => denoteGraph pm initPM p.tid)) =
        [[1]]
    simp only [List.map_cons, List.map_nil]
    rw [pm_eval_562]
    have hhead :
        ([ fw_sum (denoteGraph pm initPM 3373),
           fw_sum (denoteGraph pm initPM 3374),
           fw_sum (denoteGraph pm initPM 3375),
           fw_sum (denoteGraph pm initPM 3376) ] : List Tensor).head? =
        some (fw_sum (denoteGraph pm initPM 3373)) := rfl
    have := allReducePrim_shape 4 0 _ _ hhead
    simp [this, fw_sum_shape]
  · -- denoteGraph sm initSM 562 = reconstructWithDim 0 pm.numRanks 0 [PM 562]
    show denoteGraph sm initSM 562 =
        reconstructWithDim 0 pm.numRanks 0
          ([({ rank := 0, tid := 562 } : Piece)].map (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil, reconstructWithDim_singleton]
    rw [sm_eval_562, pm_eval_562, h712_dimN]
    -- Use bridge: fw_sum (allGather...) = allReduce [fw_sum ...]
    have hnr : pm.numRanks = 4 := rfl
    rw [hnr, hbridge]

end TrainVerify.Denote.GeneratedPatterns
