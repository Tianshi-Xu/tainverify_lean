/- Auto-generated pattern proof file.
   Pattern: 126
   Hash: ef160eacb7218322
   Goals: 256

   Structural argument:
     SM has a single `BW_sum` node `ins := [896, 712], outs := [895]`.
     PM has four `BW_sum` nodes (one per rank) `ins := [896, 337x], outs := [33yy]`.
     The reconstruction is `allGatherPrimDimN 2 4 0 [pm3387, pm3390, pm3393, pm3396]`.

     `bw_sum gradOut x` is shape-preserving and value-constant (= `valAt gradOut 0`),
     so the proof reduces to:
       bw_sum (sm 896) (sm 712) = allGatherPrimDimN 2 4 0
         [bw_sum (pm 896) (pm 3373), …, bw_sum (pm 896) (pm 3376)]
     given `sm 712 = allGatherPrimDimN 2 4 0 [pm 3373, …, pm 3376]` (from goal_106
     supplied by `prove_pattern_19`) and `sm 896 = pm 896` (from `initGoal_896`).
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_19

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_126_goalIds : List Nat := [256]
inductive pattern_126_target : Prop → Prop
  | goal_256 : pattern_126_target goal_256_stmt

def pattern_126_stmt : Prop :=
  ∀ {target : Prop}, pattern_126_target target → target

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

/-! ## Node literals (the BW_sum nodes we will rewrite via `applyNode_bw_sum_out`). -/

@[reducible] private def sm_n118 : NodeDecl :=
  { rank := 0, op := "OpName.BW_sum", ins := [896, 712], outs := [895] }

@[reducible] private def pm_n772 : NodeDecl :=
  { rank := 0, op := "OpName.BW_sum", ins := [896, 3373], outs := [3387] }
@[reducible] private def pm_n774 : NodeDecl :=
  { rank := 1, op := "OpName.BW_sum", ins := [896, 3374], outs := [3390] }
@[reducible] private def pm_n776 : NodeDecl :=
  { rank := 2, op := "OpName.BW_sum", ins := [896, 3375], outs := [3393] }
@[reducible] private def pm_n778 : NodeDecl :=
  { rank := 3, op := "OpName.BW_sum", ins := [896, 3376], outs := [3396] }

/-! ## Generic BW_sum step: traces `denoteGraph g initStore outTid` to
    `bw_sum (denoteGraph g initStore gTid) (denoteGraph g initStore xTid)` whenever
    the unique writer of `outTid` is a `BW_sum` node at index `K` and neither
    `gTid` nor `xTid` is written by `g.nodes.drop K`. -/

private theorem denote_bw_sum_step (g : GraphDecl) (initStore : Store)
    (K : Nat) (gTid xTid outTid : Tid) (rk : Nat)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.BW_sum",
                      ins := [gTid, xTid], outs := [outTid] })
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (hsuf_out : ∀ n ∈ g.nodes.drop (K+1), outTid ∉ n.outs)
    (hsuf_g : ∀ n ∈ g.nodes.drop K, gTid ∉ n.outs)
    (hsuf_x : ∀ n ∈ g.nodes.drop K, xTid ∉ n.outs) :
    denoteGraph g initStore outTid =
      bw_sum (denoteGraph g initStore gTid) (denoteGraph g initStore xTid) := by
  -- Drop nodes beyond index K (none write outTid).
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
  rw [hnode, applyNode_bw_sum_out g _ rk gTid xTid outTid]
  -- Replace stores at gTid and xTid by the full denoteGraph.
  have hg : (denoteGraph { g with nodes := g.nodes.take K } initStore) gTid =
      denoteGraph g initStore gTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore gTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_g).symm
  have hx : (denoteGraph { g with nodes := g.nodes.take K } initStore) xTid =
      denoteGraph g initStore xTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initStore xTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_x).symm
  rw [hg, hx]

/-! ## Reducing initial tids: `denoteGraph g initStore tid = initStore tid` when
    `tid` is never written by any node in `g`. -/

private theorem denote_init_tid (g : GraphDecl) (initStore : Store) (tid : Tid)
    (hno : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraph g initStore tid = initStore tid := by
  have h := denoteGraph_tid_eq_of_suffix_no_writes g initStore tid
    [] g.nodes (by simp) hno
  rw [h]
  -- `{ g with nodes := [] }` evaluates to `initStore` on every tid.
  have heq : ({ g with nodes := [] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := [] } := by cases g; rfl
  rw [heq, denoteGraph_nodes_nil]

/-! ## SM-side and PM-side evaluations. -/

private theorem sm_eval_895 (initSM : Store) :
    denoteGraph sm initSM 895 =
      bw_sum (denoteGraph sm initSM 896) (denoteGraph sm initSM 712) := by
  apply denote_bw_sum_step sm initSM 118 896 712 895 0 sm_n118 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3387 (initPM : Store) :
    denoteGraph pm initPM 3387 =
      bw_sum (denoteGraph pm initPM 896) (denoteGraph pm initPM 3373) := by
  apply denote_bw_sum_step pm initPM 772 896 3373 3387 0 pm_n772 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3390 (initPM : Store) :
    denoteGraph pm initPM 3390 =
      bw_sum (denoteGraph pm initPM 896) (denoteGraph pm initPM 3374) := by
  apply denote_bw_sum_step pm initPM 774 896 3374 3390 1 pm_n774 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3393 (initPM : Store) :
    denoteGraph pm initPM 3393 =
      bw_sum (denoteGraph pm initPM 896) (denoteGraph pm initPM 3375) := by
  apply denote_bw_sum_step pm initPM 776 896 3375 3393 2 pm_n776 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3396 (initPM : Store) :
    denoteGraph pm initPM 3396 =
      bw_sum (denoteGraph pm initPM 896) (denoteGraph pm initPM 3376) := by
  apply denote_bw_sum_step pm initPM 778 896 3376 3396 3 pm_n778 rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_896 (initSM : Store) :
    denoteGraph sm initSM 896 = initSM 896 :=
  denote_init_tid sm initSM 896 (by decide)

private theorem pm_eval_896 (initPM : Store) :
    denoteGraph pm initPM 896 = initPM 896 :=
  denote_init_tid pm initPM 896 (by decide)

/-! ## Bridge lemma: `bw_sum` distributes over `allGatherPrimDimN 2 4 0` for the
    specific shard shape `[1, 8, 32]`.

    Both sides are tensors of shape `[1, 8, 128]` whose every entry equals
    `valAt g 0`, so we prove this by `Tensor.ext`.

    Key facts:
      - `bw_sum gradOut x` at any in-bounds index = `valAt gradOut 0` (lemma
        `bw_sum_valAt_of_lt`).
      - `allGatherPrimDimN 2 4 0 ys` at any in-bounds index looks up `valAt
        yⱼ k` for some shard `yⱼ ∈ ys` and some in-bounds `k`; when each
        `yⱼ = bw_sum g xⱼ`, this is again `valAt g 0`. -/

private theorem bw_sum_allGather_bridge (g x0 x1 x2 x3 : Tensor)
    (h0 : x0.shape = [1, 8, 32])
    (h1 : x1.shape = [1, 8, 32])
    (h2 : x2.shape = [1, 8, 32])
    (h3 : x3.shape = [1, 8, 32]) :
    bw_sum g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]) =
      allGatherPrimDimN 2 4 0
        [bw_sum g x0, bw_sum g x1, bw_sum g x2, bw_sum g x3] := by
  -- Head-shape facts.
  have hhead_x : ((([x0, x1, x2, x3] : List Tensor)).head?.map (fun t => t.shape)).getD [] =
      [1, 8, 32] := by simp [h0]
  have hgather_sh : (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]).shape = [1, 8, 128] := by
    have := allGatherPrimDimN_shape 2 4 [x0, x1, x2, x3] [1, 8, 32] hhead_x
    simpa using this
  have hLHS_sh : (bw_sum g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])).shape = [1, 8, 128] := by
    rw [bw_sum_shape, hgather_sh]
  have hbws_sh0 : (bw_sum g x0).shape = [1, 8, 32] := by rw [bw_sum_shape, h0]
  have hbws_sh1 : (bw_sum g x1).shape = [1, 8, 32] := by rw [bw_sum_shape, h1]
  have hbws_sh2 : (bw_sum g x2).shape = [1, 8, 32] := by rw [bw_sum_shape, h2]
  have hbws_sh3 : (bw_sum g x3).shape = [1, 8, 32] := by rw [bw_sum_shape, h3]
  have hhead_bw : ((([bw_sum g x0, bw_sum g x1, bw_sum g x2, bw_sum g x3]
          : List Tensor)).head?.map (fun t => t.shape)).getD [] = [1, 8, 32] := by
    show (some (bw_sum g x0).shape).getD [] = [1, 8, 32]
    rw [Option.getD_some, hbws_sh0]
  have hRHS_sh : (allGatherPrimDimN 2 4 0
        [bw_sum g x0, bw_sum g x1, bw_sum g x2, bw_sum g x3]).shape = [1, 8, 128] := by
    have := allGatherPrimDimN_shape 2 4
        [bw_sum g x0, bw_sum g x1, bw_sum g x2, bw_sum g x3] [1, 8, 32] hhead_bw
    simpa using this
  -- Reduce to pointwise equality via `Tensor.ext`.
  apply Tensor.ext (by rw [hLHS_sh, hRHS_sh])
  intro idx hidx
  have hidx_lt : idx < 1024 := by
    have hh : idx < prodShape (bw_sum g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])).shape := hidx
    rw [hLHS_sh] at hh
    simpa [prodShape] using hh
  -- LHS value.
  have hLHS_val : valAt (bw_sum g (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3])) idx =
      valAt g 0 := by
    apply bw_sum_valAt_of_lt
    rw [hgather_sh]; simpa [prodShape] using hidx_lt
  rw [hLHS_val]
  -- For the RHS, generalize over the chosen shard. We show that the inner `valAt`
  -- of every shard equals `valAt g 0`. This is independent of any indexing details.
  -- Strategy: show the entire RHS tensor equals a constant-valued tensor, then
  -- read off the value at idx.
  -- Step 1: show every shard equals `bw_sum g x0`.
  have heq01 : bw_sum g x0 = bw_sum g x1 := by
    apply Tensor.ext (by rw [hbws_sh0, hbws_sh1])
    intro i hi
    have hi_lt : i < 256 := by simpa [h0, prodShape] using hi
    rw [bw_sum_valAt_of_lt g x0 i (by rw [h0]; simpa [prodShape] using hi_lt),
        bw_sum_valAt_of_lt g x1 i (by rw [h1]; simpa [prodShape] using hi_lt)]
  have heq02 : bw_sum g x0 = bw_sum g x2 := by
    apply Tensor.ext (by rw [hbws_sh0, hbws_sh2])
    intro i hi
    have hi_lt : i < 256 := by simpa [h0, prodShape] using hi
    rw [bw_sum_valAt_of_lt g x0 i (by rw [h0]; simpa [prodShape] using hi_lt),
        bw_sum_valAt_of_lt g x2 i (by rw [h2]; simpa [prodShape] using hi_lt)]
  have heq03 : bw_sum g x0 = bw_sum g x3 := by
    apply Tensor.ext (by rw [hbws_sh0, hbws_sh3])
    intro i hi
    have hi_lt : i < 256 := by simpa [h0, prodShape] using hi
    rw [bw_sum_valAt_of_lt g x0 i (by rw [h0]; simpa [prodShape] using hi_lt),
        bw_sum_valAt_of_lt g x3 i (by rw [h3]; simpa [prodShape] using hi_lt)]
  -- Now LHS list reduces to all-x0; RHS expression evaluates piecewise.
  -- Use the template approach (cf. allGather_dim1_4_1_1_8_8_valAt at Denote.lean:5314).
  have hhead_x0 : (([bw_sum g x0, bw_sum g x0, bw_sum g x0, bw_sum g x0] : List Tensor).head?.map
      (·.shape)).getD [] = [1, 8, 32] := by
    show (some (bw_sum g x0).shape).getD [] = [1, 8, 32]
    rw [Option.getD_some, hbws_sh0]
  have hRHS_sh' : (allGatherPrimDimN 2 4 0
        [bw_sum g x0, bw_sum g x0, bw_sum g x0, bw_sum g x0]).shape = [1, 8, 128] := by
    have := allGatherPrimDimN_shape 2 4
        [bw_sum g x0, bw_sum g x0, bw_sum g x0, bw_sum g x0] [1, 8, 32] hhead_x0
    simpa using this
  -- Substitute every shard by `bw_sum g x0` so we have a uniform list.
  rw [show ([bw_sum g x0, bw_sum g x1, bw_sum g x2, bw_sum g x3] : List Tensor) =
      [bw_sum g x0, bw_sum g x0, bw_sum g x0, bw_sum g x0] from by
    rw [← heq01, ← heq02, ← heq03]]
  have hidx_RHS : idx < prodShape (allGatherPrimDimN 2 4 0
      [bw_sum g x0, bw_sum g x0, bw_sum g x0, bw_sum g x0]).shape := by
    rw [hRHS_sh']; simpa [prodShape] using hidx_lt
  rw [valAt_of_lt _ _ hidx_RHS]
  -- Now reduce by unfolding allGatherPrimDimN directly.
  unfold allGatherPrimDimN Tensor.mkShape
  -- After unfold the goal is a `.val ⟨idx, _⟩` expression. We compute symbolically.
  simp only [hhead_x0]
  -- The let-bindings now contain concrete numeric expressions.
  -- We extract them as constants and case-analyze on r.
  have hpost : ([1, 8, 32] : List Nat).drop (2 + 1) = [] := by decide
  have hgD : ([1, 8, 32] : List Nat).getD 2 0 = 32 := by decide
  have hset : ([1, 8, 32] : List Nat).set 2 (32 * 4) = [1, 8, 128] := by decide
  simp only [hpost, hgD, hset, List.foldl, Nat.mul_one]
  -- After this, the if-then-else for `postStride = 0` should resolve to the `else` branch.
  -- Discharge `postStride ≠ 0` etc.
  simp only [show (1 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (32 * 4 : Nat) ≠ 0 by decide, show (32 * 4 * 1 : Nat) ≠ 0 by decide,
    ite_false]
  -- Simplify Fin (prodShape [1,8,128]) = Fin 1024 won't auto-rewrite, but we don't care
  -- because we only manipulate the `.val` component which equals `idx`.
  -- Now the goal contains: piece selection from a 4-element list based on r = jFull / 32.
  -- Compute r-bound and the inner index, then case-analyse on r ∈ {0,1,2,3}.
  have hfds : (32 * 4 * 1 : Nat) = 128 := by decide
  rw [hfds]
  -- Goal: ... idx / 128, idx % 128 ... `Nat.div_one`/`Nat.mod_one` for postStride=1.
  simp only [Nat.div_one, Nat.mod_one, Nat.mul_zero, Nat.add_zero]
  -- Now goal: valAt (([bw0,bw0,bw0,bw0]).getD (idx % 128 / 32) (zeroTensor [1,8,128]))
  --             (idx / 128 * 32 + idx % 128 % 32) = valAt g 0
  set r : Nat := idx % 128 / 32 with hr_def
  have hr_lt : r < 4 := by
    have : idx % 128 < 128 := Nat.mod_lt _ (by decide)
    have : idx % 128 / 32 < 128 / 32 := Nat.div_lt_div_of_lt_of_dvd (by decide) this
    simpa [hr_def] using this
  have hpre_lt : idx / 128 < 8 := by omega
  have hjLocal_lt : idx % 128 % 32 < 32 := Nat.mod_lt _ (by decide)
  have hinner_lt : idx / 128 * 32 + idx % 128 % 32 < 256 := by
    have hp32 : idx / 128 * 32 ≤ 7 * 32 := Nat.mul_le_mul_right 32 (by omega)
    omega
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with hr | hr | hr | hr <;>
  · rw [hr]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact (bw_sum_valAt_of_lt g x0 _
      (by rw [h0]; simpa [prodShape] using hinner_lt)).symm

/-! ## Main theorem. -/

theorem prove_pattern_126 : pattern_126_stmt := by
  intro target h
  cases h
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- Obtain goal_106 (lineage of tid 712) via Pattern_19.
  have hGoal106 := prove_pattern_19 (target := goal_106_stmt) pattern_19_target.goal_106
  have h106 := hGoal106 initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h712_sh, hpm_shapes_106, h712_rec⟩ := h106
  simp only [goal_106, List.map_cons, List.map_nil] at hpm_shapes_106 h712_rec
  -- Extract per-shard shapes for 3373..3376.
  have h3373_sh : (denoteGraph pm initPM 3373).shape = [1, 8, 32] := by
    have := hpm_shapes_106; simp only [List.cons.injEq] at this; exact this.1
  have h3374_sh : (denoteGraph pm initPM 3374).shape = [1, 8, 32] := by
    have := hpm_shapes_106; simp only [List.cons.injEq] at this; exact this.2.1
  have h3375_sh : (denoteGraph pm initPM 3375).shape = [1, 8, 32] := by
    have := hpm_shapes_106; simp only [List.cons.injEq] at this; exact this.2.2.1
  have h3376_sh : (denoteGraph pm initPM 3376).shape = [1, 8, 32] := by
    have := hpm_shapes_106; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  -- Promote reconstruction to `allGatherPrimDimN` (head shape ≠ [1]).
  have h712_dimN : denoteGraph sm initSM 712 = allGatherPrimDimN 2 pm.numRanks 0
      [ denoteGraph pm initPM 3373, denoteGraph pm initPM 3374,
        denoteGraph pm initPM 3375, denoteGraph pm initPM 3376 ] := by
    rw [h712_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [h3373_sh]; intro hc; cases hc
  -- Equality of init stores at 896 via initGoal_896.
  have hInit896 : initSM 896 = initPM 896 := by
    have h896 := hInitGoals initGoal_896 (by simp [initGoals])
    -- h896 : InitGoalHolds 4 initGoal_896 initSM initPM, with tps = [{rk=0,tid=896}]
    obtain ⟨_, _, h896_rec⟩ := h896
    simp only [initGoal_896, List.map_cons, List.map_nil,
               reconstructWithDim_singleton] at h896_rec
    exact h896_rec
  -- Equality at the graph level.
  have hsm896_eq_pm896 : denoteGraph sm initSM 896 = denoteGraph pm initPM 896 := by
    rw [sm_eval_896, pm_eval_896, hInit896]
  -- Per-shard PM evaluations.
  have hP0 := pm_eval_3387 initPM
  have hP1 := pm_eval_3390 initPM
  have hP2 := pm_eval_3393 initPM
  have hP3 := pm_eval_3396 initPM
  -- SM evaluation.
  have hS := sm_eval_895 initSM
  -- Final shape facts for the conjuncts.
  -- Reduce the `goal_106.ts`/`goal_106.tsShape` from prereq h712_sh.
  have h712_sh' : (denoteGraph sm initSM 712).shape = [1, 8, 128] := by
    have := h712_sh; simp only [goal_106] at this; exact this
  have hLHS_sh : (denoteGraph sm initSM 895).shape = [1, 8, 128] := by
    rw [hS, bw_sum_shape, h712_sh']
  have hP0_sh : (denoteGraph pm initPM 3387).shape = [1, 8, 32] := by
    rw [hP0, bw_sum_shape, h3373_sh]
  have hP1_sh : (denoteGraph pm initPM 3390).shape = [1, 8, 32] := by
    rw [hP1, bw_sum_shape, h3374_sh]
  have hP2_sh : (denoteGraph pm initPM 3393).shape = [1, 8, 32] := by
    rw [hP2, bw_sum_shape, h3375_sh]
  have hP3_sh : (denoteGraph pm initPM 3396).shape = [1, 8, 32] := by
    rw [hP3, bw_sum_shape, h3376_sh]
  -- Reconstruction equation: LHS = allGatherPrimDimN 2 4 0 [pm3387, pm3390, pm3393, pm3396].
  have hnr : pm.numRanks = 4 := rfl
  have hreco : denoteGraph sm initSM 895 = allGatherPrimDimN 2 4 0
      [ denoteGraph pm initPM 3387, denoteGraph pm initPM 3390,
        denoteGraph pm initPM 3393, denoteGraph pm initPM 3396 ] := by
    rw [hS, h712_dimN, hsm896_eq_pm896, hnr]
    rw [hP0, hP1, hP2, hP3]
    exact bw_sum_allGather_bridge (denoteGraph pm initPM 896)
      (denoteGraph pm initPM 3373) (denoteGraph pm initPM 3374)
      (denoteGraph pm initPM 3375) (denoteGraph pm initPM 3376)
      h3373_sh h3374_sh h3375_sh h3376_sh
  refine ⟨?_, ?_, ?_⟩
  · -- (denoteGraph sm initSM 895).shape = [1, 8, 128]
    show (denoteGraph sm initSM 895).shape = [1, 8, 128]
    exact hLHS_sh
  · -- List of pm shard shapes = [[1,8,32], [1,8,32], [1,8,32], [1,8,32]]
    show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 3387 } : Piece),
          ({ rank := 1, tid := 3390 } : Piece),
          ({ rank := 2, tid := 3393 } : Piece),
          ({ rank := 3, tid := 3396 } : Piece)].map (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 8, 32], [1, 8, 32], [1, 8, 32], [1, 8, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · -- Reconstruction equation.
    show denoteGraph sm initSM 895 =
        reconstructWithDim 2 pm.numRanks 0
          ([({ rank := 0, tid := 3387 } : Piece),
            ({ rank := 1, tid := 3390 } : Piece),
            ({ rank := 2, tid := 3393 } : Piece),
            ({ rank := 3, tid := 3396 } : Piece)].map (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _ (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco

end TrainVerify.Denote.GeneratedPatterns
