/- Intermediate reconstruction lemmas for the YOCO-MoE cut→full bridges.

   Goal: discharge the ~1151-element `goal_N_prereqs` requirement by proving
   each `intermediateGoal_XXXX` holds on the COMPUTED stores
   `denoteGraph sm initSM` / `denoteGraph pm initPM`, packaged as per-op
   sub-lemmas joined by `InitGoalsHold_append`.

   See PROGRESS.md / HANDOFF.md at repo root for coverage status.

   Strategy (validated): each goal's value obligation reduces the full-graph
   value at its `ts` (via `sm_val`/`pm_val` node reductions + the op's
   `applyNode_*_out` lemma) to the op applied to its input tensors, then uses
   the already-established reconstruction of those inputs (topological
   threading) plus init-weight boundary equalities.
-/
import denote.yoco_goals.BridgeKit
import denote.yoco_goals.Goal_5_Intermediate
import denote.DenoteMoE
import denote.yoco_goals.Pattern_1  -- fw_rms_norm_allGather0_commute_2 (worker #7)
import denote.GraphSlicing          -- foldl_applyNodeRingAttn_at_not_written (worker #9, ring-attn transfer)
import denote.yoco_goals.Pattern_3  -- applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair (worker #9, Priority 3)
import denote.yoco_goals.RingAttnGears -- shared ring-attn reshape/node reduction gears (worker #12)

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-! ### Ring-attention transfer gears (worker #9)

Per `ATTENTION_ANALYSIS.md`, the deliverable is restated over
`denoteGraph_ringAttn` — the value-faithful denotation for the cross-rank
`FW_attn_sliding_window` / `FW_attn_zigzag` ops. The key observation: for any
tid whose node *prefix* contains no ring-attention op, the ring denotation
agrees with the plain one (`denoteGraph_ringAttn_eq_at`), so every worker
#1–#7 gear transfers via `InitGoalHolds_transfer` with a thin per-tid rewrite.
The first ring-attn node is `sm.nodes[9]` / `pm.nodes[49]` (verified below by
`native_decide`), so every layer-0 replicated-prefix tid (all written by
`sm.nodes[≤8]` / `pm.nodes[≤42]`) is ring/plain-agnostic. -/

/-- List-level: folding `applyNodeRingAttn` over a ring-op-free node list
    coincides with folding plain `applyNode`. Standalone extraction of the
    `suffices` core of `denoteGraph_ringAttn_eq_denoteGraph_of_no_ring_attn`. -/
theorem foldl_ringAttn_eq_foldl_of_no_ring (g : GraphDecl)
    (nodes : List NodeDecl) (s : Store)
    (hno : ∀ n ∈ nodes,
      n.op ≠ "OpName.FW_attn_zigzag" ∧ n.op ≠ "OpName.FW_attn_sliding_window") :
    nodes.foldl (applyNodeRingAttn g) s = nodes.foldl (applyNode g) s := by
  induction nodes generalizing s with
  | nil => rfl
  | cons hd tl ih =>
    have hhd := hno hd (by simp)
    have htl : ∀ n ∈ tl,
        n.op ≠ "OpName.FW_attn_zigzag" ∧ n.op ≠ "OpName.FW_attn_sliding_window" :=
      fun n hn => hno n (List.mem_cons_of_mem _ hn)
    simp only [List.foldl_cons]
    rw [applyNodeRingAttn_eq_applyNode_of_not_ring g s hd hhd.1 hhd.2]
    exact ih (applyNode g s hd) htl

/-- Ring-fold prefix reduction (graph-generic; local re-derivation of Pattern_3's
    `foldl_prefix_eq_full_ringAttn`): the ring value at `tid` equals its value
    after the prefix `take k`, when the suffix `drop k` never writes `tid`. -/
theorem foldl_prefix_eq_full_ringAttn' (g : GraphDecl) (nodes : List NodeDecl)
    (s : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ nodes.drop k, n.outs ≠ [])
    (h : ∀ n ∈ nodes.drop k, tid ∉ n.outs) :
    nodes.foldl (applyNodeRingAttn g) s tid =
      (nodes.take k).foldl (applyNodeRingAttn g) s tid := by
  conv_lhs => rw [← List.take_append_drop k nodes, List.foldl_append]
  exact foldl_applyNodeRingAttn_at_not_written g _ _ tid hnil h

/-- **Per-tid transfer**: if the node prefix `take k` contains no ring-attn op
    and the suffix `drop k` never writes `tid`, the ring denotation agrees with
    the plain denotation at `tid`. -/
theorem denoteGraph_ringAttn_eq_at (g : GraphDecl) (init : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hsuf : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs)
    (hnoring : ∀ n ∈ g.nodes.take k,
      n.op ≠ "OpName.FW_attn_zigzag" ∧ n.op ≠ "OpName.FW_attn_sliding_window") :
    denoteGraph_ringAttn g init tid = denoteGraph g init tid := by
  rw [denoteGraph_ringAttn,
      foldl_prefix_eq_full_ringAttn' g g.nodes init tid k hnil hsuf,
      foldl_ringAttn_eq_foldl_of_no_ring g (g.nodes.take k) init hnoring,
      denoteGraph_tid_eq_of_suffix_no_writes g init tid (g.nodes.take k)
        (g.nodes.drop k) (List.take_append_drop k g.nodes).symm hsuf]
  simp only [denoteGraph]
  rw [applyNode_congr_numRanks { g with nodes := g.nodes.take k } g rfl]

/-- Transfer an `InitGoalHolds` obligation between two denotations that agree at
    the goal's `ts` and every `tp.tid`. -/
theorem InitGoalHolds_transfer (numParts : Nat) (gl : LineageGoal)
    (smS smS' pmS pmS' : Store)
    (hts : smS' gl.ts = smS gl.ts)
    (htps : ∀ p ∈ gl.tps, pmS' p.tid = pmS p.tid)
    (h : InitGoalHolds numParts gl smS pmS) :
    InitGoalHolds numParts gl smS' pmS' := by
  dsimp only [InitGoalHolds] at h ⊢
  rw [hts, List.map_congr_left (fun p hp => htps p hp)]
  exact h

/-- Specialization to the global SM graph: the first ring-attn node is
    `sm.nodes[9]`, so any tid unwritten by `sm.nodes.drop 9` is ring/plain-agnostic. -/
theorem sm_ring_eq (initSM : Store) (T : Tid)
    (hsuf : ∀ n ∈ sm.nodes.drop 9, T ∉ n.outs) :
    denoteGraph_ringAttn sm initSM T = denoteGraph sm initSM T :=
  denoteGraph_ringAttn_eq_at sm initSM T 9 (by native_decide) hsuf (by native_decide)

/-- Specialization to the global PM graph: the first ring-attn node is
    `pm.nodes[49]`, so any tid unwritten by `pm.nodes.drop 49` is ring/plain-agnostic. -/
theorem pm_ring_eq (initPM : Store) (T : Tid)
    (hsuf : ∀ n ∈ pm.nodes.drop 49, T ∉ n.outs) :
    denoteGraph_ringAttn pm initPM T = denoteGraph pm initPM T :=
  denoteGraph_ringAttn_eq_at pm initPM T 49 (by native_decide) hsuf (by native_decide)

/-- **The transfer gear**: lift any plain-`denoteGraph` `InitGoalHolds` for a
    layer-0 (pre-attention) goal to the ring-attn denotation. The two
    `native_decide` side-goals confirm the goal's `ts`/`tps` are written strictly
    before the first ring-attn node in each graph. -/
theorem recon_ringAttn_of_plain (gl : LineageGoal)
    (initSM initPM : Store)
    (hsm : ∀ n ∈ sm.nodes.drop 9, gl.ts ∉ n.outs)
    (hpm : ∀ p ∈ gl.tps, ∀ n ∈ pm.nodes.drop 49, p.tid ∉ n.outs)
    (hplain : InitGoalHolds pm.numRanks gl (denoteGraph sm initSM) (denoteGraph pm initPM)) :
    InitGoalHolds pm.numRanks gl (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  InitGoalHolds_transfer pm.numRanks gl (denoteGraph sm initSM) (denoteGraph_ringAttn sm initSM)
    (denoteGraph pm initPM) (denoteGraph_ringAttn pm initPM)
    (sm_ring_eq initSM gl.ts hsm)
    (fun p hp => pm_ring_eq initPM p.tid (hpm p hp))
    hplain

/-! ### Reusable gears -/

/-- Init-weight boundary equality on computed stores: for a 1-tp non-replicated
    init goal `g` mapping SM tid `W` to PM tid `W`, the computed stores agree at
    `W` (neither graph rewrites init tids, per `initGoals_preserved`). -/
theorem recon_weight (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ initGoals) (W : Tid)
    (htp : g.tps = [{rank := 0, tid := W}]) (hgd : g.gatherDim = 0)
    (hrep : g.replicated = false) (hts : g.ts = W) :
    denoteGraph sm initSM W = denoteGraph pm initPM W := by
  have hpres := initGoals_preserved initSM initPM hInit
  have h := hpres g hg
  unfold InitGoalHolds at h
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated g pm.numRanks _ hrep, htp, hts, hgd] at hval
  simp only [List.map, reconstructWithDim] at hval
  exact hval

/-- Wrap a 1-tp (`ts = tp`, non-replicated) value equality + shape into the
    `InitGoalHolds` obligation used by the bridge. -/
theorem wrap_1tp (initSM initPM : Store) (g : LineageGoal) (T : Tid) (sh : Shape)
    (htp : g.tps = [{rank := 0, tid := T}]) (hgd : g.gatherDim = 0)
    (hrep : g.replicated = false) (hts : g.ts = T) (htsShape : g.tsShape = sh)
    (htpShapes : g.tpShapes = [sh])
    (hval : denoteGraph sm initSM T = denoteGraph pm initPM T)
    (hshape : (denoteGraph sm initSM T).shape = sh) :
    InitGoalHolds pm.numRanks g (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hts, htsShape]; exact hshape
  · rw [htp, htpShapes]; simp only [List.map, List.cons.injEq, and_true]
    rw [← hval]; exact hshape
  · rw [reconstructForGoal_of_not_replicated g pm.numRanks _ hrep, htp, hts, hgd]
    simp only [List.map, reconstructWithDim]
    exact hval

/-- Generic `FW_multiref` (params `[3]`) first-output reduction. -/
theorem applyNode_fw_multiref3_first_out' (g : GraphDecl) (s : Store) (rank : Nat)
    (xTid t1 t2 t3 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := [t1, t2, t3], params := [3] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3].zip (List.replicate 3 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?]

/-- Generic `FW_multiref` (params `[3]`) second-output reduction. -/
theorem applyNode_fw_multiref3_second_out' (g : GraphDecl) (s : Store) (rank : Nat)
    (xTid t1 t2 t3 : Tid) (h12 : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := [t1, t2, t3], params := [3] } t2 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3].zip (List.replicate 3 (s xTid))) t2 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, show ¬ (t1 = t2) from h12]

/-- Generic `FW_multiref` (params `[3]`) third-output reduction. -/
theorem applyNode_fw_multiref3_third_out' (g : GraphDecl) (s : Store) (rank : Nat)
    (xTid t1 t2 t3 : Tid) (h13 : t1 ≠ t3) (h23 : t2 ≠ t3) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := [t1, t2, t3], params := [3] } t3 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2, t3].zip (List.replicate 3 (s xTid))) t3 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?,
        show ¬ (t1 = t3) from h13, show ¬ (t2 = t3) from h23]

/-- Init-weight shape on computed stores. -/
theorem shape_weight (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (g : LineageGoal) (hg : g ∈ initGoals) (W : Tid) (sh : Shape)
    (htsShape : g.tsShape = sh) (hts : g.ts = W) :
    (denoteGraph sm initSM W).shape = sh := by
  have hpres := initGoals_preserved initSM initPM hInit
  have h := hpres g hg
  unfold InitGoalHolds at h
  have := h.1; rw [hts, htsShape] at this; exact this

/-! ### Layer-0 replicated prefix (threads from goal_5 = tid 4680) -/

/-- goal_5 value equality on computed stores: `sm 4680 = pm 4680`. -/
theorem veq_4680 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph sm initSM 4680 = denoteGraph pm initPM 4680 := by
  have h := goal_5_intermediate initSM initPM hSM hPM hInit
  unfold InitGoalHolds at h
  have hval := h.2.2
  simp only [goal_5, List.map, reconstructForGoal, reconstructWithDim_singleton] at hval
  exact hval

/-- goal_5 shape: `(sm 4680).shape = [4096,1024]`. -/
theorem shape_4680 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    (denoteGraph sm initSM 4680).shape = [4096, 1024] := by
  have h := goal_5_intermediate initSM initPM hSM hPM hInit
  unfold InitGoalHolds at h
  have := h.1; simpa [goal_5] using this

/-- `sm 4681 = pm 4681` (FW_float, value-identity, from `veq_4680`). -/
theorem veq_4681 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph sm initSM 4681 = denoteGraph pm initPM 4681 := by
  have hsm : denoteGraph sm initSM 4681 = denoteGraph sm initSM 4680 := by
    rw [sm_val initSM 1 4681 (by native_decide) (by native_decide)]
    rw [show sm.nodes[1]'(by native_decide)
        = { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] }
        from by native_decide]
    rw [applyNode_fw_float_out, sm_prefix_eq initSM 1 4680 (by native_decide)]
  have hpm : denoteGraph pm initPM 4681 = denoteGraph pm initPM 4680 := by
    rw [pm_val initPM 28 4681 (by native_decide) (by native_decide)]
    rw [show pm.nodes[28]'(by native_decide)
        = { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] }
        from by native_decide]
    rw [applyNode_fw_float_out, pm_prefix_eq initPM 28 4680 (by native_decide)]
  rw [hsm, hpm]; exact veq_4680 initSM initPM hSM hPM hInit

theorem shape_4681 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    (denoteGraph sm initSM 4681).shape = [4096, 1024] := by
  have hsm : denoteGraph sm initSM 4681 = denoteGraph sm initSM 4680 := by
    rw [sm_val initSM 1 4681 (by native_decide) (by native_decide)]
    rw [show sm.nodes[1]'(by native_decide)
        = { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] }
        from by native_decide]
    rw [applyNode_fw_float_out, sm_prefix_eq initSM 1 4680 (by native_decide)]
  rw [hsm]; exact shape_4680 initSM initPM hSM hPM hInit

/-- `intermediateGoal_4681` (FW_float). -/
theorem recon_intermediateGoal_4681 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4681
      (denoteGraph sm initSM) (denoteGraph pm initPM) :=
  wrap_1tp initSM initPM intermediateGoal_4681 4681 [4096, 1024]
    rfl rfl rfl rfl rfl rfl
    (veq_4681 initSM initPM hSM hPM hInit)
    (shape_4681 initSM initPM hSM hPM hInit)

/-- `sm 4683 = pm 4683` (FW_rms_norm over multiref-copy of 4681 + weight 4682). -/
theorem veq_4683 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph sm initSM 4683 = denoteGraph pm initPM 4683 := by
  -- SM: 4683 = rms_norm(7383, 4682), 7383 = mref-copy of 4681
  have hsm7383 : denoteGraph sm initSM 7383 = denoteGraph sm initSM 4681 := by
    rw [sm_val initSM 2 7383 (by native_decide) (by native_decide)]
    rw [show sm.nodes[2]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }
        from by native_decide]
    rw [applyNode_fw_multiref2_first_out, sm_prefix_eq initSM 2 4681 (by native_decide)]
  have hsm : denoteGraph sm initSM 4683
      = fw_rms_norm (denoteGraph sm initSM 4681) (denoteGraph sm initSM 4682) := by
    rw [sm_val initSM 3 4683 (by native_decide) (by native_decide)]
    rw [show sm.nodes[3]'(by native_decide)
        = { rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683] }
        from by native_decide]
    rw [applyNode_fw_rms_norm_out_1p,
        sm_prefix_eq initSM 3 7383 (by native_decide),
        sm_prefix_eq initSM 3 4682 (by native_decide), hsm7383]
  -- PM: last writer of 4683 is node 32 (rank 1), ins=[14611,4682], 14611=mref-copy of 4681
  have hpm14611 : denoteGraph pm initPM 14611 = denoteGraph pm initPM 4681 := by
    rw [pm_val initPM 30 14611 (by native_decide) (by native_decide)]
    rw [show pm.nodes[30]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }
        from by native_decide]
    rw [applyNode_fw_multiref2_first_out, pm_prefix_eq initPM 30 4681 (by native_decide)]
  have hpm : denoteGraph pm initPM 4683
      = fw_rms_norm (denoteGraph pm initPM 4681) (denoteGraph pm initPM 4682) := by
    rw [pm_val initPM 32 4683 (by native_decide) (by native_decide)]
    rw [show pm.nodes[32]'(by native_decide)
        = { rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] }
        from by native_decide]
    rw [applyNode_fw_rms_norm_out_1p,
        pm_prefix_eq initPM 32 14611 (by native_decide),
        pm_prefix_eq initPM 32 4682 (by native_decide), hpm14611]
  rw [hsm, hpm, veq_4681 initSM initPM hSM hPM hInit,
      recon_weight initSM initPM hInit initGoal_4682 (by native_decide) 4682 rfl rfl rfl rfl]

theorem shape_4683 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    (denoteGraph sm initSM 4683).shape = [4096, 1024] := by
  have hsm7383 : denoteGraph sm initSM 7383 = denoteGraph sm initSM 4681 := by
    rw [sm_val initSM 2 7383 (by native_decide) (by native_decide)]
    rw [show sm.nodes[2]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }
        from by native_decide]
    rw [applyNode_fw_multiref2_first_out, sm_prefix_eq initSM 2 4681 (by native_decide)]
  have hsm : denoteGraph sm initSM 4683
      = fw_rms_norm (denoteGraph sm initSM 4681) (denoteGraph sm initSM 4682) := by
    rw [sm_val initSM 3 4683 (by native_decide) (by native_decide)]
    rw [show sm.nodes[3]'(by native_decide)
        = { rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683] }
        from by native_decide]
    rw [applyNode_fw_rms_norm_out_1p,
        sm_prefix_eq initSM 3 7383 (by native_decide),
        sm_prefix_eq initSM 3 4682 (by native_decide), hsm7383]
  rw [hsm, fw_rms_norm_shape, shape_4681 initSM initPM hSM hPM hInit]

/-- `intermediateGoal_4683` (FW_rms_norm). -/
theorem recon_intermediateGoal_4683 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4683
      (denoteGraph sm initSM) (denoteGraph pm initPM) :=
  wrap_1tp initSM initPM intermediateGoal_4683 4683 [4096, 1024]
    rfl rfl rfl rfl rfl rfl
    (veq_4683 initSM initPM hSM hPM hInit)
    (shape_4683 initSM initPM hSM hPM hInit)

/-! ### Per-head projections (Q/K/V) — FW_per_head_mix_precision_linear -/

/-- `sm out = pm out` for a per-head linear whose input is a multiref-copy of 4683
    and whose weight `W` is an init goal. `smMrefEq`/`pmMrefEq` reduce the SM/PM
    multiref-copy tids to 4683 (they carry the multiref-position specifics). -/
theorem veq_perhead (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (out W smSrc pmSrc : Tid) (sk pk : Nat)
    (hsk : sk < sm.nodes.length) (hpk : pk < pm.nodes.length)
    (hsm_drop : ∀ n ∈ sm.nodes.drop (sk+1), out ∉ n.outs)
    (hpm_drop : ∀ n ∈ pm.nodes.drop (pk+1), out ∉ n.outs)
    (hsm_node : (sm.nodes[sk]'hsk) = { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [smSrc, W], outs := [out] })
    (hpm_node : (pm.nodes[pk]'hpk) = { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [pmSrc, W], outs := [out] })
    (hsm_src_drop : ∀ n ∈ sm.nodes.drop sk, smSrc ∉ n.outs)
    (hsm_w_drop : ∀ n ∈ sm.nodes.drop sk, W ∉ n.outs)
    (hpm_src_drop : ∀ n ∈ pm.nodes.drop pk, pmSrc ∉ n.outs)
    (hpm_w_drop : ∀ n ∈ pm.nodes.drop pk, W ∉ n.outs)
    (hsmMref : denoteGraph sm initSM smSrc = denoteGraph sm initSM 4683)
    (hpmMref : denoteGraph pm initPM pmSrc = denoteGraph pm initPM 4683)
    (gW : LineageGoal) (hgW : gW ∈ initGoals)
    (htpW : gW.tps = [{rank := 0, tid := W}]) (hgdW : gW.gatherDim = 0)
    (hrepW : gW.replicated = false) (htsW : gW.ts = W) :
    denoteGraph sm initSM out = denoteGraph pm initPM out := by
  have hsm : denoteGraph sm initSM out
      = fw_per_head_linear (denoteGraph sm initSM 4683) (denoteGraph sm initSM W) := by
    rw [sm_val initSM sk out hsk hsm_drop, hsm_node, applyNode_fw_per_head_mix_precision_linear_out,
        sm_prefix_eq initSM sk smSrc hsm_src_drop, sm_prefix_eq initSM sk W hsm_w_drop, hsmMref]
  have hpm : denoteGraph pm initPM out
      = fw_per_head_linear (denoteGraph pm initPM 4683) (denoteGraph pm initPM W) := by
    rw [pm_val initPM pk out hpk hpm_drop, hpm_node, applyNode_fw_per_head_mix_precision_linear_out,
        pm_prefix_eq initPM pk pmSrc hpm_src_drop, pm_prefix_eq initPM pk W hpm_w_drop, hpmMref]
  rw [hsm, hpm, veq_4683 initSM initPM hSM hPM hInit,
      recon_weight initSM initPM hInit gW hgW W htpW hgdW hrepW htsW]

theorem recon_intermediateGoal_4685 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4685
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hsmMref : denoteGraph sm initSM 7392 = denoteGraph sm initSM 4683 := by
    rw [sm_val initSM 4 7392 (by native_decide) (by native_decide)]
    rw [show sm.nodes[4]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_first_out', sm_prefix_eq initSM 4 4683 (by native_decide)]
  have hpmMref : denoteGraph pm initPM 14632 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 34 14632 (by native_decide) (by native_decide)]
    rw [show pm.nodes[34]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_first_out', pm_prefix_eq initPM 34 4683 (by native_decide)]
  have hval := veq_perhead initSM initPM hSM hPM hInit 4685 4684 7392 14632 5 38
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hsmMref hpmMref initGoal_4684 (by native_decide) rfl rfl rfl rfl
  have hshape : (denoteGraph sm initSM 4685).shape = [4096, 16, 64] := by
    have hsm : denoteGraph sm initSM 4685
        = fw_per_head_linear (denoteGraph sm initSM 4683) (denoteGraph sm initSM 4684) := by
      rw [sm_val initSM 5 4685 (by native_decide) (by native_decide)]
      rw [show sm.nodes[5]'(by native_decide)
          = { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7392, 4684], outs := [4685] }
          from by native_decide]
      rw [applyNode_fw_per_head_mix_precision_linear_out,
          sm_prefix_eq initSM 5 7392 (by native_decide),
          sm_prefix_eq initSM 5 4684 (by native_decide), hsmMref]
    rw [hsm, fw_per_head_linear_shape _ _ 16 64 1024 [4096]
          (by rw [shape_4683 initSM initPM hSM hPM hInit]; rfl)
          (shape_weight initSM initPM hInit initGoal_4684 (by native_decide) 4684 [16,64,1024] rfl rfl)]
    rfl
  exact wrap_1tp initSM initPM intermediateGoal_4685 4685 [4096, 16, 64] rfl rfl rfl rfl rfl rfl hval hshape

theorem recon_intermediateGoal_4687 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4687
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hsmMref : denoteGraph sm initSM 7396 = denoteGraph sm initSM 4683 := by
    rw [sm_val initSM 4 7396 (by native_decide) (by native_decide)]
    rw [show sm.nodes[4]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_second_out' _ _ _ _ 7392 7396 7400 (by decide),
        sm_prefix_eq initSM 4 4683 (by native_decide)]
  have hpmMref : denoteGraph pm initPM 14636 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 34 14636 (by native_decide) (by native_decide)]
    rw [show pm.nodes[34]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_second_out' _ _ _ _ 14632 14636 14640 (by decide),
        pm_prefix_eq initPM 34 4683 (by native_decide)]
  have hval := veq_perhead initSM initPM hSM hPM hInit 4687 4686 7396 14636 6 39
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hsmMref hpmMref initGoal_4686 (by native_decide) rfl rfl rfl rfl
  have hshape : (denoteGraph sm initSM 4687).shape = [4096, 4, 64] := by
    have hsm : denoteGraph sm initSM 4687
        = fw_per_head_linear (denoteGraph sm initSM 4683) (denoteGraph sm initSM 4686) := by
      rw [sm_val initSM 6 4687 (by native_decide) (by native_decide)]
      rw [show sm.nodes[6]'(by native_decide)
          = { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7396, 4686], outs := [4687] }
          from by native_decide]
      rw [applyNode_fw_per_head_mix_precision_linear_out,
          sm_prefix_eq initSM 6 7396 (by native_decide),
          sm_prefix_eq initSM 6 4686 (by native_decide), hsmMref]
    rw [hsm, fw_per_head_linear_shape _ _ 4 64 1024 [4096]
          (by rw [shape_4683 initSM initPM hSM hPM hInit]; rfl)
          (shape_weight initSM initPM hInit initGoal_4686 (by native_decide) 4686 [4,64,1024] rfl rfl)]
    rfl
  exact wrap_1tp initSM initPM intermediateGoal_4687 4687 [4096, 4, 64] rfl rfl rfl rfl rfl rfl hval hshape

theorem recon_intermediateGoal_4689 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4689
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hsmMref : denoteGraph sm initSM 7400 = denoteGraph sm initSM 4683 := by
    rw [sm_val initSM 4 7400 (by native_decide) (by native_decide)]
    rw [show sm.nodes[4]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_third_out' _ _ _ _ 7392 7396 7400 (by decide) (by decide),
        sm_prefix_eq initSM 4 4683 (by native_decide)]
  have hpmMref : denoteGraph pm initPM 14640 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 34 14640 (by native_decide) (by native_decide)]
    rw [show pm.nodes[34]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_third_out' _ _ _ _ 14632 14636 14640 (by decide) (by decide),
        pm_prefix_eq initPM 34 4683 (by native_decide)]
  have hval := veq_perhead initSM initPM hSM hPM hInit 4689 4688 7400 14640 7 40
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hsmMref hpmMref initGoal_4688 (by native_decide) rfl rfl rfl rfl
  have hshape : (denoteGraph sm initSM 4689).shape = [4096, 4, 64] := by
    have hsm : denoteGraph sm initSM 4689
        = fw_per_head_linear (denoteGraph sm initSM 4683) (denoteGraph sm initSM 4688) := by
      rw [sm_val initSM 7 4689 (by native_decide) (by native_decide)]
      rw [show sm.nodes[7]'(by native_decide)
          = { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7400, 4688], outs := [4689] }
          from by native_decide]
      rw [applyNode_fw_per_head_mix_precision_linear_out,
          sm_prefix_eq initSM 7 7400 (by native_decide),
          sm_prefix_eq initSM 7 4688 (by native_decide), hsmMref]
    rw [hsm, fw_per_head_linear_shape _ _ 4 64 1024 [4096]
          (by rw [shape_4683 initSM initPM hSM hPM hInit]; rfl)
          (shape_weight initSM initPM hInit initGoal_4688 (by native_decide) 4688 [4,64,1024] rfl rfl)]
    rfl
  exact wrap_1tp initSM initPM intermediateGoal_4689 4689 [4096, 4, 64] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### Standalone value/shape equalities for the per-head Q/K outputs (reused by
    the 1-tp rotary embedding reconstruction below). -/

/-- `sm 4685 = pm 4685` (per-head Q projection). -/
theorem veq_4685 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph sm initSM 4685 = denoteGraph pm initPM 4685 := by
  have hsmMref : denoteGraph sm initSM 7392 = denoteGraph sm initSM 4683 := by
    rw [sm_val initSM 4 7392 (by native_decide) (by native_decide)]
    rw [show sm.nodes[4]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_first_out', sm_prefix_eq initSM 4 4683 (by native_decide)]
  have hpmMref : denoteGraph pm initPM 14632 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 34 14632 (by native_decide) (by native_decide)]
    rw [show pm.nodes[34]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_first_out', pm_prefix_eq initPM 34 4683 (by native_decide)]
  exact veq_perhead initSM initPM hSM hPM hInit 4685 4684 7392 14632 5 38
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hsmMref hpmMref initGoal_4684 (by native_decide) rfl rfl rfl rfl

/-- `(sm 4685).shape = [4096, 16, 64]`. -/
theorem shape_4685 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    (denoteGraph sm initSM 4685).shape = [4096, 16, 64] := by
  have hsmMref : denoteGraph sm initSM 7392 = denoteGraph sm initSM 4683 := by
    rw [sm_val initSM 4 7392 (by native_decide) (by native_decide)]
    rw [show sm.nodes[4]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_first_out', sm_prefix_eq initSM 4 4683 (by native_decide)]
  have hsm : denoteGraph sm initSM 4685
      = fw_per_head_linear (denoteGraph sm initSM 4683) (denoteGraph sm initSM 4684) := by
    rw [sm_val initSM 5 4685 (by native_decide) (by native_decide)]
    rw [show sm.nodes[5]'(by native_decide)
        = { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7392, 4684], outs := [4685] }
        from by native_decide]
    rw [applyNode_fw_per_head_mix_precision_linear_out,
        sm_prefix_eq initSM 5 7392 (by native_decide),
        sm_prefix_eq initSM 5 4684 (by native_decide), hsmMref]
  rw [hsm, fw_per_head_linear_shape _ _ 16 64 1024 [4096]
        (by rw [shape_4683 initSM initPM hSM hPM hInit]; rfl)
        (shape_weight initSM initPM hInit initGoal_4684 (by native_decide) 4684 [16,64,1024] rfl rfl)]
  rfl

/-- `sm 4687 = pm 4687` (per-head K projection). -/
theorem veq_4687 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph sm initSM 4687 = denoteGraph pm initPM 4687 := by
  have hsmMref : denoteGraph sm initSM 7396 = denoteGraph sm initSM 4683 := by
    rw [sm_val initSM 4 7396 (by native_decide) (by native_decide)]
    rw [show sm.nodes[4]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_second_out' _ _ _ _ 7392 7396 7400 (by decide),
        sm_prefix_eq initSM 4 4683 (by native_decide)]
  have hpmMref : denoteGraph pm initPM 14636 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 34 14636 (by native_decide) (by native_decide)]
    rw [show pm.nodes[34]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_second_out' _ _ _ _ 14632 14636 14640 (by decide),
        pm_prefix_eq initPM 34 4683 (by native_decide)]
  exact veq_perhead initSM initPM hSM hPM hInit 4687 4686 7396 14636 6 39
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hsmMref hpmMref initGoal_4686 (by native_decide) rfl rfl rfl rfl

/-- `(sm 4687).shape = [4096, 4, 64]`. -/
theorem shape_4687 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    (denoteGraph sm initSM 4687).shape = [4096, 4, 64] := by
  have hsmMref : denoteGraph sm initSM 7396 = denoteGraph sm initSM 4683 := by
    rw [sm_val initSM 4 7396 (by native_decide) (by native_decide)]
    rw [show sm.nodes[4]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_second_out' _ _ _ _ 7392 7396 7400 (by decide),
        sm_prefix_eq initSM 4 4683 (by native_decide)]
  have hsm : denoteGraph sm initSM 4687
      = fw_per_head_linear (denoteGraph sm initSM 4683) (denoteGraph sm initSM 4686) := by
    rw [sm_val initSM 6 4687 (by native_decide) (by native_decide)]
    rw [show sm.nodes[6]'(by native_decide)
        = { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7396, 4686], outs := [4687] }
        from by native_decide]
    rw [applyNode_fw_per_head_mix_precision_linear_out,
        sm_prefix_eq initSM 6 7396 (by native_decide),
        sm_prefix_eq initSM 6 4686 (by native_decide), hsmMref]
  rw [hsm, fw_per_head_linear_shape _ _ 4 64 1024 [4096]
        (by rw [shape_4683 initSM initPM hSM hPM hInit]; rfl)
        (shape_weight initSM initPM hInit initGoal_4686 (by native_decide) 4686 [4,64,1024] rfl rfl)]
  rfl


/-! ### Replicated multiref-copy goals (FW_multiref with `replicated := true`)

    A `FW_multiref` output that is *replicated* across ranks records a
    `replicated := true` goal whose `tps` list the per-rank full copies. Its
    reconstruction picks the rank-0 head, so the obligation reduces to
    `sm ts = pm p0` where both sides are multiref copies of the same already-
    reconstructed source (`veq_4681` / `veq_4683`). -/

/-- Generic `FW_multiref` (params `[2]`) second-output reduction. -/
theorem applyNode_fw_multiref2_second_out' (g : GraphDecl) (s : Store) (rank : Nat)
    (xTid t1 t2 : Tid) (h12 : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := [t1, t2], params := [2] } t2 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t1, t2].zip (List.replicate 2 (s xTid))) t2 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, show ¬ (t1 = t2) from h12]

/-- Wrap a replicated dual-tp goal (`replicated := true`, two full copies) into
    the `InitGoalHolds` obligation: reconstruction picks the rank-0 head. -/
theorem wrap_replicated_dual (initSM initPM : Store) (g : LineageGoal)
    (T p0 p1 : Tid) (sh : Shape)
    (htp : g.tps = [{ rank := 0, tid := p0 }, { rank := 1, tid := p1 }])
    (hrep : g.replicated = true) (hts : g.ts = T) (htsShape : g.tsShape = sh)
    (htpShapes : g.tpShapes = [sh, sh])
    (hval : denoteGraph sm initSM T = denoteGraph pm initPM p0)
    (hshape0 : (denoteGraph sm initSM T).shape = sh)
    (hshapeP0 : (denoteGraph pm initPM p0).shape = sh)
    (hshapeP1 : (denoteGraph pm initPM p1).shape = sh) :
    InitGoalHolds pm.numRanks g (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hts, htsShape]; exact hshape0
  · rw [htp, htpShapes]; simp only [List.map]; rw [hshapeP0, hshapeP1]
  · unfold reconstructForGoal
    rw [hrep]
    simp only [if_true, htp, hts, List.map, List.headD]
    exact hval

/-- `intermediateGoal_7383` (FW_multiref, replicated copy of 4681). -/
theorem recon_intermediateGoal_7383 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7383
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hsm : denoteGraph sm initSM 7383 = denoteGraph sm initSM 4681 := by
    rw [sm_val initSM 2 7383 (by native_decide) (by native_decide)]
    rw [show sm.nodes[2]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }
        from by native_decide]
    rw [applyNode_fw_multiref2_first_out, sm_prefix_eq initSM 2 4681 (by native_decide)]
  have hpm0 : denoteGraph pm initPM 14603 = denoteGraph pm initPM 4681 := by
    rw [pm_val initPM 29 14603 (by native_decide) (by native_decide)]
    rw [show pm.nodes[29]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [14603, 14607], params := [2] }
        from by native_decide]
    rw [applyNode_fw_multiref2_first_out, pm_prefix_eq initPM 29 4681 (by native_decide)]
  have hpm1 : denoteGraph pm initPM 14611 = denoteGraph pm initPM 4681 := by
    rw [pm_val initPM 30 14611 (by native_decide) (by native_decide)]
    rw [show pm.nodes[30]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }
        from by native_decide]
    rw [applyNode_fw_multiref2_first_out, pm_prefix_eq initPM 30 4681 (by native_decide)]
  have hv := veq_4681 initSM initPM hSM hPM hInit
  have hs := shape_4681 initSM initPM hSM hPM hInit
  refine wrap_replicated_dual initSM initPM intermediateGoal_7383 7383 14603 14611 [4096, 1024]
    rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [hsm, hpm0]; exact hv
  · rw [hsm]; exact hs
  · rw [hpm0, ← hv]; exact hs
  · rw [hpm1, ← hv]; exact hs

/-- `intermediateGoal_7387` (FW_multiref, replicated copy of 4681, 2nd out). -/
theorem recon_intermediateGoal_7387 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7387
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hsm : denoteGraph sm initSM 7387 = denoteGraph sm initSM 4681 := by
    rw [sm_val initSM 2 7387 (by native_decide) (by native_decide)]
    rw [show sm.nodes[2]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }
        from by native_decide]
    rw [applyNode_fw_multiref2_second_out' _ _ _ _ 7383 7387 (by decide),
        sm_prefix_eq initSM 2 4681 (by native_decide)]
  have hpm0 : denoteGraph pm initPM 14607 = denoteGraph pm initPM 4681 := by
    rw [pm_val initPM 29 14607 (by native_decide) (by native_decide)]
    rw [show pm.nodes[29]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [14603, 14607], params := [2] }
        from by native_decide]
    rw [applyNode_fw_multiref2_second_out' _ _ _ _ 14603 14607 (by decide),
        pm_prefix_eq initPM 29 4681 (by native_decide)]
  have hpm1 : denoteGraph pm initPM 14615 = denoteGraph pm initPM 4681 := by
    rw [pm_val initPM 30 14615 (by native_decide) (by native_decide)]
    rw [show pm.nodes[30]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }
        from by native_decide]
    rw [applyNode_fw_multiref2_second_out' _ _ _ _ 14611 14615 (by decide),
        pm_prefix_eq initPM 30 4681 (by native_decide)]
  have hv := veq_4681 initSM initPM hSM hPM hInit
  have hs := shape_4681 initSM initPM hSM hPM hInit
  refine wrap_replicated_dual initSM initPM intermediateGoal_7387 7387 14607 14615 [4096, 1024]
    rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [hsm, hpm0]; exact hv
  · rw [hsm]; exact hs
  · rw [hpm0, ← hv]; exact hs
  · rw [hpm1, ← hv]; exact hs

/-- `intermediateGoal_7392` (FW_multiref, replicated copy of 4683, 1st out). -/
theorem recon_intermediateGoal_7392 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7392
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hsm : denoteGraph sm initSM 7392 = denoteGraph sm initSM 4683 := by
    rw [sm_val initSM 4 7392 (by native_decide) (by native_decide)]
    rw [show sm.nodes[4]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_first_out', sm_prefix_eq initSM 4 4683 (by native_decide)]
  have hpm0 : denoteGraph pm initPM 14620 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 33 14620 (by native_decide) (by native_decide)]
    rw [show pm.nodes[33]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [14620, 14624, 14628], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_first_out', pm_prefix_eq initPM 33 4683 (by native_decide)]
  have hpm1 : denoteGraph pm initPM 14632 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 34 14632 (by native_decide) (by native_decide)]
    rw [show pm.nodes[34]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_first_out', pm_prefix_eq initPM 34 4683 (by native_decide)]
  have hv := veq_4683 initSM initPM hSM hPM hInit
  have hs := shape_4683 initSM initPM hSM hPM hInit
  refine wrap_replicated_dual initSM initPM intermediateGoal_7392 7392 14620 14632 [4096, 1024]
    rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [hsm, hpm0]; exact hv
  · rw [hsm]; exact hs
  · rw [hpm0, ← hv]; exact hs
  · rw [hpm1, ← hv]; exact hs

/-- `intermediateGoal_7396` (FW_multiref, replicated copy of 4683, 2nd out). -/
theorem recon_intermediateGoal_7396 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7396
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hsm : denoteGraph sm initSM 7396 = denoteGraph sm initSM 4683 := by
    rw [sm_val initSM 4 7396 (by native_decide) (by native_decide)]
    rw [show sm.nodes[4]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_second_out' _ _ _ _ 7392 7396 7400 (by decide),
        sm_prefix_eq initSM 4 4683 (by native_decide)]
  have hpm0 : denoteGraph pm initPM 14624 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 33 14624 (by native_decide) (by native_decide)]
    rw [show pm.nodes[33]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [14620, 14624, 14628], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_second_out' _ _ _ _ 14620 14624 14628 (by decide),
        pm_prefix_eq initPM 33 4683 (by native_decide)]
  have hpm1 : denoteGraph pm initPM 14636 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 34 14636 (by native_decide) (by native_decide)]
    rw [show pm.nodes[34]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_second_out' _ _ _ _ 14632 14636 14640 (by decide),
        pm_prefix_eq initPM 34 4683 (by native_decide)]
  have hv := veq_4683 initSM initPM hSM hPM hInit
  have hs := shape_4683 initSM initPM hSM hPM hInit
  refine wrap_replicated_dual initSM initPM intermediateGoal_7396 7396 14624 14636 [4096, 1024]
    rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [hsm, hpm0]; exact hv
  · rw [hsm]; exact hs
  · rw [hpm0, ← hv]; exact hs
  · rw [hpm1, ← hv]; exact hs

/-- `intermediateGoal_7400` (FW_multiref, replicated copy of 4683, 3rd out). -/
theorem recon_intermediateGoal_7400 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7400
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hsm : denoteGraph sm initSM 7400 = denoteGraph sm initSM 4683 := by
    rw [sm_val initSM 4 7400 (by native_decide) (by native_decide)]
    rw [show sm.nodes[4]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_third_out' _ _ _ _ 7392 7396 7400 (by decide) (by decide),
        sm_prefix_eq initSM 4 4683 (by native_decide)]
  have hpm0 : denoteGraph pm initPM 14628 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 33 14628 (by native_decide) (by native_decide)]
    rw [show pm.nodes[33]'(by native_decide)
        = { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [14620, 14624, 14628], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_third_out' _ _ _ _ 14620 14624 14628 (by decide) (by decide),
        pm_prefix_eq initPM 33 4683 (by native_decide)]
  have hpm1 : denoteGraph pm initPM 14640 = denoteGraph pm initPM 4683 := by
    rw [pm_val initPM 34 14640 (by native_decide) (by native_decide)]
    rw [show pm.nodes[34]'(by native_decide)
        = { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }
        from by native_decide]
    rw [applyNode_fw_multiref3_third_out' _ _ _ _ 14632 14636 14640 (by decide) (by decide),
        pm_prefix_eq initPM 34 4683 (by native_decide)]
  have hv := veq_4683 initSM initPM hSM hPM hInit
  have hs := shape_4683 initSM initPM hSM hPM hInit
  refine wrap_replicated_dual initSM initPM intermediateGoal_7400 7400 14628 14640 [4096, 1024]
    rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [hsm, hpm0]; exact hv
  · rw [hsm]; exact hs
  · rw [hpm0, ← hv]; exact hs
  · rw [hpm1, ← hv]; exact hs

/-! ### Rotary embedding cs-cache bridge (Worker #3, 2026-07-14)

    Refutes the "no bridge between SM tid 4691 and PM tid 11853" claim: BOTH
    graphs share init tid 4691 (`initGoal_4691 ∈ initGoals`), and PM broadcasts
    that init leaf to tids 11853..11864 via two `FW_multiref` nodes (rank 0 @
    pm idx 1, rank 1 @ pm idx 14). Hence `pm (11853+k) = pm 4691 = sm 4691`,
    a value equality provable from the PM graph structure + `hInit`. -/

/-- Any key present in `L` resolves, through a `zip` with a constant
    `List.replicate` column, to that constant value. -/
theorem storeSet_zip_replicate_mem_ir (s : Store) (v : Tensor) :
    ∀ (L : List Tid) (tid : Tid), tid ∈ L →
      storeSet s (L.zip (List.replicate L.length v)) tid = v := by
  intro L
  induction L with
  | nil => intro tid h; simp at h
  | cons a rest ih =>
    intro tid hmem
    rw [List.length_cons, List.replicate_succ, List.zip_cons_cons]
    by_cases h : a = tid
    · subst h
      show storeSet s ((a, v) :: (rest.zip (List.replicate rest.length v))) a = v
      unfold storeSet
      rw [List.find?_cons_of_pos (by simp)]
    · show storeSet s ((a, v) :: (rest.zip (List.replicate rest.length v))) tid = v
      have hmem' : tid ∈ rest := by
        rcases List.mem_cons.mp hmem with h' | h'
        · exact absurd h'.symm h
        · exact h'
      unfold storeSet
      rw [List.find?_cons_of_neg (by simp [h])]
      have := ih tid hmem'
      unfold storeSet at this
      exact this

/-- `applyNode` for `FW_multiref` (`params = [outs.length]`) at ANY output index
    present in `outs` returns the (single) input. Generalizes the head-only
    reductions to the 12-way rotary cs-cache broadcast. -/
theorem applyNode_fw_multiref_mem_out (g : GraphDecl) (s : Store) (rank : Nat)
    (xTid : Tid) (outs : List Tid) (tid : Tid) (hmem : tid ∈ outs) :
    applyNode g s { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
                    outs := outs, params := [outs.length] } tid = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s (outs.zip (List.replicate outs.length (s xTid))) tid = _
  exact storeSet_zip_replicate_mem_ir s (s xTid) outs tid hmem

/-- PM broadcasts init tid 4691 (rotary cs-cache) to tids 11853..11864 via
    two `FW_multiref` nodes; the LAST writer is rank-1 pm node idx 14. For every
    copy index `k < 12`, `pm (11853+k) = pm 4691`. -/
theorem pm_multiref_11853_broadcast (initPM : Store) (k : Nat) (hk : k < 12) :
    denoteGraph pm initPM (11853 + k) = denoteGraph pm initPM 4691 := by
  have hmem : (11853 + k) ∈ ((List.range 12).map (fun r => 11853 + r)) := by
    rw [List.mem_map]; exact ⟨k, List.mem_range.mpr hk, rfl⟩
  have hlen : ((List.range 12).map (fun r => 11853 + r)).length = 12 := by
    rw [List.length_map, List.length_range]
  have hnowrite : ∀ n ∈ pm.nodes.drop 15, (11853 + k) ∉ n.outs := by
    intro n hn
    exact (by native_decide :
      ∀ n ∈ pm.nodes.drop 15, ∀ t ∈ ((List.range 12).map (fun r => 11853 + r)), t ∉ n.outs)
      n hn (11853 + k) hmem
  rw [pm_val initPM 14 (11853 + k) (by native_decide) hnowrite]
  rw [show pm.nodes[14]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [4691],
          outs := ((List.range 12).map (fun r => 11853 + r)), params := [12] }
      from by native_decide]
  rw [show ([12] : List Nat) = [((List.range 12).map (fun r => 11853 + r)).length] from by rw [hlen]]
  rw [applyNode_fw_multiref_mem_out _ _ _ _ _ _ hmem,
      pm_prefix_eq initPM 14 4691 (by native_decide)]

/-- Rotary cs-cache agreement: `sm 4691 = pm cs` where `cs = 11853 + k` is the
    `k`-th PM broadcast copy. The `sm 4691 = pm 4691` step comes from `hInit`
    (`initGoal_4691 ∈ initGoals`), the broadcast step from the PM graph. -/
theorem sm_pm_rotary_cache_agree (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (cs k : Nat) (hk : k < 12) (hcs : cs = 11853 + k) :
    denoteGraph sm initSM 4691 = denoteGraph pm initPM cs := by
  subst hcs
  rw [pm_multiref_11853_broadcast initPM k hk]
  exact recon_weight initSM initPM hInit initGoal_4691 (by native_decide) 4691 rfl rfl rfl rfl

/-- `sm 4692 = pm 4692` (first rotary output, `.1` = Q'). Both sides apply
    `fw_rotary_embedding` to identical inputs except the cs-cache (SM 4691 vs
    PM 11853), which agree via `sm_pm_rotary_cache_agree`. -/
theorem veq_4692 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph sm initSM 4692 = denoteGraph pm initPM 4692 := by
  have hsm : denoteGraph sm initSM 4692
      = (fw_rotary_embedding (denoteGraph sm initSM 4691) (denoteGraph sm initSM 4690)
          (denoteGraph sm initSM 4685) (denoteGraph sm initSM 4687) 16 4).1 := by
    rw [sm_val initSM 8 4692 (by native_decide) (by native_decide)]
    rw [show sm.nodes[8]'(by native_decide)
        = { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }
        from by native_decide]
    rw [applyNode_fw_rotary_embedding_fst_out,
        sm_prefix_eq initSM 8 4691 (by native_decide),
        sm_prefix_eq initSM 8 4690 (by native_decide),
        sm_prefix_eq initSM 8 4685 (by native_decide),
        sm_prefix_eq initSM 8 4687 (by native_decide)]
  have hpm : denoteGraph pm initPM 4692
      = (fw_rotary_embedding (denoteGraph pm initPM 11853) (denoteGraph pm initPM 4690)
          (denoteGraph pm initPM 4685) (denoteGraph pm initPM 4687) 16 4).1 := by
    rw [pm_val initPM 42 4692 (by native_decide) (by native_decide)]
    rw [show pm.nodes[42]'(by native_decide)
        = { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }
        from by native_decide]
    rw [applyNode_fw_rotary_embedding_fst_out,
        pm_prefix_eq initPM 42 11853 (by native_decide),
        pm_prefix_eq initPM 42 4690 (by native_decide),
        pm_prefix_eq initPM 42 4685 (by native_decide),
        pm_prefix_eq initPM 42 4687 (by native_decide)]
  rw [hsm, hpm,
      sm_pm_rotary_cache_agree initSM initPM hInit 11853 0 (by norm_num) rfl,
      recon_weight initSM initPM hInit initGoal_4690 (by native_decide) 4690 rfl rfl rfl rfl,
      veq_4685 initSM initPM hSM hPM hInit,
      veq_4687 initSM initPM hSM hPM hInit]

/-- `sm 4693 = pm 4693` (second rotary output, `.2` = K'). -/
theorem veq_4693 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph sm initSM 4693 = denoteGraph pm initPM 4693 := by
  have hsm : denoteGraph sm initSM 4693
      = (fw_rotary_embedding (denoteGraph sm initSM 4691) (denoteGraph sm initSM 4690)
          (denoteGraph sm initSM 4685) (denoteGraph sm initSM 4687) 16 4).2 := by
    rw [sm_val initSM 8 4693 (by native_decide) (by native_decide)]
    rw [show sm.nodes[8]'(by native_decide)
        = { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }
        from by native_decide]
    rw [applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4690 4685 4687 4692 4693 (by decide),
        sm_prefix_eq initSM 8 4691 (by native_decide),
        sm_prefix_eq initSM 8 4690 (by native_decide),
        sm_prefix_eq initSM 8 4685 (by native_decide),
        sm_prefix_eq initSM 8 4687 (by native_decide)]
  have hpm : denoteGraph pm initPM 4693
      = (fw_rotary_embedding (denoteGraph pm initPM 11853) (denoteGraph pm initPM 4690)
          (denoteGraph pm initPM 4685) (denoteGraph pm initPM 4687) 16 4).2 := by
    rw [pm_val initPM 42 4693 (by native_decide) (by native_decide)]
    rw [show pm.nodes[42]'(by native_decide)
        = { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }
        from by native_decide]
    rw [applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11853 4690 4685 4687 4692 4693 (by decide),
        pm_prefix_eq initPM 42 11853 (by native_decide),
        pm_prefix_eq initPM 42 4690 (by native_decide),
        pm_prefix_eq initPM 42 4685 (by native_decide),
        pm_prefix_eq initPM 42 4687 (by native_decide)]
  rw [hsm, hpm,
      sm_pm_rotary_cache_agree initSM initPM hInit 11853 0 (by norm_num) rfl,
      recon_weight initSM initPM hInit initGoal_4690 (by native_decide) 4690 rfl rfl rfl rfl,
      veq_4685 initSM initPM hSM hPM hInit,
      veq_4687 initSM initPM hSM hPM hInit]

/-- `intermediateGoal_4692` (FW_rotary_embedding, 1-tp Q' — cs-cache bridge). -/
theorem recon_intermediateGoal_4692 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4692
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hshape : (denoteGraph sm initSM 4692).shape = [4096, 16, 64] := by
    have hsm : denoteGraph sm initSM 4692
        = (fw_rotary_embedding (denoteGraph sm initSM 4691) (denoteGraph sm initSM 4690)
            (denoteGraph sm initSM 4685) (denoteGraph sm initSM 4687) 16 4).1 := by
      rw [sm_val initSM 8 4692 (by native_decide) (by native_decide)]
      rw [show sm.nodes[8]'(by native_decide)
          = { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }
          from by native_decide]
      rw [applyNode_fw_rotary_embedding_fst_out,
          sm_prefix_eq initSM 8 4691 (by native_decide),
          sm_prefix_eq initSM 8 4690 (by native_decide),
          sm_prefix_eq initSM 8 4685 (by native_decide),
          sm_prefix_eq initSM 8 4687 (by native_decide)]
    rw [hsm, fw_rotary_embedding_fst_shape]
    exact shape_4685 initSM initPM hSM hPM hInit
  exact wrap_1tp initSM initPM intermediateGoal_4692 4692 [4096, 16, 64] rfl rfl rfl rfl rfl rfl
    (veq_4692 initSM initPM hSM hPM hInit) hshape

/-- `intermediateGoal_4693` (FW_rotary_embedding, 1-tp K' — cs-cache bridge). -/
theorem recon_intermediateGoal_4693 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4693
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hshape : (denoteGraph sm initSM 4693).shape = [4096, 4, 64] := by
    have hsm : denoteGraph sm initSM 4693
        = (fw_rotary_embedding (denoteGraph sm initSM 4691) (denoteGraph sm initSM 4690)
            (denoteGraph sm initSM 4685) (denoteGraph sm initSM 4687) 16 4).2 := by
      rw [sm_val initSM 8 4693 (by native_decide) (by native_decide)]
      rw [show sm.nodes[8]'(by native_decide)
          = { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }
          from by native_decide]
      rw [applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4690 4685 4687 4692 4693 (by decide),
          sm_prefix_eq initSM 8 4691 (by native_decide),
          sm_prefix_eq initSM 8 4690 (by native_decide),
          sm_prefix_eq initSM 8 4685 (by native_decide),
          sm_prefix_eq initSM 8 4687 (by native_decide)]
    rw [hsm, fw_rotary_embedding_snd_shape]
    exact shape_4687 initSM initPM hSM hPM hInit
  exact wrap_1tp initSM initPM intermediateGoal_4693 4693 [4096, 4, 64] rfl rfl rfl rfl rfl rfl
    (veq_4693 initSM initPM hSM hPM hInit) hshape

/-! ### Priority 3 (Worker #9): `intermediateGoal_4696` UNCONDITIONAL over `denoteGraph_ringAttn`

    The layer-0 attention reconstruction, restated over the value-faithful ring
    denotation. This is the first genuinely unconditional 2-tp sharded
    `intermediateGoal` (previously the floor was the attention op itself, false
    over plain `denoteGraph`). Reuses Pattern_3's ring-attn reconstruction gear
    over the GLOBAL sm/pm graphs. -/

-- global attention node literals (identical to Pattern_3 cut-graph nSM/nR0/nR1)
def nSMg : NodeDecl := { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] }
def nR0g : NodeDecl := { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7433, 7435, 7421, 4694, 4695], outs := [7437], params := [16, 4, 64, 64, 1, 512] }
def nR1g : NodeDecl := { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7434, 7436, 7422, 4694, 4695], outs := [7438], params := [16, 4, 64, 64, 1, 512] }

theorem buddy_sm_g : ringAttnBuddies sm nSMg = [nSMg] := by native_decide
theorem buddy_r0_g : ringAttnBuddies pm nR0g = [nR0g, nR1g] := by native_decide
theorem buddy_r1_g : ringAttnBuddies pm nR1g = [nR0g, nR1g] := by native_decide

/-- Extract a 1-tp (`ts = tp`, non-replicated, gatherDim 0) value equality from an
    `InitGoalHolds`, over abstract stores. -/
theorem oneTp_valeq (g : LineageGoal) (smS pmS : Store) (T : Tid)
    (htp : g.tps = [{rank := 0, tid := T}]) (hgd : g.gatherDim = 0)
    (hrep : g.replicated = false) (hts : g.ts = T)
    (h : InitGoalHolds pm.numRanks g smS pmS) :
    smS T = pmS T := by
  have hval := h.2.2
  rw [reconstructForGoal_of_not_replicated g pm.numRanks _ hrep, htp, hts, hgd] at hval
  simp only [List.map, reconstructWithDim] at hval
  exact hval

/-- Generic-store analog of `wrap_2tp_allGather`. -/
theorem wrap_2tp_allGather_gen (smS pmS : Store) (g : LineageGoal)
    (T p0 p1 : Tid) (sh sh0 : Shape)
    (htp : g.tps = [{rank := 0, tid := p0}, {rank := 1, tid := p1}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false)
    (hts : g.ts = T) (htsShape : g.tsShape = sh) (htpShapes : g.tpShapes = [sh0, sh0])
    (hne : sh0 ≠ [1])
    (hval : smS T = allGatherPrimDimN 0 pm.numRanks 0 [pmS p0, pmS p1])
    (hshape : (smS T).shape = sh)
    (hshapeP0 : (pmS p0).shape = sh0)
    (hshapeP1 : (pmS p1).shape = sh0) :
    InitGoalHolds pm.numRanks g smS pmS := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hts, htsShape]; exact hshape
  · rw [htp, htpShapes]; simp only [List.map]; rw [hshapeP0, hshapeP1]
  · rw [hts, reconstructForGoal_of_not_replicated g pm.numRanks _ hrep, hgd, htp]
    simp only [List.map]
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
          (by rw [hshapeP0]; exact hne)]
    exact hval

/-- Chunk-node value reduction on the global PM graph. -/
theorem pm_chunk_reduce (initPM : Store) (k : Nat) (rank inTid outTid : Tid)
    (hk : k < pm.nodes.length)
    (hnode : pm.nodes[k]'hk =
      {rank := rank, op := "OpName.ChunkPrim", ins := [inTid], outs := [outTid], params := [0]})
    (hdrop : ∀ n ∈ pm.nodes.drop (k+1), outTid ∉ n.outs)
    (hpre : ∀ n ∈ pm.nodes.drop k, inTid ∉ n.outs) :
    denoteGraph pm initPM outTid = chunkPrimDimN 0 pm.numRanks rank (denoteGraph pm initPM inTid) := by
  rw [pm_val initPM k outTid hk hdrop, hnode, applyNode_chunkPrimDimN_out,
      pm_prefix_eq initPM k inTid hpre]


-- =========================================================================
-- Priority 3: intermediateGoal_4696 UNCONDITIONAL over ring-attn
-- =========================================================================
/-! ### Priority 2 (Worker #10): parametrized sliding-window attention 2-tp gear

    `recon_attn_sliding_window_2tp_layer` abstracts the ASSEMBLY TAIL of
    `recon_intermediateGoal_4696_ringAttn` (node reductions → Pattern_3
    reconstruction gear → `wrap_2tp_allGather_gen`) over arbitrary:
      - SM/PM attention node literals (`nSM`/`nR0`/`nR1`),
      - the three take-prefix folds (`foldSM`/`foldPM`/`foldPM'`, opaque `Store`s),
      - output tids (`oSM`/`oR0`/`oR1`), shard length `L`, head counts `nh`/`kh`,
      - the layer `LineageGoal` `g`.
    It consumes exactly the per-layer facts a caller must discharge:
      - node reductions relating `denoteGraph_ringAttn …` to the ring-attn
        `applyNodeRingAttn_sliding_window` on the prefix fold (`hSM_red`/`hR0_red`/
        `hR1_red`), plus the r1 store bridge (`hbridge`, the take-k→take-(k+1) shift),
      - the Pattern_3 gear hypotheses (buddy detection, Q'/K'/V full
        reconstructions over the folds, cu-seqlens agreement, param agreement,
        full-output shape on BOTH folds),
      - the goal metadata (`g.tps`/`gatherDim`/`replicated`/`ts`/`tsShape`/`tpShapes`).
    Produces `InitGoalHolds pm.numRanks g (denoteGraph_ringAttn sm …)
    (denoteGraph_ringAttn pm …)`. `recon_intermediateGoal_4696_ringAttn` (layer 0,
    just below) is refactored to fire THROUGH this gear on the layer-0 witnesses —
    a faithful re-derivation demonstrating the gear is neither vacuous nor wrong.

    ======================================================================
    Priority 1 (Worker #10) — full `FW_attn_sliding_window` / `FW_attn_zigzag`
    intermediateGoal enumeration (parsed from `denote/GeneratedYOCOMoE.lean`):

    SM sliding-window nodes (sm.numRanks = 1) — 12 layers, output tid = goal tid:
      L0  outs=[4696] ins=[4692,4693,4689,4694,4695]   (Q'=4692 K'=4693 V=4689)
      L1  outs=[4750] ins=[4746,4747,4744,4748,4749]
      L2  outs=[4804] ins=[4800,4801,4798,4802,4803]
      L3  outs=[4858] ins=[4854,4855,4852,4856,4857]
      L4  outs=[4912] ins=[4908,4909,4906,4910,4911]
      L5  outs=[4966] ins=[4962,4963,4960,4964,4965]
      L6  outs=[5020] ins=[5016,5017,5014,5018,5019]
      L7  outs=[5074] ins=[5070,5071,5068,5072,5073]
      L8  outs=[5128] ins=[5124,5125,5122,5126,5127]
      L9  outs=[5182] ins=[5178,5179,5176,5180,5181]
      L10 outs=[5236] ins=[5232,5233,5230,5234,5235]
      L11 outs=[5290] ins=[5286,5287,5284,5288,5289]
    PM sliding-window nodes (pm.numRanks = 2, r0/r1 per layer):
      L0  [7437,7438]  L1  [7623,7624]  L2  [7809,7810]  L3  [7995,7996]
      L4  [8181,8182]  L5  [8367,8368]  L6  [8553,8554]  L7  [8739,8740]
      L8  [8925,8926]  L9  [9111,9112]  L10 [9297,9298]  L11 [9483,9484]
    SM zigzag nodes (`FW_attn_zigzag`, params=[16,4,64,64,1,0]) — 12 layers:
      outs = 5347, 5396, 5445, 5494, 5543, 5592, 5641, 5690, 5739, 5788, 5837, 5886
      (ins = (List.range 5).map (fun r => base+r), base = 5342, 5391, …)

    REACHABILITY (Worker #10 finding, verified from the graph): this gear fires
    UNCONDITIONALLY only for LAYER 0. All 11 further `FW_attn_sliding_window`
    layers (outs `4750`/`4804`/…/`5290`) and all 12 `FW_attn_zigzag` layers (outs
    `5347`/`5396`/…/`5886`) have Q'/K'/V inputs that descend from layer-0
    attention output `4696` through the residual stream, which passes through the
    GLOBAL graph's empty-`params` `FW_reshape` no-op nodes (Worker #9's reshape
    blocker: goal shapes structurally FALSE there). So layers 1–11 + all zigzag
    are GATED on the upstream reshape-params fix; the gear is the ready machinery
    that fires the moment that fix lands. -/
set_option maxHeartbeats 4000000 in
theorem recon_attn_sliding_window_2tp_layer
    (initSM initPM : Store) (g : LineageGoal)
    (nSM nR0 nR1 : NodeDecl)
    (foldSM foldPM foldPM' : Store)
    (oSM oR0 oR1 : Tid) (L nh kh : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hkh : 0 < kh)
    -- node reductions: ring-attn value at output tid = applyNodeRingAttn_sliding_window on prefix fold
    (hSM_red : denoteGraph_ringAttn sm initSM oSM
        = applyNodeRingAttn_sliding_window sm foldSM nSM)
    (hR0_red : denoteGraph_ringAttn pm initPM oR0
        = applyNodeRingAttn_sliding_window pm foldPM nR0)
    (hR1_red : denoteGraph_ringAttn pm initPM oR1
        = applyNodeRingAttn_sliding_window pm foldPM' nR1)
    (hbridge : applyNodeRingAttn_sliding_window pm foldPM nR1
        = applyNodeRingAttn_sliding_window pm foldPM' nR1)
    -- Pattern_3 reconstruction gear hypotheses
    (hbuddy_sm : ringAttnBuddies sm nSM = [nSM])
    (hbuddy_r0 : ringAttnBuddies pm nR0 = [nR0, nR1])
    (hbuddy_r1 : ringAttnBuddies pm nR1 = [nR0, nR1])
    (hmyIdx0 : (([nR0, nR1].findIdx? (fun m => m.rank = nR0.rank)).getD 0) = 0)
    (hmyIdx1 : (([nR0, nR1].findIdx? (fun m => m.rank = nR1.rank)).getD 0) = 1)
    (hq_sm : 0 < (foldSM (nSM.ins.getD 0 0)).shape.length)
    (hk_sm : 0 < (foldSM (nSM.ins.getD 1 0)).shape.length)
    (hv_sm : 0 < (foldSM (nSM.ins.getD 2 0)).shape.length)
    (hq_full : foldSM (nSM.ins.getD 0 0)
        = allGatherPrimDimN 0 2 0 [foldPM (nR0.ins.getD 0 0), foldPM (nR1.ins.getD 0 0)])
    (hk_full : foldSM (nSM.ins.getD 1 0)
        = allGatherPrimDimN 0 2 0 [foldPM (nR0.ins.getD 1 0), foldPM (nR1.ins.getD 1 0)])
    (hv_full : foldSM (nSM.ins.getD 2 0)
        = allGatherPrimDimN 0 2 0 [foldPM (nR0.ins.getD 2 0), foldPM (nR1.ins.getD 2 0)])
    (hcuQ_sm_pm : foldSM (nSM.ins.getD 3 0) = foldPM (nR0.ins.getD 3 0))
    (hcuK_sm_pm : foldSM (nSM.ins.getD 4 0) = foldPM (nR0.ins.getD 4 0))
    (hcuQ_same : foldPM (nR0.ins.getD 3 0) = foldPM (nR1.ins.getD 3 0))
    (hcuK_same : foldPM (nR0.ins.getD 4 0) = foldPM (nR1.ins.getD 4 0))
    (hparams_sm : nSM.params = nR0.params)
    (hparams_same : nR0.params = nR1.params)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [foldPM (nR0.ins.getD 0 0), foldPM (nR1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [foldPM (nR0.ins.getD 1 0), foldPM (nR1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [foldPM (nR0.ins.getD 2 0), foldPM (nR1.ins.getD 2 0)])
          (foldPM (nR0.ins.getD 3 0)) (foldPM (nR0.ins.getD 4 0))
          (nR0.params.getD 0 1) (nR0.params.getD 1 1) (nR0.params.getD 2 1)
          (nR0.params.getD 3 1)
          (decide (nR0.params.getD 4 0 ≠ 0)) (nR0.params.getD 5 0)).shape
        = [2 * L, nh, kh])
    -- r1-shard full-output shape over the shifted fold (analog of `hfull_shape50`)
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [foldPM' (nR0.ins.getD 0 0), foldPM' (nR1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [foldPM' (nR0.ins.getD 1 0), foldPM' (nR1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [foldPM' (nR0.ins.getD 2 0), foldPM' (nR1.ins.getD 2 0)])
          (foldPM' (nR1.ins.getD 3 0)) (foldPM' (nR1.ins.getD 4 0))
          (nR1.params.getD 0 1) (nR1.params.getD 1 1) (nR1.params.getD 2 1)
          (nR1.params.getD 3 1)
          (decide (nR1.params.getD 4 0 ≠ 0)) (nR1.params.getD 5 0)).shape
        = [2 * L, nh, kh])
    -- goal metadata
    (htp : g.tps = [{rank := 0, tid := oR0}, {rank := 1, tid := oR1}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false)
    (hts : g.ts = oSM) (htsShape : g.tsShape = [2 * L, nh, kh])
    (htpShapes : g.tpShapes = [[L, nh, kh], [L, nh, kh]]) :
    InitGoalHolds pm.numRanks g
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hrec := applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    sm pm foldSM foldPM nSM nR0 nR1 L nh kh hL hnh hkh
    hbuddy_sm hbuddy_r0 hbuddy_r1 hmyIdx0 hmyIdx1
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm hcuQ_same hcuK_same hparams_sm hparams_same hfull_shape
  have hval : denoteGraph_ringAttn sm initSM oSM
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM oR0, denoteGraph_ringAttn pm initPM oR1] := by
    rw [hSM_red, hrec, hbridge, ← hR0_red, ← hR1_red, show pm.numRanks = 2 from rfl]
  have hshapeP0 : (denoteGraph_ringAttn pm initPM oR0).shape = [L, nh, kh] := by
    rw [hR0_red, applyNodeRingAttn_sliding_window_pair_eq_chunk pm foldPM nR0 nR0 nR1 0
          hbuddy_r0 hmyIdx0,
        chunkPrimDimN_shape 0 2 0 _ [2 * L, nh, kh] hfull_shape (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [show 2 * L / 2 = L from by omega]
  have hshapeP1 : (denoteGraph_ringAttn pm initPM oR1).shape = [L, nh, kh] := by
    rw [hR1_red, applyNodeRingAttn_sliding_window_pair_eq_chunk pm foldPM' nR1 nR0 nR1 1
          hbuddy_r1 hmyIdx1,
        chunkPrimDimN_shape 0 2 1 _ [2 * L, nh, kh] hfull_shape' (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [show 2 * L / 2 = L from by omega]
  have hshape : (denoteGraph_ringAttn sm initSM oSM).shape = [2 * L, nh, kh] := by
    rw [hval, show pm.numRanks = 2 from rfl,
        allGatherPrimDimN_shape 0 2
          [denoteGraph_ringAttn pm initPM oR0, denoteGraph_ringAttn pm initPM oR1]
          [L, nh, kh] (by simpa using hshapeP0)]
    simp only [List.set, List.getD_cons_zero]
    rw [show L * 2 = 2 * L from by omega]
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    g oSM oR0 oR1 [2 * L, nh, kh] [L, nh, kh]
    htp hgd hrep hts htsShape htpShapes
    (by intro h; simpa using congrArg List.length h)
    hval hshape hshapeP0 hshapeP1

set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_4696_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4696
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- input value equalities (plain)
  have hveq4692 := veq_4692 initSM initPM hSM hPM hInit
  have hveq4693 := veq_4693 initSM initPM hSM hPM hInit
  have hveq4689 : denoteGraph sm initSM 4689 = denoteGraph pm initPM 4689 :=
    oneTp_valeq intermediateGoal_4689 _ _ 4689 rfl rfl rfl rfl
      (recon_intermediateGoal_4689 initSM initPM hSM hPM hInit)
  have hcu4694 : denoteGraph sm initSM 4694 = denoteGraph pm initPM 4694 :=
    recon_weight initSM initPM hInit initGoal_4694 (by native_decide) 4694 rfl rfl rfl rfl
  have hcu4695 : denoteGraph sm initSM 4695 = denoteGraph pm initPM 4695 :=
    recon_weight initSM initPM hInit initGoal_4695 (by native_decide) 4695 rfl rfl rfl rfl
  -- input pm-side shapes
  have hpm4692_shape : (denoteGraph pm initPM 4692).shape = [2 * 2048, 16, 64] := by
    rw [← hveq4692]; exact (recon_intermediateGoal_4692 initSM initPM hSM hPM hInit).1
  have hpm4693_shape : (denoteGraph pm initPM 4693).shape = [2 * 2048, 4, 64] := by
    rw [← hveq4693]; exact (recon_intermediateGoal_4693 initSM initPM hSM hPM hInit).1
  have hpm4689_shape : (denoteGraph pm initPM 4689).shape = [2 * 2048, 4, 64] := by
    rw [← hveq4689]; exact (recon_intermediateGoal_4689 initSM initPM hSM hPM hInit).1
  -- chunk-node value reductions (plain pm)
  have hc7433 : denoteGraph pm initPM 7433 = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph pm initPM 4692) :=
    pm_chunk_reduce initPM 45 0 4692 7433 (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7434 : denoteGraph pm initPM 7434 = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph pm initPM 4692) :=
    pm_chunk_reduce initPM 47 1 4692 7434 (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7435 : denoteGraph pm initPM 7435 = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph pm initPM 4693) :=
    pm_chunk_reduce initPM 46 0 4693 7435 (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7436 : denoteGraph pm initPM 7436 = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph pm initPM 4693) :=
    pm_chunk_reduce initPM 48 1 4693 7436 (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7421 : denoteGraph pm initPM 7421 = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph pm initPM 4689) :=
    pm_chunk_reduce initPM 43 0 4689 7421 (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7422 : denoteGraph pm initPM 7422 = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph pm initPM 4689) :=
    pm_chunk_reduce initPM 44 1 4689 7422 (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- store<->plain bridges
  have bSsm4692 : (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4692 = denoteGraph sm initSM 4692 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4692 9 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4692 (by native_decide)
  have bSsm4693 : (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4693 = denoteGraph sm initSM 4693 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4693 9 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4693 (by native_decide)
  have bSsm4689 : (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4689 = denoteGraph sm initSM 4689 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4689 9 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4689 (by native_decide)
  have bSpm7433 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7433
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph pm initPM 4692) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7433 49 (by native_decide) (by native_decide)]
    show denoteGraph_ringAttn pm initPM 7433 = _
    rw [pm_ring_eq initPM 7433 (by native_decide), hc7433]
  have bSpm7434 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7434
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph pm initPM 4692) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7434 49 (by native_decide) (by native_decide)]
    show denoteGraph_ringAttn pm initPM 7434 = _
    rw [pm_ring_eq initPM 7434 (by native_decide), hc7434]
  have bSpm7435 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7435
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph pm initPM 4693) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7435 49 (by native_decide) (by native_decide)]
    show denoteGraph_ringAttn pm initPM 7435 = _
    rw [pm_ring_eq initPM 7435 (by native_decide), hc7435]
  have bSpm7436 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7436
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph pm initPM 4693) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7436 49 (by native_decide) (by native_decide)]
    show denoteGraph_ringAttn pm initPM 7436 = _
    rw [pm_ring_eq initPM 7436 (by native_decide), hc7436]
  have bSpm7421 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7421
      = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph pm initPM 4689) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7421 49 (by native_decide) (by native_decide)]
    show denoteGraph_ringAttn pm initPM 7421 = _
    rw [pm_ring_eq initPM 7421 (by native_decide), hc7421]
  have bSpm7422 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7422
      = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph pm initPM 4689) := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7422 49 (by native_decide) (by native_decide)]
    show denoteGraph_ringAttn pm initPM 7422 = _
    rw [pm_ring_eq initPM 7422 (by native_decide), hc7422]
  -- full q/k/v reconstructions (store-level, gear form)
  have hq_full : (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4692
      = allGatherPrimDimN 0 2 0
          [(pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7433,
           (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7434] := by
    rw [bSsm4692, bSpm7433, bSpm7434, hveq4692, show pm.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega)
            (denoteGraph pm initPM 4692) hpm4692_shape).symm
  have hk_full : (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4693
      = allGatherPrimDimN 0 2 0
          [(pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7435,
           (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7436] := by
    rw [bSsm4693, bSpm7435, bSpm7436, hveq4693, show pm.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 4 64 (by omega) (by omega) (by omega)
            (denoteGraph pm initPM 4693) hpm4693_shape).symm
  have hv_full : (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4689
      = allGatherPrimDimN 0 2 0
          [(pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7421,
           (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7422] := by
    rw [bSsm4689, bSpm7421, bSpm7422, hveq4689, show pm.numRanks = 2 from rfl]
    exact (allGather0_reconstruct_chunks_3d 2048 4 64 (by omega) (by omega) (by omega)
            (denoteGraph pm initPM 4689) hpm4689_shape).symm
  -- SM input nonempty-shape facts
  have hq_sm : 0 < ((sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM (nSMg.ins.getD 0 0)).shape.length := by
    show 0 < ((sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4692).shape.length
    rw [bSsm4692, hveq4692, hpm4692_shape]; decide
  have hk_sm : 0 < ((sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM (nSMg.ins.getD 1 0)).shape.length := by
    show 0 < ((sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4693).shape.length
    rw [bSsm4693, hveq4693, hpm4693_shape]; decide
  have hv_sm : 0 < ((sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM (nSMg.ins.getD 2 0)).shape.length := by
    show 0 < ((sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4689).shape.length
    rw [bSsm4689, hveq4689, hpm4689_shape]; decide
  -- cu_seqlens equalities
  have hSM4694 : (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4694 = denoteGraph sm initSM 4694 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4694 9 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4694 (by native_decide)
  have hSM4695 : (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4695 = denoteGraph sm initSM 4695 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4695 9 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 4695 (by native_decide)
  have hPM4694 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 4694 = denoteGraph pm initPM 4694 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4694 49 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4694 (by native_decide)
  have hPM4695 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 4695 = denoteGraph pm initPM 4695 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 4695 49 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 4695 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM (nSMg.ins.getD 3 0)
      = (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM (nR0g.ins.getD 3 0) := by
    show (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4694
        = (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 4694
    rw [hSM4694, hPM4694, hcu4694]
  have hcuK_sm_pm : (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM (nSMg.ins.getD 4 0)
      = (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM (nR0g.ins.getD 4 0) := by
    show (sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM 4695
        = (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 4695
    rw [hSM4695, hPM4695, hcu4695]
  -- full attention output shape
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM (nR0g.ins.getD 0 0),
                                  (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM (nR1g.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM (nR0g.ins.getD 1 0),
                                  (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM (nR1g.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM (nR0g.ins.getD 2 0),
                                  (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM (nR1g.ins.getD 2 0)])
        ((pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM (nR0g.ins.getD 3 0))
        ((pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM (nR0g.ins.getD 4 0))
        (nR0g.params.getD 0 1) (nR0g.params.getD 1 1) (nR0g.params.getD 2 1) (nR0g.params.getD 3 1)
        (decide (nR0g.params.getD 4 0 ≠ 0)) (nR0g.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7433,
                                    (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7434]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← hq_full, bSsm4692, hveq4692, hpm4692_shape]
    rfl
  -- store bridge take49 -> take50 for r1 inputs
  have e7433 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7433
      = (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM 7433 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7433 49 50 (by omega) (by native_decide) (by native_decide)).symm
  have e7434 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7434
      = (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM 7434 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7434 49 50 (by omega) (by native_decide) (by native_decide)).symm
  have e7435 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7435
      = (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM 7435 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7435 49 50 (by omega) (by native_decide) (by native_decide)).symm
  have e7436 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7436
      = (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM 7436 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7436 49 50 (by omega) (by native_decide) (by native_decide)).symm
  have e7421 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7421
      = (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM 7421 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7421 49 50 (by omega) (by native_decide) (by native_decide)).symm
  have e7422 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 7422
      = (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM 7422 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 7422 49 50 (by omega) (by native_decide) (by native_decide)).symm
  have e4694 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 4694
      = (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM 4694 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4694 49 50 (by omega) (by native_decide) (by native_decide)).symm
  have e4695 : (pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM 4695
      = (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM 4695 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 4695 49 50 (by omega) (by native_decide) (by native_decide)).symm
  have bridge_r1 : applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM) nR1g
      = applyNodeRingAttn_sliding_window pm
        ((pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM) nR1g := by
    apply attn_sw_store_congr
    · rw [buddy_r1_g]; intro m hm; fin_cases hm
      · exact e7433
      · exact e7434
    · rw [buddy_r1_g]; intro m hm; fin_cases hm
      · exact e7435
      · exact e7436
    · rw [buddy_r1_g]; intro m hm; fin_cases hm
      · exact e7421
      · exact e7422
    · exact e4694
    · exact e4695
  -- node reductions
  have hSM4696 : denoteGraph_ringAttn sm initSM 4696
      = applyNodeRingAttn_sliding_window sm ((sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM) nSMg := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 4696 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 4696 10 (by native_decide) (by native_decide),
        show sm.nodes.take 10 = sm.nodes.take 9 ++ [nSMg] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4692 4693 4689 4694 4695 4696 [16, 4, 64, 64, 1, 512]
  have hPM7437 : denoteGraph_ringAttn pm initPM 7437
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM) nR0g := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 7437 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7437 50 (by native_decide) (by native_decide),
        show pm.nodes.take 50 = pm.nodes.take 49 ++ [nR0g] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 7433 7435 7421 4694 4695 7437 [16, 4, 64, 64, 1, 512]
  have hPM7438 : denoteGraph_ringAttn pm initPM 7438
      = applyNodeRingAttn_sliding_window pm ((pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM) nR1g := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 7438 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 7438 51 (by native_decide) (by native_decide),
        show pm.nodes.take 51 = pm.nodes.take 50 ++ [nR1g] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 7434 7436 7422 4694 4695 7438 [16, 4, 64, 64, 1, 512]
  -- r1-shard full-output shape over the take-50 fold (gear hyp `hfull_shape'`)
  have hfull_shape50 :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM (nR0g.ins.getD 0 0),
                                  (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM (nR1g.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM (nR0g.ins.getD 1 0),
                                  (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM (nR1g.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM (nR0g.ins.getD 2 0),
                                  (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM (nR1g.ins.getD 2 0)])
        ((pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM (nR1g.ins.getD 3 0))
        ((pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM (nR1g.ins.getD 4 0))
        (nR1g.params.getD 0 1) (nR1g.params.getD 1 1) (nR1g.params.getD 2 1) (nR1g.params.getD 3 1)
        (decide (nR1g.params.getD 4 0 ≠ 0)) (nR1g.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    show [(allGatherPrimDimN 0 2 0 [(pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM 7433,
                                    (pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM 7434]).shape.head?.getD 0, 16, 64]
        = [2 * 2048, 16, 64]
    rw [← e7433, ← e7434, ← hq_full, bSsm4692, hveq4692, hpm4692_shape]
    rfl
  -- Fire the Worker #10 parametrized gear on the layer-0 witnesses (faithful
  -- re-derivation of the Worker #9 assembly tail).
  exact recon_attn_sliding_window_2tp_layer initSM initPM intermediateGoal_4696
    nSMg nR0g nR1g
    ((sm.nodes.take 9).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 49).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 50).foldl (applyNodeRingAttn pm) initPM)
    4696 7437 7438 2048 16 64 (by omega) (by omega) (by omega)
    hSM4696 hPM7437 hPM7438 bridge_r1
    buddy_sm_g buddy_r0_g buddy_r1_g (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape hfull_shape50
    rfl rfl rfl rfl rfl rfl

-- =========================================================================
-- Worker #11: params-aware FW_reshape cascade — intermediateGoal_4697
-- =========================================================================
/-! ### Row-preserving reshape / dim-0 allGather commute (Worker #11)

    With the regenerated `GeneratedYOCOMoE.lean`, `FW_reshape` nodes carry
    `params := [target_shape]`, so `Denote.evalOp` denotes them as
    `fw_view target_shape` (a pure flat-data relabel) instead of the legacy
    identity. The layer-0 attention output `4696 : [4096,16,64]` is reshaped to
    `4697 : [4096,1024]` (SM) / `7439,7440 : [2048,1024]` (PM). Because the
    reshape collapses only the trailing head dims (`16*64 = 1024`) and never
    crosses the dim-0 shard boundary (`4096 = 2*2048`), it commutes with the
    2-shard dim-0 `allGatherPrimDimN`. This is the special case the general
    `fw_reshape_allGather0_commute_2` (empty-params identity only) cannot cover. -/


set_option maxHeartbeats 4000000 in
/-- **`intermediateGoal_4697` UNCONDITIONAL over ring-attn.** The layer-0
    attention output reshape `[4096,16,64] → [4096,1024]` (SM node 10) reconstructs
    as the dim-0 gather of the two PM per-rank reshapes (nodes 51/52), by chaining
    Worker #9/#10's `recon_intermediateGoal_4696_ringAttn` through the
    row-preserving-reshape commute lemma. First cascade goal unblocked by the
    params-aware regen. -/
theorem recon_intermediateGoal_4697_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4697
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have h4696 := recon_intermediateGoal_4696_ringAttn initSM initPM hSM hPM hInit
  -- extract the 4696 shard shapes
  have hshapes := h4696.2.1
  simp only [intermediateGoal_4696, List.map, List.cons.injEq, and_true] at hshapes
  obtain ⟨hs7437, hs7438⟩ := hshapes
  -- extract the 4696 value reconstruction
  have hval96 : denoteGraph_ringAttn sm initSM 4696
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7437, denoteGraph_ringAttn pm initPM 7438] := by
    have hv := h4696.2.2
    rw [reconstructForGoal_of_not_replicated intermediateGoal_4696 pm.numRanks _ rfl] at hv
    simp only [intermediateGoal_4696, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
          (by rw [hs7437]; decide)] at hv
    exact hv
  -- reshape node reductions over the ring denotation
  have rSM : denoteGraph_ringAttn sm initSM 4697
      = fw_view [4096, 1024] (denoteGraph_ringAttn sm initSM 4696) :=
    ringAttn_reshape_reduce_g12 sm initSM 10 0 4696 4697 [4096, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7439
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7437) :=
    ringAttn_reshape_reduce_g12 pm initPM 51 0 7437 7439 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7440
      = fw_view [2048, 1024] (denoteGraph_ringAttn pm initPM 7438) :=
    ringAttn_reshape_reduce_g12 pm initPM 52 1 7438 7440 [2048, 1024] (by native_decide)
      (by native_decide) (by decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- the 4697 value reconstruction, via the commute lemma
  have hval97 : denoteGraph_ringAttn sm initSM 4697
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm initPM 7439, denoteGraph_ringAttn pm initPM 7440] := by
    rw [rSM, hval96, rP0, rP1]
    exact fw_view_allGather0_reshape_16_64_2_g12 _ _ hs7437 hs7438
  -- shapes
  have hs7439 : (denoteGraph_ringAttn pm initPM 7439).shape = [2048, 1024] := by rw [rP0]; rfl
  have hs7440 : (denoteGraph_ringAttn pm initPM 7440).shape = [2048, 1024] := by rw [rP1]; rfl
  have hs4697 : (denoteGraph_ringAttn sm initSM 4697).shape = [4096, 1024] := by rw [rSM]; rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4697 4697 7439 7440 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (by decide) hval97 hs4697 hs7439 hs7440

/-! ### 2-tp `extract_dual` bridgehead — FW_rotary_embedding sharded reconstruction

    The 20 token-sharded (2-tp) rotary goals (`4800`/`4801` … `5286`/`5287`)
    reconstruct the SM full rotary output as the `allGatherPrimDimN 0 2 0` of the
    two PM per-rank rotary shards. The reconstruction transfers the token-dim
    sharding across the rotary op via `fw_rotary_embedding_allGather0_commute_2`,
    PROVIDED the three sharded INPUTS (positions / query / key) are themselves
    reconstructed as dim-0 gathers of the corresponding PM shards, and the
    cs-cache agrees (`sm_pm_rotary_cache_agree`).

    Those three input reconstructions are the attention/MoE-region 2-tp goals. For
    the lowest-tid 2-tp rotary goal `4800`, the SM q-input tid `4794` chains back
    through `2× FW_attn_sliding_window + 2× FW_all2all_moe_gmm + FW_topk_routing`
    (empirically: 141 SM tids, min init leaf 4677) — the bespoke attention/MoE
    region that has no reconstruction template yet (PROGRESS.md "Still gated").

    Hence the gears below are stated CONDITIONALLY on the input reconstructions
    (zero sorry). They are the reusable machinery that fires the moment the
    attention region is reconstructed: `recon_intermediateGoal_4800_of_inputs`
    consumes exactly the three input intermediateGoal conclusions (`4794`/`4796`/
    `4799`) plus their PM shard shapes, and produces the rotary reconstruction. -/

/-- Generic wrapper for a 2-tp (`gatherDim = 0`, non-replicated) goal whose SM
    value equals the dim-0 `allGatherPrimDimN` of its two PM shards. Analog of
    `wrap_1tp` / `wrap_replicated_dual` for the sharded (extract_dual) case. -/
theorem wrap_2tp_allGather (initSM initPM : Store) (g : LineageGoal)
    (T p0 p1 : Tid) (sh sh0 : Shape)
    (htp : g.tps = [{rank := 0, tid := p0}, {rank := 1, tid := p1}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false)
    (hts : g.ts = T) (htsShape : g.tsShape = sh) (htpShapes : g.tpShapes = [sh0, sh0])
    (hne : sh0 ≠ [1])
    (hval : denoteGraph sm initSM T
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph pm initPM p0, denoteGraph pm initPM p1])
    (hshape : (denoteGraph sm initSM T).shape = sh)
    (hshapeP0 : (denoteGraph pm initPM p0).shape = sh0)
    (hshapeP1 : (denoteGraph pm initPM p1).shape = sh0) :
    InitGoalHolds pm.numRanks g (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hts, htsShape]; exact hshape
  · rw [htp, htpShapes]; simp only [List.map]; rw [hshapeP0, hshapeP1]
  · rw [hts, reconstructForGoal_of_not_replicated g pm.numRanks _ hrep, hgd, htp]
    simp only [List.map]
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
          (by rw [hshapeP0]; exact hne)]
    exact hval

/-- Sharded rotary Q'-output commute (pure tensor algebra): if the full
    position / query / key equal the dim-0 gather of their two shards and the
    cs-cache agrees, the full rotary Q' output equals the gather of the two
    per-rank rotary Q' outputs. -/
theorem rotary_fst_gather_commute
    (csS csP posS qS kS pos0 q0 k0 pos1 q1 k1 : Tensor) (L nh kh d : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hkh : 0 < kh) (hd : 0 < d)
    (hq0 : q0.shape = [L, nh, d]) (hq1 : q1.shape = [L, nh, d])
    (hk0 : k0.shape = [L, kh, d]) (hk1 : k1.shape = [L, kh, d])
    (hp0 : pos0.shape = [L, 1]) (hp1 : pos1.shape = [L, 1])
    (hcs : csS = csP)
    (hpos : posS = allGatherPrimDimN 0 2 0 [pos0, pos1])
    (hq : qS = allGatherPrimDimN 0 2 0 [q0, q1])
    (hk : kS = allGatherPrimDimN 0 2 0 [k0, k1]) :
    (fw_rotary_embedding csS posS qS kS nh kh).1
      = allGatherPrimDimN 0 2 0
          [(fw_rotary_embedding csP pos0 q0 k0 nh kh).1,
           (fw_rotary_embedding csP pos1 q1 k1 nh kh).1] := by
  rw [hcs, hpos, hq, hk, fw_rotary_embedding_allGather0_commute_2 q0 q1 k0 k1 pos0 pos1 csP
        L nh kh d hL hnh hkh hd hq0 hq1 hk0 hk1 hp0 hp1]
  rfl

/-- Sharded rotary K'-output commute (pure tensor algebra), the `.2` companion of
    `rotary_fst_gather_commute`. -/
theorem rotary_snd_gather_commute
    (csS csP posS qS kS pos0 q0 k0 pos1 q1 k1 : Tensor) (L nh kh d : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hkh : 0 < kh) (hd : 0 < d)
    (hq0 : q0.shape = [L, nh, d]) (hq1 : q1.shape = [L, nh, d])
    (hk0 : k0.shape = [L, kh, d]) (hk1 : k1.shape = [L, kh, d])
    (hp0 : pos0.shape = [L, 1]) (hp1 : pos1.shape = [L, 1])
    (hcs : csS = csP)
    (hpos : posS = allGatherPrimDimN 0 2 0 [pos0, pos1])
    (hq : qS = allGatherPrimDimN 0 2 0 [q0, q1])
    (hk : kS = allGatherPrimDimN 0 2 0 [k0, k1]) :
    (fw_rotary_embedding csS posS qS kS nh kh).2
      = allGatherPrimDimN 0 2 0
          [(fw_rotary_embedding csP pos0 q0 k0 nh kh).2,
           (fw_rotary_embedding csP pos1 q1 k1 nh kh).2] := by
  rw [hcs, hpos, hq, hk, fw_rotary_embedding_allGather0_commute_2 q0 q1 k0 k1 pos0 pos1 csP
        L nh kh d hL hnh hkh hd hq0 hq1 hk0 hk1 hp0 hp1]
  rfl

/-! ### Fully parametrized 2-tp rotary reconstruction gears

    These abstract over the concrete tids/node-indices: to reconstruct any one of
    the 20 rotary 2-tp goals (`4800`/`4801` … `5286`/`5287`) it suffices to supply
    (a) the SM/PM node reductions (mechanical `native_decide` lemmas per layer,
    cf. `sm_rotary_4800_node` etc.), (b) the cs-cache agreement (from
    `sm_pm_rotary_cache_agree`), (c) the three sharded-input reconstructions
    (positions / query / key — the attention/MoE-region 2-tp goals), and (d) the
    six PM shard shapes. This IS the recipe for the ~910 remaining 2-tp goals in
    general (swap the rotary commute for the op-specific `_allGather0_commute_2`). -/

/-- Parametrized 2-tp rotary Q' reconstruction gear. -/
theorem recon_rotary_2tp_fst (initSM initPM : Store) (g : LineageGoal)
    (T p0 p1 csS posS qS kS csP pos0 q0 k0 pos1 q1 k1 : Tid) (L nh kh d : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hkh : 0 < kh) (hd : 0 < d)
    (htp : g.tps = [{rank := 0, tid := p0}, {rank := 1, tid := p1}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = T)
    (htsShape : g.tsShape = [L * 2, nh, d]) (htpShapes : g.tpShapes = [[L, nh, d], [L, nh, d]])
    (hne : ([L, nh, d] : Shape) ≠ [1])
    (hsmNode : denoteGraph sm initSM T
        = (fw_rotary_embedding (denoteGraph sm initSM csS) (denoteGraph sm initSM posS)
            (denoteGraph sm initSM qS) (denoteGraph sm initSM kS) nh kh).1)
    (hpm0 : denoteGraph pm initPM p0
        = (fw_rotary_embedding (denoteGraph pm initPM csP) (denoteGraph pm initPM pos0)
            (denoteGraph pm initPM q0) (denoteGraph pm initPM k0) nh kh).1)
    (hpm1 : denoteGraph pm initPM p1
        = (fw_rotary_embedding (denoteGraph pm initPM csP) (denoteGraph pm initPM pos1)
            (denoteGraph pm initPM q1) (denoteGraph pm initPM k1) nh kh).1)
    (hcs : denoteGraph sm initSM csS = denoteGraph pm initPM csP)
    (hpos : denoteGraph sm initSM posS
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM pos0, denoteGraph pm initPM pos1])
    (hq : denoteGraph sm initSM qS
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM q0, denoteGraph pm initPM q1])
    (hk : denoteGraph sm initSM kS
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM k0, denoteGraph pm initPM k1])
    (hq0 : (denoteGraph pm initPM q0).shape = [L, nh, d])
    (hq1 : (denoteGraph pm initPM q1).shape = [L, nh, d])
    (hk0 : (denoteGraph pm initPM k0).shape = [L, kh, d])
    (hk1 : (denoteGraph pm initPM k1).shape = [L, kh, d])
    (hp0 : (denoteGraph pm initPM pos0).shape = [L, 1])
    (hp1 : (denoteGraph pm initPM pos1).shape = [L, 1]) :
    InitGoalHolds pm.numRanks g (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hval : denoteGraph sm initSM T
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph pm initPM p0, denoteGraph pm initPM p1] := by
    rw [hsmNode, hpm0, hpm1]
    exact rotary_fst_gather_commute _ _ _ _ _ _ _ _ _ _ _ L nh kh d
      hL hnh hkh hd hq0 hq1 hk0 hk1 hp0 hp1 hcs hpos hq hk
  have hshape : (denoteGraph sm initSM T).shape = [L * 2, nh, d] := by
    rw [hsmNode, fw_rotary_embedding_fst_shape, hq,
        allGatherPrimDimN_shape 0 2 _ [L, nh, d]
          (by simp only [List.head?_cons, Option.map_some, Option.getD_some]; exact hq0)]
    rfl
  refine wrap_2tp_allGather initSM initPM g T p0 p1 [L * 2, nh, d] [L, nh, d]
    htp hgd hrep hts htsShape htpShapes hne hval hshape ?_ ?_
  · rw [hpm0, fw_rotary_embedding_fst_shape]; exact hq0
  · rw [hpm1, fw_rotary_embedding_fst_shape]; exact hq1

/-- Parametrized 2-tp rotary K' reconstruction gear (the `.2` companion). -/
theorem recon_rotary_2tp_snd (initSM initPM : Store) (g : LineageGoal)
    (T p0 p1 csS posS qS kS csP pos0 q0 k0 pos1 q1 k1 : Tid) (L nh kh d : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hkh : 0 < kh) (hd : 0 < d)
    (htp : g.tps = [{rank := 0, tid := p0}, {rank := 1, tid := p1}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = T)
    (htsShape : g.tsShape = [L * 2, kh, d]) (htpShapes : g.tpShapes = [[L, kh, d], [L, kh, d]])
    (hne : ([L, kh, d] : Shape) ≠ [1])
    (hsmNode : denoteGraph sm initSM T
        = (fw_rotary_embedding (denoteGraph sm initSM csS) (denoteGraph sm initSM posS)
            (denoteGraph sm initSM qS) (denoteGraph sm initSM kS) nh kh).2)
    (hpm0 : denoteGraph pm initPM p0
        = (fw_rotary_embedding (denoteGraph pm initPM csP) (denoteGraph pm initPM pos0)
            (denoteGraph pm initPM q0) (denoteGraph pm initPM k0) nh kh).2)
    (hpm1 : denoteGraph pm initPM p1
        = (fw_rotary_embedding (denoteGraph pm initPM csP) (denoteGraph pm initPM pos1)
            (denoteGraph pm initPM q1) (denoteGraph pm initPM k1) nh kh).2)
    (hcs : denoteGraph sm initSM csS = denoteGraph pm initPM csP)
    (hpos : denoteGraph sm initSM posS
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM pos0, denoteGraph pm initPM pos1])
    (hq : denoteGraph sm initSM qS
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM q0, denoteGraph pm initPM q1])
    (hk : denoteGraph sm initSM kS
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM k0, denoteGraph pm initPM k1])
    (hq0 : (denoteGraph pm initPM q0).shape = [L, nh, d])
    (hq1 : (denoteGraph pm initPM q1).shape = [L, nh, d])
    (hk0 : (denoteGraph pm initPM k0).shape = [L, kh, d])
    (hk1 : (denoteGraph pm initPM k1).shape = [L, kh, d])
    (hp0 : (denoteGraph pm initPM pos0).shape = [L, 1])
    (hp1 : (denoteGraph pm initPM pos1).shape = [L, 1]) :
    InitGoalHolds pm.numRanks g (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hval : denoteGraph sm initSM T
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph pm initPM p0, denoteGraph pm initPM p1] := by
    rw [hsmNode, hpm0, hpm1]
    exact rotary_snd_gather_commute _ _ _ _ _ _ _ _ _ _ _ L nh kh d
      hL hnh hkh hd hq0 hq1 hk0 hk1 hp0 hp1 hcs hpos hq hk
  have hshape : (denoteGraph sm initSM T).shape = [L * 2, kh, d] := by
    rw [hsmNode, fw_rotary_embedding_snd_shape, hk,
        allGatherPrimDimN_shape 0 2 _ [L, kh, d]
          (by simp only [List.head?_cons, Option.map_some, Option.getD_some]; exact hk0)]
    rfl
  refine wrap_2tp_allGather initSM initPM g T p0 p1 [L * 2, kh, d] [L, kh, d]
    htp hgd hrep hts htsShape htpShapes hne hval hshape ?_ ?_
  · rw [hpm0, fw_rotary_embedding_snd_shape]; exact hk0
  · rw [hpm1, fw_rotary_embedding_snd_shape]; exact hk1

/-! ### Fully parametrized 2-tp per-head linear reconstruction gear (worker #6)

    Analog of `recon_rotary_2tp_fst/snd` for `FW_per_head_mix_precision_linear`.
    Structurally per-head linear = a linear followed by a per-head reshape of the
    output columns; it commutes with dim-0 (token) sharding exactly like plain
    linear because each output token row depends only on the matching input row
    (the weight is replicated). Backed by
    `fw_per_head_mix_precision_linear_allGather0_commute_2` (Denote.lean) — the
    per-head companion of `fw_linear_allGather0_commute_2_of` (Pattern_1.lean).

    To reconstruct any `FW_per_head_mix_precision_linear` 2-tp goal it suffices to
    supply (a) the SM/PM node reductions (mechanical `native_decide` per tid),
    (b) the sharded input-activation reconstruction (`hx`), (c) the replicated
    weight agreement (`hw`), and (d) the input/weight shapes. -/

/-- Raw value+shape bundle for a 2-tp per-head linear reconstruction: the SM value
    equals the dim-0 gather of the two PM per-head shards, and each shard has the
    per-head shape `[L, hW, dW]`. Shared by `recon_per_head_linear_2tp` (the goal
    wrapper) and by the rotary composition that threads at the rms boundary. -/
theorem perhead_2tp_val_shapes (initSM initPM : Store)
    (T p0 p1 xS wS x0 x1 wP : Tid) (L k hW dW : Nat)
    (hL : 0 < L) (hk : 0 < k) (hW0 : 0 < hW) (hdW0 : 0 < dW)
    (hsmNode : denoteGraph sm initSM T
        = fw_per_head_linear (denoteGraph sm initSM xS) (denoteGraph sm initSM wS))
    (hpm0 : denoteGraph pm initPM p0
        = fw_per_head_linear (denoteGraph pm initPM x0) (denoteGraph pm initPM wP))
    (hpm1 : denoteGraph pm initPM p1
        = fw_per_head_linear (denoteGraph pm initPM x1) (denoteGraph pm initPM wP))
    (hw : denoteGraph sm initSM wS = denoteGraph pm initPM wP)
    (hx : denoteGraph sm initSM xS
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM x0, denoteGraph pm initPM x1])
    (hx0 : (denoteGraph pm initPM x0).shape = [L, k])
    (hx1 : (denoteGraph pm initPM x1).shape = [L, k])
    (hwshape : (denoteGraph pm initPM wP).shape = [hW, dW, k]) :
    denoteGraph sm initSM T
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM p0, denoteGraph pm initPM p1]
      ∧ (denoteGraph pm initPM p0).shape = [L, hW, dW]
      ∧ (denoteGraph pm initPM p1).shape = [L, hW, dW] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hsmNode, hw, hx,
        fw_per_head_mix_precision_linear_allGather0_commute_2
          (denoteGraph pm initPM x0) (denoteGraph pm initPM x1) (denoteGraph pm initPM wP)
          L k hW dW hL hk hW0 hdW0 hx0 hx1 hwshape,
        ← hpm0, ← hpm1]
  · rw [hpm0]
    exact fw_per_head_linear_shape _ _ hW dW k [L] (by rw [hx0]; rfl) hwshape
  · rw [hpm1]
    exact fw_per_head_linear_shape _ _ hW dW k [L] (by rw [hx1]; rfl) hwshape

/-- Parametrized 2-tp per-head linear reconstruction gear. Closes any
    `FW_per_head_mix_precision_linear` 2-tp (`gatherDim = 0`, non-replicated)
    goal whose sharded input activation reconstructs as the dim-0 gather of its
    two PM shards and whose (replicated) weight agrees SM↔PM. -/
theorem recon_per_head_linear_2tp (initSM initPM : Store) (g : LineageGoal)
    (T p0 p1 xS wS x0 x1 wP : Tid) (L k hW dW : Nat)
    (hL : 0 < L) (hk : 0 < k) (hW0 : 0 < hW) (hdW0 : 0 < dW)
    (htp : g.tps = [{rank := 0, tid := p0}, {rank := 1, tid := p1}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = T)
    (htsShape : g.tsShape = [L * 2, hW, dW])
    (htpShapes : g.tpShapes = [[L, hW, dW], [L, hW, dW]])
    (hne : ([L, hW, dW] : Shape) ≠ [1])
    (hsmNode : denoteGraph sm initSM T
        = fw_per_head_linear (denoteGraph sm initSM xS) (denoteGraph sm initSM wS))
    (hpm0 : denoteGraph pm initPM p0
        = fw_per_head_linear (denoteGraph pm initPM x0) (denoteGraph pm initPM wP))
    (hpm1 : denoteGraph pm initPM p1
        = fw_per_head_linear (denoteGraph pm initPM x1) (denoteGraph pm initPM wP))
    (hw : denoteGraph sm initSM wS = denoteGraph pm initPM wP)
    (hx : denoteGraph sm initSM xS
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM x0, denoteGraph pm initPM x1])
    (hx0 : (denoteGraph pm initPM x0).shape = [L, k])
    (hx1 : (denoteGraph pm initPM x1).shape = [L, k])
    (hwshape : (denoteGraph pm initPM wP).shape = [hW, dW, k]) :
    InitGoalHolds pm.numRanks g (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  obtain ⟨hval2, hp0shape, hp1shape⟩ :=
    perhead_2tp_val_shapes initSM initPM T p0 p1 xS wS x0 x1 wP L k hW dW
      hL hk hW0 hdW0 hsmNode hpm0 hpm1 hw hx hx0 hx1 hwshape
  have hval : denoteGraph sm initSM T
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph pm initPM p0, denoteGraph pm initPM p1] := hval2
  have hshape : (denoteGraph sm initSM T).shape = [L * 2, hW, dW] := by
    rw [hval2, allGatherPrimDimN_shape 0 2 _ [L, hW, dW]
          (by simp only [List.head?_cons, Option.map_some, Option.getD_some]; exact hp0shape)]
    rfl
  exact wrap_2tp_allGather initSM initPM g T p0 p1 [L * 2, hW, dW] [L, hW, dW]
    htp hgd hrep hts htsShape htpShapes hne hval hshape hp0shape hp1shape

/-- SM node reduction for the layer-2 per-head Q projection (tid 4794, sm node 83). -/
theorem sm_perhead_4794_node (initSM : Store) :
    denoteGraph sm initSM 4794
      = fw_per_head_linear (denoteGraph sm initSM 7496) (denoteGraph sm initSM 4793) := by
  rw [sm_val initSM 83 4794 (by native_decide) (by native_decide)]
  rw [show sm.nodes[83]'(by native_decide)
      = { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7496, 4793], outs := [4794] }
      from by native_decide]
  rw [applyNode_fw_per_head_mix_precision_linear_out,
      sm_prefix_eq initSM 83 7496 (by native_decide),
      sm_prefix_eq initSM 83 4793 (by native_decide)]

/-- SM node reduction for the layer-2 per-head K projection (tid 4796, sm node 84). -/
theorem sm_perhead_4796_node (initSM : Store) :
    denoteGraph sm initSM 4796
      = fw_per_head_linear (denoteGraph sm initSM 7500) (denoteGraph sm initSM 4795) := by
  rw [sm_val initSM 84 4796 (by native_decide) (by native_decide)]
  rw [show sm.nodes[84]'(by native_decide)
      = { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7500, 4795], outs := [4796] }
      from by native_decide]
  rw [applyNode_fw_per_head_mix_precision_linear_out,
      sm_prefix_eq initSM 84 7500 (by native_decide),
      sm_prefix_eq initSM 84 4795 (by native_decide)]

/-- PM rank-0 node reduction for the per-head Q shard (tid 7771, pm node 227). -/
theorem pm_perhead_7771_node (initPM : Store) :
    denoteGraph pm initPM 7771
      = fw_per_head_linear (denoteGraph pm initPM 14718) (denoteGraph pm initPM 4793) := by
  rw [pm_val initPM 227 7771 (by native_decide) (by native_decide)]
  rw [show pm.nodes[227]'(by native_decide)
      = { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14718, 4793], outs := [7771] }
      from by native_decide]
  rw [applyNode_fw_per_head_mix_precision_linear_out,
      pm_prefix_eq initPM 227 14718 (by native_decide),
      pm_prefix_eq initPM 227 4793 (by native_decide)]

/-- PM rank-1 node reduction for the per-head Q shard (tid 7772, pm node 230). -/
theorem pm_perhead_7772_node (initPM : Store) :
    denoteGraph pm initPM 7772
      = fw_per_head_linear (denoteGraph pm initPM 14731) (denoteGraph pm initPM 4793) := by
  rw [pm_val initPM 230 7772 (by native_decide) (by native_decide)]
  rw [show pm.nodes[230]'(by native_decide)
      = { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14731, 4793], outs := [7772] }
      from by native_decide]
  rw [applyNode_fw_per_head_mix_precision_linear_out,
      pm_prefix_eq initPM 230 14731 (by native_decide),
      pm_prefix_eq initPM 230 4793 (by native_decide)]

/-- PM rank-0 node reduction for the per-head K shard (tid 7783, pm node 228). -/
theorem pm_perhead_7783_node (initPM : Store) :
    denoteGraph pm initPM 7783
      = fw_per_head_linear (denoteGraph pm initPM 14722) (denoteGraph pm initPM 4795) := by
  rw [pm_val initPM 228 7783 (by native_decide) (by native_decide)]
  rw [show pm.nodes[228]'(by native_decide)
      = { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14722, 4795], outs := [7783] }
      from by native_decide]
  rw [applyNode_fw_per_head_mix_precision_linear_out,
      pm_prefix_eq initPM 228 14722 (by native_decide),
      pm_prefix_eq initPM 228 4795 (by native_decide)]

/-- PM rank-1 node reduction for the per-head K shard (tid 7784, pm node 231). -/
theorem pm_perhead_7784_node (initPM : Store) :
    denoteGraph pm initPM 7784
      = fw_per_head_linear (denoteGraph pm initPM 14735) (denoteGraph pm initPM 4795) := by
  rw [pm_val initPM 231 7784 (by native_decide) (by native_decide)]
  rw [show pm.nodes[231]'(by native_decide)
      = { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14735, 4795], outs := [7784] }
      from by native_decide]
  rw [applyNode_fw_per_head_mix_precision_linear_out,
      pm_prefix_eq initPM 231 14735 (by native_decide),
      pm_prefix_eq initPM 231 4795 (by native_decide)]

/-- **2-tp per-head Q bridgehead (tid 4794).** `intermediateGoal_4794` holds given
    the reconstruction of the sharded input activation (7496, gathered from PM
    shards 14718/14731) plus the two shard shapes. The replicated weight (init tid
    4793) is closed internally via `recon_weight`. The input `hx` is transitively
    attention/MoE-gated (7496 = rms_norm → residual → attention/MoE), so this is
    CONDITIONAL on `hx`, threaded as an honest theorem parameter. -/
theorem recon_intermediateGoal_4794_of_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hx : denoteGraph sm initSM 7496
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14718, denoteGraph pm initPM 14731])
    (hx0 : (denoteGraph pm initPM 14718).shape = [2048, 1024])
    (hx1 : (denoteGraph pm initPM 14731).shape = [2048, 1024]) :
    InitGoalHolds pm.numRanks intermediateGoal_4794
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hw : denoteGraph sm initSM 4793 = denoteGraph pm initPM 4793 :=
    recon_weight initSM initPM hInit initGoal_4793 (by native_decide) 4793 rfl rfl rfl rfl
  have hwshape : (denoteGraph pm initPM 4793).shape = [16, 64, 1024] := by
    rw [← hw]
    exact shape_weight initSM initPM hInit initGoal_4793 (by native_decide) 4793 [16, 64, 1024] rfl rfl
  exact recon_per_head_linear_2tp initSM initPM intermediateGoal_4794
    4794 7771 7772 7496 4793 14718 14731 4793 2048 1024 16 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl rfl rfl rfl rfl rfl (by decide)
    (sm_perhead_4794_node initSM) (pm_perhead_7771_node initPM) (pm_perhead_7772_node initPM)
    hw hx hx0 hx1 hwshape

/-- **2-tp per-head K bridgehead (tid 4796).** K companion of
    `recon_intermediateGoal_4794_of_inputs`; input 7500 (PM shards 14722/14735),
    replicated weight init tid 4795. CONDITIONAL on `hx`. -/
theorem recon_intermediateGoal_4796_of_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hx : denoteGraph sm initSM 7500
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14722, denoteGraph pm initPM 14735])
    (hx0 : (denoteGraph pm initPM 14722).shape = [2048, 1024])
    (hx1 : (denoteGraph pm initPM 14735).shape = [2048, 1024]) :
    InitGoalHolds pm.numRanks intermediateGoal_4796
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hw : denoteGraph sm initSM 4795 = denoteGraph pm initPM 4795 :=
    recon_weight initSM initPM hInit initGoal_4795 (by native_decide) 4795 rfl rfl rfl rfl
  have hwshape : (denoteGraph pm initPM 4795).shape = [4, 64, 1024] := by
    rw [← hw]
    exact shape_weight initSM initPM hInit initGoal_4795 (by native_decide) 4795 [4, 64, 1024] rfl rfl
  exact recon_per_head_linear_2tp initSM initPM intermediateGoal_4796
    4796 7783 7784 7500 4795 14722 14735 4795 2048 1024 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl rfl rfl rfl rfl rfl (by decide)
    (sm_perhead_4796_node initSM) (pm_perhead_7783_node initPM) (pm_perhead_7784_node initPM)
    hw hx hx0 hx1 hwshape

/-- Canonically-named deliverable — 2-tp per-head Q projection (tid 4794). -/
theorem recon_intermediateGoal_4794 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hx : denoteGraph sm initSM 7496
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14718, denoteGraph pm initPM 14731])
    (hx0 : (denoteGraph pm initPM 14718).shape = [2048, 1024])
    (hx1 : (denoteGraph pm initPM 14731).shape = [2048, 1024]) :
    InitGoalHolds pm.numRanks intermediateGoal_4794
      (denoteGraph sm initSM) (denoteGraph pm initPM) :=
  recon_intermediateGoal_4794_of_inputs initSM initPM hInit hx hx0 hx1

/-- Canonically-named deliverable — 2-tp per-head K projection (tid 4796). -/
theorem recon_intermediateGoal_4796 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hx : denoteGraph sm initSM 7500
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14722, denoteGraph pm initPM 14735])
    (hx0 : (denoteGraph pm initPM 14722).shape = [2048, 1024])
    (hx1 : (denoteGraph pm initPM 14735).shape = [2048, 1024]) :
    InitGoalHolds pm.numRanks intermediateGoal_4796
      (denoteGraph sm initSM) (denoteGraph pm initPM) :=
  recon_intermediateGoal_4796_of_inputs initSM initPM hInit hx hx0 hx1

/-! ### Fully parametrized 2-tp rms-norm reconstruction gear (worker #7)

    Analog of `recon_per_head_linear_2tp` / `recon_rotary_2tp_fst/snd` for
    `FW_rms_norm`. Row-wise (per-token) reduction is orthogonal to dim-0 (token)
    sharding — each output row's normalization depends only on the matching input
    row and the replicated weight — so rms-norm commutes cleanly with dim-0
    sharding. Backed by `fw_rms_norm_allGather0_commute_2` (Pattern_1.lean, proven
    zero-sorry with a full `Tensor.ext`).

    To reconstruct any `FW_rms_norm` 2-tp goal it suffices to supply (a) the SM/PM
    node reductions (mechanical `native_decide` per tid), (b) the sharded input
    reconstruction (`hx`), (c) the replicated weight agreement (`hw`), and (d) the
    two input shard shapes. Note: unlike the per-head gear, NO weight-shape
    hypothesis is needed — the commute lemma leaves the weight unconstrained. -/

/-- Raw value+shape bundle for a 2-tp rms-norm reconstruction: the SM value equals
    the dim-0 gather of the two PM shards, and each shard has shape `[shard, hidden]`
    (rms-norm is shape-preserving). Shared by `recon_rms_norm_2tp` (goal wrapper)
    and by any composition that threads at the rms boundary. -/
theorem rms_2tp_val_shapes (initSM initPM : Store)
    (T p0 p1 xS wS x0 x1 wP : Tid) (shard hidden : Nat)
    (hshard : 0 < shard) (hhid : 0 < hidden)
    (hsmNode : denoteGraph sm initSM T
        = fw_rms_norm (denoteGraph sm initSM xS) (denoteGraph sm initSM wS))
    (hpm0 : denoteGraph pm initPM p0
        = fw_rms_norm (denoteGraph pm initPM x0) (denoteGraph pm initPM wP))
    (hpm1 : denoteGraph pm initPM p1
        = fw_rms_norm (denoteGraph pm initPM x1) (denoteGraph pm initPM wP))
    (hw : denoteGraph sm initSM wS = denoteGraph pm initPM wP)
    (hx : denoteGraph sm initSM xS
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM x0, denoteGraph pm initPM x1])
    (hx0 : (denoteGraph pm initPM x0).shape = [shard, hidden])
    (hx1 : (denoteGraph pm initPM x1).shape = [shard, hidden]) :
    denoteGraph sm initSM T
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM p0, denoteGraph pm initPM p1]
      ∧ (denoteGraph pm initPM p0).shape = [shard, hidden]
      ∧ (denoteGraph pm initPM p1).shape = [shard, hidden] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hsmNode, hw, hx,
        fw_rms_norm_allGather0_commute_2
          (denoteGraph pm initPM x0) (denoteGraph pm initPM x1) (denoteGraph pm initPM wP)
          shard hidden hshard hhid hx0 hx1,
        ← hpm0, ← hpm1]
  · rw [hpm0, TrainVerify.Denote.fw_rms_norm_shape]; exact hx0
  · rw [hpm1, TrainVerify.Denote.fw_rms_norm_shape]; exact hx1

/-- Parametrized 2-tp rms-norm reconstruction gear. Closes any `FW_rms_norm` 2-tp
    (`gatherDim = 0`, non-replicated) goal whose sharded input reconstructs as the
    dim-0 gather of its two PM shards and whose (replicated) weight agrees SM↔PM. -/
theorem recon_rms_norm_2tp (initSM initPM : Store) (g : LineageGoal)
    (T p0 p1 xS wS x0 x1 wP : Tid) (shard hidden : Nat)
    (hshard : 0 < shard) (hhid : 0 < hidden)
    (htp : g.tps = [{ rank := 0, tid := p0 }, { rank := 1, tid := p1 }])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = T)
    (htsShape : g.tsShape = [shard * 2, hidden])
    (htpShapes : g.tpShapes = [[shard, hidden], [shard, hidden]])
    (hne : ([shard, hidden] : Shape) ≠ [1])
    (hsmNode : denoteGraph sm initSM T
        = fw_rms_norm (denoteGraph sm initSM xS) (denoteGraph sm initSM wS))
    (hpm0 : denoteGraph pm initPM p0
        = fw_rms_norm (denoteGraph pm initPM x0) (denoteGraph pm initPM wP))
    (hpm1 : denoteGraph pm initPM p1
        = fw_rms_norm (denoteGraph pm initPM x1) (denoteGraph pm initPM wP))
    (hw : denoteGraph sm initSM wS = denoteGraph pm initPM wP)
    (hx : denoteGraph sm initSM xS
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM x0, denoteGraph pm initPM x1])
    (hx0 : (denoteGraph pm initPM x0).shape = [shard, hidden])
    (hx1 : (denoteGraph pm initPM x1).shape = [shard, hidden]) :
    InitGoalHolds pm.numRanks g (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  obtain ⟨hval2, hp0shape, hp1shape⟩ :=
    rms_2tp_val_shapes initSM initPM T p0 p1 xS wS x0 x1 wP shard hidden
      hshard hhid hsmNode hpm0 hpm1 hw hx hx0 hx1
  have hval : denoteGraph sm initSM T
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph pm initPM p0, denoteGraph pm initPM p1] := hval2
  have hshape : (denoteGraph sm initSM T).shape = [shard * 2, hidden] := by
    rw [hval2, allGatherPrimDimN_shape 0 2 _ [shard, hidden]
          (by simp only [List.head?_cons, Option.map_some, Option.getD_some]; exact hp0shape)]
    rfl
  exact wrap_2tp_allGather initSM initPM g T p0 p1 [shard * 2, hidden] [shard, hidden]
    htp hgd hrep hts htsShape htpShapes hne hval hshape hp0shape hp1shape

/-- SM node reduction for the layer-2 input-layernorm rms output (tid 4792, sm node 81). -/
theorem sm_rms_4792_node (initSM : Store) :
    denoteGraph sm initSM 4792
      = fw_rms_norm (denoteGraph sm initSM 7487) (denoteGraph sm initSM 4791) := by
  rw [sm_val initSM 81 4792 (by native_decide) (by native_decide)]
  rw [show sm.nodes[81]'(by native_decide)
      = { rank := 0, op := "OpName.FW_rms_norm", ins := [7487, 4791], outs := [4792] }
      from by native_decide]
  rw [applyNode_fw_rms_norm_out_1p,
      sm_prefix_eq initSM 81 7487 (by native_decide),
      sm_prefix_eq initSM 81 4791 (by native_decide)]

/-- PM rank-0 node reduction for the rms shard (tid 7769, pm node 223). -/
theorem pm_rms_7769_node (initPM : Store) :
    denoteGraph pm initPM 7769
      = fw_rms_norm (denoteGraph pm initPM 14701) (denoteGraph pm initPM 4791) := by
  rw [pm_val initPM 223 7769 (by native_decide) (by native_decide)]
  rw [show pm.nodes[223]'(by native_decide)
      = { rank := 0, op := "OpName.FW_rms_norm", ins := [14701, 4791], outs := [7769] }
      from by native_decide]
  rw [applyNode_fw_rms_norm_out_1p,
      pm_prefix_eq initPM 223 14701 (by native_decide),
      pm_prefix_eq initPM 223 4791 (by native_decide)]

/-- PM rank-1 node reduction for the rms shard (tid 7770, pm node 224). -/
theorem pm_rms_7770_node (initPM : Store) :
    denoteGraph pm initPM 7770
      = fw_rms_norm (denoteGraph pm initPM 14709) (denoteGraph pm initPM 4791) := by
  rw [pm_val initPM 224 7770 (by native_decide) (by native_decide)]
  rw [show pm.nodes[224]'(by native_decide)
      = { rank := 1, op := "OpName.FW_rms_norm", ins := [14709, 4791], outs := [7770] }
      from by native_decide]
  rw [applyNode_fw_rms_norm_out_1p,
      pm_prefix_eq initPM 224 14709 (by native_decide),
      pm_prefix_eq initPM 224 4791 (by native_decide)]

/-- **2-tp rms-norm bridgehead (tid 4792).** `intermediateGoal_4792` holds given
    the reconstruction of the sharded residual input (7487, gathered from PM shards
    14701/14709) plus the two shard shapes. The replicated weight (init tid 4791)
    is closed internally via `recon_weight`. The input `hx` is transitively
    attention/MoE-gated (7487 ← 4790 = residual add ← attention + MoE), so this is
    CONDITIONAL on `hx`, threaded as an honest theorem parameter. -/
theorem recon_intermediateGoal_4792_of_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hx : denoteGraph sm initSM 7487
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14701, denoteGraph pm initPM 14709])
    (hx0 : (denoteGraph pm initPM 14701).shape = [2048, 1024])
    (hx1 : (denoteGraph pm initPM 14709).shape = [2048, 1024]) :
    InitGoalHolds pm.numRanks intermediateGoal_4792
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hw : denoteGraph sm initSM 4791 = denoteGraph pm initPM 4791 :=
    recon_weight initSM initPM hInit initGoal_4791 (by native_decide) 4791 rfl rfl rfl rfl
  exact recon_rms_norm_2tp initSM initPM intermediateGoal_4792
    4792 7769 7770 7487 4791 14701 14709 4791 2048 1024
    (by norm_num) (by norm_num)
    rfl rfl rfl rfl rfl rfl (by decide)
    (sm_rms_4792_node initSM) (pm_rms_7769_node initPM) (pm_rms_7770_node initPM)
    hw hx hx0 hx1

/-- Canonically-named deliverable — 2-tp input-layernorm rms output (tid 4792). -/
theorem recon_intermediateGoal_4792 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hx : denoteGraph sm initSM 7487
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14701, denoteGraph pm initPM 14709])
    (hx0 : (denoteGraph pm initPM 14701).shape = [2048, 1024])
    (hx1 : (denoteGraph pm initPM 14709).shape = [2048, 1024]) :
    InitGoalHolds pm.numRanks intermediateGoal_4792
      (denoteGraph sm initSM) (denoteGraph pm initPM) :=
  recon_intermediateGoal_4792_of_inputs initSM initPM hInit hx hx0 hx1

/-- SM node reduction for the layer-2 rotary Q' output (tid 4800, sm node 86). -/
theorem sm_rotary_4800_node (initSM : Store) :
    denoteGraph sm initSM 4800
      = (fw_rotary_embedding (denoteGraph sm initSM 4691) (denoteGraph sm initSM 4799)
          (denoteGraph sm initSM 4794) (denoteGraph sm initSM 4796) 16 4).1 := by
  rw [sm_val initSM 86 4800 (by native_decide) (by native_decide)]
  rw [show sm.nodes[86]'(by native_decide)
      = { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4799, 4794, 4796], outs := [4800, 4801], params := [16, 4] }
      from by native_decide]
  rw [applyNode_fw_rotary_embedding_fst_out,
      sm_prefix_eq initSM 86 4691 (by native_decide),
      sm_prefix_eq initSM 86 4799 (by native_decide),
      sm_prefix_eq initSM 86 4794 (by native_decide),
      sm_prefix_eq initSM 86 4796 (by native_decide)]

/-- SM node reduction for the layer-2 rotary K' output (tid 4801, sm node 86). -/
theorem sm_rotary_4801_node (initSM : Store) :
    denoteGraph sm initSM 4801
      = (fw_rotary_embedding (denoteGraph sm initSM 4691) (denoteGraph sm initSM 4799)
          (denoteGraph sm initSM 4794) (denoteGraph sm initSM 4796) 16 4).2 := by
  rw [sm_val initSM 86 4801 (by native_decide) (by native_decide)]
  rw [show sm.nodes[86]'(by native_decide)
      = { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4799, 4794, 4796], outs := [4800, 4801], params := [16, 4] }
      from by native_decide]
  rw [applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4799 4794 4796 4800 4801 (by decide),
      sm_prefix_eq initSM 86 4691 (by native_decide),
      sm_prefix_eq initSM 86 4799 (by native_decide),
      sm_prefix_eq initSM 86 4794 (by native_decide),
      sm_prefix_eq initSM 86 4796 (by native_decide)]

/-- PM rank-0 node reduction for the layer-2 rotary Q' shard (tid 7805, pm node 227). -/
theorem pm_rotary_7805_node (initPM : Store) :
    denoteGraph pm initPM 7805
      = (fw_rotary_embedding (denoteGraph pm initPM 11855) (denoteGraph pm initPM 7803)
          (denoteGraph pm initPM 7771) (denoteGraph pm initPM 7783) 16 4).1 := by
  rw [pm_val initPM 233 7805 (by native_decide) (by native_decide)]
  rw [show pm.nodes[233]'(by native_decide)
      = { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11855, 7803, 7771, 7783], outs := [7805, 7807], params := [16, 4] }
      from by native_decide]
  rw [applyNode_fw_rotary_embedding_fst_out,
      pm_prefix_eq initPM 233 11855 (by native_decide),
      pm_prefix_eq initPM 233 7803 (by native_decide),
      pm_prefix_eq initPM 233 7771 (by native_decide),
      pm_prefix_eq initPM 233 7783 (by native_decide)]

/-- PM rank-1 node reduction for the layer-2 rotary Q' shard (tid 7806, pm node 228). -/
theorem pm_rotary_7806_node (initPM : Store) :
    denoteGraph pm initPM 7806
      = (fw_rotary_embedding (denoteGraph pm initPM 11855) (denoteGraph pm initPM 7804)
          (denoteGraph pm initPM 7772) (denoteGraph pm initPM 7784) 16 4).1 := by
  rw [pm_val initPM 234 7806 (by native_decide) (by native_decide)]
  rw [show pm.nodes[234]'(by native_decide)
      = { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11855, 7804, 7772, 7784], outs := [7806, 7808], params := [16, 4] }
      from by native_decide]
  rw [applyNode_fw_rotary_embedding_fst_out,
      pm_prefix_eq initPM 234 11855 (by native_decide),
      pm_prefix_eq initPM 234 7804 (by native_decide),
      pm_prefix_eq initPM 234 7772 (by native_decide),
      pm_prefix_eq initPM 234 7784 (by native_decide)]

/-- PM rank-0 node reduction for the layer-2 rotary K' shard (tid 7807, pm node 227). -/
theorem pm_rotary_7807_node (initPM : Store) :
    denoteGraph pm initPM 7807
      = (fw_rotary_embedding (denoteGraph pm initPM 11855) (denoteGraph pm initPM 7803)
          (denoteGraph pm initPM 7771) (denoteGraph pm initPM 7783) 16 4).2 := by
  rw [pm_val initPM 233 7807 (by native_decide) (by native_decide)]
  rw [show pm.nodes[233]'(by native_decide)
      = { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11855, 7803, 7771, 7783], outs := [7805, 7807], params := [16, 4] }
      from by native_decide]
  rw [applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11855 7803 7771 7783 7805 7807 (by decide),
      pm_prefix_eq initPM 233 11855 (by native_decide),
      pm_prefix_eq initPM 233 7803 (by native_decide),
      pm_prefix_eq initPM 233 7771 (by native_decide),
      pm_prefix_eq initPM 233 7783 (by native_decide)]

/-- PM rank-1 node reduction for the layer-2 rotary K' shard (tid 7808, pm node 228). -/
theorem pm_rotary_7808_node (initPM : Store) :
    denoteGraph pm initPM 7808
      = (fw_rotary_embedding (denoteGraph pm initPM 11855) (denoteGraph pm initPM 7804)
          (denoteGraph pm initPM 7772) (denoteGraph pm initPM 7784) 16 4).2 := by
  rw [pm_val initPM 234 7808 (by native_decide) (by native_decide)]
  rw [show pm.nodes[234]'(by native_decide)
      = { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11855, 7804, 7772, 7784], outs := [7806, 7808], params := [16, 4] }
      from by native_decide]
  rw [applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11855 7804 7772 7784 7806 7808 (by decide),
      pm_prefix_eq initPM 234 11855 (by native_decide),
      pm_prefix_eq initPM 234 7804 (by native_decide),
      pm_prefix_eq initPM 234 7772 (by native_decide),
      pm_prefix_eq initPM 234 7784 (by native_decide)]

/-- **2-tp rotary bridgehead — Q' (tid 4800).** `intermediateGoal_4800` holds given
    the reconstructions of the three sharded rotary inputs (positions 4799, query
    4794, key 4796) plus their PM shard shapes. The cs-cache is closed internally
    via `sm_pm_rotary_cache_agree`. Instantiating this closes goal 4800 the moment
    the attention/MoE region feeding 4794/4796/4799 is reconstructed. -/
theorem recon_intermediateGoal_4800_of_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hpos : denoteGraph sm initSM 4799
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7803, denoteGraph pm initPM 7804])
    (hq : denoteGraph sm initSM 4794
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7771, denoteGraph pm initPM 7772])
    (hk : denoteGraph sm initSM 4796
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7783, denoteGraph pm initPM 7784])
    (hq0 : (denoteGraph pm initPM 7771).shape = [2048, 16, 64])
    (hq1 : (denoteGraph pm initPM 7772).shape = [2048, 16, 64])
    (hk0 : (denoteGraph pm initPM 7783).shape = [2048, 4, 64])
    (hk1 : (denoteGraph pm initPM 7784).shape = [2048, 4, 64])
    (hp0 : (denoteGraph pm initPM 7803).shape = [2048, 1])
    (hp1 : (denoteGraph pm initPM 7804).shape = [2048, 1]) :
    InitGoalHolds pm.numRanks intermediateGoal_4800
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hcs : denoteGraph sm initSM 4691 = denoteGraph pm initPM 11855 :=
    sm_pm_rotary_cache_agree initSM initPM hInit 11855 2 (by norm_num) (by norm_num)
  exact recon_rotary_2tp_fst initSM initPM intermediateGoal_4800 4800 7805 7806
    4691 4799 4794 4796 11855 7803 7771 7783 7804 7772 7784 2048 16 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl rfl rfl rfl rfl rfl (by decide)
    (sm_rotary_4800_node initSM) (pm_rotary_7805_node initPM) (pm_rotary_7806_node initPM)
    hcs hpos hq hk hq0 hq1 hk0 hk1 hp0 hp1

/-- **2-tp rotary bridgehead — K' (tid 4801).** The `.2` companion of
    `recon_intermediateGoal_4800_of_inputs`. -/
theorem recon_intermediateGoal_4801_of_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hpos : denoteGraph sm initSM 4799
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7803, denoteGraph pm initPM 7804])
    (hq : denoteGraph sm initSM 4794
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7771, denoteGraph pm initPM 7772])
    (hk : denoteGraph sm initSM 4796
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7783, denoteGraph pm initPM 7784])
    (hq0 : (denoteGraph pm initPM 7771).shape = [2048, 16, 64])
    (hq1 : (denoteGraph pm initPM 7772).shape = [2048, 16, 64])
    (hk0 : (denoteGraph pm initPM 7783).shape = [2048, 4, 64])
    (hk1 : (denoteGraph pm initPM 7784).shape = [2048, 4, 64])
    (hp0 : (denoteGraph pm initPM 7803).shape = [2048, 1])
    (hp1 : (denoteGraph pm initPM 7804).shape = [2048, 1]) :
    InitGoalHolds pm.numRanks intermediateGoal_4801
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hcs : denoteGraph sm initSM 4691 = denoteGraph pm initPM 11855 :=
    sm_pm_rotary_cache_agree initSM initPM hInit 11855 2 (by norm_num) (by norm_num)
  exact recon_rotary_2tp_snd initSM initPM intermediateGoal_4801 4801 7807 7808
    4691 4799 4794 4796 11855 7803 7771 7783 7804 7772 7784 2048 16 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rfl rfl rfl rfl rfl rfl (by decide)
    (sm_rotary_4801_node initSM) (pm_rotary_7807_node initPM) (pm_rotary_7808_node initPM)
    hcs hpos hq hk hq0 hq1 hk0 hk1 hp0 hp1

/-! ### Worker #6 (2026-07-15) — rotary hypothesis reduction via shared rms input

    The per-head Q (4794) and K (4796) projections both consume the SAME rms-norm
    output (SM tid 4792) via a single `FW_multiref [4792] → [7496, 7500, 7504]`
    (sm node 82). On PM the two ranks' rms shards are `7769` (rank 0) and `7770`
    (rank 1), each multiref'd into the per-head input copies (pm nodes 225/226).

    So instead of threading the two per-head outputs (4794/4796) as separate 2-tp
    reconstructions plus their four shard shapes (6 hypotheses), we thread ONE
    shared rms reconstruction (`hrms`) plus its two shard shapes, and derive
    everything else via the multiref bridges + `perhead_2tp_val_shapes` + the
    per-head node reductions. This cuts the rotary conditional hypothesis count
    from 9 to 6 (see `recon_intermediateGoal_4800_of_rms_inputs`). -/

/-- `sm 7496 = sm 4792` (per-head Q input is a multiref copy of the rms output). -/
theorem sm_mref_7496_eq_4792 (initSM : Store) :
    denoteGraph sm initSM 7496 = denoteGraph sm initSM 4792 := by
  rw [sm_val initSM 82 7496 (by native_decide) (by native_decide)]
  rw [show sm.nodes[82]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_first_out', sm_prefix_eq initSM 82 4792 (by native_decide)]

/-- `sm 7500 = sm 4792` (per-head K input is a multiref copy of the rms output). -/
theorem sm_mref_7500_eq_4792 (initSM : Store) :
    denoteGraph sm initSM 7500 = denoteGraph sm initSM 4792 := by
  rw [sm_val initSM 82 7500 (by native_decide) (by native_decide)]
  rw [show sm.nodes[82]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out' _ _ _ _ 7496 7500 7504 (by decide),
      sm_prefix_eq initSM 82 4792 (by native_decide)]

/-- `pm 14718 = pm 7769` (PM rank-0 per-head Q input is a multiref copy of the rms shard). -/
theorem pm_mref_14718_eq_7769 (initPM : Store) :
    denoteGraph pm initPM 14718 = denoteGraph pm initPM 7769 := by
  rw [pm_val initPM 225 14718 (by native_decide) (by native_decide)]
  rw [show pm.nodes[225]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_first_out', pm_prefix_eq initPM 225 7769 (by native_decide)]

/-- `pm 14722 = pm 7769` (PM rank-0 per-head K input is a multiref copy of the rms shard). -/
theorem pm_mref_14722_eq_7769 (initPM : Store) :
    denoteGraph pm initPM 14722 = denoteGraph pm initPM 7769 := by
  rw [pm_val initPM 225 14722 (by native_decide) (by native_decide)]
  rw [show pm.nodes[225]'(by native_decide)
      = { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out' _ _ _ _ 14718 14722 14726 (by decide),
      pm_prefix_eq initPM 225 7769 (by native_decide)]

/-- `pm 14731 = pm 7770` (PM rank-1 per-head Q input is a multiref copy of the rms shard). -/
theorem pm_mref_14731_eq_7770 (initPM : Store) :
    denoteGraph pm initPM 14731 = denoteGraph pm initPM 7770 := by
  rw [pm_val initPM 226 14731 (by native_decide) (by native_decide)]
  rw [show pm.nodes[226]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_first_out', pm_prefix_eq initPM 226 7770 (by native_decide)]

/-- `pm 14735 = pm 7770` (PM rank-1 per-head K input is a multiref copy of the rms shard). -/
theorem pm_mref_14735_eq_7770 (initPM : Store) :
    denoteGraph pm initPM 14735 = denoteGraph pm initPM 7770 := by
  rw [pm_val initPM 226 14735 (by native_decide) (by native_decide)]
  rw [show pm.nodes[226]'(by native_decide)
      = { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739], params := [3] }
      from by native_decide]
  rw [applyNode_fw_multiref3_second_out' _ _ _ _ 14731 14735 14739 (by decide),
      pm_prefix_eq initPM 226 7770 (by native_decide)]

/-- **Reduced 2-tp rotary Q' bridgehead (tid 4800).** Threads only the SHARED rms
    reconstruction (`hrms`, sm tid 4792 → pm shards 7769/7770) + its two shard
    shapes + positions — **6 hypotheses** versus the 9 of
    `recon_intermediateGoal_4800`. The per-head Q/K reconstructions (4794/4796) and
    their four shard shapes are derived internally via the multiref bridges and
    `perhead_2tp_val_shapes`. -/
theorem recon_intermediateGoal_4800_of_rms_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hpos : denoteGraph sm initSM 4799
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7803, denoteGraph pm initPM 7804])
    (hrms : denoteGraph sm initSM 4792
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7769, denoteGraph pm initPM 7770])
    (hs0 : (denoteGraph pm initPM 7769).shape = [2048, 1024])
    (hs1 : (denoteGraph pm initPM 7770).shape = [2048, 1024])
    (hp0 : (denoteGraph pm initPM 7803).shape = [2048, 1])
    (hp1 : (denoteGraph pm initPM 7804).shape = [2048, 1]) :
    InitGoalHolds pm.numRanks intermediateGoal_4800
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hx0_14718 : (denoteGraph pm initPM 14718).shape = [2048, 1024] := by
    rw [pm_mref_14718_eq_7769]; exact hs0
  have hx1_14731 : (denoteGraph pm initPM 14731).shape = [2048, 1024] := by
    rw [pm_mref_14731_eq_7770]; exact hs1
  have hx0_14722 : (denoteGraph pm initPM 14722).shape = [2048, 1024] := by
    rw [pm_mref_14722_eq_7769]; exact hs0
  have hx1_14735 : (denoteGraph pm initPM 14735).shape = [2048, 1024] := by
    rw [pm_mref_14735_eq_7770]; exact hs1
  have hx7496 : denoteGraph sm initSM 7496
      = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14718, denoteGraph pm initPM 14731] := by
    rw [sm_mref_7496_eq_4792, hrms, pm_mref_14718_eq_7769, pm_mref_14731_eq_7770]
  have hx7500 : denoteGraph sm initSM 7500
      = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14722, denoteGraph pm initPM 14735] := by
    rw [sm_mref_7500_eq_4792, hrms, pm_mref_14722_eq_7769, pm_mref_14735_eq_7770]
  have hw4793 : denoteGraph sm initSM 4793 = denoteGraph pm initPM 4793 :=
    recon_weight initSM initPM hInit initGoal_4793 (by native_decide) 4793 rfl rfl rfl rfl
  have hwshape4793 : (denoteGraph pm initPM 4793).shape = [16, 64, 1024] := by
    rw [← hw4793]
    exact shape_weight initSM initPM hInit initGoal_4793 (by native_decide) 4793 [16, 64, 1024] rfl rfl
  have hw4795 : denoteGraph sm initSM 4795 = denoteGraph pm initPM 4795 :=
    recon_weight initSM initPM hInit initGoal_4795 (by native_decide) 4795 rfl rfl rfl rfl
  have hwshape4795 : (denoteGraph pm initPM 4795).shape = [4, 64, 1024] := by
    rw [← hw4795]
    exact shape_weight initSM initPM hInit initGoal_4795 (by native_decide) 4795 [4, 64, 1024] rfl rfl
  obtain ⟨hq, hq0, hq1⟩ := perhead_2tp_val_shapes initSM initPM
    4794 7771 7772 7496 4793 14718 14731 4793 2048 1024 16 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (sm_perhead_4794_node initSM) (pm_perhead_7771_node initPM) (pm_perhead_7772_node initPM)
    hw4793 hx7496 hx0_14718 hx1_14731 hwshape4793
  obtain ⟨hk, hk0, hk1⟩ := perhead_2tp_val_shapes initSM initPM
    4796 7783 7784 7500 4795 14722 14735 4795 2048 1024 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (sm_perhead_4796_node initSM) (pm_perhead_7783_node initPM) (pm_perhead_7784_node initPM)
    hw4795 hx7500 hx0_14722 hx1_14735 hwshape4795
  exact recon_intermediateGoal_4800_of_inputs initSM initPM hInit
    hpos hq hk hq0 hq1 hk0 hk1 hp0 hp1

/-- **Reduced 2-tp rotary K' bridgehead (tid 4801).** K companion of
    `recon_intermediateGoal_4800_of_rms_inputs`; same 6 hypotheses. -/
theorem recon_intermediateGoal_4801_of_rms_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hpos : denoteGraph sm initSM 4799
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7803, denoteGraph pm initPM 7804])
    (hrms : denoteGraph sm initSM 4792
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7769, denoteGraph pm initPM 7770])
    (hs0 : (denoteGraph pm initPM 7769).shape = [2048, 1024])
    (hs1 : (denoteGraph pm initPM 7770).shape = [2048, 1024])
    (hp0 : (denoteGraph pm initPM 7803).shape = [2048, 1])
    (hp1 : (denoteGraph pm initPM 7804).shape = [2048, 1]) :
    InitGoalHolds pm.numRanks intermediateGoal_4801
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hx0_14718 : (denoteGraph pm initPM 14718).shape = [2048, 1024] := by
    rw [pm_mref_14718_eq_7769]; exact hs0
  have hx1_14731 : (denoteGraph pm initPM 14731).shape = [2048, 1024] := by
    rw [pm_mref_14731_eq_7770]; exact hs1
  have hx0_14722 : (denoteGraph pm initPM 14722).shape = [2048, 1024] := by
    rw [pm_mref_14722_eq_7769]; exact hs0
  have hx1_14735 : (denoteGraph pm initPM 14735).shape = [2048, 1024] := by
    rw [pm_mref_14735_eq_7770]; exact hs1
  have hx7496 : denoteGraph sm initSM 7496
      = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14718, denoteGraph pm initPM 14731] := by
    rw [sm_mref_7496_eq_4792, hrms, pm_mref_14718_eq_7769, pm_mref_14731_eq_7770]
  have hx7500 : denoteGraph sm initSM 7500
      = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14722, denoteGraph pm initPM 14735] := by
    rw [sm_mref_7500_eq_4792, hrms, pm_mref_14722_eq_7769, pm_mref_14735_eq_7770]
  have hw4793 : denoteGraph sm initSM 4793 = denoteGraph pm initPM 4793 :=
    recon_weight initSM initPM hInit initGoal_4793 (by native_decide) 4793 rfl rfl rfl rfl
  have hwshape4793 : (denoteGraph pm initPM 4793).shape = [16, 64, 1024] := by
    rw [← hw4793]
    exact shape_weight initSM initPM hInit initGoal_4793 (by native_decide) 4793 [16, 64, 1024] rfl rfl
  have hw4795 : denoteGraph sm initSM 4795 = denoteGraph pm initPM 4795 :=
    recon_weight initSM initPM hInit initGoal_4795 (by native_decide) 4795 rfl rfl rfl rfl
  have hwshape4795 : (denoteGraph pm initPM 4795).shape = [4, 64, 1024] := by
    rw [← hw4795]
    exact shape_weight initSM initPM hInit initGoal_4795 (by native_decide) 4795 [4, 64, 1024] rfl rfl
  obtain ⟨hq, hq0, hq1⟩ := perhead_2tp_val_shapes initSM initPM
    4794 7771 7772 7496 4793 14718 14731 4793 2048 1024 16 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (sm_perhead_4794_node initSM) (pm_perhead_7771_node initPM) (pm_perhead_7772_node initPM)
    hw4793 hx7496 hx0_14718 hx1_14731 hwshape4793
  obtain ⟨hk, hk0, hk1⟩ := perhead_2tp_val_shapes initSM initPM
    4796 7783 7784 7500 4795 14722 14735 4795 2048 1024 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (sm_perhead_4796_node initSM) (pm_perhead_7783_node initPM) (pm_perhead_7784_node initPM)
    hw4795 hx7500 hx0_14722 hx1_14735 hwshape4795
  exact recon_intermediateGoal_4801_of_inputs initSM initPM hInit
    hpos hq hk hq0 hq1 hk0 hk1 hp0 hp1

/-! ### Worker #7 — rotary chain pushed ONE MORE HOP up (residual input)

    `recon_intermediateGoal_4800/4801_of_residual_inputs` thread the rms-norm
    RESIDUAL input (sm 7487 = allGather[pm 14701, pm 14709]) + its two input shard
    shapes + positions, and derive the rms-output reconstruction (`hrms`, sm 4792 →
    pm 7769/7770) + its two shard shapes INTERNALLY via `rms_2tp_val_shapes` (the
    new rms gear). Still **6 hypotheses** — this is a boundary RELOCATION (not a
    count reduction): it moves the threaded fact from the rms output (4792) one hop
    closer to the true attention/MoE blocker (7487 ← 4790 = residual add ←
    FW_attn_sliding_window + FW_all2all_moe_gmm). The rms shard shapes are no longer
    threaded — they are derived (rms-norm is shape-preserving). -/
theorem recon_intermediateGoal_4800_of_residual_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hpos : denoteGraph sm initSM 4799
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7803, denoteGraph pm initPM 7804])
    (hres : denoteGraph sm initSM 7487
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14701, denoteGraph pm initPM 14709])
    (hr0 : (denoteGraph pm initPM 14701).shape = [2048, 1024])
    (hr1 : (denoteGraph pm initPM 14709).shape = [2048, 1024])
    (hp0 : (denoteGraph pm initPM 7803).shape = [2048, 1])
    (hp1 : (denoteGraph pm initPM 7804).shape = [2048, 1]) :
    InitGoalHolds pm.numRanks intermediateGoal_4800
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hw : denoteGraph sm initSM 4791 = denoteGraph pm initPM 4791 :=
    recon_weight initSM initPM hInit initGoal_4791 (by native_decide) 4791 rfl rfl rfl rfl
  obtain ⟨hrms, hs0, hs1⟩ := rms_2tp_val_shapes initSM initPM
    4792 7769 7770 7487 4791 14701 14709 4791 2048 1024
    (by norm_num) (by norm_num)
    (sm_rms_4792_node initSM) (pm_rms_7769_node initPM) (pm_rms_7770_node initPM)
    hw hres hr0 hr1
  exact recon_intermediateGoal_4800_of_rms_inputs initSM initPM hInit
    hpos hrms hs0 hs1 hp0 hp1

/-- K companion of `recon_intermediateGoal_4800_of_residual_inputs`; same 6
    hypotheses, rms output derived internally. -/
theorem recon_intermediateGoal_4801_of_residual_inputs (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hpos : denoteGraph sm initSM 4799
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7803, denoteGraph pm initPM 7804])
    (hres : denoteGraph sm initSM 7487
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 14701, denoteGraph pm initPM 14709])
    (hr0 : (denoteGraph pm initPM 14701).shape = [2048, 1024])
    (hr1 : (denoteGraph pm initPM 14709).shape = [2048, 1024])
    (hp0 : (denoteGraph pm initPM 7803).shape = [2048, 1])
    (hp1 : (denoteGraph pm initPM 7804).shape = [2048, 1]) :
    InitGoalHolds pm.numRanks intermediateGoal_4801
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  have hw : denoteGraph sm initSM 4791 = denoteGraph pm initPM 4791 :=
    recon_weight initSM initPM hInit initGoal_4791 (by native_decide) 4791 rfl rfl rfl rfl
  obtain ⟨hrms, hs0, hs1⟩ := rms_2tp_val_shapes initSM initPM
    4792 7769 7770 7487 4791 14701 14709 4791 2048 1024
    (by norm_num) (by norm_num)
    (sm_rms_4792_node initSM) (pm_rms_7769_node initPM) (pm_rms_7770_node initPM)
    hw hres hr0 hr1
  exact recon_intermediateGoal_4801_of_rms_inputs initSM initPM hInit
    hpos hrms hs0 hs1 hp0 hp1

/-! ### Worker #5 (2026-07-14) — adversarial hypothesis inventory for goal 4800

    `recon_intermediateGoal_4800` / `_4801` are the canonically-named deliverable
    theorems for the LOWEST-tid rotary 2-tp goal (4800/4801). They thread the
    EXACT minimal hypothesis set discovered by the adversarial audit: the three
    sharded rotary inputs (positions 4799, query 4794, key 4796) as 2-tp
    allGather reconstructions, plus their six PM shard shapes. The rotary
    cos/sin cache input (4691) is NOT threaded — it is closed internally via
    `sm_pm_rotary_cache_agree` from `hInit` (init tid 4691 is broadcast in PM to
    11855 through two `FW_multiref` nodes; worker #3's bridge).

    Classification of the three threaded value-eq inputs (see
    `~/HYPOTHESIS_INVENTORY.md`):
    - `hq` (4794) / `hk` (4796): DIRECT producing op `FW_per_head_mix_precision_linear`,
      each HAS an `intermediateGoal_*` (4794/4796) — but that goal's reconstruction is
      transitively gated on `FW_all2all_moe_gmm` + `FW_attn_sliding_window` (the MoE /
      attention region has no reconstruction template). These are the genuinely
      attention-shaped, irreducible hypotheses.
    - `hpos` (4799): the SM position tensor is an INIT LEAF (`initGoal_4799 ∈ initGoals`),
      sharded in PM by two `ChunkPrim` nodes (7803/7804). NO `intermediateGoal_4799`.
      This hypothesis is INDEPENDENT of attention — it is a ChunkPrim-of-init roundtrip
      (with a `[4096] → [2048,1]` reshape), reducible in principle from `hInit` alone,
      but distinct in kind from the attention-gated `hq`/`hk`. -/
theorem recon_intermediateGoal_4800 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hpos : denoteGraph sm initSM 4799
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7803, denoteGraph pm initPM 7804])
    (hq : denoteGraph sm initSM 4794
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7771, denoteGraph pm initPM 7772])
    (hk : denoteGraph sm initSM 4796
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7783, denoteGraph pm initPM 7784])
    (hq0 : (denoteGraph pm initPM 7771).shape = [2048, 16, 64])
    (hq1 : (denoteGraph pm initPM 7772).shape = [2048, 16, 64])
    (hk0 : (denoteGraph pm initPM 7783).shape = [2048, 4, 64])
    (hk1 : (denoteGraph pm initPM 7784).shape = [2048, 4, 64])
    (hp0 : (denoteGraph pm initPM 7803).shape = [2048, 1])
    (hp1 : (denoteGraph pm initPM 7804).shape = [2048, 1]) :
    InitGoalHolds pm.numRanks intermediateGoal_4800
      (denoteGraph sm initSM) (denoteGraph pm initPM) :=
  recon_intermediateGoal_4800_of_inputs initSM initPM hInit
    hpos hq hk hq0 hq1 hk0 hk1 hp0 hp1

/-- K' companion of `recon_intermediateGoal_4800`. Same threaded hypothesis set. -/
theorem recon_intermediateGoal_4801 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hpos : denoteGraph sm initSM 4799
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7803, denoteGraph pm initPM 7804])
    (hq : denoteGraph sm initSM 4794
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7771, denoteGraph pm initPM 7772])
    (hk : denoteGraph sm initSM 4796
        = allGatherPrimDimN 0 2 0 [denoteGraph pm initPM 7783, denoteGraph pm initPM 7784])
    (hq0 : (denoteGraph pm initPM 7771).shape = [2048, 16, 64])
    (hq1 : (denoteGraph pm initPM 7772).shape = [2048, 16, 64])
    (hk0 : (denoteGraph pm initPM 7783).shape = [2048, 4, 64])
    (hk1 : (denoteGraph pm initPM 7784).shape = [2048, 4, 64])
    (hp0 : (denoteGraph pm initPM 7803).shape = [2048, 1])
    (hp1 : (denoteGraph pm initPM 7804).shape = [2048, 1]) :
    InitGoalHolds pm.numRanks intermediateGoal_4801
      (denoteGraph sm initSM) (denoteGraph pm initPM) :=
  recon_intermediateGoal_4801_of_inputs initSM initPM hInit
    hpos hq hk hq0 hq1 hk0 hk1 hp0 hp1

/-- Full list of all 1151 intermediate reconstruction goals (infrastructure). -/
def all_intermediateGoals_list : List LineageGoal :=
  [
    intermediateGoal_4681, intermediateGoal_4683, intermediateGoal_4685, intermediateGoal_4687, intermediateGoal_4689, intermediateGoal_4692, intermediateGoal_4693, intermediateGoal_4696,
    intermediateGoal_4697, intermediateGoal_4698, intermediateGoal_4700, intermediateGoal_4701, intermediateGoal_4702, intermediateGoal_4703, intermediateGoal_4705, intermediateGoal_4706,
    intermediateGoal_4708, intermediateGoal_4709, intermediateGoal_4710, intermediateGoal_4714, intermediateGoal_4715, intermediateGoal_4717, intermediateGoal_4718, intermediateGoal_4719,
    intermediateGoal_4720, intermediateGoal_4722, intermediateGoal_4723, intermediateGoal_4724, intermediateGoal_4726, intermediateGoal_4727, intermediateGoal_4728, intermediateGoal_4729,
    intermediateGoal_4731, intermediateGoal_4732, intermediateGoal_4733, intermediateGoal_4734, intermediateGoal_4735, intermediateGoal_4736, intermediateGoal_4738, intermediateGoal_4740,
    intermediateGoal_4742, intermediateGoal_4744, intermediateGoal_4746, intermediateGoal_4747, intermediateGoal_4750, intermediateGoal_4751, intermediateGoal_4752, intermediateGoal_4754,
    intermediateGoal_4755, intermediateGoal_4756, intermediateGoal_4757, intermediateGoal_4759, intermediateGoal_4760, intermediateGoal_4762, intermediateGoal_4763, intermediateGoal_4764,
    intermediateGoal_4768, intermediateGoal_4769, intermediateGoal_4771, intermediateGoal_4772, intermediateGoal_4773, intermediateGoal_4774, intermediateGoal_4776, intermediateGoal_4777,
    intermediateGoal_4778, intermediateGoal_4780, intermediateGoal_4781, intermediateGoal_4782, intermediateGoal_4783, intermediateGoal_4785, intermediateGoal_4786, intermediateGoal_4787,
    intermediateGoal_4788, intermediateGoal_4789, intermediateGoal_4790, intermediateGoal_4792, intermediateGoal_4794, intermediateGoal_4796, intermediateGoal_4798, intermediateGoal_4800,
    intermediateGoal_4801, intermediateGoal_4804, intermediateGoal_4805, intermediateGoal_4806, intermediateGoal_4808, intermediateGoal_4809, intermediateGoal_4810, intermediateGoal_4811,
    intermediateGoal_4813, intermediateGoal_4814, intermediateGoal_4816, intermediateGoal_4817, intermediateGoal_4818, intermediateGoal_4822, intermediateGoal_4823, intermediateGoal_4825,
    intermediateGoal_4826, intermediateGoal_4827, intermediateGoal_4828, intermediateGoal_4830, intermediateGoal_4831, intermediateGoal_4832, intermediateGoal_4834, intermediateGoal_4835,
    intermediateGoal_4836, intermediateGoal_4837, intermediateGoal_4839, intermediateGoal_4840, intermediateGoal_4841, intermediateGoal_4842, intermediateGoal_4843, intermediateGoal_4844,
    intermediateGoal_4846, intermediateGoal_4848, intermediateGoal_4850, intermediateGoal_4852, intermediateGoal_4854, intermediateGoal_4855, intermediateGoal_4858, intermediateGoal_4859,
    intermediateGoal_4860, intermediateGoal_4862, intermediateGoal_4863, intermediateGoal_4864, intermediateGoal_4865, intermediateGoal_4867, intermediateGoal_4868, intermediateGoal_4870,
    intermediateGoal_4871, intermediateGoal_4872, intermediateGoal_4876, intermediateGoal_4877, intermediateGoal_4879, intermediateGoal_4880, intermediateGoal_4881, intermediateGoal_4882,
    intermediateGoal_4884, intermediateGoal_4885, intermediateGoal_4886, intermediateGoal_4888, intermediateGoal_4889, intermediateGoal_4890, intermediateGoal_4891, intermediateGoal_4893,
    intermediateGoal_4894, intermediateGoal_4895, intermediateGoal_4896, intermediateGoal_4897, intermediateGoal_4898, intermediateGoal_4900, intermediateGoal_4902, intermediateGoal_4904,
    intermediateGoal_4906, intermediateGoal_4908, intermediateGoal_4909, intermediateGoal_4912, intermediateGoal_4913, intermediateGoal_4914, intermediateGoal_4916, intermediateGoal_4917,
    intermediateGoal_4918, intermediateGoal_4919, intermediateGoal_4921, intermediateGoal_4922, intermediateGoal_4924, intermediateGoal_4925, intermediateGoal_4926, intermediateGoal_4930,
    intermediateGoal_4931, intermediateGoal_4933, intermediateGoal_4934, intermediateGoal_4935, intermediateGoal_4936, intermediateGoal_4938, intermediateGoal_4939, intermediateGoal_4940,
    intermediateGoal_4942, intermediateGoal_4943, intermediateGoal_4944, intermediateGoal_4945, intermediateGoal_4947, intermediateGoal_4948, intermediateGoal_4949, intermediateGoal_4950,
    intermediateGoal_4951, intermediateGoal_4952, intermediateGoal_4954, intermediateGoal_4956, intermediateGoal_4958, intermediateGoal_4960, intermediateGoal_4962, intermediateGoal_4963,
    intermediateGoal_4966, intermediateGoal_4967, intermediateGoal_4968, intermediateGoal_4970, intermediateGoal_4971, intermediateGoal_4972, intermediateGoal_4973, intermediateGoal_4975,
    intermediateGoal_4976, intermediateGoal_4978, intermediateGoal_4979, intermediateGoal_4980, intermediateGoal_4984, intermediateGoal_4985, intermediateGoal_4987, intermediateGoal_4988,
    intermediateGoal_4989, intermediateGoal_4990, intermediateGoal_4992, intermediateGoal_4993, intermediateGoal_4994, intermediateGoal_4996, intermediateGoal_4997, intermediateGoal_4998,
    intermediateGoal_4999, intermediateGoal_5001, intermediateGoal_5002, intermediateGoal_5003, intermediateGoal_5004, intermediateGoal_5005, intermediateGoal_5006, intermediateGoal_5008,
    intermediateGoal_5010, intermediateGoal_5012, intermediateGoal_5014, intermediateGoal_5016, intermediateGoal_5017, intermediateGoal_5020, intermediateGoal_5021, intermediateGoal_5022,
    intermediateGoal_5024, intermediateGoal_5025, intermediateGoal_5026, intermediateGoal_5027, intermediateGoal_5029, intermediateGoal_5030, intermediateGoal_5032, intermediateGoal_5033,
    intermediateGoal_5034, intermediateGoal_5038, intermediateGoal_5039, intermediateGoal_5041, intermediateGoal_5042, intermediateGoal_5043, intermediateGoal_5044, intermediateGoal_5046,
    intermediateGoal_5047, intermediateGoal_5048, intermediateGoal_5050, intermediateGoal_5051, intermediateGoal_5052, intermediateGoal_5053, intermediateGoal_5055, intermediateGoal_5056,
    intermediateGoal_5057, intermediateGoal_5058, intermediateGoal_5059, intermediateGoal_5060, intermediateGoal_5062, intermediateGoal_5064, intermediateGoal_5066, intermediateGoal_5068,
    intermediateGoal_5070, intermediateGoal_5071, intermediateGoal_5074, intermediateGoal_5075, intermediateGoal_5076, intermediateGoal_5078, intermediateGoal_5079, intermediateGoal_5080,
    intermediateGoal_5081, intermediateGoal_5083, intermediateGoal_5084, intermediateGoal_5086, intermediateGoal_5087, intermediateGoal_5088, intermediateGoal_5092, intermediateGoal_5093,
    intermediateGoal_5095, intermediateGoal_5096, intermediateGoal_5097, intermediateGoal_5098, intermediateGoal_5100, intermediateGoal_5101, intermediateGoal_5102, intermediateGoal_5104,
    intermediateGoal_5105, intermediateGoal_5106, intermediateGoal_5107, intermediateGoal_5109, intermediateGoal_5110, intermediateGoal_5111, intermediateGoal_5112, intermediateGoal_5113,
    intermediateGoal_5114, intermediateGoal_5116, intermediateGoal_5118, intermediateGoal_5120, intermediateGoal_5122, intermediateGoal_5124, intermediateGoal_5125, intermediateGoal_5128,
    intermediateGoal_5129, intermediateGoal_5130, intermediateGoal_5132, intermediateGoal_5133, intermediateGoal_5134, intermediateGoal_5135, intermediateGoal_5137, intermediateGoal_5138,
    intermediateGoal_5140, intermediateGoal_5141, intermediateGoal_5142, intermediateGoal_5146, intermediateGoal_5147, intermediateGoal_5149, intermediateGoal_5150, intermediateGoal_5151,
    intermediateGoal_5152, intermediateGoal_5154, intermediateGoal_5155, intermediateGoal_5156, intermediateGoal_5158, intermediateGoal_5159, intermediateGoal_5160, intermediateGoal_5161,
    intermediateGoal_5163, intermediateGoal_5164, intermediateGoal_5165, intermediateGoal_5166, intermediateGoal_5167, intermediateGoal_5168, intermediateGoal_5170, intermediateGoal_5172,
    intermediateGoal_5174, intermediateGoal_5176, intermediateGoal_5178, intermediateGoal_5179, intermediateGoal_5182, intermediateGoal_5183, intermediateGoal_5184, intermediateGoal_5186,
    intermediateGoal_5187, intermediateGoal_5188, intermediateGoal_5189, intermediateGoal_5191, intermediateGoal_5192, intermediateGoal_5194, intermediateGoal_5195, intermediateGoal_5196,
    intermediateGoal_5200, intermediateGoal_5201, intermediateGoal_5203, intermediateGoal_5204, intermediateGoal_5205, intermediateGoal_5206, intermediateGoal_5208, intermediateGoal_5209,
    intermediateGoal_5210, intermediateGoal_5212, intermediateGoal_5213, intermediateGoal_5214, intermediateGoal_5215, intermediateGoal_5217, intermediateGoal_5218, intermediateGoal_5219,
    intermediateGoal_5220, intermediateGoal_5221, intermediateGoal_5222, intermediateGoal_5224, intermediateGoal_5226, intermediateGoal_5228, intermediateGoal_5230, intermediateGoal_5232,
    intermediateGoal_5233, intermediateGoal_5236, intermediateGoal_5237, intermediateGoal_5238, intermediateGoal_5240, intermediateGoal_5241, intermediateGoal_5242, intermediateGoal_5243,
    intermediateGoal_5245, intermediateGoal_5246, intermediateGoal_5248, intermediateGoal_5249, intermediateGoal_5250, intermediateGoal_5254, intermediateGoal_5255, intermediateGoal_5257,
    intermediateGoal_5258, intermediateGoal_5259, intermediateGoal_5260, intermediateGoal_5262, intermediateGoal_5263, intermediateGoal_5264, intermediateGoal_5266, intermediateGoal_5267,
    intermediateGoal_5268, intermediateGoal_5269, intermediateGoal_5271, intermediateGoal_5272, intermediateGoal_5273, intermediateGoal_5274, intermediateGoal_5275, intermediateGoal_5276,
    intermediateGoal_5278, intermediateGoal_5280, intermediateGoal_5282, intermediateGoal_5284, intermediateGoal_5286, intermediateGoal_5287, intermediateGoal_5290, intermediateGoal_5291,
    intermediateGoal_5292, intermediateGoal_5294, intermediateGoal_5295, intermediateGoal_5296, intermediateGoal_5297, intermediateGoal_5299, intermediateGoal_5300, intermediateGoal_5302,
    intermediateGoal_5303, intermediateGoal_5304, intermediateGoal_5308, intermediateGoal_5309, intermediateGoal_5311, intermediateGoal_5312, intermediateGoal_5313, intermediateGoal_5314,
    intermediateGoal_5316, intermediateGoal_5317, intermediateGoal_5318, intermediateGoal_5320, intermediateGoal_5321, intermediateGoal_5322, intermediateGoal_5323, intermediateGoal_5325,
    intermediateGoal_5326, intermediateGoal_5327, intermediateGoal_5328, intermediateGoal_5329, intermediateGoal_5330, intermediateGoal_5332, intermediateGoal_5334, intermediateGoal_5336,
    intermediateGoal_5338, intermediateGoal_5340, intermediateGoal_5342, intermediateGoal_5343, intermediateGoal_5344, intermediateGoal_5347, intermediateGoal_5348, intermediateGoal_5349,
    intermediateGoal_5351, intermediateGoal_5352, intermediateGoal_5353, intermediateGoal_5354, intermediateGoal_5356, intermediateGoal_5357, intermediateGoal_5359, intermediateGoal_5360,
    intermediateGoal_5361, intermediateGoal_5365, intermediateGoal_5366, intermediateGoal_5368, intermediateGoal_5369, intermediateGoal_5370, intermediateGoal_5371, intermediateGoal_5373,
    intermediateGoal_5374, intermediateGoal_5375, intermediateGoal_5377, intermediateGoal_5378, intermediateGoal_5379, intermediateGoal_5380, intermediateGoal_5382, intermediateGoal_5383,
    intermediateGoal_5384, intermediateGoal_5385, intermediateGoal_5386, intermediateGoal_5387, intermediateGoal_5389, intermediateGoal_5391, intermediateGoal_5392, intermediateGoal_5393,
    intermediateGoal_5396, intermediateGoal_5397, intermediateGoal_5398, intermediateGoal_5400, intermediateGoal_5401, intermediateGoal_5402, intermediateGoal_5403, intermediateGoal_5405,
    intermediateGoal_5406, intermediateGoal_5408, intermediateGoal_5409, intermediateGoal_5410, intermediateGoal_5414, intermediateGoal_5415, intermediateGoal_5417, intermediateGoal_5418,
    intermediateGoal_5419, intermediateGoal_5420, intermediateGoal_5422, intermediateGoal_5423, intermediateGoal_5424, intermediateGoal_5426, intermediateGoal_5427, intermediateGoal_5428,
    intermediateGoal_5429, intermediateGoal_5431, intermediateGoal_5432, intermediateGoal_5433, intermediateGoal_5434, intermediateGoal_5435, intermediateGoal_5436, intermediateGoal_5438,
    intermediateGoal_5440, intermediateGoal_5441, intermediateGoal_5442, intermediateGoal_5445, intermediateGoal_5446, intermediateGoal_5447, intermediateGoal_5449, intermediateGoal_5450,
    intermediateGoal_5451, intermediateGoal_5452, intermediateGoal_5454, intermediateGoal_5455, intermediateGoal_5457, intermediateGoal_5458, intermediateGoal_5459, intermediateGoal_5463,
    intermediateGoal_5464, intermediateGoal_5466, intermediateGoal_5467, intermediateGoal_5468, intermediateGoal_5469, intermediateGoal_5471, intermediateGoal_5472, intermediateGoal_5473,
    intermediateGoal_5475, intermediateGoal_5476, intermediateGoal_5477, intermediateGoal_5478, intermediateGoal_5480, intermediateGoal_5481, intermediateGoal_5482, intermediateGoal_5483,
    intermediateGoal_5484, intermediateGoal_5485, intermediateGoal_5487, intermediateGoal_5489, intermediateGoal_5490, intermediateGoal_5491, intermediateGoal_5494, intermediateGoal_5495,
    intermediateGoal_5496, intermediateGoal_5498, intermediateGoal_5499, intermediateGoal_5500, intermediateGoal_5501, intermediateGoal_5503, intermediateGoal_5504, intermediateGoal_5506,
    intermediateGoal_5507, intermediateGoal_5508, intermediateGoal_5512, intermediateGoal_5513, intermediateGoal_5515, intermediateGoal_5516, intermediateGoal_5517, intermediateGoal_5518,
    intermediateGoal_5520, intermediateGoal_5521, intermediateGoal_5522, intermediateGoal_5524, intermediateGoal_5525, intermediateGoal_5526, intermediateGoal_5527, intermediateGoal_5529,
    intermediateGoal_5530, intermediateGoal_5531, intermediateGoal_5532, intermediateGoal_5533, intermediateGoal_5534, intermediateGoal_5536, intermediateGoal_5538, intermediateGoal_5539,
    intermediateGoal_5540, intermediateGoal_5543, intermediateGoal_5544, intermediateGoal_5545, intermediateGoal_5547, intermediateGoal_5548, intermediateGoal_5549, intermediateGoal_5550,
    intermediateGoal_5552, intermediateGoal_5553, intermediateGoal_5555, intermediateGoal_5556, intermediateGoal_5557, intermediateGoal_5561, intermediateGoal_5562, intermediateGoal_5564,
    intermediateGoal_5565, intermediateGoal_5566, intermediateGoal_5567, intermediateGoal_5569, intermediateGoal_5570, intermediateGoal_5571, intermediateGoal_5573, intermediateGoal_5574,
    intermediateGoal_5575, intermediateGoal_5576, intermediateGoal_5578, intermediateGoal_5579, intermediateGoal_5580, intermediateGoal_5581, intermediateGoal_5582, intermediateGoal_5583,
    intermediateGoal_5585, intermediateGoal_5587, intermediateGoal_5588, intermediateGoal_5589, intermediateGoal_5592, intermediateGoal_5593, intermediateGoal_5594, intermediateGoal_5596,
    intermediateGoal_5597, intermediateGoal_5598, intermediateGoal_5599, intermediateGoal_5601, intermediateGoal_5602, intermediateGoal_5604, intermediateGoal_5605, intermediateGoal_5606,
    intermediateGoal_5610, intermediateGoal_5611, intermediateGoal_5613, intermediateGoal_5614, intermediateGoal_5615, intermediateGoal_5616, intermediateGoal_5618, intermediateGoal_5619,
    intermediateGoal_5620, intermediateGoal_5622, intermediateGoal_5623, intermediateGoal_5624, intermediateGoal_5625, intermediateGoal_5627, intermediateGoal_5628, intermediateGoal_5629,
    intermediateGoal_5630, intermediateGoal_5631, intermediateGoal_5632, intermediateGoal_5634, intermediateGoal_5636, intermediateGoal_5637, intermediateGoal_5638, intermediateGoal_5641,
    intermediateGoal_5642, intermediateGoal_5643, intermediateGoal_5645, intermediateGoal_5646, intermediateGoal_5647, intermediateGoal_5648, intermediateGoal_5650, intermediateGoal_5651,
    intermediateGoal_5653, intermediateGoal_5654, intermediateGoal_5655, intermediateGoal_5659, intermediateGoal_5660, intermediateGoal_5662, intermediateGoal_5663, intermediateGoal_5664,
    intermediateGoal_5665, intermediateGoal_5667, intermediateGoal_5668, intermediateGoal_5669, intermediateGoal_5671, intermediateGoal_5672, intermediateGoal_5673, intermediateGoal_5674,
    intermediateGoal_5676, intermediateGoal_5677, intermediateGoal_5678, intermediateGoal_5679, intermediateGoal_5680, intermediateGoal_5681, intermediateGoal_5683, intermediateGoal_5685,
    intermediateGoal_5686, intermediateGoal_5687, intermediateGoal_5690, intermediateGoal_5691, intermediateGoal_5692, intermediateGoal_5694, intermediateGoal_5695, intermediateGoal_5696,
    intermediateGoal_5697, intermediateGoal_5699, intermediateGoal_5700, intermediateGoal_5702, intermediateGoal_5703, intermediateGoal_5704, intermediateGoal_5708, intermediateGoal_5709,
    intermediateGoal_5711, intermediateGoal_5712, intermediateGoal_5713, intermediateGoal_5714, intermediateGoal_5716, intermediateGoal_5717, intermediateGoal_5718, intermediateGoal_5720,
    intermediateGoal_5721, intermediateGoal_5722, intermediateGoal_5723, intermediateGoal_5725, intermediateGoal_5726, intermediateGoal_5727, intermediateGoal_5728, intermediateGoal_5729,
    intermediateGoal_5730, intermediateGoal_5732, intermediateGoal_5734, intermediateGoal_5735, intermediateGoal_5736, intermediateGoal_5739, intermediateGoal_5740, intermediateGoal_5741,
    intermediateGoal_5743, intermediateGoal_5744, intermediateGoal_5745, intermediateGoal_5746, intermediateGoal_5748, intermediateGoal_5749, intermediateGoal_5751, intermediateGoal_5752,
    intermediateGoal_5753, intermediateGoal_5757, intermediateGoal_5758, intermediateGoal_5760, intermediateGoal_5761, intermediateGoal_5762, intermediateGoal_5763, intermediateGoal_5765,
    intermediateGoal_5766, intermediateGoal_5767, intermediateGoal_5769, intermediateGoal_5770, intermediateGoal_5771, intermediateGoal_5772, intermediateGoal_5774, intermediateGoal_5775,
    intermediateGoal_5776, intermediateGoal_5777, intermediateGoal_5778, intermediateGoal_5779, intermediateGoal_5781, intermediateGoal_5783, intermediateGoal_5784, intermediateGoal_5785,
    intermediateGoal_5788, intermediateGoal_5789, intermediateGoal_5790, intermediateGoal_5792, intermediateGoal_5793, intermediateGoal_5794, intermediateGoal_5795, intermediateGoal_5797,
    intermediateGoal_5798, intermediateGoal_5800, intermediateGoal_5801, intermediateGoal_5802, intermediateGoal_5806, intermediateGoal_5807, intermediateGoal_5809, intermediateGoal_5810,
    intermediateGoal_5811, intermediateGoal_5812, intermediateGoal_5814, intermediateGoal_5815, intermediateGoal_5816, intermediateGoal_5818, intermediateGoal_5819, intermediateGoal_5820,
    intermediateGoal_5821, intermediateGoal_5823, intermediateGoal_5824, intermediateGoal_5825, intermediateGoal_5826, intermediateGoal_5827, intermediateGoal_5828, intermediateGoal_5830,
    intermediateGoal_5832, intermediateGoal_5833, intermediateGoal_5834, intermediateGoal_5837, intermediateGoal_5838, intermediateGoal_5839, intermediateGoal_5841, intermediateGoal_5842,
    intermediateGoal_5843, intermediateGoal_5844, intermediateGoal_5846, intermediateGoal_5847, intermediateGoal_5849, intermediateGoal_5850, intermediateGoal_5851, intermediateGoal_5855,
    intermediateGoal_5856, intermediateGoal_5858, intermediateGoal_5859, intermediateGoal_5860, intermediateGoal_5861, intermediateGoal_5863, intermediateGoal_5864, intermediateGoal_5865,
    intermediateGoal_5867, intermediateGoal_5868, intermediateGoal_5869, intermediateGoal_5870, intermediateGoal_5872, intermediateGoal_5873, intermediateGoal_5874, intermediateGoal_5875,
    intermediateGoal_5876, intermediateGoal_5877, intermediateGoal_5879, intermediateGoal_5881, intermediateGoal_5882, intermediateGoal_5883, intermediateGoal_5886, intermediateGoal_5887,
    intermediateGoal_5888, intermediateGoal_5890, intermediateGoal_5891, intermediateGoal_5892, intermediateGoal_5893, intermediateGoal_5895, intermediateGoal_5896, intermediateGoal_5898,
    intermediateGoal_5899, intermediateGoal_5900, intermediateGoal_5904, intermediateGoal_5905, intermediateGoal_5907, intermediateGoal_5908, intermediateGoal_5909, intermediateGoal_5910,
    intermediateGoal_5912, intermediateGoal_5913, intermediateGoal_5914, intermediateGoal_5916, intermediateGoal_5917, intermediateGoal_5918, intermediateGoal_5919, intermediateGoal_5921,
    intermediateGoal_5922, intermediateGoal_5923, intermediateGoal_5924, intermediateGoal_5925, intermediateGoal_5926, intermediateGoal_5928, intermediateGoal_5930, intermediateGoal_7383,
    intermediateGoal_7387, intermediateGoal_7392, intermediateGoal_7396, intermediateGoal_7400, intermediateGoal_7404, intermediateGoal_7408, intermediateGoal_7415, intermediateGoal_7419,
    intermediateGoal_7423, intermediateGoal_7427, intermediateGoal_7431, intermediateGoal_7435, intermediateGoal_7439, intermediateGoal_7444, intermediateGoal_7448, intermediateGoal_7452,
    intermediateGoal_7456, intermediateGoal_7460, intermediateGoal_7467, intermediateGoal_7471, intermediateGoal_7475, intermediateGoal_7479, intermediateGoal_7483, intermediateGoal_7487,
    intermediateGoal_7491, intermediateGoal_7496, intermediateGoal_7500, intermediateGoal_7504, intermediateGoal_7508, intermediateGoal_7512, intermediateGoal_7519, intermediateGoal_7523,
    intermediateGoal_7527, intermediateGoal_7531, intermediateGoal_7535, intermediateGoal_7539, intermediateGoal_7543, intermediateGoal_7548, intermediateGoal_7552, intermediateGoal_7556,
    intermediateGoal_7560, intermediateGoal_7564, intermediateGoal_7571, intermediateGoal_7575, intermediateGoal_7579, intermediateGoal_7583, intermediateGoal_7587, intermediateGoal_7591,
    intermediateGoal_7595, intermediateGoal_7600, intermediateGoal_7604, intermediateGoal_7608, intermediateGoal_7612, intermediateGoal_7616, intermediateGoal_7623, intermediateGoal_7627,
    intermediateGoal_7631, intermediateGoal_7635, intermediateGoal_7639, intermediateGoal_7643, intermediateGoal_7647, intermediateGoal_7652, intermediateGoal_7656, intermediateGoal_7660,
    intermediateGoal_7664, intermediateGoal_7668, intermediateGoal_7675, intermediateGoal_7679, intermediateGoal_7683, intermediateGoal_7687, intermediateGoal_7691, intermediateGoal_7695,
    intermediateGoal_7699, intermediateGoal_7704, intermediateGoal_7708, intermediateGoal_7712, intermediateGoal_7716, intermediateGoal_7720, intermediateGoal_7727, intermediateGoal_7731,
    intermediateGoal_7735, intermediateGoal_7739, intermediateGoal_7743, intermediateGoal_7747, intermediateGoal_7751, intermediateGoal_7756, intermediateGoal_7760, intermediateGoal_7764,
    intermediateGoal_7768, intermediateGoal_7772, intermediateGoal_7779, intermediateGoal_7783, intermediateGoal_7787, intermediateGoal_7791, intermediateGoal_7795, intermediateGoal_7799,
    intermediateGoal_7803, intermediateGoal_7808, intermediateGoal_7812, intermediateGoal_7816, intermediateGoal_7820, intermediateGoal_7824, intermediateGoal_7831, intermediateGoal_7835,
    intermediateGoal_7839, intermediateGoal_7843, intermediateGoal_7847, intermediateGoal_7851, intermediateGoal_7855, intermediateGoal_7860, intermediateGoal_7864, intermediateGoal_7868,
    intermediateGoal_7872, intermediateGoal_7876, intermediateGoal_7883, intermediateGoal_7887, intermediateGoal_7891, intermediateGoal_7895, intermediateGoal_7899, intermediateGoal_7903,
    intermediateGoal_7907, intermediateGoal_7912, intermediateGoal_7916, intermediateGoal_7920, intermediateGoal_7924, intermediateGoal_7928, intermediateGoal_7935, intermediateGoal_7939,
    intermediateGoal_7943, intermediateGoal_7947, intermediateGoal_7951, intermediateGoal_7955, intermediateGoal_7959, intermediateGoal_7964, intermediateGoal_7968, intermediateGoal_7972,
    intermediateGoal_7976, intermediateGoal_7980, intermediateGoal_7987, intermediateGoal_7991, intermediateGoal_7995, intermediateGoal_7999, intermediateGoal_8003, intermediateGoal_8007,
    intermediateGoal_8011, intermediateGoal_8015, intermediateGoal_8019, intermediateGoal_8033, intermediateGoal_8037, intermediateGoal_8041, intermediateGoal_8045, intermediateGoal_8049,
    intermediateGoal_8053, intermediateGoal_8057, intermediateGoal_8061, intermediateGoal_8065, intermediateGoal_8069, intermediateGoal_8073, intermediateGoal_8077, intermediateGoal_8091,
    intermediateGoal_8095, intermediateGoal_8099, intermediateGoal_8103, intermediateGoal_8107, intermediateGoal_8111, intermediateGoal_8115, intermediateGoal_8119, intermediateGoal_8123,
    intermediateGoal_8127, intermediateGoal_8131, intermediateGoal_8135, intermediateGoal_8139, intermediateGoal_8143, intermediateGoal_8147, intermediateGoal_8151, intermediateGoal_8158,
    intermediateGoal_8162, intermediateGoal_8166, intermediateGoal_8170, intermediateGoal_8174, intermediateGoal_8178, intermediateGoal_8182, intermediateGoal_8186, intermediateGoal_8190,
    intermediateGoal_8197, intermediateGoal_8201, intermediateGoal_8205, intermediateGoal_8209, intermediateGoal_8213, intermediateGoal_8217, intermediateGoal_8221, intermediateGoal_8225,
    intermediateGoal_8229, intermediateGoal_8236, intermediateGoal_8240, intermediateGoal_8244, intermediateGoal_8248, intermediateGoal_8252, intermediateGoal_8256, intermediateGoal_8260,
    intermediateGoal_8264, intermediateGoal_8268, intermediateGoal_8275, intermediateGoal_8279, intermediateGoal_8283, intermediateGoal_8287, intermediateGoal_8291, intermediateGoal_8295,
    intermediateGoal_8299, intermediateGoal_8303, intermediateGoal_8307, intermediateGoal_8314, intermediateGoal_8318, intermediateGoal_8322, intermediateGoal_8326, intermediateGoal_8330,
    intermediateGoal_8334, intermediateGoal_8338, intermediateGoal_8342, intermediateGoal_8346, intermediateGoal_8353, intermediateGoal_8357, intermediateGoal_8361, intermediateGoal_8365,
    intermediateGoal_8369, intermediateGoal_8373, intermediateGoal_8377, intermediateGoal_8381, intermediateGoal_8385, intermediateGoal_8392, intermediateGoal_8396, intermediateGoal_8400,
    intermediateGoal_8404, intermediateGoal_8408, intermediateGoal_8412, intermediateGoal_8416, intermediateGoal_8420, intermediateGoal_8424, intermediateGoal_8431, intermediateGoal_8435,
    intermediateGoal_8439, intermediateGoal_8443, intermediateGoal_8447, intermediateGoal_8451, intermediateGoal_8455, intermediateGoal_8459, intermediateGoal_8463, intermediateGoal_8470,
    intermediateGoal_8474, intermediateGoal_8478, intermediateGoal_8482, intermediateGoal_8486, intermediateGoal_8490, intermediateGoal_8494, intermediateGoal_8498, intermediateGoal_8502,
    intermediateGoal_8509, intermediateGoal_8513, intermediateGoal_8517, intermediateGoal_8521, intermediateGoal_8525, intermediateGoal_8529, intermediateGoal_8533, intermediateGoal_8537,
    intermediateGoal_8541, intermediateGoal_8548, intermediateGoal_8552, intermediateGoal_8556, intermediateGoal_8560, intermediateGoal_8564, intermediateGoal_8568, intermediateGoal_8572,
    intermediateGoal_8576, intermediateGoal_8580, intermediateGoal_8587, intermediateGoal_8591, intermediateGoal_8595, intermediateGoal_8599, intermediateGoal_8603]

/-- Sub-list of intermediate goals proven in this file (layer-0 replicated prefix:
    FW_float, FW_rms_norm, FW_per_head_mix_precision_linear categories). -/
def all_intermediateGoals_proven_list : List LineageGoal :=
  [ intermediateGoal_4681, intermediateGoal_4683, intermediateGoal_4685,
    intermediateGoal_4687, intermediateGoal_4689,
    intermediateGoal_7383, intermediateGoal_7387, intermediateGoal_7392,
    intermediateGoal_7396, intermediateGoal_7400,
    intermediateGoal_4692, intermediateGoal_4693 ]

/-- Partial assembly: `InitGoalsHold` for the proven sub-list, joined from the
    per-goal reconstruction lemmas. Kept SEPARATE from the (unproven) ideal
    `all_intermediateGoals_hold` over the full list, per ground rule R6. -/
theorem all_intermediateGoals_proven_hold
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalsHold pm.numRanks all_intermediateGoals_proven_list
      (denoteGraph sm initSM) (denoteGraph pm initPM) := by
  intro g hg
  simp only [all_intermediateGoals_proven_list, List.mem_cons, List.mem_singleton] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h]; exact recon_intermediateGoal_4681 initSM initPM hSM hPM hInit
  · rw [h]; exact recon_intermediateGoal_4683 initSM initPM hSM hPM hInit
  · rw [h]; exact recon_intermediateGoal_4685 initSM initPM hSM hPM hInit
  · rw [h]; exact recon_intermediateGoal_4687 initSM initPM hSM hPM hInit
  · rw [h]; exact recon_intermediateGoal_4689 initSM initPM hSM hPM hInit
  · rw [h]; exact recon_intermediateGoal_7383 initSM initPM hSM hPM hInit
  · rw [h]; exact recon_intermediateGoal_7387 initSM initPM hSM hPM hInit
  · rw [h]; exact recon_intermediateGoal_7392 initSM initPM hSM hPM hInit
  · rw [h]; exact recon_intermediateGoal_7396 initSM initPM hSM hPM hInit
  · rw [h]; exact recon_intermediateGoal_7400 initSM initPM hSM hPM hInit
  · rw [h]; exact recon_intermediateGoal_4692 initSM initPM hSM hPM hInit
  · rcases h with h | h
    · rw [h]; exact recon_intermediateGoal_4693 initSM initPM hSM hPM hInit
    · exact absurd h (by simp)

/-- **Ring-attention restatement of the proven assembly (worker #9).**
    Every proven layer-0 goal is written strictly before the first ring-attn
    node in both graphs, so the plain reconstruction transfers verbatim to the
    value-faithful `denoteGraph_ringAttn` denotation via `recon_ringAttn_of_plain`.
    This is the ring-attn analog of `all_intermediateGoals_proven_hold`; the
    plain version is kept intact for existing consumers. -/
theorem all_intermediateGoals_proven_hold_ringAttn
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalsHold pm.numRanks all_intermediateGoals_proven_list
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  intro g hg
  simp only [all_intermediateGoals_proven_list, List.mem_cons, List.mem_singleton] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_4681 initSM initPM hSM hPM hInit)
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_4683 initSM initPM hSM hPM hInit)
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_4685 initSM initPM hSM hPM hInit)
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_4687 initSM initPM hSM hPM hInit)
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_4689 initSM initPM hSM hPM hInit)
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_7383 initSM initPM hSM hPM hInit)
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_7387 initSM initPM hSM hPM hInit)
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_7392 initSM initPM hSM hPM hInit)
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_7396 initSM initPM hSM hPM hInit)
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_7400 initSM initPM hSM hPM hInit)
  · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
      (recon_intermediateGoal_4692 initSM initPM hSM hPM hInit)
  · rcases h with h | h
    · rw [h]; exact recon_ringAttn_of_plain _ initSM initPM (by native_decide) (by native_decide)
        (recon_intermediateGoal_4693 initSM initPM hSM hPM hInit)
    · exact absurd h (by simp)

/-- The ring-attn proven list: the 12 upstream (pre-attention) goals PLUS the
    layer-0 attention goal `4696`, which is genuinely unconditional only over the
    value-faithful `denoteGraph_ringAttn`. -/
def all_intermediateGoals_proven_list_ringAttn : List LineageGoal :=
  intermediateGoal_4696 :: all_intermediateGoals_proven_list

/-- **Full ring-attn proven assembly (worker #9).** `InitGoalsHold` over the
    ring denotation for all 12 upstream goals AND the layer-0 attention goal
    `4696` — the first genuinely unconditional 2-tp sharded attention goal. -/
theorem all_intermediateGoals_proven_hold_ringAttn_with_attn
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalsHold pm.numRanks all_intermediateGoals_proven_list_ringAttn
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  intro g hg
  rw [all_intermediateGoals_proven_list_ringAttn, List.mem_cons] at hg
  rcases hg with h | h
  · rw [h]; exact recon_intermediateGoal_4696_ringAttn initSM initPM hSM hPM hInit
  · exact all_intermediateGoals_proven_hold_ringAttn initSM initPM hSM hPM hInit g h

end TrainVerify.Denote.GeneratedPatterns
