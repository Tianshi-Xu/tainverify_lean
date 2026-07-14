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

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

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
theorem storeSet_zip_replicate_mem (s : Store) (v : Tensor) :
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
  exact storeSet_zip_replicate_mem s (s xTid) outs tid hmem

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

end TrainVerify.Denote.GeneratedPatterns
