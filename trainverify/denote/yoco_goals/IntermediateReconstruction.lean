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

end TrainVerify.Denote.GeneratedPatterns
