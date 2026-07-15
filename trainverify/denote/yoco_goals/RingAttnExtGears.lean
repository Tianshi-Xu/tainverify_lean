/- Extended ring-attention 2-tp reconstruction gears (worker #15).

   Two families of standalone, fully-parametrized gears used by worker #16 to
   discharge the L2–L11 sliding-window rotary boundary and the `FW_attn_zigzag`
   cross-attention 2-tp intermediate goals over `denoteGraph_ringAttn`:

   1. `recon_attn_rotary_2tp_layer` (+ `_snd`) — the per-rank rotary boundary.
      For sliding layers L2–L11 the PM graph re-computes `FW_rotary_embedding`
      per rank (e.g. pm nodes 7805/7806), so Q'/K' feeding attention come from
      per-rank rotary on chunks of the shared SM cos/sin cache and the per-rank
      Q/K linear outputs. The gear commutes rotary with the dim-0 (token) gather
      of the two shards: `rotary(csP, gather[pos0,pos1], gather[q0,q1],
      gather[k0,k1]) = gather[rotary(csP,pos0,q0,k0), rotary(csP,pos1,q1,k1)]`,
      then packages the SM/PM value+shape equalities as an `InitGoalHolds`.
      Backed by `fw_rotary_embedding_allGather0_commute_2` (Denote.lean) via
      `rotary_fst_gather_commute` / `rotary_snd_gather_commute` (worker #10) —
      pure tensor algebra, so the same commute holds verbatim over the
      ring-attention store `denoteGraph_ringAttn`.

   2. `recon_attn_zigzag_2tp_layer` — the `FW_attn_zigzag` (windowLeft=0) analog
      of worker #10's `recon_attn_sliding_window_2tp_layer`. `FW_attn_zigzag`'s
      ring-attention denotation (`applyNodeRingAttn_zigzag`) has exactly the same
      allgather→attn→chunk shape as the sliding-window one, so this gear reuses
      `applyNodeRingAttn_zigzag_reconstruction_2_of_buddy_pair` and
      `applyNodeRingAttn_zigzag_pair_eq_chunk` (worker #9, Pattern_3.lean) in
      place of the sliding-window versions. Everything else (buddy detection,
      Q'/K'/V full reconstruction, cu-seqlens agreement, param agreement,
      full-output shapes, goal metadata) is identical.

   Zero `sorry`, zero user axiom; kernel triple + `native_decide` only. The gears
   have clean signatures — worker #16 discharges only per-tid mechanical facts
   (node reductions, buddy `native_decide`s, upstream input reconstructions,
   shard shapes) with no further gear-hypothesis expansion.
-/
import denote.yoco_goals.IntermediateReconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-! ### Rotary 2-tp gears over `denoteGraph_ringAttn` (L2–L11 boundary)

    The ring-attention analog of worker #10's `recon_rotary_2tp_fst`/`snd`. The
    only change is that stores are `denoteGraph_ringAttn sm/pm` (not plain
    `denoteGraph`); since `FW_rotary_embedding` is NOT a ring-attention op, the
    only effect of the ring denotation is on the *fold* that produces each input
    tensor — which the caller abstracts through the node-reduction hypotheses
    `hsmNode`/`hpm0`/`hpm1`. The rotary commute itself is pure tensor algebra
    (`rotary_fst_gather_commute`), independent of the store. -/

/-- Parametrized 2-tp rotary **Q'** (`.1`) reconstruction gear over ring-attn. -/
theorem recon_attn_rotary_2tp_layer
    (initSM initPM : Store) (g : LineageGoal)
    (T p0 p1 csS posS qS kS csP pos0 q0 k0 pos1 q1 k1 : Tid) (L nh kh d : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hkh : 0 < kh) (hd : 0 < d)
    (htp : g.tps = [{rank := 0, tid := p0}, {rank := 1, tid := p1}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = T)
    (htsShape : g.tsShape = [L * 2, nh, d]) (htpShapes : g.tpShapes = [[L, nh, d], [L, nh, d]])
    (hne : ([L, nh, d] : Shape) ≠ [1])
    (hsmNode : denoteGraph_ringAttn sm initSM T
        = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM csS) (denoteGraph_ringAttn sm initSM posS)
            (denoteGraph_ringAttn sm initSM qS) (denoteGraph_ringAttn sm initSM kS) nh kh).1)
    (hpm0 : denoteGraph_ringAttn pm initPM p0
        = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM csP) (denoteGraph_ringAttn pm initPM pos0)
            (denoteGraph_ringAttn pm initPM q0) (denoteGraph_ringAttn pm initPM k0) nh kh).1)
    (hpm1 : denoteGraph_ringAttn pm initPM p1
        = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM csP) (denoteGraph_ringAttn pm initPM pos1)
            (denoteGraph_ringAttn pm initPM q1) (denoteGraph_ringAttn pm initPM k1) nh kh).1)
    (hcs : denoteGraph_ringAttn sm initSM csS = denoteGraph_ringAttn pm initPM csP)
    (hpos : denoteGraph_ringAttn sm initSM posS
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM pos0, denoteGraph_ringAttn pm initPM pos1])
    (hq : denoteGraph_ringAttn sm initSM qS
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM q0, denoteGraph_ringAttn pm initPM q1])
    (hk : denoteGraph_ringAttn sm initSM kS
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM k0, denoteGraph_ringAttn pm initPM k1])
    (hq0 : (denoteGraph_ringAttn pm initPM q0).shape = [L, nh, d])
    (hq1 : (denoteGraph_ringAttn pm initPM q1).shape = [L, nh, d])
    (hk0 : (denoteGraph_ringAttn pm initPM k0).shape = [L, kh, d])
    (hk1 : (denoteGraph_ringAttn pm initPM k1).shape = [L, kh, d])
    (hp0 : (denoteGraph_ringAttn pm initPM pos0).shape = [L, 1])
    (hp1 : (denoteGraph_ringAttn pm initPM pos1).shape = [L, 1]) :
    InitGoalHolds pm.numRanks g (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hval : denoteGraph_ringAttn sm initSM T
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM p0, denoteGraph_ringAttn pm initPM p1] := by
    rw [hsmNode, hpm0, hpm1]
    exact rotary_fst_gather_commute _ _ _ _ _ _ _ _ _ _ _ L nh kh d
      hL hnh hkh hd hq0 hq1 hk0 hk1 hp0 hp1 hcs hpos hq hk
  have hshape : (denoteGraph_ringAttn sm initSM T).shape = [L * 2, nh, d] := by
    rw [hsmNode, fw_rotary_embedding_fst_shape, hq,
        allGatherPrimDimN_shape 0 2 _ [L, nh, d]
          (by simp only [List.head?_cons, Option.map_some, Option.getD_some]; exact hq0)]
    rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    g T p0 p1 [L * 2, nh, d] [L, nh, d]
    htp hgd hrep hts htsShape htpShapes hne hval hshape
    (by rw [hpm0, fw_rotary_embedding_fst_shape]; exact hq0)
    (by rw [hpm1, fw_rotary_embedding_fst_shape]; exact hq1)

/-- Parametrized 2-tp rotary **K'** (`.2`) reconstruction gear over ring-attn
    (the companion of `recon_attn_rotary_2tp_layer`). -/
theorem recon_attn_rotary_2tp_layer_snd
    (initSM initPM : Store) (g : LineageGoal)
    (T p0 p1 csS posS qS kS csP pos0 q0 k0 pos1 q1 k1 : Tid) (L nh kh d : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hkh : 0 < kh) (hd : 0 < d)
    (htp : g.tps = [{rank := 0, tid := p0}, {rank := 1, tid := p1}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = T)
    (htsShape : g.tsShape = [L * 2, kh, d]) (htpShapes : g.tpShapes = [[L, kh, d], [L, kh, d]])
    (hne : ([L, kh, d] : Shape) ≠ [1])
    (hsmNode : denoteGraph_ringAttn sm initSM T
        = (fw_rotary_embedding (denoteGraph_ringAttn sm initSM csS) (denoteGraph_ringAttn sm initSM posS)
            (denoteGraph_ringAttn sm initSM qS) (denoteGraph_ringAttn sm initSM kS) nh kh).2)
    (hpm0 : denoteGraph_ringAttn pm initPM p0
        = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM csP) (denoteGraph_ringAttn pm initPM pos0)
            (denoteGraph_ringAttn pm initPM q0) (denoteGraph_ringAttn pm initPM k0) nh kh).2)
    (hpm1 : denoteGraph_ringAttn pm initPM p1
        = (fw_rotary_embedding (denoteGraph_ringAttn pm initPM csP) (denoteGraph_ringAttn pm initPM pos1)
            (denoteGraph_ringAttn pm initPM q1) (denoteGraph_ringAttn pm initPM k1) nh kh).2)
    (hcs : denoteGraph_ringAttn sm initSM csS = denoteGraph_ringAttn pm initPM csP)
    (hpos : denoteGraph_ringAttn sm initSM posS
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM pos0, denoteGraph_ringAttn pm initPM pos1])
    (hq : denoteGraph_ringAttn sm initSM qS
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM q0, denoteGraph_ringAttn pm initPM q1])
    (hk : denoteGraph_ringAttn sm initSM kS
        = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM k0, denoteGraph_ringAttn pm initPM k1])
    (hq0 : (denoteGraph_ringAttn pm initPM q0).shape = [L, nh, d])
    (hq1 : (denoteGraph_ringAttn pm initPM q1).shape = [L, nh, d])
    (hk0 : (denoteGraph_ringAttn pm initPM k0).shape = [L, kh, d])
    (hk1 : (denoteGraph_ringAttn pm initPM k1).shape = [L, kh, d])
    (hp0 : (denoteGraph_ringAttn pm initPM pos0).shape = [L, 1])
    (hp1 : (denoteGraph_ringAttn pm initPM pos1).shape = [L, 1]) :
    InitGoalHolds pm.numRanks g (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hval : denoteGraph_ringAttn sm initSM T
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM p0, denoteGraph_ringAttn pm initPM p1] := by
    rw [hsmNode, hpm0, hpm1]
    exact rotary_snd_gather_commute _ _ _ _ _ _ _ _ _ _ _ L nh kh d
      hL hnh hkh hd hq0 hq1 hk0 hk1 hp0 hp1 hcs hpos hq hk
  have hshape : (denoteGraph_ringAttn sm initSM T).shape = [L * 2, kh, d] := by
    rw [hsmNode, fw_rotary_embedding_snd_shape, hk,
        allGatherPrimDimN_shape 0 2 _ [L, kh, d]
          (by simp only [List.head?_cons, Option.map_some, Option.getD_some]; exact hk0)]
    rfl
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    g T p0 p1 [L * 2, kh, d] [L, kh, d]
    htp hgd hrep hts htsShape htpShapes hne hval hshape
    (by rw [hpm0, fw_rotary_embedding_snd_shape]; exact hk0)
    (by rw [hpm1, fw_rotary_embedding_snd_shape]; exact hk1)

/-! ### Zigzag attention 2-tp gear over `denoteGraph_ringAttn`

    Verbatim structural analog of worker #10's
    `recon_attn_sliding_window_2tp_layer`, with the sliding-window ring machinery
    (`applyNodeRingAttn_sliding_window*`) replaced by the `FW_attn_zigzag`
    machinery (`applyNodeRingAttn_zigzag*`). `FW_attn_zigzag` carries
    `params = [qh, kvh, d, vd, causal, windowLeft]` with `windowLeft = 0`
    (see `graph_to_lean.py:468` / `GeneratedYOCOMoE.lean` params
    `[16, 4, 64, 64, 1, 0]`); the gear leaves `windowLeft` fully abstract via
    `n*.params.getD 5 0`, so the `= 0` value is discharged by the caller's
    concrete node literals. -/
-- Raised heartbeat limit: mirrors `recon_attn_sliding_window_2tp_layer`; the
-- buddy-pair reconstruction + three `chunkPrimDimN_shape`/`allGatherPrimDimN_shape`
-- rewrites over abstract folds exceed the default budget.
set_option maxHeartbeats 4000000 in
theorem recon_attn_zigzag_2tp_layer
    (initSM initPM : Store) (g : LineageGoal)
    (nSM nR0 nR1 : NodeDecl)
    (foldSM foldPM foldPM' : Store)
    (oSM oR0 oR1 : Tid) (L nh kh : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hkh : 0 < kh)
    (hSM_red : denoteGraph_ringAttn sm initSM oSM
        = applyNodeRingAttn_zigzag sm foldSM nSM)
    (hR0_red : denoteGraph_ringAttn pm initPM oR0
        = applyNodeRingAttn_zigzag pm foldPM nR0)
    (hR1_red : denoteGraph_ringAttn pm initPM oR1
        = applyNodeRingAttn_zigzag pm foldPM' nR1)
    (hbridge : applyNodeRingAttn_zigzag pm foldPM nR1
        = applyNodeRingAttn_zigzag pm foldPM' nR1)
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
    (htp : g.tps = [{rank := 0, tid := oR0}, {rank := 1, tid := oR1}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false)
    (hts : g.ts = oSM) (htsShape : g.tsShape = [2 * L, nh, kh])
    (htpShapes : g.tpShapes = [[L, nh, kh], [L, nh, kh]]) :
    InitGoalHolds pm.numRanks g
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_of_buddy_pair
    sm pm foldSM foldPM nSM nR0 nR1 L nh kh hL hnh hkh
    hbuddy_sm hbuddy_r0 hbuddy_r1 hmyIdx0 hmyIdx1
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm hcuQ_same hcuK_same hparams_sm hparams_same hfull_shape
  have hval : denoteGraph_ringAttn sm initSM oSM
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM oR0, denoteGraph_ringAttn pm initPM oR1] := by
    rw [hSM_red, hrec, hbridge, ← hR0_red, ← hR1_red, show pm.numRanks = 2 from rfl]
  have hshapeP0 : (denoteGraph_ringAttn pm initPM oR0).shape = [L, nh, kh] := by
    rw [hR0_red, applyNodeRingAttn_zigzag_pair_eq_chunk pm foldPM nR0 nR0 nR1 0
          hbuddy_r0 hmyIdx0,
        chunkPrimDimN_shape 0 2 0 _ [2 * L, nh, kh] hfull_shape (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [show 2 * L / 2 = L from by omega]
  have hshapeP1 : (denoteGraph_ringAttn pm initPM oR1).shape = [L, nh, kh] := by
    rw [hR1_red, applyNodeRingAttn_zigzag_pair_eq_chunk pm foldPM' nR1 nR0 nR1 1
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

-- Force type resolution of all three gears.
#check @recon_attn_rotary_2tp_layer
#check @recon_attn_rotary_2tp_layer_snd
#check @recon_attn_zigzag_2tp_layer

end TrainVerify.Denote.GeneratedPatterns
