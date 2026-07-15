/- Zigzag (cross-decoder) attention 2-tp reconstruction over `denoteGraph_ringAttn`
   (worker #19).

   The YOCO-MoE cross-decoder uses `FW_attn_zigzag` (windowLeft = 0, full-causal
   ring attention) for layers L0..L11 (SM tids 5347, 5396, …, 5886).  Unlike the
   self-decoder's sliding-window layer (worker #9/#10, 2-tp *sharded* K/V), the
   zigzag layers use the *context-parallel* (CP) layout: only Q is sharded across
   the two ranks, while K/V (and the cu-seqlens) are **replicated** — both PM
   buddies read the *same* K/V tid as the SM node (e.g. zigzag L0 node 5347 has
   ins `[5342, 5343, 5344, 5345, 5346]`, PM r0 node 9687 has `[9659, 5343, 5344,
   5345, 5346]`, PM r1 node 9688 has `[9660, 5343, 5344, 5345, 5346]` — only Q
   differs).  So worker #15's *sharded* gear `recon_attn_zigzag_2tp_layer` does
   not apply; we use worker #9's CP reconstruction lemma
   `applyNodeRingAttn_zigzag_reconstruction_2_cp` (Pattern_3.lean) instead, which
   bridges the SM single-K attention to the PM row-doubled `allGather [K, K]`
   gather through `fw_attn_varlen_kv_append_invariant`.

   `recon_attn_zigzag_2tp_layer_cp` below is the CP analog of worker #15's
   `recon_attn_zigzag_2tp_layer`: it packages the CP reconstruction + shard-shape
   facts into an `InitGoalHolds` over `denoteGraph_ringAttn`.  Zero `sorry`, zero
   user axiom; kernel triple + `native_decide` only.
-/
import denote.yoco_goals.RingAttnExtGears
import denote.yoco_goals.MoEShardedReconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-! ### Context-parallel zigzag 2-tp gear over `denoteGraph_ringAttn`

    Verbatim structural analog of worker #15's `recon_attn_zigzag_2tp_layer`, but
    for the CP (replicated-K/V) layout.  The sharded reconstruction lemma is
    replaced by `applyNodeRingAttn_zigzag_reconstruction_2_cp`, and the sharded
    `hk_full`/`hv_full` all-gather hypotheses are replaced by the CP replication
    equalities `hk_repl`/`hv_repl` plus the K/V shape / cu-seqlens-bound facts the
    `fw_attn_varlen_kv_append_invariant` bridge requires. `nh`/`kh` (= qh/vd) are
    exposed for the goal metadata via the param equalities `hnh`/`hkh`. -/
set_option maxHeartbeats 4000000 in
theorem recon_attn_zigzag_2tp_layer_cp
    (initSM initPM : Store) (g : LineageGoal)
    (nSM nR0 nR1 : NodeDecl)
    (foldSM foldPM foldPM' : Store)
    (oSM oR0 oR1 : Tid) (L Lk nh kh : Nat)
    (hL : 0 < L)
    (hqh : 0 < nR0.params.getD 0 1) (hkvh : 0 < nR0.params.getD 1 1)
    (hd : 0 < nR0.params.getD 2 1) (hvd : 0 < nR0.params.getD 3 1)
    (hdvd : nR0.params.getD 1 1 ∣ nR0.params.getD 0 1)
    (hnh : nR0.params.getD 0 1 = nh) (hkh : nR0.params.getD 3 1 = kh)
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
    (hkins : nR1.ins.getD 1 0 = nR0.ins.getD 1 0)
    (hvins : nR1.ins.getD 2 0 = nR0.ins.getD 2 0)
    (hq_full : foldSM (nSM.ins.getD 0 0)
        = allGatherPrimDimN 0 2 0 [foldPM (nR0.ins.getD 0 0), foldPM (nR1.ins.getD 0 0)])
    (hk_repl : foldSM (nSM.ins.getD 1 0) = foldPM (nR0.ins.getD 1 0))
    (hv_repl : foldSM (nSM.ins.getD 2 0) = foldPM (nR0.ins.getD 2 0))
    (hk_shape : (foldPM (nR0.ins.getD 1 0)).shape
        = [Lk, nR0.params.getD 1 1, nR0.params.getD 2 1])
    (hv_shape : (foldPM (nR0.ins.getD 2 0)).shape
        = [Lk, nR0.params.getD 1 1, nR0.params.getD 3 1])
    (h_bound : ∀ t, (decodeCuSeqlens (foldPM (nR0.ins.getD 4 0))).getD (t+1) 0 ≤ Lk)
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
        = [2 * L, nR0.params.getD 0 1, nR0.params.getD 3 1])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [foldPM' (nR0.ins.getD 0 0), foldPM' (nR1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [foldPM' (nR0.ins.getD 1 0), foldPM' (nR1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [foldPM' (nR0.ins.getD 2 0), foldPM' (nR1.ins.getD 2 0)])
          (foldPM' (nR1.ins.getD 3 0)) (foldPM' (nR1.ins.getD 4 0))
          (nR1.params.getD 0 1) (nR1.params.getD 1 1) (nR1.params.getD 2 1)
          (nR1.params.getD 3 1)
          (decide (nR1.params.getD 4 0 ≠ 0)) (nR1.params.getD 5 0)).shape
        = [2 * L, nR1.params.getD 0 1, nR1.params.getD 3 1])
    (htp : g.tps = [{rank := 0, tid := oR0}, {rank := 1, tid := oR1}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false)
    (hts : g.ts = oSM) (htsShape : g.tsShape = [2 * L, nh, kh])
    (htpShapes : g.tpShapes = [[L, nh, kh], [L, nh, kh]]) :
    InitGoalHolds pm.numRanks g
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm pm foldSM foldPM nSM nR0 nR1 L Lk hL hqh hkvh hd hvd hdvd
    hbuddy_sm hbuddy_r0 hbuddy_r1 hmyIdx0 hmyIdx1
    hq_sm hk_sm hv_sm hkins hvins
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm hcuQ_same hcuK_same hparams_sm hparams_same hfull_shape
  have hval : denoteGraph_ringAttn sm initSM oSM
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM oR0, denoteGraph_ringAttn pm initPM oR1] := by
    rw [hSM_red, hrec, hbridge, ← hR0_red, ← hR1_red, show pm.numRanks = 2 from rfl]
  have hshapeP0 : (denoteGraph_ringAttn pm initPM oR0).shape = [L, nh, kh] := by
    rw [hR0_red, applyNodeRingAttn_zigzag_pair_eq_chunk pm foldPM nR0 nR0 nR1 0
          hbuddy_r0 hmyIdx0,
        chunkPrimDimN_shape 0 2 0 _ [2 * L, nR0.params.getD 0 1, nR0.params.getD 3 1]
          hfull_shape (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [show 2 * L / 2 = L from by omega, hnh, hkh]
  have hshapeP1 : (denoteGraph_ringAttn pm initPM oR1).shape = [L, nh, kh] := by
    rw [hR1_red, applyNodeRingAttn_zigzag_pair_eq_chunk pm foldPM' nR1 nR0 nR1 1
          hbuddy_r1 hmyIdx1,
        chunkPrimDimN_shape 0 2 1 _ [2 * L, nR1.params.getD 0 1, nR1.params.getD 3 1]
          hfull_shape' (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [show 2 * L / 2 = L from by omega, ← hparams_same, hnh, hkh]
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

#check @recon_attn_zigzag_2tp_layer_cp

/-! ### Zigzag L0 firing over the full graph (tid 5347)

    The full-graph node literals for zigzag layer 0: SM node index 505 writes
    5347; PM r0 node index 1072 writes 9687; PM r1 node index 1073 writes 9688.
    The SM node carries `ins := (List.range 5).map (5342 + ·)`, which is
    definitionally `[5342, 5343, 5344, 5345, 5346]`. -/

/-- SM zigzag L0 node (`outs = [5347]`). -/
def nSMz0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5342, 5343, 5344, 5345, 5346], outs := [5347], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L0 node (`outs = [9687]`). -/
def nR0z0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [9659, 5343, 5344, 5345, 5346], outs := [9687], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L0 node (`outs = [9688]`). -/
def nR1z0 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [9660, 5343, 5344, 5345, 5346], outs := [9688], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L0 (`intermediateGoal_5347`) over `denoteGraph_ringAttn`, conditional
    on the CP Q/K/V input reconstructions.**  The Q full-sharding commute
    (`hq_full`) and the K/V replication equalities (`hk_repl`/`hv_repl`) thread
    the incoming self-decoder residual carry through `per_head_mix_precision_linear
    ∘ rms_norm` (worker #7's 2-tp commute) — these depend on the residual carry
    `5330 = allGather[9625, 9626]`, which lies in the self-decoder chain (worker
    #20 / upstream), so they are exposed as hypotheses (folded-store form,
    mirroring `Pattern_3.sm_pm_attention_L12_commute`).  Everything downstream —
    node reductions, buddy detection, cu-seqlens agreement, the r1 store bridge,
    and the CP reconstruction assembly — is discharged here. -/
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_5347_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5342
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9659,
             (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9660])
    (hk_repl : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5343
        = (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5343)
    (hv_repl : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5344
        = (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5344)
    (hq_sm : 0 < ((sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5342).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5343).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5344).shape.length)
    (hk_shape : ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5343).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5344).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5346)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9659,
             (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9660])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5343,
             (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5343])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5344,
             (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5344])
          ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5345)
          ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5346)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 9659,
             (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 9660])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5343,
             (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5343])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5344,
             (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5344])
          ((pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5345)
          ((pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5346)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5347
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5347 : denoteGraph_ringAttn sm initSM 5347
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM) nSMz0 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5347 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5347 506 (by native_decide) (by native_decide),
        show sm.nodes.take 506 = sm.nodes.take 505 ++ [nSMz0] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5342 5343 5344 5345 5346 5347 [16, 4, 64, 64, 1, 0]
  have hPM9687 : denoteGraph_ringAttn pm initPM 9687
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM) nR0z0 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 9687 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9687 1073 (by native_decide) (by native_decide),
        show pm.nodes.take 1073 = pm.nodes.take 1072 ++ [nR0z0] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 9659 5343 5344 5345 5346 9687 [16, 4, 64, 64, 1, 0]
  have hPM9688 : denoteGraph_ringAttn pm initPM 9688
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM) nR1z0 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 9688 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9688 1074 (by native_decide) (by native_decide),
        show pm.nodes.take 1074 = pm.nodes.take 1073 ++ [nR1z0] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 9660 5343 5344 5345 5346 9688 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1072 ↔ take 1073 agree on nR1z0's inputs (9660,5343,5344,5345,5346)
  have e9660 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9660
      = (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 9660 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9660 1072 1073 (by omega) (by native_decide) (by native_decide)).symm
  have e5343 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5343
      = (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5343 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5343 1072 1073 (by omega) (by native_decide) (by native_decide)).symm
  have e5344 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5344
      = (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5344 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5344 1072 1073 (by omega) (by native_decide) (by native_decide)).symm
  have e5345 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5345
      = (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5345 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5345 1072 1073 (by omega) (by native_decide) (by native_decide)).symm
  have e5346 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5346
      = (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 5346 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5346 1072 1073 (by omega) (by native_decide) (by native_decide)).symm
  have e9659 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 9659
      = (pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM 9659 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9659 1072 1073 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM) nR1z0
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM) nR1z0 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z0 = [nR0z0, nR1z0] from by native_decide]
      intro m hm; fin_cases hm
      · exact e9659
      · exact e9660
    · rw [show ringAttnBuddies pm nR1z0 = [nR0z0, nR1z0] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5343
      · exact e5343
    · rw [show ringAttnBuddies pm nR1z0 = [nR0z0, nR1z0] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5344
      · exact e5344
    · exact e5345
    · exact e5346
  -- cu-seqlens agreement (5345/5346 are init leaves in both graphs, equal via init goals)
  have hcu5345 : denoteGraph sm initSM 5345 = denoteGraph pm initPM 5345 :=
    recon_weight initSM initPM hInit initGoal_5345 (by native_decide) 5345 rfl rfl rfl rfl
  have hcu5346 : denoteGraph sm initSM 5346 = denoteGraph pm initPM 5346 :=
    recon_weight initSM initPM hInit initGoal_5346 (by native_decide) 5346 rfl rfl rfl rfl
  have hSM5345 : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5345 = denoteGraph sm initSM 5345 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5345 505 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5345 (by native_decide)
  have hSM5346 : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5346 = denoteGraph sm initSM 5346 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5346 505 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5346 (by native_decide)
  have hPM5345 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5345 = denoteGraph pm initPM 5345 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5345 1072 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5345 (by native_decide)
  have hPM5346 : (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5346 = denoteGraph pm initPM 5346 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5346 1072 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5346 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5345
      = (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5345 := by
    rw [hSM5345, hPM5345, hcu5345]
  have hcuK_sm_pm : (sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM 5346
      = (pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM 5346 := by
    rw [hSM5346, hPM5346, hcu5346]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5347
    nSMz0 nR0z0 nR1z0
    ((sm.nodes.take 505).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1072).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1073).foldl (applyNodeRingAttn pm) initPM)
    5347 9687 9688 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5347 hPM9687 hPM9688 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

#check @recon_intermediateGoal_5347_ringAttn_of_qkv

end TrainVerify.Denote.GeneratedPatterns
