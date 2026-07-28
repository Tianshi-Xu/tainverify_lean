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

/-! ### Ring-attention-track goal records for the CP zigzag attention outputs

These 12 tids are CP zigzag-owned, so `Verdict/graph_to_lean.py` no longer emits
an `intermediateGoal_N` for them: on the FAITHFUL full graph an ordinary gather
over their shards is false (`ZigzagGoalRefutation.gatheredZigzag_ne_full`), and
the true obligation is the emitted `intermediateGoal_N_zigzag`
(`ZigzagLineageGoal`, discharged against `Zigzag2Rel`).

Every theorem in THIS file is stated over `denoteGraph_ringAttn`, which models
the shuffle as identity (AGENTS #24: shape-correct, value-lossy for cpSize > 1).
On that track the ordinary-gather record is the right statement, so the records
are re-declared here — scoped to this module rather than published globally, so
they cannot be mistaken for faithful-track goals.
-/

def intermediateGoal_5347 : LineageGoal :=
  { ts := 5347, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 9687 }, { rank := 1, tid := 9688 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5396 : LineageGoal :=
  { ts := 5396, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 9859 }, { rank := 1, tid := 9860 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5445 : LineageGoal :=
  { ts := 5445, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 10031 }, { rank := 1, tid := 10032 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5494 : LineageGoal :=
  { ts := 5494, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 10203 }, { rank := 1, tid := 10204 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5543 : LineageGoal :=
  { ts := 5543, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 10375 }, { rank := 1, tid := 10376 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5592 : LineageGoal :=
  { ts := 5592, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 10547 }, { rank := 1, tid := 10548 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5641 : LineageGoal :=
  { ts := 5641, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 10719 }, { rank := 1, tid := 10720 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5690 : LineageGoal :=
  { ts := 5690, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 10891 }, { rank := 1, tid := 10892 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5739 : LineageGoal :=
  { ts := 5739, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 11063 }, { rank := 1, tid := 11064 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5788 : LineageGoal :=
  { ts := 5788, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 11235 }, { rank := 1, tid := 11236 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5837 : LineageGoal :=
  { ts := 5837, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 11407 }, { rank := 1, tid := 11408 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

def intermediateGoal_5886 : LineageGoal :=
  { ts := 5886, tsShape := [4096, 16, 64], tps := [{ rank := 0, tid := 11579 }, { rank := 1, tid := 11580 }], tpShapes := [[2048, 16, 64], [2048, 16, 64]] }

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

/-! ### Zigzag L1 firing (tid 5396) -/
/-- SM zigzag L1 node (`outs = [5396]`). -/
def nSMz1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5391, 5392, 5393, 5394, 5395], outs := [5396], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L1 node (`outs = [9859]`). -/
def nR0z1 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [9835, 5392, 5393, 5394, 5395], outs := [9859], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L1 node (`outs = [9860]`). -/
def nR1z1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [9836, 5392, 5393, 5394, 5395], outs := [9860], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L1 (`intermediateGoal_5396`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5396_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM 5391
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 9835,
             (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 9836])
    (hk_repl : (sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM 5392
        = (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5392)
    (hv_repl : (sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM 5393
        = (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5393)
    (hq_sm : 0 < ((sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM 5391).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM 5392).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM 5393).shape.length)
    (hk_shape : ((pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5392).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5393).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5395)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 9835,
             (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 9836])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5392,
             (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5392])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5393,
             (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5393])
          ((pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5394)
          ((pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5395)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 9835,
             (pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 9836])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 5392,
             (pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 5392])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 5393,
             (pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 5393])
          ((pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 5394)
          ((pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 5395)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5396
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5396 : denoteGraph_ringAttn sm initSM 5396
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM) nSMz1 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5396 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5396 541 (by native_decide) (by native_decide),
        show sm.nodes.take 541 = sm.nodes.take 540 ++ [nSMz1] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5391 5392 5393 5394 5395 5396 [16, 4, 64, 64, 1, 0]
  have hPM9859 : denoteGraph_ringAttn pm initPM 9859
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM) nR0z1 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 9859 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9859 1143 (by native_decide) (by native_decide),
        show pm.nodes.take 1143 = pm.nodes.take 1142 ++ [nR0z1] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 9835 5392 5393 5394 5395 9859 [16, 4, 64, 64, 1, 0]
  have hPM9860 : denoteGraph_ringAttn pm initPM 9860
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM) nR1z1 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 9860 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 9860 1144 (by native_decide) (by native_decide),
        show pm.nodes.take 1144 = pm.nodes.take 1143 ++ [nR1z1] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 9836 5392 5393 5394 5395 9860 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1142 ↔ take 1143 agree on nR1z1's inputs (9836,5392,5393,5394,5395)
  have e9836 : (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 9836
      = (pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 9836 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9836 1142 1143 (by omega) (by native_decide) (by native_decide)).symm
  have e5392 : (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5392
      = (pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 5392 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5392 1142 1143 (by omega) (by native_decide) (by native_decide)).symm
  have e5393 : (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5393
      = (pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 5393 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5393 1142 1143 (by omega) (by native_decide) (by native_decide)).symm
  have e5394 : (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5394
      = (pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 5394 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5394 1142 1143 (by omega) (by native_decide) (by native_decide)).symm
  have e5395 : (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5395
      = (pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 5395 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5395 1142 1143 (by omega) (by native_decide) (by native_decide)).symm
  have e9835 : (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 9835
      = (pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM 9835 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 9835 1142 1143 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM) nR1z1
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM) nR1z1 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z1 = [nR0z1, nR1z1] from by native_decide]
      intro m hm; fin_cases hm
      · exact e9835
      · exact e9836
    · rw [show ringAttnBuddies pm nR1z1 = [nR0z1, nR1z1] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5392
      · exact e5392
    · rw [show ringAttnBuddies pm nR1z1 = [nR0z1, nR1z1] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5393
      · exact e5393
    · exact e5394
    · exact e5395
  -- cu-seqlens agreement (5394/5395 are init leaves in both graphs, equal via init goals)
  have hcu5394 : denoteGraph sm initSM 5394 = denoteGraph pm initPM 5394 :=
    recon_weight initSM initPM hInit initGoal_5394 (by native_decide) 5394 rfl rfl rfl rfl
  have hcu5395 : denoteGraph sm initSM 5395 = denoteGraph pm initPM 5395 :=
    recon_weight initSM initPM hInit initGoal_5395 (by native_decide) 5395 rfl rfl rfl rfl
  have hSM5394 : (sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM 5394 = denoteGraph sm initSM 5394 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5394 540 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5394 (by native_decide)
  have hSM5395 : (sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM 5395 = denoteGraph sm initSM 5395 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5395 540 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5395 (by native_decide)
  have hPM5394 : (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5394 = denoteGraph pm initPM 5394 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5394 1142 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5394 (by native_decide)
  have hPM5395 : (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5395 = denoteGraph pm initPM 5395 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5395 1142 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5395 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM 5394
      = (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5394 := by
    rw [hSM5394, hPM5394, hcu5394]
  have hcuK_sm_pm : (sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM 5395
      = (pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM 5395 := by
    rw [hSM5395, hPM5395, hcu5395]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5396
    nSMz1 nR0z1 nR1z1
    ((sm.nodes.take 540).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1142).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1143).foldl (applyNodeRingAttn pm) initPM)
    5396 9859 9860 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5396 hPM9859 hPM9860 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

/-! ### Zigzag L2 firing (tid 5445) -/
/-- SM zigzag L2 node (`outs = [5445]`). -/
def nSMz2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5440, 5441, 5442, 5443, 5444], outs := [5445], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L2 node (`outs = [10031]`). -/
def nR0z2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10007, 5441, 5442, 5443, 5444], outs := [10031], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L2 node (`outs = [10032]`). -/
def nR1z2 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10008, 5441, 5442, 5443, 5444], outs := [10032], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L2 (`intermediateGoal_5445`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5445_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM 5440
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 10007,
             (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 10008])
    (hk_repl : (sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM 5441
        = (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5441)
    (hv_repl : (sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM 5442
        = (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5442)
    (hq_sm : 0 < ((sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM 5440).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM 5441).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM 5442).shape.length)
    (hk_shape : ((pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5441).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5442).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5444)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 10007,
             (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 10008])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5441,
             (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5441])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5442,
             (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5442])
          ((pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5443)
          ((pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5444)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 10007,
             (pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 10008])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 5441,
             (pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 5441])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 5442,
             (pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 5442])
          ((pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 5443)
          ((pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 5444)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5445
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5445 : denoteGraph_ringAttn sm initSM 5445
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM) nSMz2 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5445 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5445 576 (by native_decide) (by native_decide),
        show sm.nodes.take 576 = sm.nodes.take 575 ++ [nSMz2] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5440 5441 5442 5443 5444 5445 [16, 4, 64, 64, 1, 0]
  have hPM10031 : denoteGraph_ringAttn pm initPM 10031
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM) nR0z2 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10031 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10031 1213 (by native_decide) (by native_decide),
        show pm.nodes.take 1213 = pm.nodes.take 1212 ++ [nR0z2] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 10007 5441 5442 5443 5444 10031 [16, 4, 64, 64, 1, 0]
  have hPM10032 : denoteGraph_ringAttn pm initPM 10032
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM) nR1z2 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10032 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10032 1214 (by native_decide) (by native_decide),
        show pm.nodes.take 1214 = pm.nodes.take 1213 ++ [nR1z2] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 10008 5441 5442 5443 5444 10032 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1212 ↔ take 1213 agree on nR1z2's inputs (10008,5441,5442,5443,5444)
  have e10008 : (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 10008
      = (pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 10008 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10008 1212 1213 (by omega) (by native_decide) (by native_decide)).symm
  have e5441 : (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5441
      = (pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 5441 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5441 1212 1213 (by omega) (by native_decide) (by native_decide)).symm
  have e5442 : (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5442
      = (pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 5442 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5442 1212 1213 (by omega) (by native_decide) (by native_decide)).symm
  have e5443 : (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5443
      = (pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 5443 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5443 1212 1213 (by omega) (by native_decide) (by native_decide)).symm
  have e5444 : (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5444
      = (pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 5444 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5444 1212 1213 (by omega) (by native_decide) (by native_decide)).symm
  have e10007 : (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 10007
      = (pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM 10007 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10007 1212 1213 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM) nR1z2
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM) nR1z2 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z2 = [nR0z2, nR1z2] from by native_decide]
      intro m hm; fin_cases hm
      · exact e10007
      · exact e10008
    · rw [show ringAttnBuddies pm nR1z2 = [nR0z2, nR1z2] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5441
      · exact e5441
    · rw [show ringAttnBuddies pm nR1z2 = [nR0z2, nR1z2] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5442
      · exact e5442
    · exact e5443
    · exact e5444
  -- cu-seqlens agreement (5443/5444 are init leaves in both graphs, equal via init goals)
  have hcu5443 : denoteGraph sm initSM 5443 = denoteGraph pm initPM 5443 :=
    recon_weight initSM initPM hInit initGoal_5443 (by native_decide) 5443 rfl rfl rfl rfl
  have hcu5444 : denoteGraph sm initSM 5444 = denoteGraph pm initPM 5444 :=
    recon_weight initSM initPM hInit initGoal_5444 (by native_decide) 5444 rfl rfl rfl rfl
  have hSM5443 : (sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM 5443 = denoteGraph sm initSM 5443 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5443 575 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5443 (by native_decide)
  have hSM5444 : (sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM 5444 = denoteGraph sm initSM 5444 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5444 575 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5444 (by native_decide)
  have hPM5443 : (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5443 = denoteGraph pm initPM 5443 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5443 1212 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5443 (by native_decide)
  have hPM5444 : (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5444 = denoteGraph pm initPM 5444 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5444 1212 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5444 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM 5443
      = (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5443 := by
    rw [hSM5443, hPM5443, hcu5443]
  have hcuK_sm_pm : (sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM 5444
      = (pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM 5444 := by
    rw [hSM5444, hPM5444, hcu5444]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5445
    nSMz2 nR0z2 nR1z2
    ((sm.nodes.take 575).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1212).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1213).foldl (applyNodeRingAttn pm) initPM)
    5445 10031 10032 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5445 hPM10031 hPM10032 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

/-! ### Zigzag L3 firing (tid 5494) -/
/-- SM zigzag L3 node (`outs = [5494]`). -/
def nSMz3 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5489, 5490, 5491, 5492, 5493], outs := [5494], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L3 node (`outs = [10203]`). -/
def nR0z3 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10179, 5490, 5491, 5492, 5493], outs := [10203], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L3 node (`outs = [10204]`). -/
def nR1z3 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10180, 5490, 5491, 5492, 5493], outs := [10204], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L3 (`intermediateGoal_5494`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5494_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM 5489
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 10179,
             (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 10180])
    (hk_repl : (sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM 5490
        = (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5490)
    (hv_repl : (sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM 5491
        = (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5491)
    (hq_sm : 0 < ((sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM 5489).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM 5490).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM 5491).shape.length)
    (hk_shape : ((pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5490).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5491).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5493)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 10179,
             (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 10180])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5490,
             (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5490])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5491,
             (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5491])
          ((pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5492)
          ((pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5493)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 10179,
             (pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 10180])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 5490,
             (pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 5490])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 5491,
             (pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 5491])
          ((pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 5492)
          ((pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 5493)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5494
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5494 : denoteGraph_ringAttn sm initSM 5494
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM) nSMz3 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5494 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5494 611 (by native_decide) (by native_decide),
        show sm.nodes.take 611 = sm.nodes.take 610 ++ [nSMz3] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5489 5490 5491 5492 5493 5494 [16, 4, 64, 64, 1, 0]
  have hPM10203 : denoteGraph_ringAttn pm initPM 10203
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM) nR0z3 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10203 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10203 1283 (by native_decide) (by native_decide),
        show pm.nodes.take 1283 = pm.nodes.take 1282 ++ [nR0z3] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 10179 5490 5491 5492 5493 10203 [16, 4, 64, 64, 1, 0]
  have hPM10204 : denoteGraph_ringAttn pm initPM 10204
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM) nR1z3 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10204 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10204 1284 (by native_decide) (by native_decide),
        show pm.nodes.take 1284 = pm.nodes.take 1283 ++ [nR1z3] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 10180 5490 5491 5492 5493 10204 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1282 ↔ take 1283 agree on nR1z3's inputs (10180,5490,5491,5492,5493)
  have e10180 : (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 10180
      = (pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 10180 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10180 1282 1283 (by omega) (by native_decide) (by native_decide)).symm
  have e5490 : (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5490
      = (pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 5490 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5490 1282 1283 (by omega) (by native_decide) (by native_decide)).symm
  have e5491 : (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5491
      = (pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 5491 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5491 1282 1283 (by omega) (by native_decide) (by native_decide)).symm
  have e5492 : (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5492
      = (pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 5492 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5492 1282 1283 (by omega) (by native_decide) (by native_decide)).symm
  have e5493 : (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5493
      = (pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 5493 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5493 1282 1283 (by omega) (by native_decide) (by native_decide)).symm
  have e10179 : (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 10179
      = (pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM 10179 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10179 1282 1283 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM) nR1z3
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM) nR1z3 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z3 = [nR0z3, nR1z3] from by native_decide]
      intro m hm; fin_cases hm
      · exact e10179
      · exact e10180
    · rw [show ringAttnBuddies pm nR1z3 = [nR0z3, nR1z3] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5490
      · exact e5490
    · rw [show ringAttnBuddies pm nR1z3 = [nR0z3, nR1z3] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5491
      · exact e5491
    · exact e5492
    · exact e5493
  -- cu-seqlens agreement (5492/5493 are init leaves in both graphs, equal via init goals)
  have hcu5492 : denoteGraph sm initSM 5492 = denoteGraph pm initPM 5492 :=
    recon_weight initSM initPM hInit initGoal_5492 (by native_decide) 5492 rfl rfl rfl rfl
  have hcu5493 : denoteGraph sm initSM 5493 = denoteGraph pm initPM 5493 :=
    recon_weight initSM initPM hInit initGoal_5493 (by native_decide) 5493 rfl rfl rfl rfl
  have hSM5492 : (sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM 5492 = denoteGraph sm initSM 5492 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5492 610 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5492 (by native_decide)
  have hSM5493 : (sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM 5493 = denoteGraph sm initSM 5493 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5493 610 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5493 (by native_decide)
  have hPM5492 : (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5492 = denoteGraph pm initPM 5492 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5492 1282 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5492 (by native_decide)
  have hPM5493 : (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5493 = denoteGraph pm initPM 5493 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5493 1282 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5493 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM 5492
      = (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5492 := by
    rw [hSM5492, hPM5492, hcu5492]
  have hcuK_sm_pm : (sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM 5493
      = (pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM 5493 := by
    rw [hSM5493, hPM5493, hcu5493]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5494
    nSMz3 nR0z3 nR1z3
    ((sm.nodes.take 610).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1282).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1283).foldl (applyNodeRingAttn pm) initPM)
    5494 10203 10204 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5494 hPM10203 hPM10204 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

/-! ### Zigzag L4 firing (tid 5543) -/
/-- SM zigzag L4 node (`outs = [5543]`). -/
def nSMz4 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5538, 5539, 5540, 5541, 5542], outs := [5543], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L4 node (`outs = [10375]`). -/
def nR0z4 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10351, 5539, 5540, 5541, 5542], outs := [10375], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L4 node (`outs = [10376]`). -/
def nR1z4 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10352, 5539, 5540, 5541, 5542], outs := [10376], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L4 (`intermediateGoal_5543`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5543_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM 5538
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 10351,
             (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 10352])
    (hk_repl : (sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM 5539
        = (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5539)
    (hv_repl : (sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM 5540
        = (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5540)
    (hq_sm : 0 < ((sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM 5538).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM 5539).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM 5540).shape.length)
    (hk_shape : ((pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5539).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5540).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5542)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 10351,
             (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 10352])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5539,
             (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5539])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5540,
             (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5540])
          ((pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5541)
          ((pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5542)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 10351,
             (pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 10352])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 5539,
             (pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 5539])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 5540,
             (pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 5540])
          ((pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 5541)
          ((pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 5542)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5543
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5543 : denoteGraph_ringAttn sm initSM 5543
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM) nSMz4 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5543 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5543 646 (by native_decide) (by native_decide),
        show sm.nodes.take 646 = sm.nodes.take 645 ++ [nSMz4] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5538 5539 5540 5541 5542 5543 [16, 4, 64, 64, 1, 0]
  have hPM10375 : denoteGraph_ringAttn pm initPM 10375
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM) nR0z4 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10375 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10375 1353 (by native_decide) (by native_decide),
        show pm.nodes.take 1353 = pm.nodes.take 1352 ++ [nR0z4] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 10351 5539 5540 5541 5542 10375 [16, 4, 64, 64, 1, 0]
  have hPM10376 : denoteGraph_ringAttn pm initPM 10376
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM) nR1z4 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10376 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10376 1354 (by native_decide) (by native_decide),
        show pm.nodes.take 1354 = pm.nodes.take 1353 ++ [nR1z4] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 10352 5539 5540 5541 5542 10376 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1352 ↔ take 1353 agree on nR1z4's inputs (10352,5539,5540,5541,5542)
  have e10352 : (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 10352
      = (pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 10352 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10352 1352 1353 (by omega) (by native_decide) (by native_decide)).symm
  have e5539 : (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5539
      = (pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 5539 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5539 1352 1353 (by omega) (by native_decide) (by native_decide)).symm
  have e5540 : (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5540
      = (pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 5540 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5540 1352 1353 (by omega) (by native_decide) (by native_decide)).symm
  have e5541 : (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5541
      = (pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 5541 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5541 1352 1353 (by omega) (by native_decide) (by native_decide)).symm
  have e5542 : (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5542
      = (pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 5542 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5542 1352 1353 (by omega) (by native_decide) (by native_decide)).symm
  have e10351 : (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 10351
      = (pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM 10351 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10351 1352 1353 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM) nR1z4
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM) nR1z4 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z4 = [nR0z4, nR1z4] from by native_decide]
      intro m hm; fin_cases hm
      · exact e10351
      · exact e10352
    · rw [show ringAttnBuddies pm nR1z4 = [nR0z4, nR1z4] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5539
      · exact e5539
    · rw [show ringAttnBuddies pm nR1z4 = [nR0z4, nR1z4] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5540
      · exact e5540
    · exact e5541
    · exact e5542
  -- cu-seqlens agreement (5541/5542 are init leaves in both graphs, equal via init goals)
  have hcu5541 : denoteGraph sm initSM 5541 = denoteGraph pm initPM 5541 :=
    recon_weight initSM initPM hInit initGoal_5541 (by native_decide) 5541 rfl rfl rfl rfl
  have hcu5542 : denoteGraph sm initSM 5542 = denoteGraph pm initPM 5542 :=
    recon_weight initSM initPM hInit initGoal_5542 (by native_decide) 5542 rfl rfl rfl rfl
  have hSM5541 : (sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM 5541 = denoteGraph sm initSM 5541 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5541 645 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5541 (by native_decide)
  have hSM5542 : (sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM 5542 = denoteGraph sm initSM 5542 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5542 645 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5542 (by native_decide)
  have hPM5541 : (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5541 = denoteGraph pm initPM 5541 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5541 1352 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5541 (by native_decide)
  have hPM5542 : (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5542 = denoteGraph pm initPM 5542 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5542 1352 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5542 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM 5541
      = (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5541 := by
    rw [hSM5541, hPM5541, hcu5541]
  have hcuK_sm_pm : (sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM 5542
      = (pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM 5542 := by
    rw [hSM5542, hPM5542, hcu5542]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5543
    nSMz4 nR0z4 nR1z4
    ((sm.nodes.take 645).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1352).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1353).foldl (applyNodeRingAttn pm) initPM)
    5543 10375 10376 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5543 hPM10375 hPM10376 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

/-! ### Zigzag L5 firing (tid 5592) -/
/-- SM zigzag L5 node (`outs = [5592]`). -/
def nSMz5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5587, 5588, 5589, 5590, 5591], outs := [5592], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L5 node (`outs = [10547]`). -/
def nR0z5 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10523, 5588, 5589, 5590, 5591], outs := [10547], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L5 node (`outs = [10548]`). -/
def nR1z5 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10524, 5588, 5589, 5590, 5591], outs := [10548], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L5 (`intermediateGoal_5592`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5592_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM 5587
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 10523,
             (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 10524])
    (hk_repl : (sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM 5588
        = (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5588)
    (hv_repl : (sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM 5589
        = (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5589)
    (hq_sm : 0 < ((sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM 5587).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM 5588).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM 5589).shape.length)
    (hk_shape : ((pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5588).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5589).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5591)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 10523,
             (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 10524])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5588,
             (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5588])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5589,
             (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5589])
          ((pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5590)
          ((pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5591)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 10523,
             (pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 10524])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 5588,
             (pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 5588])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 5589,
             (pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 5589])
          ((pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 5590)
          ((pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 5591)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5592
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5592 : denoteGraph_ringAttn sm initSM 5592
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM) nSMz5 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5592 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5592 681 (by native_decide) (by native_decide),
        show sm.nodes.take 681 = sm.nodes.take 680 ++ [nSMz5] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5587 5588 5589 5590 5591 5592 [16, 4, 64, 64, 1, 0]
  have hPM10547 : denoteGraph_ringAttn pm initPM 10547
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM) nR0z5 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10547 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10547 1423 (by native_decide) (by native_decide),
        show pm.nodes.take 1423 = pm.nodes.take 1422 ++ [nR0z5] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 10523 5588 5589 5590 5591 10547 [16, 4, 64, 64, 1, 0]
  have hPM10548 : denoteGraph_ringAttn pm initPM 10548
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM) nR1z5 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10548 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10548 1424 (by native_decide) (by native_decide),
        show pm.nodes.take 1424 = pm.nodes.take 1423 ++ [nR1z5] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 10524 5588 5589 5590 5591 10548 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1422 ↔ take 1423 agree on nR1z5's inputs (10524,5588,5589,5590,5591)
  have e10524 : (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 10524
      = (pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 10524 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10524 1422 1423 (by omega) (by native_decide) (by native_decide)).symm
  have e5588 : (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5588
      = (pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 5588 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5588 1422 1423 (by omega) (by native_decide) (by native_decide)).symm
  have e5589 : (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5589
      = (pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 5589 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5589 1422 1423 (by omega) (by native_decide) (by native_decide)).symm
  have e5590 : (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5590
      = (pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 5590 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5590 1422 1423 (by omega) (by native_decide) (by native_decide)).symm
  have e5591 : (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5591
      = (pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 5591 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5591 1422 1423 (by omega) (by native_decide) (by native_decide)).symm
  have e10523 : (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 10523
      = (pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM 10523 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10523 1422 1423 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM) nR1z5
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM) nR1z5 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z5 = [nR0z5, nR1z5] from by native_decide]
      intro m hm; fin_cases hm
      · exact e10523
      · exact e10524
    · rw [show ringAttnBuddies pm nR1z5 = [nR0z5, nR1z5] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5588
      · exact e5588
    · rw [show ringAttnBuddies pm nR1z5 = [nR0z5, nR1z5] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5589
      · exact e5589
    · exact e5590
    · exact e5591
  -- cu-seqlens agreement (5590/5591 are init leaves in both graphs, equal via init goals)
  have hcu5590 : denoteGraph sm initSM 5590 = denoteGraph pm initPM 5590 :=
    recon_weight initSM initPM hInit initGoal_5590 (by native_decide) 5590 rfl rfl rfl rfl
  have hcu5591 : denoteGraph sm initSM 5591 = denoteGraph pm initPM 5591 :=
    recon_weight initSM initPM hInit initGoal_5591 (by native_decide) 5591 rfl rfl rfl rfl
  have hSM5590 : (sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM 5590 = denoteGraph sm initSM 5590 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5590 680 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5590 (by native_decide)
  have hSM5591 : (sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM 5591 = denoteGraph sm initSM 5591 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5591 680 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5591 (by native_decide)
  have hPM5590 : (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5590 = denoteGraph pm initPM 5590 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5590 1422 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5590 (by native_decide)
  have hPM5591 : (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5591 = denoteGraph pm initPM 5591 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5591 1422 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5591 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM 5590
      = (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5590 := by
    rw [hSM5590, hPM5590, hcu5590]
  have hcuK_sm_pm : (sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM 5591
      = (pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM 5591 := by
    rw [hSM5591, hPM5591, hcu5591]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5592
    nSMz5 nR0z5 nR1z5
    ((sm.nodes.take 680).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1422).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1423).foldl (applyNodeRingAttn pm) initPM)
    5592 10547 10548 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5592 hPM10547 hPM10548 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

/-! ### Zigzag L6 firing (tid 5641) -/
/-- SM zigzag L6 node (`outs = [5641]`). -/
def nSMz6 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5636, 5637, 5638, 5639, 5640], outs := [5641], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L6 node (`outs = [10719]`). -/
def nR0z6 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10695, 5637, 5638, 5639, 5640], outs := [10719], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L6 node (`outs = [10720]`). -/
def nR1z6 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10696, 5637, 5638, 5639, 5640], outs := [10720], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L6 (`intermediateGoal_5641`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5641_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM 5636
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 10695,
             (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 10696])
    (hk_repl : (sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM 5637
        = (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5637)
    (hv_repl : (sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM 5638
        = (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5638)
    (hq_sm : 0 < ((sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM 5636).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM 5637).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM 5638).shape.length)
    (hk_shape : ((pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5637).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5638).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5640)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 10695,
             (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 10696])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5637,
             (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5637])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5638,
             (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5638])
          ((pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5639)
          ((pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5640)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 10695,
             (pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 10696])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 5637,
             (pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 5637])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 5638,
             (pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 5638])
          ((pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 5639)
          ((pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 5640)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5641
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5641 : denoteGraph_ringAttn sm initSM 5641
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM) nSMz6 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5641 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5641 716 (by native_decide) (by native_decide),
        show sm.nodes.take 716 = sm.nodes.take 715 ++ [nSMz6] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5636 5637 5638 5639 5640 5641 [16, 4, 64, 64, 1, 0]
  have hPM10719 : denoteGraph_ringAttn pm initPM 10719
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM) nR0z6 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10719 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10719 1493 (by native_decide) (by native_decide),
        show pm.nodes.take 1493 = pm.nodes.take 1492 ++ [nR0z6] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 10695 5637 5638 5639 5640 10719 [16, 4, 64, 64, 1, 0]
  have hPM10720 : denoteGraph_ringAttn pm initPM 10720
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM) nR1z6 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10720 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10720 1494 (by native_decide) (by native_decide),
        show pm.nodes.take 1494 = pm.nodes.take 1493 ++ [nR1z6] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 10696 5637 5638 5639 5640 10720 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1492 ↔ take 1493 agree on nR1z6's inputs (10696,5637,5638,5639,5640)
  have e10696 : (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 10696
      = (pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 10696 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10696 1492 1493 (by omega) (by native_decide) (by native_decide)).symm
  have e5637 : (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5637
      = (pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 5637 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5637 1492 1493 (by omega) (by native_decide) (by native_decide)).symm
  have e5638 : (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5638
      = (pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 5638 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5638 1492 1493 (by omega) (by native_decide) (by native_decide)).symm
  have e5639 : (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5639
      = (pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 5639 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5639 1492 1493 (by omega) (by native_decide) (by native_decide)).symm
  have e5640 : (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5640
      = (pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 5640 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5640 1492 1493 (by omega) (by native_decide) (by native_decide)).symm
  have e10695 : (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 10695
      = (pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM 10695 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10695 1492 1493 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM) nR1z6
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM) nR1z6 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z6 = [nR0z6, nR1z6] from by native_decide]
      intro m hm; fin_cases hm
      · exact e10695
      · exact e10696
    · rw [show ringAttnBuddies pm nR1z6 = [nR0z6, nR1z6] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5637
      · exact e5637
    · rw [show ringAttnBuddies pm nR1z6 = [nR0z6, nR1z6] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5638
      · exact e5638
    · exact e5639
    · exact e5640
  -- cu-seqlens agreement (5639/5640 are init leaves in both graphs, equal via init goals)
  have hcu5639 : denoteGraph sm initSM 5639 = denoteGraph pm initPM 5639 :=
    recon_weight initSM initPM hInit initGoal_5639 (by native_decide) 5639 rfl rfl rfl rfl
  have hcu5640 : denoteGraph sm initSM 5640 = denoteGraph pm initPM 5640 :=
    recon_weight initSM initPM hInit initGoal_5640 (by native_decide) 5640 rfl rfl rfl rfl
  have hSM5639 : (sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM 5639 = denoteGraph sm initSM 5639 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5639 715 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5639 (by native_decide)
  have hSM5640 : (sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM 5640 = denoteGraph sm initSM 5640 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5640 715 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5640 (by native_decide)
  have hPM5639 : (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5639 = denoteGraph pm initPM 5639 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5639 1492 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5639 (by native_decide)
  have hPM5640 : (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5640 = denoteGraph pm initPM 5640 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5640 1492 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5640 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM 5639
      = (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5639 := by
    rw [hSM5639, hPM5639, hcu5639]
  have hcuK_sm_pm : (sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM 5640
      = (pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM 5640 := by
    rw [hSM5640, hPM5640, hcu5640]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5641
    nSMz6 nR0z6 nR1z6
    ((sm.nodes.take 715).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1492).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1493).foldl (applyNodeRingAttn pm) initPM)
    5641 10719 10720 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5641 hPM10719 hPM10720 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

/-! ### Zigzag L7 firing (tid 5690) -/
/-- SM zigzag L7 node (`outs = [5690]`). -/
def nSMz7 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5685, 5686, 5687, 5688, 5689], outs := [5690], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L7 node (`outs = [10891]`). -/
def nR0z7 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10867, 5686, 5687, 5688, 5689], outs := [10891], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L7 node (`outs = [10892]`). -/
def nR1z7 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10868, 5686, 5687, 5688, 5689], outs := [10892], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L7 (`intermediateGoal_5690`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5690_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM 5685
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 10867,
             (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 10868])
    (hk_repl : (sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM 5686
        = (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5686)
    (hv_repl : (sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM 5687
        = (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5687)
    (hq_sm : 0 < ((sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM 5685).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM 5686).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM 5687).shape.length)
    (hk_shape : ((pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5686).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5687).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5689)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 10867,
             (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 10868])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5686,
             (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5686])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5687,
             (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5687])
          ((pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5688)
          ((pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5689)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 10867,
             (pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 10868])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 5686,
             (pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 5686])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 5687,
             (pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 5687])
          ((pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 5688)
          ((pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 5689)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5690
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5690 : denoteGraph_ringAttn sm initSM 5690
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM) nSMz7 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5690 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5690 751 (by native_decide) (by native_decide),
        show sm.nodes.take 751 = sm.nodes.take 750 ++ [nSMz7] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5685 5686 5687 5688 5689 5690 [16, 4, 64, 64, 1, 0]
  have hPM10891 : denoteGraph_ringAttn pm initPM 10891
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM) nR0z7 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10891 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10891 1563 (by native_decide) (by native_decide),
        show pm.nodes.take 1563 = pm.nodes.take 1562 ++ [nR0z7] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 10867 5686 5687 5688 5689 10891 [16, 4, 64, 64, 1, 0]
  have hPM10892 : denoteGraph_ringAttn pm initPM 10892
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM) nR1z7 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 10892 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 10892 1564 (by native_decide) (by native_decide),
        show pm.nodes.take 1564 = pm.nodes.take 1563 ++ [nR1z7] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 10868 5686 5687 5688 5689 10892 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1562 ↔ take 1563 agree on nR1z7's inputs (10868,5686,5687,5688,5689)
  have e10868 : (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 10868
      = (pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 10868 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10868 1562 1563 (by omega) (by native_decide) (by native_decide)).symm
  have e5686 : (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5686
      = (pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 5686 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5686 1562 1563 (by omega) (by native_decide) (by native_decide)).symm
  have e5687 : (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5687
      = (pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 5687 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5687 1562 1563 (by omega) (by native_decide) (by native_decide)).symm
  have e5688 : (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5688
      = (pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 5688 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5688 1562 1563 (by omega) (by native_decide) (by native_decide)).symm
  have e5689 : (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5689
      = (pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 5689 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5689 1562 1563 (by omega) (by native_decide) (by native_decide)).symm
  have e10867 : (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 10867
      = (pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM 10867 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 10867 1562 1563 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM) nR1z7
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM) nR1z7 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z7 = [nR0z7, nR1z7] from by native_decide]
      intro m hm; fin_cases hm
      · exact e10867
      · exact e10868
    · rw [show ringAttnBuddies pm nR1z7 = [nR0z7, nR1z7] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5686
      · exact e5686
    · rw [show ringAttnBuddies pm nR1z7 = [nR0z7, nR1z7] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5687
      · exact e5687
    · exact e5688
    · exact e5689
  -- cu-seqlens agreement (5688/5689 are init leaves in both graphs, equal via init goals)
  have hcu5688 : denoteGraph sm initSM 5688 = denoteGraph pm initPM 5688 :=
    recon_weight initSM initPM hInit initGoal_5688 (by native_decide) 5688 rfl rfl rfl rfl
  have hcu5689 : denoteGraph sm initSM 5689 = denoteGraph pm initPM 5689 :=
    recon_weight initSM initPM hInit initGoal_5689 (by native_decide) 5689 rfl rfl rfl rfl
  have hSM5688 : (sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM 5688 = denoteGraph sm initSM 5688 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5688 750 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5688 (by native_decide)
  have hSM5689 : (sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM 5689 = denoteGraph sm initSM 5689 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5689 750 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5689 (by native_decide)
  have hPM5688 : (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5688 = denoteGraph pm initPM 5688 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5688 1562 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5688 (by native_decide)
  have hPM5689 : (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5689 = denoteGraph pm initPM 5689 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5689 1562 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5689 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM 5688
      = (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5688 := by
    rw [hSM5688, hPM5688, hcu5688]
  have hcuK_sm_pm : (sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM 5689
      = (pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM 5689 := by
    rw [hSM5689, hPM5689, hcu5689]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5690
    nSMz7 nR0z7 nR1z7
    ((sm.nodes.take 750).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1562).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1563).foldl (applyNodeRingAttn pm) initPM)
    5690 10891 10892 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5690 hPM10891 hPM10892 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

/-! ### Zigzag L8 firing (tid 5739) -/
/-- SM zigzag L8 node (`outs = [5739]`). -/
def nSMz8 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5734, 5735, 5736, 5737, 5738], outs := [5739], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L8 node (`outs = [11063]`). -/
def nR0z8 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11039, 5735, 5736, 5737, 5738], outs := [11063], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L8 node (`outs = [11064]`). -/
def nR1z8 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11040, 5735, 5736, 5737, 5738], outs := [11064], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L8 (`intermediateGoal_5739`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5739_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM 5734
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 11039,
             (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 11040])
    (hk_repl : (sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM 5735
        = (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5735)
    (hv_repl : (sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM 5736
        = (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5736)
    (hq_sm : 0 < ((sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM 5734).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM 5735).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM 5736).shape.length)
    (hk_shape : ((pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5735).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5736).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5738)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 11039,
             (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 11040])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5735,
             (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5735])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5736,
             (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5736])
          ((pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5737)
          ((pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5738)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 11039,
             (pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 11040])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 5735,
             (pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 5735])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 5736,
             (pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 5736])
          ((pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 5737)
          ((pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 5738)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5739
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5739 : denoteGraph_ringAttn sm initSM 5739
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM) nSMz8 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5739 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5739 786 (by native_decide) (by native_decide),
        show sm.nodes.take 786 = sm.nodes.take 785 ++ [nSMz8] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5734 5735 5736 5737 5738 5739 [16, 4, 64, 64, 1, 0]
  have hPM11063 : denoteGraph_ringAttn pm initPM 11063
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM) nR0z8 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 11063 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 11063 1633 (by native_decide) (by native_decide),
        show pm.nodes.take 1633 = pm.nodes.take 1632 ++ [nR0z8] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 11039 5735 5736 5737 5738 11063 [16, 4, 64, 64, 1, 0]
  have hPM11064 : denoteGraph_ringAttn pm initPM 11064
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM) nR1z8 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 11064 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 11064 1634 (by native_decide) (by native_decide),
        show pm.nodes.take 1634 = pm.nodes.take 1633 ++ [nR1z8] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 11040 5735 5736 5737 5738 11064 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1632 ↔ take 1633 agree on nR1z8's inputs (11040,5735,5736,5737,5738)
  have e11040 : (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 11040
      = (pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 11040 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 11040 1632 1633 (by omega) (by native_decide) (by native_decide)).symm
  have e5735 : (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5735
      = (pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 5735 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5735 1632 1633 (by omega) (by native_decide) (by native_decide)).symm
  have e5736 : (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5736
      = (pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 5736 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5736 1632 1633 (by omega) (by native_decide) (by native_decide)).symm
  have e5737 : (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5737
      = (pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 5737 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5737 1632 1633 (by omega) (by native_decide) (by native_decide)).symm
  have e5738 : (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5738
      = (pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 5738 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5738 1632 1633 (by omega) (by native_decide) (by native_decide)).symm
  have e11039 : (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 11039
      = (pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM 11039 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 11039 1632 1633 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM) nR1z8
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM) nR1z8 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z8 = [nR0z8, nR1z8] from by native_decide]
      intro m hm; fin_cases hm
      · exact e11039
      · exact e11040
    · rw [show ringAttnBuddies pm nR1z8 = [nR0z8, nR1z8] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5735
      · exact e5735
    · rw [show ringAttnBuddies pm nR1z8 = [nR0z8, nR1z8] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5736
      · exact e5736
    · exact e5737
    · exact e5738
  -- cu-seqlens agreement (5737/5738 are init leaves in both graphs, equal via init goals)
  have hcu5737 : denoteGraph sm initSM 5737 = denoteGraph pm initPM 5737 :=
    recon_weight initSM initPM hInit initGoal_5737 (by native_decide) 5737 rfl rfl rfl rfl
  have hcu5738 : denoteGraph sm initSM 5738 = denoteGraph pm initPM 5738 :=
    recon_weight initSM initPM hInit initGoal_5738 (by native_decide) 5738 rfl rfl rfl rfl
  have hSM5737 : (sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM 5737 = denoteGraph sm initSM 5737 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5737 785 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5737 (by native_decide)
  have hSM5738 : (sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM 5738 = denoteGraph sm initSM 5738 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5738 785 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5738 (by native_decide)
  have hPM5737 : (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5737 = denoteGraph pm initPM 5737 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5737 1632 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5737 (by native_decide)
  have hPM5738 : (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5738 = denoteGraph pm initPM 5738 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5738 1632 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5738 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM 5737
      = (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5737 := by
    rw [hSM5737, hPM5737, hcu5737]
  have hcuK_sm_pm : (sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM 5738
      = (pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM 5738 := by
    rw [hSM5738, hPM5738, hcu5738]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5739
    nSMz8 nR0z8 nR1z8
    ((sm.nodes.take 785).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1632).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1633).foldl (applyNodeRingAttn pm) initPM)
    5739 11063 11064 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5739 hPM11063 hPM11064 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

/-! ### Zigzag L9 firing (tid 5788) -/
/-- SM zigzag L9 node (`outs = [5788]`). -/
def nSMz9 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5783, 5784, 5785, 5786, 5787], outs := [5788], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L9 node (`outs = [11235]`). -/
def nR0z9 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11211, 5784, 5785, 5786, 5787], outs := [11235], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L9 node (`outs = [11236]`). -/
def nR1z9 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11212, 5784, 5785, 5786, 5787], outs := [11236], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L9 (`intermediateGoal_5788`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5788_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM 5783
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 11211,
             (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 11212])
    (hk_repl : (sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM 5784
        = (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5784)
    (hv_repl : (sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM 5785
        = (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5785)
    (hq_sm : 0 < ((sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM 5783).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM 5784).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM 5785).shape.length)
    (hk_shape : ((pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5784).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5785).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5787)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 11211,
             (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 11212])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5784,
             (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5784])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5785,
             (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5785])
          ((pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5786)
          ((pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5787)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 11211,
             (pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 11212])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 5784,
             (pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 5784])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 5785,
             (pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 5785])
          ((pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 5786)
          ((pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 5787)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5788
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5788 : denoteGraph_ringAttn sm initSM 5788
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM) nSMz9 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5788 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5788 821 (by native_decide) (by native_decide),
        show sm.nodes.take 821 = sm.nodes.take 820 ++ [nSMz9] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5783 5784 5785 5786 5787 5788 [16, 4, 64, 64, 1, 0]
  have hPM11235 : denoteGraph_ringAttn pm initPM 11235
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM) nR0z9 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 11235 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 11235 1703 (by native_decide) (by native_decide),
        show pm.nodes.take 1703 = pm.nodes.take 1702 ++ [nR0z9] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 11211 5784 5785 5786 5787 11235 [16, 4, 64, 64, 1, 0]
  have hPM11236 : denoteGraph_ringAttn pm initPM 11236
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM) nR1z9 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 11236 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 11236 1704 (by native_decide) (by native_decide),
        show pm.nodes.take 1704 = pm.nodes.take 1703 ++ [nR1z9] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 11212 5784 5785 5786 5787 11236 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1702 ↔ take 1703 agree on nR1z9's inputs (11212,5784,5785,5786,5787)
  have e11212 : (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 11212
      = (pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 11212 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 11212 1702 1703 (by omega) (by native_decide) (by native_decide)).symm
  have e5784 : (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5784
      = (pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 5784 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5784 1702 1703 (by omega) (by native_decide) (by native_decide)).symm
  have e5785 : (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5785
      = (pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 5785 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5785 1702 1703 (by omega) (by native_decide) (by native_decide)).symm
  have e5786 : (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5786
      = (pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 5786 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5786 1702 1703 (by omega) (by native_decide) (by native_decide)).symm
  have e5787 : (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5787
      = (pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 5787 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5787 1702 1703 (by omega) (by native_decide) (by native_decide)).symm
  have e11211 : (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 11211
      = (pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM 11211 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 11211 1702 1703 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM) nR1z9
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM) nR1z9 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z9 = [nR0z9, nR1z9] from by native_decide]
      intro m hm; fin_cases hm
      · exact e11211
      · exact e11212
    · rw [show ringAttnBuddies pm nR1z9 = [nR0z9, nR1z9] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5784
      · exact e5784
    · rw [show ringAttnBuddies pm nR1z9 = [nR0z9, nR1z9] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5785
      · exact e5785
    · exact e5786
    · exact e5787
  -- cu-seqlens agreement (5786/5787 are init leaves in both graphs, equal via init goals)
  have hcu5786 : denoteGraph sm initSM 5786 = denoteGraph pm initPM 5786 :=
    recon_weight initSM initPM hInit initGoal_5786 (by native_decide) 5786 rfl rfl rfl rfl
  have hcu5787 : denoteGraph sm initSM 5787 = denoteGraph pm initPM 5787 :=
    recon_weight initSM initPM hInit initGoal_5787 (by native_decide) 5787 rfl rfl rfl rfl
  have hSM5786 : (sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM 5786 = denoteGraph sm initSM 5786 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5786 820 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5786 (by native_decide)
  have hSM5787 : (sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM 5787 = denoteGraph sm initSM 5787 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5787 820 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5787 (by native_decide)
  have hPM5786 : (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5786 = denoteGraph pm initPM 5786 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5786 1702 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5786 (by native_decide)
  have hPM5787 : (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5787 = denoteGraph pm initPM 5787 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5787 1702 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5787 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM 5786
      = (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5786 := by
    rw [hSM5786, hPM5786, hcu5786]
  have hcuK_sm_pm : (sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM 5787
      = (pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM 5787 := by
    rw [hSM5787, hPM5787, hcu5787]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5788
    nSMz9 nR0z9 nR1z9
    ((sm.nodes.take 820).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1702).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1703).foldl (applyNodeRingAttn pm) initPM)
    5788 11235 11236 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5788 hPM11235 hPM11236 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

/-! ### Zigzag L10 firing (tid 5837) -/
/-- SM zigzag L10 node (`outs = [5837]`). -/
def nSMz10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5832, 5833, 5834, 5835, 5836], outs := [5837], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L10 node (`outs = [11407]`). -/
def nR0z10 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11383, 5833, 5834, 5835, 5836], outs := [11407], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L10 node (`outs = [11408]`). -/
def nR1z10 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11384, 5833, 5834, 5835, 5836], outs := [11408], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L10 (`intermediateGoal_5837`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5837_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM 5832
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 11383,
             (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 11384])
    (hk_repl : (sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM 5833
        = (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5833)
    (hv_repl : (sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM 5834
        = (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5834)
    (hq_sm : 0 < ((sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM 5832).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM 5833).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM 5834).shape.length)
    (hk_shape : ((pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5833).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5834).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5836)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 11383,
             (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 11384])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5833,
             (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5833])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5834,
             (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5834])
          ((pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5835)
          ((pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5836)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 11383,
             (pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 11384])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 5833,
             (pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 5833])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 5834,
             (pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 5834])
          ((pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 5835)
          ((pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 5836)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5837
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5837 : denoteGraph_ringAttn sm initSM 5837
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM) nSMz10 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5837 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5837 856 (by native_decide) (by native_decide),
        show sm.nodes.take 856 = sm.nodes.take 855 ++ [nSMz10] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5832 5833 5834 5835 5836 5837 [16, 4, 64, 64, 1, 0]
  have hPM11407 : denoteGraph_ringAttn pm initPM 11407
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM) nR0z10 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 11407 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 11407 1773 (by native_decide) (by native_decide),
        show pm.nodes.take 1773 = pm.nodes.take 1772 ++ [nR0z10] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 11383 5833 5834 5835 5836 11407 [16, 4, 64, 64, 1, 0]
  have hPM11408 : denoteGraph_ringAttn pm initPM 11408
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM) nR1z10 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 11408 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 11408 1774 (by native_decide) (by native_decide),
        show pm.nodes.take 1774 = pm.nodes.take 1773 ++ [nR1z10] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 11384 5833 5834 5835 5836 11408 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1772 ↔ take 1773 agree on nR1z10's inputs (11384,5833,5834,5835,5836)
  have e11384 : (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 11384
      = (pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 11384 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 11384 1772 1773 (by omega) (by native_decide) (by native_decide)).symm
  have e5833 : (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5833
      = (pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 5833 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5833 1772 1773 (by omega) (by native_decide) (by native_decide)).symm
  have e5834 : (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5834
      = (pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 5834 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5834 1772 1773 (by omega) (by native_decide) (by native_decide)).symm
  have e5835 : (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5835
      = (pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 5835 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5835 1772 1773 (by omega) (by native_decide) (by native_decide)).symm
  have e5836 : (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5836
      = (pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 5836 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5836 1772 1773 (by omega) (by native_decide) (by native_decide)).symm
  have e11383 : (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 11383
      = (pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM 11383 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 11383 1772 1773 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM) nR1z10
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM) nR1z10 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z10 = [nR0z10, nR1z10] from by native_decide]
      intro m hm; fin_cases hm
      · exact e11383
      · exact e11384
    · rw [show ringAttnBuddies pm nR1z10 = [nR0z10, nR1z10] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5833
      · exact e5833
    · rw [show ringAttnBuddies pm nR1z10 = [nR0z10, nR1z10] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5834
      · exact e5834
    · exact e5835
    · exact e5836
  -- cu-seqlens agreement (5835/5836 are init leaves in both graphs, equal via init goals)
  have hcu5835 : denoteGraph sm initSM 5835 = denoteGraph pm initPM 5835 :=
    recon_weight initSM initPM hInit initGoal_5835 (by native_decide) 5835 rfl rfl rfl rfl
  have hcu5836 : denoteGraph sm initSM 5836 = denoteGraph pm initPM 5836 :=
    recon_weight initSM initPM hInit initGoal_5836 (by native_decide) 5836 rfl rfl rfl rfl
  have hSM5835 : (sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM 5835 = denoteGraph sm initSM 5835 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5835 855 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5835 (by native_decide)
  have hSM5836 : (sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM 5836 = denoteGraph sm initSM 5836 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5836 855 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5836 (by native_decide)
  have hPM5835 : (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5835 = denoteGraph pm initPM 5835 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5835 1772 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5835 (by native_decide)
  have hPM5836 : (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5836 = denoteGraph pm initPM 5836 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5836 1772 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5836 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM 5835
      = (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5835 := by
    rw [hSM5835, hPM5835, hcu5835]
  have hcuK_sm_pm : (sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM 5836
      = (pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM 5836 := by
    rw [hSM5836, hPM5836, hcu5836]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5837
    nSMz10 nR0z10 nR1z10
    ((sm.nodes.take 855).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1772).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1773).foldl (applyNodeRingAttn pm) initPM)
    5837 11407 11408 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5837 hPM11407 hPM11408 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

/-! ### Zigzag L11 firing (tid 5886) -/
/-- SM zigzag L11 node (`outs = [5886]`). -/
def nSMz11 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5881, 5882, 5883, 5884, 5885], outs := [5886], params := [16, 4, 64, 64, 1, 0] }

/-- PM r0 zigzag L11 node (`outs = [11579]`). -/
def nR0z11 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [11555, 5882, 5883, 5884, 5885], outs := [11579], params := [16, 4, 64, 64, 1, 0] }

/-- PM r1 zigzag L11 node (`outs = [11580]`). -/
def nR1z11 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [11556, 5882, 5883, 5884, 5885], outs := [11580], params := [16, 4, 64, 64, 1, 0] }

/- **Zigzag L11 (`intermediateGoal_5886`) over `denoteGraph_ringAttn`, conditional
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
theorem recon_intermediateGoal_5886_ringAttn_of_qkv (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hq_full : (sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM 5881
        = allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 11555,
             (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 11556])
    (hk_repl : (sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM 5882
        = (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5882)
    (hv_repl : (sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM 5883
        = (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5883)
    (hq_sm : 0 < ((sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM 5881).shape.length)
    (hk_sm : 0 < ((sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM 5882).shape.length)
    (hv_sm : 0 < ((sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM 5883).shape.length)
    (hk_shape : ((pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5882).shape
        = [4096, 4, 64])
    (hv_shape : ((pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5883).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5885)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 11555,
             (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 11556])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5882,
             (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5882])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5883,
             (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5883])
          ((pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5884)
          ((pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5885)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64])
    (hfull_shape' :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 11555,
             (pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 11556])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 5882,
             (pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 5882])
          (allGatherPrimDimN 0 2 0
            [(pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 5883,
             (pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 5883])
          ((pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 5884)
          ((pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 5885)
          16 4 64 64 (decide ((1 : Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    InitGoalHolds pm.numRanks intermediateGoal_5886
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- node reductions (denote ↔ applyNodeRingAttn_zigzag over prefix folds)
  have hSM5886 : denoteGraph_ringAttn sm initSM 5886
      = applyNodeRingAttn_zigzag sm ((sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM) nSMz11 := by
    show sm.nodes.foldl (applyNodeRingAttn sm) initSM 5886 = _
    rw [foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5886 891 (by native_decide) (by native_decide),
        show sm.nodes.take 891 = sm.nodes.take 890 ++ [nSMz11] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm _ 0 5881 5882 5883 5884 5885 5886 [16, 4, 64, 64, 1, 0]
  have hPM11579 : denoteGraph_ringAttn pm initPM 11579
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM) nR0z11 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 11579 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 11579 1843 (by native_decide) (by native_decide),
        show pm.nodes.take 1843 = pm.nodes.take 1842 ++ [nR0z11] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 0 11555 5882 5883 5884 5885 11579 [16, 4, 64, 64, 1, 0]
  have hPM11580 : denoteGraph_ringAttn pm initPM 11580
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM) nR1z11 := by
    show pm.nodes.foldl (applyNodeRingAttn pm) initPM 11580 = _
    rw [foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 11580 1844 (by native_decide) (by native_decide),
        show pm.nodes.take 1844 = pm.nodes.take 1843 ++ [nR1z11] from by native_decide,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out pm _ 1 11556 5882 5883 5884 5885 11580 [16, 4, 64, 64, 1, 0]
  -- r1 store bridge: take 1842 ↔ take 1843 agree on nR1z11's inputs (11556,5882,5883,5884,5885)
  have e11556 : (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 11556
      = (pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 11556 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 11556 1842 1843 (by omega) (by native_decide) (by native_decide)).symm
  have e5882 : (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5882
      = (pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 5882 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5882 1842 1843 (by omega) (by native_decide) (by native_decide)).symm
  have e5883 : (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5883
      = (pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 5883 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5883 1842 1843 (by omega) (by native_decide) (by native_decide)).symm
  have e5884 : (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5884
      = (pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 5884 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5884 1842 1843 (by omega) (by native_decide) (by native_decide)).symm
  have e5885 : (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5885
      = (pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 5885 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 5885 1842 1843 (by omega) (by native_decide) (by native_decide)).symm
  have e11555 : (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 11555
      = (pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM 11555 :=
    (foldl_take_split_at_not_written_ringAttn pm pm.nodes initPM 11555 1842 1843 (by omega) (by native_decide) (by native_decide)).symm
  have hbridge : applyNodeRingAttn_zigzag pm ((pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM) nR1z11
      = applyNodeRingAttn_zigzag pm ((pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM) nR1z11 := by
    apply attn_zigzag_store_congr
    · rw [show ringAttnBuddies pm nR1z11 = [nR0z11, nR1z11] from by native_decide]
      intro m hm; fin_cases hm
      · exact e11555
      · exact e11556
    · rw [show ringAttnBuddies pm nR1z11 = [nR0z11, nR1z11] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5882
      · exact e5882
    · rw [show ringAttnBuddies pm nR1z11 = [nR0z11, nR1z11] from by native_decide]
      intro m hm; fin_cases hm
      · exact e5883
      · exact e5883
    · exact e5884
    · exact e5885
  -- cu-seqlens agreement (5884/5885 are init leaves in both graphs, equal via init goals)
  have hcu5884 : denoteGraph sm initSM 5884 = denoteGraph pm initPM 5884 :=
    recon_weight initSM initPM hInit initGoal_5884 (by native_decide) 5884 rfl rfl rfl rfl
  have hcu5885 : denoteGraph sm initSM 5885 = denoteGraph pm initPM 5885 :=
    recon_weight initSM initPM hInit initGoal_5885 (by native_decide) 5885 rfl rfl rfl rfl
  have hSM5884 : (sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM 5884 = denoteGraph sm initSM 5884 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5884 890 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5884 (by native_decide)
  have hSM5885 : (sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM 5885 = denoteGraph sm initSM 5885 := by
    rw [← foldl_prefix_eq_full_ringAttn' sm sm.nodes initSM 5885 890 (by native_decide) (by native_decide)]
    exact sm_ring_eq initSM 5885 (by native_decide)
  have hPM5884 : (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5884 = denoteGraph pm initPM 5884 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5884 1842 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5884 (by native_decide)
  have hPM5885 : (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5885 = denoteGraph pm initPM 5885 := by
    rw [← foldl_prefix_eq_full_ringAttn' pm pm.nodes initPM 5885 1842 (by native_decide) (by native_decide)]
    exact pm_ring_eq initPM 5885 (by native_decide)
  have hcuQ_sm_pm : (sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM 5884
      = (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5884 := by
    rw [hSM5884, hPM5884, hcu5884]
  have hcuK_sm_pm : (sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM 5885
      = (pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM 5885 := by
    rw [hSM5885, hPM5885, hcu5885]
  -- Fire the CP gear.
  exact recon_attn_zigzag_2tp_layer_cp initSM initPM intermediateGoal_5886
    nSMz11 nR0z11 nR1z11
    ((sm.nodes.take 890).foldl (applyNodeRingAttn sm) initSM)
    ((pm.nodes.take 1842).foldl (applyNodeRingAttn pm) initPM)
    ((pm.nodes.take 1843).foldl (applyNodeRingAttn pm) initPM)
    5886 11579 11580 2048 4096 16 64 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
    hSM5886 hPM11579 hPM11580 hbridge
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hq_sm hk_sm hv_sm (by rfl) (by rfl)
    hq_full hk_repl hv_repl hk_shape hv_shape h_bound
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl
    hfull_shape hfull_shape'
    rfl rfl rfl rfl rfl rfl

#check @recon_intermediateGoal_5396_ringAttn_of_qkv
#check @recon_intermediateGoal_5445_ringAttn_of_qkv
#check @recon_intermediateGoal_5494_ringAttn_of_qkv
#check @recon_intermediateGoal_5543_ringAttn_of_qkv
#check @recon_intermediateGoal_5592_ringAttn_of_qkv
#check @recon_intermediateGoal_5641_ringAttn_of_qkv
#check @recon_intermediateGoal_5690_ringAttn_of_qkv
#check @recon_intermediateGoal_5739_ringAttn_of_qkv
#check @recon_intermediateGoal_5788_ringAttn_of_qkv
#check @recon_intermediateGoal_5837_ringAttn_of_qkv
#check @recon_intermediateGoal_5886_ringAttn_of_qkv


end TrainVerify.Denote.GeneratedPatterns
