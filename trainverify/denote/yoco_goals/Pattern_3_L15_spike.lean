/-
  Pattern_3_L15_spike.lean — L15 zigzag-band proof.

  L15 is a *generic* (non-boundary) zigzag band layer.  Unlike the L12 boundary
  layer, it has NO `fw_maybe_shuffle` on the Q path (the residual is already in
  zigzag CP layout, carried from L14).  The K/V path is *shared* with L12: the
  K/V projection is computed once in the L12 boundary block and broadcast to all
  12 band layers via a 12-way `FW_multiref` (SM node 512/513); L15's K/V are the
  4th `FW_to` fan-out (`5490 = FW_to 8045`, `5491 = FW_to 8103`).  Hence the K/V
  replication commute reuses the L12 machinery keyed on `hcarry5330`
  (`sm_pm_carry_5330_commute`, proven on `main`).

  The Q path + residual + router head depend on L15's own input carry `5485`
  (= L14's residual output), which is NOT proven on `main`, so it is taken as a
  statement-level hypothesis `hcarry5485` with a vacuity witness (AGENTS.md #29).

  All op-parametric machinery (`applyNodeRingAttn_zigzag_reconstruction_2_cp`,
  `applyNodeRingAttn_zigzag_pair_eq_chunk`, `attn_zigzag_store_congr`, the shape
  helpers, and the K/V/RMS commutes) is imported from Pattern_3_L12_spike.
-/
import denote.yoco_goals.Pattern_3_L12_spike

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

/-! ## L15 attention node declarations -/

def nSM_15 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5489, 5490, 5491, 5492, 5493], outs := [5494],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_15 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [10179, 5490, 5491, 5492, 5493], outs := [10203],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_15 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [10180, 5490, 5491, 5492, 5493], outs := [10204],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_15 : ringAttnBuddies sm_goal_3 nSM_15 = [nSM_15] := by
  show (List.filter (fun m => decide (m.op = nSM_15.op) && decide (m.params = nSM_15.params) &&
      decide (m.ins.getD 3 0 = nSM_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_15.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_15]
  rw [show (List.filter (fun m => decide (m.op = nSM_15.op) && decide (m.params = nSM_15.params) &&
      decide (m.ins.getD 3 0 = nSM_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_15.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_15] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_15 : ringAttnBuddies pm_goal_3 nR0_15 = [nR0_15, nR1_15] := by
  show (List.filter (fun m => decide (m.op = nR0_15.op) && decide (m.params = nR0_15.params) &&
      decide (m.ins.getD 3 0 = nR0_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_15.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_15, nR1_15]
  rw [show (List.filter (fun m => decide (m.op = nR0_15.op) && decide (m.params = nR0_15.params) &&
      decide (m.ins.getD 3 0 = nR0_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_15.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_15, nR1_15] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_15 : ringAttnBuddies pm_goal_3 nR1_15 = [nR0_15, nR1_15] := by
  show (List.filter (fun m => decide (m.op = nR1_15.op) && decide (m.params = nR1_15.params) &&
      decide (m.ins.getD 3 0 = nR1_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_15.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_15, nR1_15]
  rw [show (List.filter (fun m => decide (m.op = nR1_15.op) && decide (m.params = nR1_15.params) &&
      decide (m.ins.getD 3 0 = nR1_15.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_15.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_15, nR1_15] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L15 attention denote ↔ applyNodeRingAttn_zigzag bridges
    SM attn node index = 609, PM r0 = 1277, PM r1 = 1278. -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L15_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5494
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 609).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_15 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5494
      = (sm_goal_3.nodes.take 610).foldl (applyNodeRingAttn sm_goal_3) initSM 5494 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5494 610 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 610 = sm_goal_3.nodes.take 609 ++ [nSM_15] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5489 5490 5491 5492 5493 5494 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L15_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10203
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1277).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_15 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10203
      = (pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM 10203 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10203 1278 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1278 = pm_goal_3.nodes.take 1277 ++ [nR0_15] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 10179 5490 5491 5492 5493 10203 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L15_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 10204
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1278).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_15 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 10204
      = (pm_goal_3.nodes.take 1279).foldl (applyNodeRingAttn pm_goal_3) initPM 10204 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 10204 1279 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1279 = pm_goal_3.nodes.take 1278 ++ [nR1_15] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 10180 5490 5491 5492 5493 10204 [16, 4, 64, 64, 1, 0]

/-! ## L15 well-formed-input `h_bound` vacuity witness (AGENTS.md #29).
    The all-zero cu_seqlens store (leaf 5493) satisfies the K cu_seqlens bound. -/
theorem sm_pm_router_L15_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5493)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _

/-! ## L15 completion roadmap (structural analysis — verified against Goal_3.lean)

  L15 is a *generic* zigzag band layer (NOT the boundary layer L12).  The
  foundation above (node decls `nSM_15`/`nR0_15`/`nR1_15`, buddy proofs, and the
  three attn denote↔applyNode bridges) is verified by direct analogy to the
  proven L12 spike, with L15 TIDs and node indices extracted from Goal_3.lean.

  Remaining assembly (all machinery imported from Pattern_3_L12_spike; only
  TID-specific denote-unfolds are new):

  * **K/V replication (reuse `hcarry5330`, proven on `main`).**
    The K/V projection is computed ONCE in the L12 boundary block and broadcast
    to all 12 band layers by the 12-way `FW_multiref` (SM nodes 512/513).  L15's
    K/V are the 4th fan-out:
      - SM  K `5490 = FW_to 8045`,  V `5491 = FW_to 8103`   (8045/8103 = 4th out
        of `multiref 5334`/`multiref 5336`).
      - PM  K `5490 = FW_to 15827`, V `5491 = FW_to 15933`  (rank-1 last writer).
    The upstream RMS commute `SM 5332 = PM 5332` is `sm_pm_rms_L12_commute`
    (imported); K/V commutes follow exactly as `sm_pm_krepl_L12_commute` /
    `sm_pm_vrepl_L12_commute` with the FW_to output tid `5490`/`5491`.

  * **Q path (NO shuffle — simpler than L12).**  L15's residual is already in
    zigzag CP layout, so the Q RMS reads the carry directly (no `fw_maybe_shuffle`):
      - SM  `5487 = rms(8256, 5486)`, `5489 = per_head(5487, 5488)`;
        `8256 = multiref 5485`.
      - PM r0 `10177 = rms(16203, 5486)`, `10179 = per_head(10177, 5488)`;
        `16203 = multiref 10173`.  r1: `10178`/`10180`, `16211 = multiref 10174`.
    `sm_pm_qfull_L15_commute` is `sm_pm_qfull_L12_commute` MINUS the
    `fw_maybe_shuffle`/`denote_pm_goal_3_1325{7,8}` rewrites, using
    `fw_rms_norm_allGather0_commute_2` + `fw_per_head_..._allGather0_commute_2`
    directly on the carry.

  * **Input carry `hcarry5485` (statement-level hypothesis, L14 not on `main`).**
      `SM 5485 = allGather[PM 10173, PM 10174]`.
    Vacuity: satisfiable since both sides denote the same reconstructed residual;
    threaded as a hypothesis into `sm_pm_router_commute_L15_full` alongside
    `h_bound` (witnessed above).

  * **Attention commute.**  Compose `applyNodeRingAttn_zigzag_reconstruction_2_cp`
    (imported, op-parametric) with the three L15 bridges and `attn_zigzag_store_congr`
    exactly as `sm_pm_attention_L12_commute`, substituting `nSM_15`/`nR0_15`/`nR1_15`
    and take-indices 609 / 1277 / 1278.

  * **Reshape/float/residual + router head.**  Uniform `+147` (SM) / `+516` (PM)
    from the L12 tids: SM residual `5501`, router rms `5503`, `norm_linear 5506`,
    topk `5506 → [5507,5508,5509]` (target `5508`); PM router topk outputs
    `10249`/`10250` (targets).  These reuse the L12 reshape/float/carry/router
    lemma bodies with the shifted TIDs.

  Final statement:
    `sm_pm_router_commute_L15_full` :
      `denoteGraph_ringAttn sm_goal_3 initSM 5508
         = allGatherPrimDimN 0 2 0 [pm 10249, pm 10250]`
    under `StoreShapesHold` (both), `InitGoalsHold`, `hcarry5485`, and `h_bound`.
-/

end TrainVerify.Denote.GeneratedPatterns
