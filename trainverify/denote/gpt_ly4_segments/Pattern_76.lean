/- Auto-generated pattern proof file.
   Pattern: 76
   Hash: 9ccba3af8a3158d9
   Goals: 135, 141, 176, 179, 255

   Structural argument:
     Each SM graph is a single `BW_linear` node producing dW (the `.snd` output).
     Each PM graph has four `BW_linear` nodes, one per rank, producing per-rank
     dW shards.  Across the 5 goals the shape parameters differ but the pattern
     is identical:

       SM:    gradOut :: [B, S, full_o]   x :: [B, S, i]   w :: [full_o, i]
       PM_r:  gradOut :: [B, S, shard_o]  x :: [B, S, i]   w :: [shard_o, i]

       gradOut_SM   = allGatherPrimDimN 2 4 0 [gradOut_PM_0..3]  (cut prereq)
       w_SM         = allGatherPrimDimN 0 4 0 [w_PM_0..3]        (initGoal)
       x_SM         = x_PM_r for every r                         (singleton
                                                                  prereq)
       dW_SM        = allGatherPrimDimN 0 4 0 [dW_PM_0..3]       (this goal)

     `bw_linear`'s dW component does not depend on `w` — it is
     `gradOut.T @ x` — so the splitting argument only needs the gradOut split
     on the output dim and a shared `x`.  We prove this once as `bridge_dW`
     and apply it to all five goals.
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_18
import denote.gpt_ly4_segments.Pattern_21
import denote.gpt_ly4_segments.Pattern_35
import denote.gpt_ly4_segments.Pattern_77
import denote.gpt_ly4_segments.Pattern_79
import denote.gpt_ly4_segments.Pattern_98
import denote.gpt_ly4_segments.Pattern_99
import denote.gpt_ly4_segments.Pattern_126

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_76_goalIds : List Nat := [135, 141, 176, 179, 255]
inductive pattern_76_target : Prop → Prop
  | goal_135 : pattern_76_target goal_135_stmt
  | goal_141 : pattern_76_target goal_141_stmt
  | goal_176 : pattern_76_target goal_176_stmt
  | goal_179 : pattern_76_target goal_179_stmt
  | goal_255 : pattern_76_target goal_255_stmt

def pattern_76_stmt : Prop :=
  ∀ {target : Prop}, pattern_76_target target → target

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000

/-! ## value-level helper: dW component of 3D bw_linear. -/

private theorem bw_linear_3d_snd_valAt
    (B S i o : Nat) (gradOut x w : Tensor)
    (hg : gradOut.shape = [B, S, o])
    (hx : x.shape = [B, S, i])
    (hw : w.shape = [o, i])
    (c : Nat) (hc : c < o) (k : Nat) (hk : k < i) :
    valAt (bw_linear gradOut x w).2 (c * i + k) =
      ∑ p ∈ Finset.range (B * S),
        (valAt gradOut (p * o + c)) * (valAt x (p * i + k)) := by
  have hbw : (bw_linear gradOut x w).2 =
      Tensor.mkShape [o, i] (k_matmul_transpose (B * S) o i gradOut x) := by
    simp only [bw_linear, hg, hx, hw, Tensor.mkShape]
  rw [hbw]
  -- Inline `matmul_transpose_valAt` since it requires explicit 2D shape hypotheses
  -- which we cannot supply for 3D inputs.
  have hi_pos : 0 < i := Nat.lt_of_le_of_lt (Nat.zero_le _) hk
  have hlt_ni : c * i + k < o * i := by
    have h2 : c * i + i = (c + 1) * i := by ring
    have h3 : (c + 1) * i ≤ o * i := Nat.mul_le_mul_right _ (by omega)
    omega
  have hlt' : (c * i + k) < prodShape ([o, i] : Shape) := by
    simpa [prodShape] using hlt_ni
  have hdiv : (c * i + k) / i = c := by
    rw [show c * i + k = k + i * c from by ring, Nat.add_mul_div_left _ _ hi_pos,
        Nat.div_eq_of_lt hk, Nat.zero_add]
  have hmod : (c * i + k) % i = k := by
    rw [show c * i + k = k + i * c from by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hk]
  simp only [valAt, hlt', Tensor.mkShape, dite_true]
  simp only [k_matmul_transpose, hdiv, hmod, valAt]

/-! ## value-level helper: dim-2 allGather valAt on [B, S, shard]. -/

private theorem allGatherDim2_3d_valAt
    (numParts B S shard : Nat) (xs : List Tensor)
    (hparts : 0 < numParts) (hshard : 0 < shard)
    (hxs_head : (xs.head?.map (fun t => t.shape)).getD [] = [B, S, shard])
    (p : Nat) (hp : p < B * S) (r : Nat) (hr : r < numParts)
    (c' : Nat) (hc' : c' < shard) :
    valAt (allGatherPrimDimN 2 numParts 0 xs) (p * (shard * numParts) + (r * shard + c')) =
      valAt (xs.getD r (zeroTensor [B, S, shard])) (p * shard + c') := by
  set full := shard * numParts with hfull
  have hfull_pos : 0 < full := Nat.mul_pos hshard hparts
  have hfull_ne : full ≠ 0 := Nat.ne_of_gt hfull_pos
  have hshard_ne : shard ≠ 0 := Nat.ne_of_gt hshard
  have hgshape : (allGatherPrimDimN 2 numParts 0 xs).shape = [B, S, full] := by
    have := allGatherPrimDimN_shape 2 numParts xs [B, S, shard] hxs_head
    simpa [List.set, hfull] using this
  have hrk_lt : r * shard + c' < full := by
    have h2 : r * shard + c' < (r + 1) * shard := by
      have : r * shard + shard = (r + 1) * shard := by ring
      omega
    have hle : (r + 1) * shard ≤ numParts * shard := Nat.mul_le_mul_right _ hr
    have hcomm : numParts * shard = full := by simp [hfull, Nat.mul_comm]
    omega
  have hidx_lt_full : p * full + (r * shard + c') < B * S * full := by
    have hp2 : p * full + full = (p + 1) * full := by ring
    have hp3 : (p + 1) * full ≤ B * S * full := Nat.mul_le_mul_right _ (by omega)
    omega
  have hidx_lt_prod : p * full + (r * shard + c') <
      prodShape (allGatherPrimDimN 2 numParts 0 xs).shape := by
    rw [hgshape]
    show p * full + (r * shard + c') < ((1 * B) * S) * full
    have heq : ((1 * B) * S) * full = B * S * full := by ring
    rw [heq]
    exact hidx_lt_full
  rw [valAt_of_lt _ _ hidx_lt_prod]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hxs_head, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, Nat.one_mul, Nat.mul_one]
  have hpost_ne : (1 : Nat) ≠ 0 := by decide
  have hsn_eq : shard * numParts = full := by simp [hfull]
  have hsn_ne : shard * numParts ≠ 0 := by rw [hsn_eq]; exact hfull_ne
  simp only [hpost_ne, hsn_ne, hshard_ne, ↓reduceIte, Nat.div_one, Nat.mod_one,
    Nat.add_zero]
  rw [hsn_eq]
  have hidx_div_full : (p * full + (r * shard + c')) / full = p := by
    rw [show p * full + (r * shard + c') = (r * shard + c') + p * full from by ring,
        Nat.add_mul_div_right _ _ hfull_pos, Nat.div_eq_of_lt hrk_lt, Nat.zero_add]
  have hidx_mod_full : (p * full + (r * shard + c')) % full = r * shard + c' := by
    rw [show p * full + (r * shard + c') = (r * shard + c') + p * full from by ring,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrk_lt]
  have hrj_div_shard : (r * shard + c') / shard = r := by
    rw [show r * shard + c' = c' + shard * r from by ring,
        Nat.add_mul_div_left _ _ hshard, Nat.div_eq_of_lt hc', Nat.zero_add]
  have hrj_mod_shard : (r * shard + c') % shard = c' := by
    rw [show r * shard + c' = c' + shard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc']
  rw [hidx_div_full, hidx_mod_full, hrj_div_shard, hrj_mod_shard]

/-! ## Main bridging lemma: row-parallel dW for 3D bw_linear with shared x. -/

private theorem bridge_dW
    (numParts B S shard_o full_o i : Nat)
    (gs : List Tensor) (x w : Tensor) (ws : List Tensor)
    (hgs_len : gs.length = numParts)
    (hgs_shapes : ∀ g ∈ gs, g.shape = [B, S, shard_o])
    (hws_len : ws.length = numParts)
    (hws_shapes : ∀ w' ∈ ws, w'.shape = [shard_o, i])
    (hx : x.shape = [B, S, i])
    (hw : w.shape = [full_o, i])
    (hfull : full_o = shard_o * numParts)
    (hparts : 0 < numParts) (hshard_o : 0 < shard_o)
    (_hB : 0 < B) (_hS : 0 < S) (hi : 0 < i) :
    (bw_linear (allGatherPrimDimN 2 numParts 0 gs) x w).2 =
      allGatherPrimDimN 0 numParts 0
        (List.ofFn (fun r : Fin numParts =>
          (bw_linear (gs.get ⟨r.val, by omega⟩) x (ws.get ⟨r.val, by omega⟩)).2)) := by
  classical
  have hfull_pos : 0 < full_o := by rw [hfull]; exact Nat.mul_pos hshard_o hparts
  have hgs_head : (gs.head?.map (fun t => t.shape)).getD [] = [B, S, shard_o] := by
    cases hgs' : gs with
    | nil => simp [hgs'] at hgs_len; omega
    | cons g0 _ => simp [hgs_shapes g0 (by simp [hgs'])]
  set gSM := allGatherPrimDimN 2 numParts 0 gs with hgSM_def
  have hgSM_shape : gSM.shape = [B, S, full_o] := by
    have := allGatherPrimDimN_shape 2 numParts gs [B, S, shard_o] hgs_head
    rw [hgSM_def, this]
    simp [List.set, hfull]
  have hLHS_shape : (bw_linear gSM x w).2.shape = [full_o, i] := by
    simp [bw_linear, hgSM_shape, hx, hw, Tensor.mkShape]
  set pieces := List.ofFn (fun r : Fin numParts =>
    (bw_linear (gs.get ⟨r.val, by omega⟩) x (ws.get ⟨r.val, by omega⟩)).2) with hpieces_def
  have hpiece_shape : ∀ r : Fin numParts,
      (bw_linear (gs.get ⟨r.val, by omega⟩) x (ws.get ⟨r.val, by omega⟩)).2.shape =
        [shard_o, i] := by
    intro r
    have hr_g : r.val < gs.length := by omega
    have hr_w : r.val < ws.length := by omega
    have hgr : (gs.get ⟨r.val, hr_g⟩).shape = [B, S, shard_o] :=
      hgs_shapes _ (List.get_mem gs ⟨r.val, hr_g⟩)
    have hwr : (ws.get ⟨r.val, hr_w⟩).shape = [shard_o, i] :=
      hws_shapes _ (List.get_mem ws ⟨r.val, hr_w⟩)
    show (bw_linear (gs.get ⟨r.val, hr_g⟩) x (ws.get ⟨r.val, hr_w⟩)).2.shape = [shard_o, i]
    unfold bw_linear
    rw [hgr, hx, hwr]
    rfl
  have hpieces_head : (pieces.head?.map (fun t => t.shape)).getD [] = [shard_o, i] := by
    cases hnp : numParts with
    | zero => omega
    | succ n =>
      simp only [pieces, hnp]
      rw [list_ofFn_head_eq]
      change (bw_linear (gs.get ⟨0, by omega⟩) x (ws.get ⟨0, by omega⟩)).2.shape = [shard_o, i]
      exact hpiece_shape ⟨0, by omega⟩
  have hRHS_shape : (allGatherPrimDimN 0 numParts 0 pieces).shape = [full_o, i] := by
    have := allGatherPrimDimN_shape 0 numParts pieces [shard_o, i] hpieces_head
    rw [this]
    simp [List.set, hfull]
  have hshape_eq : (bw_linear gSM x w).2.shape =
      (allGatherPrimDimN 0 numParts 0 pieces).shape := by rw [hLHS_shape, hRHS_shape]
  apply Tensor.ext hshape_eq
  intro idx hidx
  have hidx_lt : idx < full_o * i := by
    have := hidx
    rw [hLHS_shape] at this
    simpa [prodShape] using this
  set c := idx / i with hc_def
  set k := idx % i with hk_def
  have hk_lt : k < i := Nat.mod_lt idx hi
  have hc_lt : c < full_o := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidx_lt)
  have hidx_eq : idx = c * i + k := by
    rw [hc_def, hk_def]
    exact (Nat.div_add_mod' idx i).symm
  set r := c / shard_o with hr_def
  set c' := c % shard_o with hc'_def
  have hc'_lt : c' < shard_o := Nat.mod_lt c hshard_o
  have hr_lt : r < numParts := by
    have hc_lt_full : c < shard_o * numParts := by rw [← hfull]; exact hc_lt
    exact Nat.div_lt_of_lt_mul hc_lt_full
  have hc_eq : c = r * shard_o + c' := by
    rw [hr_def, hc'_def]
    exact (Nat.div_add_mod' c shard_o).symm
  have hpieces_len : pieces.length = numParts := by simp [pieces]
  have hpieces_shape_get : ∀ rr, rr < numParts →
      (pieces.getD rr (zeroTensor [shard_o, i])).shape = [shard_o, i] := by
    intro rr hrr
    have hrr_len : rr < pieces.length := by rw [hpieces_len]; exact hrr
    have heq : pieces.getD rr (zeroTensor [shard_o, i]) = pieces.get ⟨rr, hrr_len⟩ := by
      simp only [List.getD, List.getElem?_eq_getElem hrr_len, Option.getD_some,
        List.get_eq_getElem]
    rw [heq]
    have hval : pieces.get ⟨rr, hrr_len⟩ =
        (bw_linear (gs.get ⟨rr, by rw [hgs_len]; exact hrr⟩) x
            (ws.get ⟨rr, by rw [hws_len]; exact hrr⟩)).2 := by
      simp [pieces, List.get_ofFn]
    rw [hval]
    exact hpiece_shape ⟨rr, hrr⟩
  have hvalL : valAt (bw_linear gSM x w).2 (c * i + k) =
      ∑ p ∈ Finset.range (B * S),
        (valAt gSM (p * full_o + c)) * (valAt x (p * i + k)) :=
    bw_linear_3d_snd_valAt B S i full_o gSM x w hgSM_shape hx hw c hc_lt k hk_lt
  have hvalR_gather : valAt (allGatherPrimDimN 0 numParts 0 pieces)
      ((r * shard_o + c') * i + k) =
      valAt (pieces.getD r (zeroTensor [shard_o, i])) (c' * i + k) :=
    allGatherPrimDimN0_valAt numParts shard_o i pieces hparts hshard_o hi
      hpieces_head hpieces_shape_get r hr_lt c' hc'_lt k hk_lt
  have hr_len_pieces : r < pieces.length := by rw [hpieces_len]; exact hr_lt
  have hpieces_getD : pieces.getD r (zeroTensor [shard_o, i]) =
      (bw_linear (gs.get ⟨r, by rw [hgs_len]; exact hr_lt⟩) x
          (ws.get ⟨r, by rw [hws_len]; exact hr_lt⟩)).2 := by
    have heq : pieces.getD r (zeroTensor [shard_o, i]) = pieces.get ⟨r, hr_len_pieces⟩ := by
      simp only [List.getD, List.getElem?_eq_getElem hr_len_pieces, Option.getD_some,
        List.get_eq_getElem]
    rw [heq]
    simp [pieces, List.get_ofFn]
  have hvalPiece : valAt (bw_linear (gs.get ⟨r, by rw [hgs_len]; exact hr_lt⟩) x
        (ws.get ⟨r, by rw [hws_len]; exact hr_lt⟩)).2 (c' * i + k) =
      ∑ p ∈ Finset.range (B * S),
        (valAt (gs.get ⟨r, by rw [hgs_len]; exact hr_lt⟩) (p * shard_o + c')) *
          (valAt x (p * i + k)) := by
    apply bw_linear_3d_snd_valAt B S i shard_o
    · exact hgs_shapes (gs.get ⟨r, by rw [hgs_len]; exact hr_lt⟩)
        (List.get_mem gs ⟨r, by rw [hgs_len]; exact hr_lt⟩)
    · exact hx
    · exact hws_shapes (ws.get ⟨r, by rw [hws_len]; exact hr_lt⟩)
        (List.get_mem ws ⟨r, by rw [hws_len]; exact hr_lt⟩)
    · exact hc'_lt
    · exact hk_lt
  have hgather_g_val : ∀ p, p < B * S →
      valAt gSM (p * full_o + c) =
        valAt (gs.getD r (zeroTensor [B, S, shard_o])) (p * shard_o + c') := by
    intro p hp
    rw [hc_eq]
    rw [show p * full_o + (r * shard_o + c') =
        p * (shard_o * numParts) + (r * shard_o + c') from by rw [hfull]]
    exact allGatherDim2_3d_valAt numParts B S shard_o gs hparts hshard_o hgs_head
      p hp r hr_lt c' hc'_lt
  have hr_len_gs : r < gs.length := by rw [hgs_len]; exact hr_lt
  have hgs_getD : gs.getD r (zeroTensor [B, S, shard_o]) = gs.get ⟨r, hr_len_gs⟩ := by
    simp only [List.getD, List.getElem?_eq_getElem hr_len_gs, Option.getD_some,
      List.get_eq_getElem]
  rw [hidx_eq, hvalL]
  conv_rhs => rw [show c * i + k = (r * shard_o + c') * i + k from by rw [← hc_eq]]
  rw [hvalR_gather, hpieces_getD, hvalPiece]
  apply Finset.sum_congr rfl
  intro p hp
  have hp_lt : p < B * S := Finset.mem_range.mp hp
  have h := hgather_g_val p hp_lt
  rw [hgs_getD] at h
  rw [h]

/-! ## Generic graph-evaluation helpers. -/

private theorem denote_init_tid (g : GraphDecl) (init : Store) (tid : Tid)
    (hno : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraph g init tid = init tid := by
  have h := denoteGraph_tid_eq_of_suffix_no_writes g init tid
    [] g.nodes (by simp) hno
  rw [h]
  have heq : ({ g with nodes := [] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := [] } := by cases g; rfl
  rw [heq, denoteGraph_nodes_nil]

private theorem sm_eval_bw_linear_snd
    (g : GraphDecl) (initSM : Store) (rk : Nat)
    (gTid xTid wTid dxTid dwTid : Tid)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.BW_linear",
                        ins := [gTid, xTid, wTid], outs := [dxTid, dwTid] })
    (hgraph : g.nodes = [node])
    (hne : dxTid ≠ dwTid) :
    denoteGraph g initSM dwTid =
      (bw_linear (initSM gTid) (initSM xTid) (initSM wTid)).2 := by
  have hg_eq : g = { numRanks := g.numRanks, nodes := node :: [] } := by
    cases g with
    | mk nr ns => simp only [GraphDecl.mk.injEq, true_and]; exact hgraph
  rw [hg_eq, denoteGraph_cons_eq g node []]
  show applyNode g (denoteGraph { numRanks := g.numRanks, nodes := [] } initSM) node dwTid = _
  have hempty : denoteGraph { numRanks := g.numRanks, nodes := [] } initSM = initSM := by
    simp [denoteGraph_nodes_nil]
  rw [hempty, hnode]
  exact applyNode_bw_linear_snd_out g initSM rk gTid xTid wTid dxTid dwTid hne

private theorem pm_eval_bw_linear_snd_at
    (g : GraphDecl) (initPM : Store) (K : Nat) (rk : Nat)
    (gTid xTid wTid dxTid dwTid : Tid)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.BW_linear",
                        ins := [gTid, xTid, wTid], outs := [dxTid, dwTid] })
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (hsuf_dw : ∀ n ∈ g.nodes.drop (K + 1), dwTid ∉ n.outs)
    (hsuf_g : ∀ n ∈ g.nodes.drop K, gTid ∉ n.outs)
    (hsuf_x : ∀ n ∈ g.nodes.drop K, xTid ∉ n.outs)
    (hsuf_w : ∀ n ∈ g.nodes.drop K, wTid ∉ n.outs)
    (hne : dxTid ≠ dwTid) :
    denoteGraph g initPM dwTid =
      (bw_linear (denoteGraph g initPM gTid) (denoteGraph g initPM xTid)
        (denoteGraph g initPM wTid)).2 := by
  have h1 : denoteGraph g initPM dwTid =
      denoteGraph { g with nodes := g.nodes.take (K + 1) } initPM dwTid :=
    denoteGraph_tid_eq_of_suffix_no_writes g initPM dwTid
      (g.nodes.take (K + 1)) (g.nodes.drop (K + 1))
      (List.take_append_drop (K + 1) _).symm hsuf_dw
  rw [h1]
  have htake : g.nodes.take (K + 1) = g.nodes.take K ++ [node] := by
    rw [list_take_succ_eq_take_append_get g.nodes K hKlt, hidx]
  have hg_eq : ({ g with nodes := g.nodes.take (K + 1) } : GraphDecl) =
      { g with nodes := g.nodes.take K ++ [node] } := by
    cases g; congr 1
  rw [hg_eq, denoteGraph_nodes_append]
  have hsing : ({ g with nodes := [node] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := node :: [] } := by cases g; rfl
  rw [hsing, denoteGraph_cons_eq g node []]
  change applyNode g (denoteGraph { g with nodes := g.nodes.take K } initPM) node dwTid = _
  rw [hnode]
  rw [applyNode_bw_linear_snd_out g _ rk gTid xTid wTid dxTid dwTid hne]
  -- Replace each input lookup: denote of prefix-graph equals denote of full graph,
  -- since the suffix (from K) never writes the input tid.
  have hpre_g : (denoteGraph { g with nodes := g.nodes.take K } initPM) gTid =
      denoteGraph g initPM gTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initPM gTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_g).symm
  have hpre_x : (denoteGraph { g with nodes := g.nodes.take K } initPM) xTid =
      denoteGraph g initPM xTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initPM xTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_x).symm
  have hpre_w : (denoteGraph { g with nodes := g.nodes.take K } initPM) wTid =
      denoteGraph g initPM wTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initPM wTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_w).symm
  rw [hpre_g, hpre_x, hpre_w]

/-! ## Per-goal SM and PM node literals. -/

@[reducible] private def sm_n135 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [752, 590, 591], outs := [750, 751] }
@[reducible] private def pm_n135_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [1491, 590, 1473], outs := [1498, 1490] }
@[reducible] private def pm_n135_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_linear", ins := [1494, 590, 1474], outs := [1495, 1493] }
@[reducible] private def pm_n135_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_linear", ins := [1497, 590, 1475], outs := [1492, 1496] }
@[reducible] private def pm_n135_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_linear", ins := [1500, 590, 1476], outs := [1489, 1499] }

@[reducible] private def sm_n141 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [760, 596, 597], outs := [758, 759] }
@[reducible] private def pm_n141_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [1575, 596, 1557], outs := [1582, 1574] }
@[reducible] private def pm_n141_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_linear", ins := [1578, 596, 1558], outs := [1579, 1577] }
@[reducible] private def pm_n141_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_linear", ins := [1581, 596, 1559], outs := [1576, 1580] }
@[reducible] private def pm_n141_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_linear", ins := [1584, 596, 1560], outs := [1573, 1583] }

@[reducible] private def sm_n176 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [802, 631, 632], outs := [800, 801] }
@[reducible] private def pm_n176_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [2131, 631, 2113], outs := [2138, 2130] }
@[reducible] private def pm_n176_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_linear", ins := [2134, 631, 2114], outs := [2135, 2133] }
@[reducible] private def pm_n176_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_linear", ins := [2137, 631, 2115], outs := [2132, 2136] }
@[reducible] private def pm_n176_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_linear", ins := [2140, 631, 2116], outs := [2129, 2139] }

@[reducible] private def sm_n179 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [805, 634, 635], outs := [803, 804] }
@[reducible] private def pm_n179_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [2183, 634, 2165], outs := [2190, 2182] }
@[reducible] private def pm_n179_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_linear", ins := [2186, 634, 2166], outs := [2187, 2185] }
@[reducible] private def pm_n179_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_linear", ins := [2189, 634, 2167], outs := [2184, 2188] }
@[reducible] private def pm_n179_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_linear", ins := [2192, 634, 2168], outs := [2181, 2191] }

@[reducible] private def sm_n255 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [895, 710, 711], outs := [893, 894] }
@[reducible] private def pm_n255_0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_linear", ins := [3387, 710, 3369], outs := [3394, 3386] }
@[reducible] private def pm_n255_1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_linear", ins := [3390, 710, 3370], outs := [3391, 3389] }
@[reducible] private def pm_n255_2 : NodeDecl :=
  { rank := 2, op := "OpName.BW_linear", ins := [3393, 710, 3371], outs := [3388, 3392] }
@[reducible] private def pm_n255_3 : NodeDecl :=
  { rank := 3, op := "OpName.BW_linear", ins := [3396, 710, 3372], outs := [3385, 3395] }

/-! ## Specialization of `bridge_dW` to `numParts = 4` (literal 4-element lists). -/

private theorem bridge_dW_4
    (B S shard_o i : Nat)
    (g0 g1 g2 g3 x w w0 w1 w2 w3 : Tensor)
    (hg0 : g0.shape = [B, S, shard_o]) (hg1 : g1.shape = [B, S, shard_o])
    (hg2 : g2.shape = [B, S, shard_o]) (hg3 : g3.shape = [B, S, shard_o])
    (hw0 : w0.shape = [shard_o, i]) (hw1 : w1.shape = [shard_o, i])
    (hw2 : w2.shape = [shard_o, i]) (hw3 : w3.shape = [shard_o, i])
    (hx : x.shape = [B, S, i]) (hw : w.shape = [shard_o * 4, i])
    (hshard_o : 0 < shard_o) (hB : 0 < B) (hS : 0 < S) (hi : 0 < i) :
    (bw_linear (allGatherPrimDimN 2 4 0 [g0, g1, g2, g3]) x w).2 =
      allGatherPrimDimN 0 4 0
        [(bw_linear g0 x w0).2, (bw_linear g1 x w1).2,
         (bw_linear g2 x w2).2, (bw_linear g3 x w3).2] := by
  have hgs_shapes : ∀ g ∈ ([g0, g1, g2, g3] : List Tensor), g.shape = [B, S, shard_o] := by
    intro g hg
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h
    · rw [h]; exact hg0
    · rw [h]; exact hg1
    · rw [h]; exact hg2
    · rw [h]; exact hg3
  have hws_shapes : ∀ w' ∈ ([w0, w1, w2, w3] : List Tensor), w'.shape = [shard_o, i] := by
    intro w' hw'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw'
    rcases hw' with h | h | h | h
    · rw [h]; exact hw0
    · rw [h]; exact hw1
    · rw [h]; exact hw2
    · rw [h]; exact hw3
  have h := bridge_dW 4 B S shard_o (shard_o * 4) i
    [g0, g1, g2, g3] x w [w0, w1, w2, w3]
    rfl hgs_shapes rfl hws_shapes hx hw rfl
    (by norm_num) hshard_o hB hS hi
  rw [h]
  rfl

/-! ## SM dW evaluation helpers. -/

private theorem sm_eval_751 (initSM : Store) :
    denoteGraph sm initSM 751 =
      (bw_linear (denoteGraph sm initSM 752) (denoteGraph sm initSM 590)
        (denoteGraph sm initSM 591)).2 :=
  pm_eval_bw_linear_snd_at sm initSM 212 0 752 590 591 750 751 sm_n135 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_759 (initSM : Store) :
    denoteGraph sm initSM 759 =
      (bw_linear (denoteGraph sm initSM 760) (denoteGraph sm initSM 596)
        (denoteGraph sm initSM 597)).2 :=
  pm_eval_bw_linear_snd_at sm initSM 208 0 760 596 597 758 759 sm_n141 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_801 (initSM : Store) :
    denoteGraph sm initSM 801 =
      (bw_linear (denoteGraph sm initSM 802) (denoteGraph sm initSM 631)
        (denoteGraph sm initSM 632)).2 :=
  pm_eval_bw_linear_snd_at sm initSM 180 0 802 631 632 800 801 sm_n176 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_804 (initSM : Store) :
    denoteGraph sm initSM 804 =
      (bw_linear (denoteGraph sm initSM 805) (denoteGraph sm initSM 634)
        (denoteGraph sm initSM 635)).2 :=
  pm_eval_bw_linear_snd_at sm initSM 178 0 805 634 635 803 804 sm_n179 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem sm_eval_894 (initSM : Store) :
    denoteGraph sm initSM 894 =
      (bw_linear (denoteGraph sm initSM 895) (denoteGraph sm initSM 710)
        (denoteGraph sm initSM 711)).2 :=
  pm_eval_bw_linear_snd_at sm initSM 119 0 895 710 711 893 894 sm_n255 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## PM dW evaluation helpers (one per shard per goal). -/

private theorem pm_eval_1490 (initPM : Store) :
    denoteGraph pm initPM 1490 =
      (bw_linear (denoteGraph pm initPM 1491) (denoteGraph pm initPM 590)
        (denoteGraph pm initPM 1473)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1412 0 1491 590 1473 1498 1490 pm_n135_0 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1493 (initPM : Store) :
    denoteGraph pm initPM 1493 =
      (bw_linear (denoteGraph pm initPM 1494) (denoteGraph pm initPM 590)
        (denoteGraph pm initPM 1474)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1413 1 1494 590 1474 1495 1493 pm_n135_1 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1496 (initPM : Store) :
    denoteGraph pm initPM 1496 =
      (bw_linear (denoteGraph pm initPM 1497) (denoteGraph pm initPM 590)
        (denoteGraph pm initPM 1475)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1414 2 1497 590 1475 1492 1496 pm_n135_2 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1499 (initPM : Store) :
    denoteGraph pm initPM 1499 =
      (bw_linear (denoteGraph pm initPM 1500) (denoteGraph pm initPM 590)
        (denoteGraph pm initPM 1476)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1415 3 1500 590 1476 1489 1499 pm_n135_3 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1574 (initPM : Store) :
    denoteGraph pm initPM 1574 =
      (bw_linear (denoteGraph pm initPM 1575) (denoteGraph pm initPM 596)
        (denoteGraph pm initPM 1557)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1385 0 1575 596 1557 1582 1574 pm_n141_0 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1577 (initPM : Store) :
    denoteGraph pm initPM 1577 =
      (bw_linear (denoteGraph pm initPM 1578) (denoteGraph pm initPM 596)
        (denoteGraph pm initPM 1558)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1386 1 1578 596 1558 1579 1577 pm_n141_1 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1580 (initPM : Store) :
    denoteGraph pm initPM 1580 =
      (bw_linear (denoteGraph pm initPM 1581) (denoteGraph pm initPM 596)
        (denoteGraph pm initPM 1559)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1387 2 1581 596 1559 1576 1580 pm_n141_2 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_1583 (initPM : Store) :
    denoteGraph pm initPM 1583 =
      (bw_linear (denoteGraph pm initPM 1584) (denoteGraph pm initPM 596)
        (denoteGraph pm initPM 1560)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1388 3 1584 596 1560 1573 1583 pm_n141_3 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2130 (initPM : Store) :
    denoteGraph pm initPM 2130 =
      (bw_linear (denoteGraph pm initPM 2131) (denoteGraph pm initPM 631)
        (denoteGraph pm initPM 2113)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1192 0 2131 631 2113 2138 2130 pm_n176_0 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2133 (initPM : Store) :
    denoteGraph pm initPM 2133 =
      (bw_linear (denoteGraph pm initPM 2134) (denoteGraph pm initPM 631)
        (denoteGraph pm initPM 2114)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1193 1 2134 631 2114 2135 2133 pm_n176_1 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2136 (initPM : Store) :
    denoteGraph pm initPM 2136 =
      (bw_linear (denoteGraph pm initPM 2137) (denoteGraph pm initPM 631)
        (denoteGraph pm initPM 2115)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1194 2 2137 631 2115 2132 2136 pm_n176_2 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2139 (initPM : Store) :
    denoteGraph pm initPM 2139 =
      (bw_linear (denoteGraph pm initPM 2140) (denoteGraph pm initPM 631)
        (denoteGraph pm initPM 2116)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1195 3 2140 631 2116 2129 2139 pm_n176_3 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2182 (initPM : Store) :
    denoteGraph pm initPM 2182 =
      (bw_linear (denoteGraph pm initPM 2183) (denoteGraph pm initPM 634)
        (denoteGraph pm initPM 2165)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1175 0 2183 634 2165 2190 2182 pm_n179_0 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2185 (initPM : Store) :
    denoteGraph pm initPM 2185 =
      (bw_linear (denoteGraph pm initPM 2186) (denoteGraph pm initPM 634)
        (denoteGraph pm initPM 2166)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1176 1 2186 634 2166 2187 2185 pm_n179_1 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2188 (initPM : Store) :
    denoteGraph pm initPM 2188 =
      (bw_linear (denoteGraph pm initPM 2189) (denoteGraph pm initPM 634)
        (denoteGraph pm initPM 2167)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1177 2 2189 634 2167 2184 2188 pm_n179_2 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_2191 (initPM : Store) :
    denoteGraph pm initPM 2191 =
      (bw_linear (denoteGraph pm initPM 2192) (denoteGraph pm initPM 634)
        (denoteGraph pm initPM 2168)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 1178 3 2192 634 2168 2181 2191 pm_n179_3 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3386 (initPM : Store) :
    denoteGraph pm initPM 3386 =
      (bw_linear (denoteGraph pm initPM 3387) (denoteGraph pm initPM 710)
        (denoteGraph pm initPM 3369)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 779 0 3387 710 3369 3394 3386 pm_n255_0 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3389 (initPM : Store) :
    denoteGraph pm initPM 3389 =
      (bw_linear (denoteGraph pm initPM 3390) (denoteGraph pm initPM 710)
        (denoteGraph pm initPM 3370)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 780 1 3390 710 3370 3391 3389 pm_n255_1 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3392 (initPM : Store) :
    denoteGraph pm initPM 3392 =
      (bw_linear (denoteGraph pm initPM 3393) (denoteGraph pm initPM 710)
        (denoteGraph pm initPM 3371)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 781 2 3393 710 3371 3388 3392 pm_n255_2 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem pm_eval_3395 (initPM : Store) :
    denoteGraph pm initPM 3395 =
      (bw_linear (denoteGraph pm initPM 3396) (denoteGraph pm initPM 710)
        (denoteGraph pm initPM 3372)).2 :=
  pm_eval_bw_linear_snd_at pm initPM 783 3 3396 710 3372 3385 3395 pm_n255_3 rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## Per-goal proofs for `pattern_76`. -/

private theorem prove_goal_135 :
    ∀ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv → StoreShapesHold initPM pmInitEnv →
      InitGoalsHold pm.numRanks initGoals initSM initPM →
      let smStore := denoteGraph sm initSM
      let pmStore := denoteGraph pm initPM
      (smStore goal_135.ts).shape = goal_135.tsShape ∧
        ((goal_135.tps.map (fun p => pmStore p.tid)).map (·.shape)) = goal_135.tpShapes ∧
        smStore goal_135.ts =
          reconstructWithDim goal_135.gatherDim pm.numRanks 0
            (goal_135.tps.map (fun p => pmStore p.tid)) := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- gradOut prereq (goal_136 ↦ Pattern_77)
  have h136 := prove_pattern_77 (target := goal_136_stmt) pattern_77_target.goal_136
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h752_sh, hgr_sh, h752_rec⟩ := h136
  simp only [goal_136, List.map_cons, List.map_nil] at hgr_sh h752_rec
  have hgr0_sh : (denoteGraph pm initPM 1491).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.1
  have hgr1_sh : (denoteGraph pm initPM 1494).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hgr2_sh : (denoteGraph pm initPM 1497).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hgr3_sh : (denoteGraph pm initPM 1500).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h752_dimN : denoteGraph sm initSM 752 = allGatherPrimDimN 2 pm.numRanks 0
      [denoteGraph pm initPM 1491, denoteGraph pm initPM 1494,
       denoteGraph pm initPM 1497, denoteGraph pm initPM 1500] := by
    rw [h752_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hgr0_sh]; intro hc; cases hc
  -- x prereq (goal_22 ↦ Pattern_18, singleton)
  have h22 := prove_pattern_18 (target := goal_22_stmt) pattern_18_target.goal_22
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h590_sh, _, h590_rec⟩ := h22
  simp only [goal_22, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h590_rec
  have h590_sh' : (denoteGraph sm initSM 590).shape = [1, 8, 32] := by
    have := h590_sh; simp only [goal_22] at this; exact this
  -- weight initGoal_591
  have h591_init := hInitGoals initGoal_591 (by simp [initGoals])
  obtain ⟨h591_sh, hw_sh, h591_rec⟩ := h591_init
  simp only [initGoal_591, List.map_cons, List.map_nil] at h591_rec hw_sh
  have hwr0_sh : (initPM 1473).shape = [8, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have h591_dimN : initSM 591 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 1473, initPM 1474, initPM 1475, initPM 1476] := by
    rw [h591_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  -- Lift 591 / 1473-1476 from init store to denoteGraph.
  have hsm591 : denoteGraph sm initSM 591 = initSM 591 :=
    denote_init_tid sm initSM 591 (by decide)
  have hpm1473 : denoteGraph pm initPM 1473 = initPM 1473 :=
    denote_init_tid pm initPM 1473 (by decide)
  have hpm1474 : denoteGraph pm initPM 1474 = initPM 1474 :=
    denote_init_tid pm initPM 1474 (by decide)
  have hpm1475 : denoteGraph pm initPM 1475 = initPM 1475 :=
    denote_init_tid pm initPM 1475 (by decide)
  have hpm1476 : denoteGraph pm initPM 1476 = initPM 1476 :=
    denote_init_tid pm initPM 1476 (by decide)
  -- sm / pm dW evaluations
  have hS := sm_eval_751 initSM
  have hP0 := pm_eval_1490 initPM
  have hP1 := pm_eval_1493 initPM
  have hP2 := pm_eval_1496 initPM
  have hP3 := pm_eval_1499 initPM
  -- per-shard shapes / final result shape
  have h591_sh' : (denoteGraph sm initSM 591).shape = [32, 32] := by
    rw [hsm591]
    have := h591_sh; simp only [initGoal_591] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 1473).shape = [8, 32] := by rw [hpm1473]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 1474).shape = [8, 32] := by
    rw [hpm1474]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_pm_sh : (denoteGraph pm initPM 1475).shape = [8, 32] := by
    rw [hpm1475]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_pm_sh : (denoteGraph pm initPM 1476).shape = [8, 32] := by
    rw [hpm1476]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  -- bridge_dW_4 application: full_o = shard_o * 4 = 8 * 4 = 32
  have h590_pm_sh : (denoteGraph pm initPM 590).shape = [1, 8, 32] := by
    rw [← h590_rec]; exact h590_sh'
  have h591_full_sh : (denoteGraph sm initSM 591).shape = [8 * 4, 32] := by
    have := h591_sh'; show (denoteGraph sm initSM 591).shape = [32, 32]; exact this
  have hbridge := bridge_dW_4 1 8 8 32
      (denoteGraph pm initPM 1491) (denoteGraph pm initPM 1494)
      (denoteGraph pm initPM 1497) (denoteGraph pm initPM 1500)
      (denoteGraph pm initPM 590) (denoteGraph sm initSM 591)
      (denoteGraph pm initPM 1473) (denoteGraph pm initPM 1474)
      (denoteGraph pm initPM 1475) (denoteGraph pm initPM 1476)
      hgr0_sh hgr1_sh hgr2_sh hgr3_sh
      hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      h590_pm_sh h591_full_sh
      (by decide) (by decide) (by decide) (by decide)
  -- Final result shape for sm 751
  have h752_sh' : (denoteGraph sm initSM 752).shape = [1, 8, 32] := by
    have := h752_sh; simp only [goal_136] at this; exact this
  have hLHS_sh : (denoteGraph sm initSM 751).shape = [32, 32] := by
    rw [hS]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [h752_sh', h590_sh', h591_sh']
    rfl
  have hP0_sh : (denoteGraph pm initPM 1490).shape = [8, 32] := by
    rw [hP0]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr0_sh, h590_pm_sh, hwr0_pm_sh]
    rfl
  have hP1_sh : (denoteGraph pm initPM 1493).shape = [8, 32] := by
    rw [hP1]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr1_sh, h590_pm_sh, hwr1_pm_sh]
    rfl
  have hP2_sh : (denoteGraph pm initPM 1496).shape = [8, 32] := by
    rw [hP2]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr2_sh, h590_pm_sh, hwr2_pm_sh]
    rfl
  have hP3_sh : (denoteGraph pm initPM 1499).shape = [8, 32] := by
    rw [hP3]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr3_sh, h590_pm_sh, hwr3_pm_sh]
    rfl
  have hnr : pm.numRanks = 4 := rfl
  -- Reconstruction equation: denoteGraph sm 751 = allGatherPrimDimN 0 4 0 [pm 1490, ...]
  have h752_dimN4 : denoteGraph sm initSM 752 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 1491, denoteGraph pm initPM 1494,
       denoteGraph pm initPM 1497, denoteGraph pm initPM 1500] := by
    rw [h752_dimN, hnr]
  have hreco : denoteGraph sm initSM 751 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 1490, denoteGraph pm initPM 1493,
       denoteGraph pm initPM 1496, denoteGraph pm initPM 1499] := by
    rw [hS, h752_dimN4, h590_rec]
    rw [hbridge]
    rw [← hP0, ← hP1, ← hP2, ← hP3]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 751).shape = [32, 32]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 1490 } : Piece),
          ({ rank := 1, tid := 1493 } : Piece),
          ({ rank := 2, tid := 1496 } : Piece),
          ({ rank := 3, tid := 1499 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[8, 32], [8, 32], [8, 32], [8, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · show denoteGraph sm initSM 751 =
        reconstructWithDim 0 pm.numRanks 0
          ([({ rank := 0, tid := 1490 } : Piece),
            ({ rank := 1, tid := 1493 } : Piece),
            ({ rank := 2, tid := 1496 } : Piece),
            ({ rank := 3, tid := 1499 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 0 4 0 _ _ _ (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco
private theorem prove_goal_141 :
    ∀ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv → StoreShapesHold initPM pmInitEnv →
      InitGoalsHold pm.numRanks initGoals initSM initPM →
      let smStore := denoteGraph sm initSM
      let pmStore := denoteGraph pm initPM
      (smStore goal_141.ts).shape = goal_141.tsShape ∧
        ((goal_141.tps.map (fun p => pmStore p.tid)).map (·.shape)) = goal_141.tpShapes ∧
        smStore goal_141.ts =
          reconstructWithDim goal_141.gatherDim pm.numRanks 0
            (goal_141.tps.map (fun p => pmStore p.tid)) := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- gradOut prereq (goal_142 ↦ Pattern_77)
  have h142 := prove_pattern_79 (target := goal_142_stmt) pattern_79_target.goal_142
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h142_SH, hgr_sh, h142_REC⟩ := h142
  simp only [goal_142, List.map_cons, List.map_nil] at hgr_sh h142_REC
  have hgr0_sh : (denoteGraph pm initPM 1575).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.1
  have hgr1_sh : (denoteGraph pm initPM 1578).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hgr2_sh : (denoteGraph pm initPM 1581).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hgr3_sh : (denoteGraph pm initPM 1584).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h142_DIMN : denoteGraph sm initSM 760 = allGatherPrimDimN 2 pm.numRanks 0
      [denoteGraph pm initPM 1575, denoteGraph pm initPM 1578,
       denoteGraph pm initPM 1581, denoteGraph pm initPM 1584] := by
    rw [h142_REC]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hgr0_sh]; intro hc; cases hc
  -- x prereq (goal_25 ↦ Pattern_18, singleton)
  have h25 := prove_pattern_21 (target := goal_25_stmt) pattern_21_target.goal_25
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h25_SH, _, h25_REC⟩ := h25
  simp only [goal_25, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h25_REC
  have h25_SH' : (denoteGraph sm initSM 596).shape = [1, 8, 32] := by
    have := h25_SH; simp only [goal_25] at this; exact this
  -- weight initGoal_597
  have h597_init := hInitGoals initGoal_597 (by simp [initGoals])
  obtain ⟨h597_sh, hw_sh, h597_rec⟩ := h597_init
  simp only [initGoal_597, List.map_cons, List.map_nil] at h597_rec hw_sh
  have hwr0_sh : (initPM 1557).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have h597_dimN : initSM 597 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 1557, initPM 1558, initPM 1559, initPM 1560] := by
    rw [h597_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  -- Lift 597 / 1557-1560 from init store to denoteGraph.
  have H597 : denoteGraph sm initSM 597 = initSM 597 :=
    denote_init_tid sm initSM 597 (by decide)
  have H1557 : denoteGraph pm initPM 1557 = initPM 1557 :=
    denote_init_tid pm initPM 1557 (by decide)
  have H1558 : denoteGraph pm initPM 1558 = initPM 1558 :=
    denote_init_tid pm initPM 1558 (by decide)
  have H1559 : denoteGraph pm initPM 1559 = initPM 1559 :=
    denote_init_tid pm initPM 1559 (by decide)
  have H1560 : denoteGraph pm initPM 1560 = initPM 1560 :=
    denote_init_tid pm initPM 1560 (by decide)
  -- sm / pm dW evaluations
  have hS := sm_eval_759 initSM
  have hP0 := pm_eval_1574 initPM
  have hP1 := pm_eval_1577 initPM
  have hP2 := pm_eval_1580 initPM
  have hP3 := pm_eval_1583 initPM
  -- per-shard shapes / final result shape
  have h597_sh' : (denoteGraph sm initSM 597).shape = [128, 32] := by
    rw [H597]
    have := h597_sh; simp only [initGoal_597] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 1557).shape = [32, 32] := by rw [H1557]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 1558).shape = [32, 32] := by
    rw [H1558]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_pm_sh : (denoteGraph pm initPM 1559).shape = [32, 32] := by
    rw [H1559]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_pm_sh : (denoteGraph pm initPM 1560).shape = [32, 32] := by
    rw [H1560]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  -- bridge_dW_4 application: full_o = shard_o * 4 = 32 * 4 = 32
  have h25_PM_SH : (denoteGraph pm initPM 596).shape = [1, 8, 32] := by
    rw [← h25_REC]; exact h25_SH'
  have h597_full_sh : (denoteGraph sm initSM 597).shape = [32 * 4, 32] := by
    have := h597_sh'; show (denoteGraph sm initSM 597).shape = [128, 32]; exact this
  have hbridge := bridge_dW_4 1 8 32 32
      (denoteGraph pm initPM 1575) (denoteGraph pm initPM 1578)
      (denoteGraph pm initPM 1581) (denoteGraph pm initPM 1584)
      (denoteGraph pm initPM 596) (denoteGraph sm initSM 597)
      (denoteGraph pm initPM 1557) (denoteGraph pm initPM 1558)
      (denoteGraph pm initPM 1559) (denoteGraph pm initPM 1560)
      hgr0_sh hgr1_sh hgr2_sh hgr3_sh
      hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      h25_PM_SH h597_full_sh
      (by decide) (by decide) (by decide) (by decide)
  -- Final result shape for sm 759
  have h142_SH' : (denoteGraph sm initSM 760).shape = [1, 8, 128] := by
    have := h142_SH; simp only [goal_142] at this; exact this
  have hLHS_sh : (denoteGraph sm initSM 759).shape = [128, 32] := by
    rw [hS]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [h142_SH', h25_SH', h597_sh']
    rfl
  have hP0_sh : (denoteGraph pm initPM 1574).shape = [32, 32] := by
    rw [hP0]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr0_sh, h25_PM_SH, hwr0_pm_sh]
    rfl
  have hP1_sh : (denoteGraph pm initPM 1577).shape = [32, 32] := by
    rw [hP1]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr1_sh, h25_PM_SH, hwr1_pm_sh]
    rfl
  have hP2_sh : (denoteGraph pm initPM 1580).shape = [32, 32] := by
    rw [hP2]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr2_sh, h25_PM_SH, hwr2_pm_sh]
    rfl
  have hP3_sh : (denoteGraph pm initPM 1583).shape = [32, 32] := by
    rw [hP3]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr3_sh, h25_PM_SH, hwr3_pm_sh]
    rfl
  have hnr : pm.numRanks = 4 := rfl
  -- Reconstruction equation: denoteGraph sm 759 = allGatherPrimDimN 0 4 0 [pm 1574, ...]
  have h142_DIMN4 : denoteGraph sm initSM 760 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 1575, denoteGraph pm initPM 1578,
       denoteGraph pm initPM 1581, denoteGraph pm initPM 1584] := by
    rw [h142_DIMN, hnr]
  have hreco : denoteGraph sm initSM 759 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 1574, denoteGraph pm initPM 1577,
       denoteGraph pm initPM 1580, denoteGraph pm initPM 1583] := by
    rw [hS, h142_DIMN4, h25_REC]
    rw [hbridge]
    rw [← hP0, ← hP1, ← hP2, ← hP3]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 759).shape = [128, 32]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 1574 } : Piece),
          ({ rank := 1, tid := 1577 } : Piece),
          ({ rank := 2, tid := 1580 } : Piece),
          ({ rank := 3, tid := 1583 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[32, 32], [32, 32], [32, 32], [32, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · show denoteGraph sm initSM 759 =
        reconstructWithDim 0 pm.numRanks 0
          ([({ rank := 0, tid := 1574 } : Piece),
            ({ rank := 1, tid := 1577 } : Piece),
            ({ rank := 2, tid := 1580 } : Piece),
            ({ rank := 3, tid := 1583 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 0 4 0 _ _ _ (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco
private theorem prove_goal_176 :
    ∀ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv → StoreShapesHold initPM pmInitEnv →
      InitGoalsHold pm.numRanks initGoals initSM initPM →
      let smStore := denoteGraph sm initSM
      let pmStore := denoteGraph pm initPM
      (smStore goal_176.ts).shape = goal_176.tsShape ∧
        ((goal_176.tps.map (fun p => pmStore p.tid)).map (·.shape)) = goal_176.tpShapes ∧
        smStore goal_176.ts =
          reconstructWithDim goal_176.gatherDim pm.numRanks 0
            (goal_176.tps.map (fun p => pmStore p.tid)) := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- gradOut prereq (goal_177 ↦ Pattern_77)
  have h177 := prove_pattern_98 (target := goal_177_stmt) pattern_98_target.goal_177
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h177_SH, hgr_sh, h177_REC⟩ := h177
  simp only [goal_177, List.map_cons, List.map_nil] at hgr_sh h177_REC
  have hgr0_sh : (denoteGraph pm initPM 2131).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.1
  have hgr1_sh : (denoteGraph pm initPM 2134).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hgr2_sh : (denoteGraph pm initPM 2137).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hgr3_sh : (denoteGraph pm initPM 2140).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h177_DIMN : denoteGraph sm initSM 802 = allGatherPrimDimN 2 pm.numRanks 0
      [denoteGraph pm initPM 2131, denoteGraph pm initPM 2134,
       denoteGraph pm initPM 2137, denoteGraph pm initPM 2140] := by
    rw [h177_REC]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hgr0_sh]; intro hc; cases hc
  -- x prereq (goal_50 ↦ Pattern_18, singleton)
  have h50 := prove_pattern_21 (target := goal_50_stmt) pattern_21_target.goal_50
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h50_SH, _, h50_REC⟩ := h50
  simp only [goal_50, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h50_REC
  have h50_SH' : (denoteGraph sm initSM 631).shape = [1, 8, 32] := by
    have := h50_SH; simp only [goal_50] at this; exact this
  -- weight initGoal_632
  have h632_init := hInitGoals initGoal_632 (by simp [initGoals])
  obtain ⟨h632_sh, hw_sh, h632_rec⟩ := h632_init
  simp only [initGoal_632, List.map_cons, List.map_nil] at h632_rec hw_sh
  have hwr0_sh : (initPM 2113).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have h632_dimN : initSM 632 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 2113, initPM 2114, initPM 2115, initPM 2116] := by
    rw [h632_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  -- Lift 632 / 2113-2116 from init store to denoteGraph.
  have H632 : denoteGraph sm initSM 632 = initSM 632 :=
    denote_init_tid sm initSM 632 (by decide)
  have H2113 : denoteGraph pm initPM 2113 = initPM 2113 :=
    denote_init_tid pm initPM 2113 (by decide)
  have H2114 : denoteGraph pm initPM 2114 = initPM 2114 :=
    denote_init_tid pm initPM 2114 (by decide)
  have H2115 : denoteGraph pm initPM 2115 = initPM 2115 :=
    denote_init_tid pm initPM 2115 (by decide)
  have H2116 : denoteGraph pm initPM 2116 = initPM 2116 :=
    denote_init_tid pm initPM 2116 (by decide)
  -- sm / pm dW evaluations
  have hS := sm_eval_801 initSM
  have hP0 := pm_eval_2130 initPM
  have hP1 := pm_eval_2133 initPM
  have hP2 := pm_eval_2136 initPM
  have hP3 := pm_eval_2139 initPM
  -- per-shard shapes / final result shape
  have h632_sh' : (denoteGraph sm initSM 632).shape = [128, 32] := by
    rw [H632]
    have := h632_sh; simp only [initGoal_632] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 2113).shape = [32, 32] := by rw [H2113]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 2114).shape = [32, 32] := by
    rw [H2114]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_pm_sh : (denoteGraph pm initPM 2115).shape = [32, 32] := by
    rw [H2115]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_pm_sh : (denoteGraph pm initPM 2116).shape = [32, 32] := by
    rw [H2116]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  -- bridge_dW_4 application: full_o = shard_o * 4 = 32 * 4 = 32
  have h50_PM_SH : (denoteGraph pm initPM 631).shape = [1, 8, 32] := by
    rw [← h50_REC]; exact h50_SH'
  have h632_full_sh : (denoteGraph sm initSM 632).shape = [32 * 4, 32] := by
    have := h632_sh'; show (denoteGraph sm initSM 632).shape = [128, 32]; exact this
  have hbridge := bridge_dW_4 1 8 32 32
      (denoteGraph pm initPM 2131) (denoteGraph pm initPM 2134)
      (denoteGraph pm initPM 2137) (denoteGraph pm initPM 2140)
      (denoteGraph pm initPM 631) (denoteGraph sm initSM 632)
      (denoteGraph pm initPM 2113) (denoteGraph pm initPM 2114)
      (denoteGraph pm initPM 2115) (denoteGraph pm initPM 2116)
      hgr0_sh hgr1_sh hgr2_sh hgr3_sh
      hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      h50_PM_SH h632_full_sh
      (by decide) (by decide) (by decide) (by decide)
  -- Final result shape for sm 801
  have h177_SH' : (denoteGraph sm initSM 802).shape = [1, 8, 128] := by
    have := h177_SH; simp only [goal_177] at this; exact this
  have hLHS_sh : (denoteGraph sm initSM 801).shape = [128, 32] := by
    rw [hS]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [h177_SH', h50_SH', h632_sh']
    rfl
  have hP0_sh : (denoteGraph pm initPM 2130).shape = [32, 32] := by
    rw [hP0]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr0_sh, h50_PM_SH, hwr0_pm_sh]
    rfl
  have hP1_sh : (denoteGraph pm initPM 2133).shape = [32, 32] := by
    rw [hP1]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr1_sh, h50_PM_SH, hwr1_pm_sh]
    rfl
  have hP2_sh : (denoteGraph pm initPM 2136).shape = [32, 32] := by
    rw [hP2]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr2_sh, h50_PM_SH, hwr2_pm_sh]
    rfl
  have hP3_sh : (denoteGraph pm initPM 2139).shape = [32, 32] := by
    rw [hP3]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr3_sh, h50_PM_SH, hwr3_pm_sh]
    rfl
  have hnr : pm.numRanks = 4 := rfl
  -- Reconstruction equation: denoteGraph sm 801 = allGatherPrimDimN 0 4 0 [pm 2130, ...]
  have h177_DIMN4 : denoteGraph sm initSM 802 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 2131, denoteGraph pm initPM 2134,
       denoteGraph pm initPM 2137, denoteGraph pm initPM 2140] := by
    rw [h177_DIMN, hnr]
  have hreco : denoteGraph sm initSM 801 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 2130, denoteGraph pm initPM 2133,
       denoteGraph pm initPM 2136, denoteGraph pm initPM 2139] := by
    rw [hS, h177_DIMN4, h50_REC]
    rw [hbridge]
    rw [← hP0, ← hP1, ← hP2, ← hP3]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 801).shape = [128, 32]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 2130 } : Piece),
          ({ rank := 1, tid := 2133 } : Piece),
          ({ rank := 2, tid := 2136 } : Piece),
          ({ rank := 3, tid := 2139 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[32, 32], [32, 32], [32, 32], [32, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · show denoteGraph sm initSM 801 =
        reconstructWithDim 0 pm.numRanks 0
          ([({ rank := 0, tid := 2130 } : Piece),
            ({ rank := 1, tid := 2133 } : Piece),
            ({ rank := 2, tid := 2136 } : Piece),
            ({ rank := 3, tid := 2139 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 0 4 0 _ _ _ (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco
private theorem prove_goal_179 :
    ∀ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv → StoreShapesHold initPM pmInitEnv →
      InitGoalsHold pm.numRanks initGoals initSM initPM →
      let smStore := denoteGraph sm initSM
      let pmStore := denoteGraph pm initPM
      (smStore goal_179.ts).shape = goal_179.tsShape ∧
        ((goal_179.tps.map (fun p => pmStore p.tid)).map (·.shape)) = goal_179.tpShapes ∧
        smStore goal_179.ts =
          reconstructWithDim goal_179.gatherDim pm.numRanks 0
            (goal_179.tps.map (fun p => pmStore p.tid)) := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- gradOut prereq (goal_180 ↦ Pattern_77)
  have h180 := prove_pattern_99 (target := goal_180_stmt) pattern_99_target.goal_180
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h180_SH, hgr_sh, h180_REC⟩ := h180
  simp only [goal_180, List.map_cons, List.map_nil] at hgr_sh h180_REC
  have hgr0_sh : (denoteGraph pm initPM 2183).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.1
  have hgr1_sh : (denoteGraph pm initPM 2186).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hgr2_sh : (denoteGraph pm initPM 2189).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hgr3_sh : (denoteGraph pm initPM 2192).shape = [1, 8, 8] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h180_DIMN : denoteGraph sm initSM 805 = allGatherPrimDimN 2 pm.numRanks 0
      [denoteGraph pm initPM 2183, denoteGraph pm initPM 2186,
       denoteGraph pm initPM 2189, denoteGraph pm initPM 2192] := by
    rw [h180_REC]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hgr0_sh]; intro hc; cases hc
  -- x prereq (goal_52 ↦ Pattern_18, singleton)
  have h52 := prove_pattern_35 (target := goal_52_stmt) pattern_35_target.goal_52
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h52_SH, _, h52_REC⟩ := h52
  simp only [goal_52, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h52_REC
  have h52_SH' : (denoteGraph sm initSM 634).shape = [1, 8, 128] := by
    have := h52_SH; simp only [goal_52] at this; exact this
  -- weight initGoal_635
  have h635_init := hInitGoals initGoal_635 (by simp [initGoals])
  obtain ⟨h635_sh, hw_sh, h635_rec⟩ := h635_init
  simp only [initGoal_635, List.map_cons, List.map_nil] at h635_rec hw_sh
  have hwr0_sh : (initPM 2165).shape = [8, 128] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have h635_dimN : initSM 635 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 2165, initPM 2166, initPM 2167, initPM 2168] := by
    rw [h635_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  -- Lift 635 / 2165-2168 from init store to denoteGraph.
  have H635 : denoteGraph sm initSM 635 = initSM 635 :=
    denote_init_tid sm initSM 635 (by decide)
  have H2165 : denoteGraph pm initPM 2165 = initPM 2165 :=
    denote_init_tid pm initPM 2165 (by decide)
  have H2166 : denoteGraph pm initPM 2166 = initPM 2166 :=
    denote_init_tid pm initPM 2166 (by decide)
  have H2167 : denoteGraph pm initPM 2167 = initPM 2167 :=
    denote_init_tid pm initPM 2167 (by decide)
  have H2168 : denoteGraph pm initPM 2168 = initPM 2168 :=
    denote_init_tid pm initPM 2168 (by decide)
  -- sm / pm dW evaluations
  have hS := sm_eval_804 initSM
  have hP0 := pm_eval_2182 initPM
  have hP1 := pm_eval_2185 initPM
  have hP2 := pm_eval_2188 initPM
  have hP3 := pm_eval_2191 initPM
  -- per-shard shapes / final result shape
  have h635_sh' : (denoteGraph sm initSM 635).shape = [32, 128] := by
    rw [H635]
    have := h635_sh; simp only [initGoal_635] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 2165).shape = [8, 128] := by rw [H2165]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 2166).shape = [8, 128] := by
    rw [H2166]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_pm_sh : (denoteGraph pm initPM 2167).shape = [8, 128] := by
    rw [H2167]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_pm_sh : (denoteGraph pm initPM 2168).shape = [8, 128] := by
    rw [H2168]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  -- bridge_dW_4 application: full_o = shard_o * 4 = 8 * 4 = 32
  have h52_PM_SH : (denoteGraph pm initPM 634).shape = [1, 8, 128] := by
    rw [← h52_REC]; exact h52_SH'
  have h635_full_sh : (denoteGraph sm initSM 635).shape = [8 * 4, 128] := by
    have := h635_sh'; show (denoteGraph sm initSM 635).shape = [32, 128]; exact this
  have hbridge := bridge_dW_4 1 8 8 128
      (denoteGraph pm initPM 2183) (denoteGraph pm initPM 2186)
      (denoteGraph pm initPM 2189) (denoteGraph pm initPM 2192)
      (denoteGraph pm initPM 634) (denoteGraph sm initSM 635)
      (denoteGraph pm initPM 2165) (denoteGraph pm initPM 2166)
      (denoteGraph pm initPM 2167) (denoteGraph pm initPM 2168)
      hgr0_sh hgr1_sh hgr2_sh hgr3_sh
      hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      h52_PM_SH h635_full_sh
      (by decide) (by decide) (by decide) (by decide)
  -- Final result shape for sm 804
  have h180_SH' : (denoteGraph sm initSM 805).shape = [1, 8, 32] := by
    have := h180_SH; simp only [goal_180] at this; exact this
  have hLHS_sh : (denoteGraph sm initSM 804).shape = [32, 128] := by
    rw [hS]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [h180_SH', h52_SH', h635_sh']
    rfl
  have hP0_sh : (denoteGraph pm initPM 2182).shape = [8, 128] := by
    rw [hP0]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr0_sh, h52_PM_SH, hwr0_pm_sh]
    rfl
  have hP1_sh : (denoteGraph pm initPM 2185).shape = [8, 128] := by
    rw [hP1]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr1_sh, h52_PM_SH, hwr1_pm_sh]
    rfl
  have hP2_sh : (denoteGraph pm initPM 2188).shape = [8, 128] := by
    rw [hP2]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr2_sh, h52_PM_SH, hwr2_pm_sh]
    rfl
  have hP3_sh : (denoteGraph pm initPM 2191).shape = [8, 128] := by
    rw [hP3]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr3_sh, h52_PM_SH, hwr3_pm_sh]
    rfl
  have hnr : pm.numRanks = 4 := rfl
  -- Reconstruction equation: denoteGraph sm 804 = allGatherPrimDimN 0 4 0 [pm 2182, ...]
  have h180_DIMN4 : denoteGraph sm initSM 805 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 2183, denoteGraph pm initPM 2186,
       denoteGraph pm initPM 2189, denoteGraph pm initPM 2192] := by
    rw [h180_DIMN, hnr]
  have hreco : denoteGraph sm initSM 804 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 2182, denoteGraph pm initPM 2185,
       denoteGraph pm initPM 2188, denoteGraph pm initPM 2191] := by
    rw [hS, h180_DIMN4, h52_REC]
    rw [hbridge]
    rw [← hP0, ← hP1, ← hP2, ← hP3]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 804).shape = [32, 128]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 2182 } : Piece),
          ({ rank := 1, tid := 2185 } : Piece),
          ({ rank := 2, tid := 2188 } : Piece),
          ({ rank := 3, tid := 2191 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[8, 128], [8, 128], [8, 128], [8, 128]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · show denoteGraph sm initSM 804 =
        reconstructWithDim 0 pm.numRanks 0
          ([({ rank := 0, tid := 2182 } : Piece),
            ({ rank := 1, tid := 2185 } : Piece),
            ({ rank := 2, tid := 2188 } : Piece),
            ({ rank := 3, tid := 2191 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 0 4 0 _ _ _ (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco
private theorem prove_goal_255 :
    ∀ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv → StoreShapesHold initPM pmInitEnv →
      InitGoalsHold pm.numRanks initGoals initSM initPM →
      let smStore := denoteGraph sm initSM
      let pmStore := denoteGraph pm initPM
      (smStore goal_255.ts).shape = goal_255.tsShape ∧
        ((goal_255.tps.map (fun p => pmStore p.tid)).map (·.shape)) = goal_255.tpShapes ∧
        smStore goal_255.ts =
          reconstructWithDim goal_255.gatherDim pm.numRanks 0
            (goal_255.tps.map (fun p => pmStore p.tid)) := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- gradOut prereq (goal_256 ↦ Pattern_77)
  have h256 := prove_pattern_126 (target := goal_256_stmt) pattern_126_target.goal_256
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h256_SH, hgr_sh, h256_REC⟩ := h256
  simp only [goal_256, List.map_cons, List.map_nil] at hgr_sh h256_REC
  have hgr0_sh : (denoteGraph pm initPM 3387).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.1
  have hgr1_sh : (denoteGraph pm initPM 3390).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hgr2_sh : (denoteGraph pm initPM 3393).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hgr3_sh : (denoteGraph pm initPM 3396).shape = [1, 8, 32] := by
    have := hgr_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h256_DIMN : denoteGraph sm initSM 895 = allGatherPrimDimN 2 pm.numRanks 0
      [denoteGraph pm initPM 3387, denoteGraph pm initPM 3390,
       denoteGraph pm initPM 3393, denoteGraph pm initPM 3396] := by
    rw [h256_REC]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hgr0_sh]; intro hc; cases hc
  -- x prereq (goal_105 ↦ Pattern_18, singleton)
  have h105 := prove_pattern_21 (target := goal_105_stmt) pattern_21_target.goal_105
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h105_SH, _, h105_REC⟩ := h105
  simp only [goal_105, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h105_REC
  have h105_SH' : (denoteGraph sm initSM 710).shape = [1, 8, 32] := by
    have := h105_SH; simp only [goal_105] at this; exact this
  -- weight initGoal_711
  have h711_init := hInitGoals initGoal_711 (by simp [initGoals])
  obtain ⟨h711_sh, hw_sh, h711_rec⟩ := h711_init
  simp only [initGoal_711, List.map_cons, List.map_nil] at h711_rec hw_sh
  have hwr0_sh : (initPM 3369).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have h711_dimN : initSM 711 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 3369, initPM 3370, initPM 3371, initPM 3372] := by
    rw [h711_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  -- Lift 711 / 3369-3372 from init store to denoteGraph.
  have H711 : denoteGraph sm initSM 711 = initSM 711 :=
    denote_init_tid sm initSM 711 (by decide)
  have H3369 : denoteGraph pm initPM 3369 = initPM 3369 :=
    denote_init_tid pm initPM 3369 (by decide)
  have H3370 : denoteGraph pm initPM 3370 = initPM 3370 :=
    denote_init_tid pm initPM 3370 (by decide)
  have H3371 : denoteGraph pm initPM 3371 = initPM 3371 :=
    denote_init_tid pm initPM 3371 (by decide)
  have H3372 : denoteGraph pm initPM 3372 = initPM 3372 :=
    denote_init_tid pm initPM 3372 (by decide)
  -- sm / pm dW evaluations
  have hS := sm_eval_894 initSM
  have hP0 := pm_eval_3386 initPM
  have hP1 := pm_eval_3389 initPM
  have hP2 := pm_eval_3392 initPM
  have hP3 := pm_eval_3395 initPM
  -- per-shard shapes / final result shape
  have h711_sh' : (denoteGraph sm initSM 711).shape = [128, 32] := by
    rw [H711]
    have := h711_sh; simp only [initGoal_711] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 3369).shape = [32, 32] := by rw [H3369]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 3370).shape = [32, 32] := by
    rw [H3370]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_pm_sh : (denoteGraph pm initPM 3371).shape = [32, 32] := by
    rw [H3371]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_pm_sh : (denoteGraph pm initPM 3372).shape = [32, 32] := by
    rw [H3372]; have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  -- bridge_dW_4 application: full_o = shard_o * 4 = 32 * 4 = 32
  have h105_PM_SH : (denoteGraph pm initPM 710).shape = [1, 8, 32] := by
    rw [← h105_REC]; exact h105_SH'
  have h711_full_sh : (denoteGraph sm initSM 711).shape = [32 * 4, 32] := by
    have := h711_sh'; show (denoteGraph sm initSM 711).shape = [128, 32]; exact this
  have hbridge := bridge_dW_4 1 8 32 32
      (denoteGraph pm initPM 3387) (denoteGraph pm initPM 3390)
      (denoteGraph pm initPM 3393) (denoteGraph pm initPM 3396)
      (denoteGraph pm initPM 710) (denoteGraph sm initSM 711)
      (denoteGraph pm initPM 3369) (denoteGraph pm initPM 3370)
      (denoteGraph pm initPM 3371) (denoteGraph pm initPM 3372)
      hgr0_sh hgr1_sh hgr2_sh hgr3_sh
      hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      h105_PM_SH h711_full_sh
      (by decide) (by decide) (by decide) (by decide)
  -- Final result shape for sm 894
  have h256_SH' : (denoteGraph sm initSM 895).shape = [1, 8, 128] := by
    have := h256_SH; simp only [goal_256] at this; exact this
  have hLHS_sh : (denoteGraph sm initSM 894).shape = [128, 32] := by
    rw [hS]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [h256_SH', h105_SH', h711_sh']
    rfl
  have hP0_sh : (denoteGraph pm initPM 3386).shape = [32, 32] := by
    rw [hP0]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr0_sh, h105_PM_SH, hwr0_pm_sh]
    rfl
  have hP1_sh : (denoteGraph pm initPM 3389).shape = [32, 32] := by
    rw [hP1]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr1_sh, h105_PM_SH, hwr1_pm_sh]
    rfl
  have hP2_sh : (denoteGraph pm initPM 3392).shape = [32, 32] := by
    rw [hP2]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr2_sh, h105_PM_SH, hwr2_pm_sh]
    rfl
  have hP3_sh : (denoteGraph pm initPM 3395).shape = [32, 32] := by
    rw [hP3]; show (bw_linear _ _ _).2.shape = _
    unfold bw_linear
    rw [hgr3_sh, h105_PM_SH, hwr3_pm_sh]
    rfl
  have hnr : pm.numRanks = 4 := rfl
  -- Reconstruction equation: denoteGraph sm 894 = allGatherPrimDimN 0 4 0 [pm 3386, ...]
  have h256_DIMN4 : denoteGraph sm initSM 895 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 3387, denoteGraph pm initPM 3390,
       denoteGraph pm initPM 3393, denoteGraph pm initPM 3396] := by
    rw [h256_DIMN, hnr]
  have hreco : denoteGraph sm initSM 894 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 3386, denoteGraph pm initPM 3389,
       denoteGraph pm initPM 3392, denoteGraph pm initPM 3395] := by
    rw [hS, h256_DIMN4, h105_REC]
    rw [hbridge]
    rw [← hP0, ← hP1, ← hP2, ← hP3]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 894).shape = [128, 32]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 3386 } : Piece),
          ({ rank := 1, tid := 3389 } : Piece),
          ({ rank := 2, tid := 3392 } : Piece),
          ({ rank := 3, tid := 3395 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[32, 32], [32, 32], [32, 32], [32, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · show denoteGraph sm initSM 894 =
        reconstructWithDim 0 pm.numRanks 0
          ([({ rank := 0, tid := 3386 } : Piece),
            ({ rank := 1, tid := 3389 } : Piece),
            ({ rank := 2, tid := 3392 } : Piece),
            ({ rank := 3, tid := 3395 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 0 4 0 _ _ _ (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco
theorem prove_pattern_76 : pattern_76_stmt := by
  intro target h
  cases h with
  | goal_135 => exact prove_goal_135
  | goal_141 => exact prove_goal_141
  | goal_176 => exact prove_goal_176
  | goal_179 => exact prove_goal_179
  | goal_255 => exact prove_goal_255


end TrainVerify.Denote.GeneratedPatterns
