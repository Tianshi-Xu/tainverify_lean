/- Pattern_3: 24-layer YOCO attention pipeline sharding-commute proof.

   Pattern: 3
   Hash: b3365746c5960899
   Goals: 3 (prereq: goal_5)
   Op flavour: full attention pipeline
     SM = 903 ops, PM = 1866 ops
     - rms_norm, per_head_mix_precision_linear, rotary_embedding
     - attn_sliding_window (windowLeft=512, intra-rank)
     - attn_zigzag (cross-rank ring-attention → uses ring semantics)
     - all2all_moe_gmm (expert-parallel MoE, same as Pattern_1)
     - fw_add, fw_mul, view, reshape, multiref, sigmoid, swiglu, mix_precision_linear
     - final fw_stack of 24 layer outputs; AllGatherPrim on dim 1

   Design decision (2026-07-04): use ring-attention semantics
   (`denoteGraph_ringAttn` + `CoarseLineageHoldsWithInit_ringAttn`) rather
   than the identity model, to be 100% faithful to Python
   `wrap_zigzag_attn_func` behavior. See Denote.lean line 20821+.

   The `goal_3_stmt_cut_ringAttn` below is the ring-attention–aware version
   of `goal_3_stmt_cut`; the plain version uses the identity model on
   FW_attn_zigzag which would make the goal false (SM=full attn ≠ PM=identity).
-/
import denote.yoco_goals.Goal_3
import denote.yoco_goals.Pattern_1  -- reuse fw_topk_routing_snd_fst_allGather0_commute_2_of (routing_map commute)

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

/-- Ring-attention–aware variant of `goal_3_stmt_cut`. Uses `denoteGraph_ringAttn`
    to model the cross-rank ring attention in `FW_attn_zigzag` faithfully. -/
def goal_3_stmt_cut_ringAttn : Prop :=
  CoarseLineageHoldsWithInit_ringAttn sm_goal_3 pm_goal_3 goal_3
    sm_goal_3InitEnv pm_goal_3InitEnv goal_3_cut_initGoals

def pattern_3_goalIds : List Nat := [3]

inductive pattern_3_target : Prop → Prop
  | goal_3 : pattern_3_target goal_3_stmt_cut_ringAttn

def pattern_3_stmt : Prop :=
  ∀ {target : Prop}, pattern_3_target target → target

/-- Prerequisite: proves `goal_3_stmt_cut_ringAttn` given all Store shape
    hypotheses, init goal hypotheses (including goal_5 as a prereq). -/
theorem prove_goal_3 : goal_3_stmt_cut_ringAttn := by
  sorry
  -- Hand-proof: uses Pattern_1's fw_all2all_moe_gmm_full_split_commute_2
  -- lemma (already proven), applied per layer, chained through 24 layers,
  -- lifted via fw_stack + AllGatherPrim on dim 1. Ring-attn semantics
  -- ensure attn commutes with token-dim chunking (via allgather-then-attn).

theorem prove_pattern_3 : pattern_3_stmt := by
  intro target ht
  cases ht
  exact prove_goal_3

/-! ### Phase C1: concrete `ringAttnBuddies` structure lemmas.

    The graphs `sm_goal_3` / `pm_goal_3` are concrete literal node lists, so the
    buddy structure of every `FW_attn_zigzag` node is fully computational. We
    package the fact as a decidable bounded quantifier over the (finite) node
    list and discharge it with `native_decide`. -/

/-- Auxiliary (decidable, computational): every zigzag node in the SM graph is
    its own unique ring-attention buddy. -/
theorem sm_goal_3_zigzag_buddies_singleton_aux :
    ∀ n ∈ sm_goal_3.nodes,
      n.op = "OpName.FW_attn_zigzag" → ringAttnBuddies sm_goal_3 n = [n] := by
  native_decide

/-- For sm_goal_3 (numRanks=1), each FW_attn_zigzag node in the graph is its own
    unique ring-attention buddy (buddies list = [node itself]). -/
theorem sm_goal_3_zigzag_buddies_singleton (n : NodeDecl)
    (hn_mem : n ∈ sm_goal_3.nodes)
    (hn_op : n.op = "OpName.FW_attn_zigzag") :
    ringAttnBuddies sm_goal_3 n = [n] :=
  sm_goal_3_zigzag_buddies_singleton_aux n hn_mem hn_op

/-- Auxiliary (decidable, computational): every zigzag node in the PM graph has
    exactly two ring-attention buddies and is a member of its own buddy list. -/
theorem pm_goal_3_zigzag_buddies_pair_aux :
    ∀ n ∈ pm_goal_3.nodes,
      n.op = "OpName.FW_attn_zigzag" →
        (ringAttnBuddies pm_goal_3 n).length = 2
        ∧ n ∈ ringAttnBuddies pm_goal_3 n := by
  native_decide

/-- For pm_goal_3 (numRanks=2), each FW_attn_zigzag node has exactly one other
    buddy (the partner at the matching layer with different rank). The buddies
    list has length 2 and includes n itself. -/
theorem pm_goal_3_zigzag_buddies_pair (n : NodeDecl)
    (hn_mem : n ∈ pm_goal_3.nodes)
    (hn_op : n.op = "OpName.FW_attn_zigzag") :
    (ringAttnBuddies pm_goal_3 n).length = 2
    ∧ n ∈ ringAttnBuddies pm_goal_3 n :=
  pm_goal_3_zigzag_buddies_pair_aux n hn_mem hn_op

/-! ### Phase A revised (sliding_window): concrete `ringAttnBuddies` structure.

    The same buddy-structure facts, but for `FW_attn_sliding_window` nodes. These
    feed the sliding-window ring semantics (`applyNodeRingAttn_sliding_window`)
    the way the zigzag lemmas above feed `applyNodeRingAttn_zigzag`. -/

/-- Auxiliary (decidable, computational): every sliding-window node in the SM
    graph is its own unique ring-attention buddy. -/
theorem sm_goal_3_sliding_window_buddies_singleton_aux :
    ∀ n ∈ sm_goal_3.nodes,
      n.op = "OpName.FW_attn_sliding_window" → ringAttnBuddies sm_goal_3 n = [n] := by
  native_decide

/-- For sm_goal_3 (numRanks=1), each FW_attn_sliding_window node in the graph is
    its own unique ring-attention buddy (buddies list = [node itself]). -/
theorem sm_goal_3_sliding_window_buddies_singleton (n : NodeDecl)
    (hn_mem : n ∈ sm_goal_3.nodes)
    (hn_op : n.op = "OpName.FW_attn_sliding_window") :
    ringAttnBuddies sm_goal_3 n = [n] :=
  sm_goal_3_sliding_window_buddies_singleton_aux n hn_mem hn_op

/-- Auxiliary (decidable, computational): every sliding-window node in the PM
    graph has exactly two ring-attention buddies and is a member of its own
    buddy list. -/
theorem pm_goal_3_sliding_window_buddies_pair_aux :
    ∀ n ∈ pm_goal_3.nodes,
      n.op = "OpName.FW_attn_sliding_window" →
        (ringAttnBuddies pm_goal_3 n).length = 2
        ∧ n ∈ ringAttnBuddies pm_goal_3 n := by
  native_decide

/-- For pm_goal_3 (numRanks=2), each FW_attn_sliding_window node has exactly one
    other buddy (the partner at the matching layer with different rank). The
    buddies list has length 2 and includes n itself. -/
theorem pm_goal_3_sliding_window_buddies_pair (n : NodeDecl)
    (hn_mem : n ∈ pm_goal_3.nodes)
    (hn_op : n.op = "OpName.FW_attn_sliding_window") :
    (ringAttnBuddies pm_goal_3 n).length = 2
    ∧ n ∈ ringAttnBuddies pm_goal_3 n :=
  pm_goal_3_sliding_window_buddies_pair_aux n hn_mem hn_op

/-! ### Phase C2b: ring-attention chunk-gather reconstruction (numShards = 2).

    Core building block for the `FW_attn_zigzag` per-rank commute: gathering the
    two sequence-dim chunks of a `[2*Lshard, d1, d2]` tensor rebuilds it exactly.
    This is the Denote-level statement that `applyNodeRingAttn_zigzag` on a buddy
    *pair* (PM, numRanks=2) reconstructs the full attention output that the
    singleton (SM, numRanks=1) case computes directly:
      `allGather0 [chunk0 fullOut, chunk1 fullOut] = fullOut`. -/

/-- Local copy of the 3D allGather value-at fact (the Denote version is private). -/
private theorem gather0_3d_valAt
    (numParts Lshard d1 d2 : Nat)
    (Ws : List Tensor)
    (hparts : 0 < numParts) (hL : 0 < Lshard) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [Lshard, d1, d2])
    (r : Nat) (hr : r < numParts)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1)
    (inner : Nat) (hinner : inner < d2) :
    valAt (allGatherPrimDimN 0 numParts 0 Ws)
          (((r * Lshard + row) * d1 + col) * d2 + inner) =
      valAt (Ws.getD r (zeroTensor [Lshard, d1, d2]))
            ((row * d1 + col) * d2 + inner) := by
  have hP_pos : 0 < d1 * d2 := Nat.mul_pos hd1 hd2
  have hP_ne : d1 * d2 ≠ 0 := Nat.ne_of_gt hP_pos
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hE_pos : 0 < Lshard * numParts * (d1 * d2) :=
    Nat.mul_pos (Nat.mul_pos hL hparts) hP_pos
  have hE_ne : Lshard * numParts * (d1 * d2) ≠ 0 := Nat.ne_of_gt hE_pos
  have hlow : col * d2 + inner < d1 * d2 := by
    calc col * d2 + inner < col * d2 + d2 := by omega
      _ = (col + 1) * d2 := by ring
      _ ≤ d1 * d2 := Nat.mul_le_mul_right _ (by omega)
  have hrr : r * Lshard + row < Lshard * numParts := by
    have hsi : r * Lshard + row < (r + 1) * Lshard := by
      calc r * Lshard + row < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
    have hle : (r + 1) * Lshard ≤ numParts * Lshard := Nat.mul_le_mul_right _ hr
    calc r * Lshard + row < (r + 1) * Lshard := hsi
      _ ≤ numParts * Lshard := hle
      _ = Lshard * numParts := by ring
  have hidx_eq : ((r * Lshard + row) * d1 + col) * d2 + inner
      = (col * d2 + inner) + (d1 * d2) * (r * Lshard + row) := by ring
  have hidx_lt_E : ((r * Lshard + row) * d1 + col) * d2 + inner
      < Lshard * numParts * (d1 * d2) := by
    rw [hidx_eq]
    calc (col * d2 + inner) + (d1 * d2) * (r * Lshard + row)
        < (d1 * d2) + (d1 * d2) * (r * Lshard + row) := by omega
      _ = (d1 * d2) * (r * Lshard + row + 1) := by ring
      _ ≤ (d1 * d2) * (Lshard * numParts) := Nat.mul_le_mul_left _ (by omega)
      _ = Lshard * numParts * (d1 * d2) := by ring
  have hdiv_E : (((r * Lshard + row) * d1 + col) * d2 + inner)
      / (Lshard * numParts * (d1 * d2)) = 0 := Nat.div_eq_of_lt hidx_lt_E
  have hmod_E : (((r * Lshard + row) * d1 + col) * d2 + inner)
      % (Lshard * numParts * (d1 * d2))
      = ((r * Lshard + row) * d1 + col) * d2 + inner := Nat.mod_eq_of_lt hidx_lt_E
  have hdiv_P : (((r * Lshard + row) * d1 + col) * d2 + inner) / (d1 * d2)
      = r * Lshard + row := by
    rw [hidx_eq, Nat.add_mul_div_left _ _ hP_pos, Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hmod_P : (((r * Lshard + row) * d1 + col) * d2 + inner) % (d1 * d2)
      = col * d2 + inner := by
    rw [hidx_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hdiv_L : (r * Lshard + row) / Lshard = r := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hrow, Nat.zero_add]
  have hmod_L : (r * Lshard + row) % Lshard = row := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow]
  have hshape_out : (allGatherPrimDimN 0 numParts 0 Ws).shape
      = [Lshard * numParts, d1, d2] := by
    have := allGatherPrimDimN_shape 0 numParts Ws [Lshard, d1, d2] hhead
    simpa using this
  have hidx_lt_prod : ((r * Lshard + row) * d1 + col) * d2 + inner
      < prodShape (allGatherPrimDimN 0 numParts 0 Ws).shape := by
    rw [hshape_out]
    have hpe : prodShape [Lshard * numParts, d1, d2] = Lshard * numParts * (d1 * d2) := by
      simp [prodShape]; ring
    rw [hpe]; exact hidx_lt_E
  have h0 : valAt (allGatherPrimDimN 0 numParts 0 Ws)
        (((r * Lshard + row) * d1 + col) * d2 + inner)
      = (allGatherPrimDimN 0 numParts 0 Ws).val
          ⟨((r * Lshard + row) * d1 + col) * d2 + inner, hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    hP_ne, hL_ne, hE_ne, ite_false]
  rw [hmod_E, hdiv_E, hdiv_P, hmod_P, hdiv_L, hmod_L]
  rw [show 0 * (Lshard * (d1 * d2)) + row * (d1 * d2) + (col * d2 + inner)
        = (row * d1 + col) * d2 + inner from by ring]

/-- Chunk value-at (dim 0, numParts 2): reading local index `(row,col,inner)` of the
    r-th chunk of `T : [2*Lshard, d1, d2]` reads `T` at the full index. -/
private theorem chunk0_3d_valAt
    (Lshard d1 d2 : Nat) (hL : 0 < Lshard) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (T : Tensor) (hT : T.shape = [2 * Lshard, d1, d2])
    (r : Nat) (hr : r < 2)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1)
    (inner : Nat) (hinner : inner < d2) :
    valAt (chunkPrimDimN 0 2 r T) ((row * d1 + col) * d2 + inner) =
      valAt T (((r * Lshard + row) * d1 + col) * d2 + inner) := by
  have hP_pos : 0 < d1 * d2 := Nat.mul_pos hd1 hd2
  have hP_ne : d1 * d2 ≠ 0 := Nat.ne_of_gt hP_pos
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hLd_pos : 0 < Lshard * (d1 * d2) := Nat.mul_pos hL hP_pos
  have hLd_ne : Lshard * (d1 * d2) ≠ 0 := Nat.ne_of_gt hLd_pos
  have hlow : col * d2 + inner < d1 * d2 := by
    calc col * d2 + inner < col * d2 + d2 := by omega
      _ = (col + 1) * d2 := by ring
      _ ≤ d1 * d2 := Nat.mul_le_mul_right _ (by omega)
  -- local index in canonical form
  have hloc_eq : (row * d1 + col) * d2 + inner
      = (col * d2 + inner) + (d1 * d2) * row := by ring
  have hloc_lt : (row * d1 + col) * d2 + inner < Lshard * (d1 * d2) := by
    rw [hloc_eq]
    calc (col * d2 + inner) + (d1 * d2) * row
        < (d1 * d2) + (d1 * d2) * row := by omega
      _ = (d1 * d2) * (row + 1) := by ring
      _ ≤ (d1 * d2) * Lshard := Nat.mul_le_mul_left _ (by omega)
      _ = Lshard * (d1 * d2) := by ring
  have hdiv_S : ((row * d1 + col) * d2 + inner) / (Lshard * (d1 * d2)) = 0 :=
    Nat.div_eq_of_lt hloc_lt
  have hmod_S : ((row * d1 + col) * d2 + inner) % (Lshard * (d1 * d2))
      = (row * d1 + col) * d2 + inner := Nat.mod_eq_of_lt hloc_lt
  have hdiv_P : ((row * d1 + col) * d2 + inner) / (d1 * d2) = row := by
    rw [hloc_eq, Nat.add_mul_div_left _ _ hP_pos, Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hmod_P : ((row * d1 + col) * d2 + inner) % (d1 * d2) = col * d2 + inner := by
    rw [hloc_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
  have hrmod : r % 2 = r := Nat.mod_eq_of_lt hr
  have hsh : (2 * Lshard) / 2 = Lshard := by omega
  -- chunk shape
  have hchunk_shape : (chunkPrimDimN 0 2 r T).shape = [Lshard, d1, d2] := by
    rw [chunkPrimDimN_shape 0 2 r T [2 * Lshard, d1, d2] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [hsh]
  have hloc_lt_prod : (row * d1 + col) * d2 + inner
      < prodShape (chunkPrimDimN 0 2 r T).shape := by
    rw [hchunk_shape]
    have hpe : prodShape [Lshard, d1, d2] = Lshard * (d1 * d2) := by simp [prodShape]; ring
    rw [hpe]; exact hloc_lt
  -- T index bound
  have hfull_eq : ((r * Lshard + row) * d1 + col) * d2 + inner
      = (col * d2 + inner) + (d1 * d2) * (r * Lshard + row) := by ring
  have hrr : r * Lshard + row < 2 * Lshard := by
    have hsi : r * Lshard + row < (r + 1) * Lshard := by
      calc r * Lshard + row < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
    have hle : (r + 1) * Lshard ≤ 2 * Lshard := Nat.mul_le_mul_right _ (by omega)
    exact lt_of_lt_of_le hsi hle
  have hfull_lt : ((r * Lshard + row) * d1 + col) * d2 + inner < prodShape T.shape := by
    rw [hT]
    have hpe : prodShape [2 * Lshard, d1, d2] = 2 * Lshard * (d1 * d2) := by
      simp [prodShape]; ring
    rw [hpe, hfull_eq]
    calc (col * d2 + inner) + (d1 * d2) * (r * Lshard + row)
        < (d1 * d2) + (d1 * d2) * (r * Lshard + row) := by omega
      _ = (d1 * d2) * (r * Lshard + row + 1) := by ring
      _ ≤ (d1 * d2) * (2 * Lshard) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * Lshard * (d1 * d2) := by ring
  rw [valAt_of_lt _ _ hloc_lt_prod]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hT, List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    show ((2:Nat) = 0) = False from by decide, ite_false,
    hsh, hrmod, hP_ne, hLd_ne]
  rw [hmod_S, hdiv_S, hdiv_P, hmod_P]
  congr 1
  ring

/-- Ring-attention reconstruction (numParts = 2, seq dim = 0):
    gathering the two seq-chunks of a `[2*Lshard, d1, d2]` tensor rebuilds it. -/
theorem allGather0_reconstruct_chunks_3d
    (Lshard d1 d2 : Nat) (hL : 0 < Lshard) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (T : Tensor) (hT : T.shape = [2 * Lshard, d1, d2]) :
    allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T] = T := by
  have hsh : (2 * Lshard) / 2 = Lshard := by omega
  have hc_shape : ∀ r, (chunkPrimDimN 0 2 r T).shape = [Lshard, d1, d2] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r T [2 * Lshard, d1, d2] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]; rw [hsh]
  have hhead : (([chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].head?.map
      (fun t => t.shape)).getD []) = [Lshard, d1, d2] := by simp [hc_shape 0]
  have hgshape : (allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T]).shape
      = [2 * Lshard, d1, d2] := by
    rw [allGatherPrimDimN_shape 0 2 _ [Lshard, d1, d2] hhead]
    simp only [List.set, List.getD_cons_zero]; rw [Nat.mul_comm Lshard 2]
  apply Tensor.ext
  · rw [hgshape, hT]
  · intro idx hidx
    rw [hgshape] at hidx
    have hprod : prodShape [2 * Lshard, d1, d2] = 2 * Lshard * (d1 * d2) := by
      simp [prodShape]; ring
    rw [hprod] at hidx
    set inner := idx % d2 with hinner_def
    set col := (idx / d2) % d1 with hcol_def
    set fullrow := (idx / d2 / d1) with hfullrow_def
    have hinner : inner < d2 := by rw [hinner_def]; exact Nat.mod_lt _ hd2
    have hcol : col < d1 := by rw [hcol_def]; exact Nat.mod_lt _ hd1
    have hfullrow_lt : fullrow < 2 * Lshard := by
      rw [hfullrow_def]
      apply Nat.div_lt_of_lt_mul
      apply Nat.div_lt_of_lt_mul
      calc idx < 2 * Lshard * (d1 * d2) := hidx
        _ = d2 * (d1 * (2 * Lshard)) := by ring
    set r := fullrow / Lshard with hr_def
    set row := fullrow % Lshard with hrow_def
    have hrow : row < Lshard := by rw [hrow_def]; exact Nat.mod_lt _ hL
    have hr : r < 2 := by
      rw [hr_def]
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact hfullrow_lt
    have hfullrow_split : fullrow = r * Lshard + row := by
      rw [hr_def, hrow_def]; rw [Nat.mul_comm]; exact (Nat.div_add_mod fullrow Lshard).symm
    have hidx_decomp : idx = ((r * Lshard + row) * d1 + col) * d2 + inner := by
      rw [← hfullrow_split]
      rw [hinner_def, hcol_def, hfullrow_def]
      -- idx = ((idx/d2/d1)*d1 + (idx/d2)%d1)*d2 + idx%d2
      have e1 : (idx / d2 / d1) * d1 + (idx / d2) % d1 = idx / d2 := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod (idx / d2) d1
      rw [e1]
      rw [Nat.mul_comm (idx / d2) d2]
      exact (Nat.div_add_mod idx d2).symm
    rw [hidx_decomp]
    rw [gather0_3d_valAt 2 Lshard d1 d2 _ (by omega) hL hd1 hd2 hhead r hr row hrow col hcol inner hinner]
    have hgetD : [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].getD r (zeroTensor [Lshard, d1, d2])
        = chunkPrimDimN 0 2 r T := by
      interval_cases r <;> rfl
    rw [hgetD]
    exact chunk0_3d_valAt Lshard d1 d2 hL hd1 hd2 T hT r hr row hrow col hcol inner hinner


/-! ### Deliverable 1 (routing_map seq-chunk commute): usability of the existing lemma.

    Pattern_3 issues 24 `FW_topk_routing` nodes per rank. Each takes a logits
    tensor sharded on the sequence/token dim (dim 0). The routing_map output
    (`.snd.fst`, shape `[S, numExperts]`) is *row-local*: each token's top-k pick
    depends only on that token's score row (`inTopK` reads a single row `l`).
    Therefore the general shape-`[S, k]` lemma
    `Pattern_1`'s `fw_topk_routing_snd_fst_allGather0_commute_2_of` applies
    **directly** at Pattern_3's per-layer routing input shape — no specialized
    variant is needed. We record a concrete-shape `example` witnessing that the
    existing lemma type-checks at a representative Pattern_3 shape
    (per-rank shard `S = 2048`, `top_k = 8`, `numExperts = 8`). -/

example (a b : Tensor)
    (ha : a.shape = [2048, 8]) (hb : b.shape = [2048, 8]) :
    (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) 8 8).snd.fst
      = allGatherPrimDimN 0 2 0
          [(fw_topk_routing a 8 8).snd.fst, (fw_topk_routing b 8 8).snd.fst] :=
  fw_topk_routing_snd_fst_allGather0_commute_2_of a b 2048 8 8
    (by norm_num) (by norm_num) ha hb

/-! ### Deliverable 2: per-attention reconstruction primitives.

    These lift a single ring-attention node from SM (numRanks=1, singleton buddy)
    to the buddy *pair* on PM (numRanks=2), showing that the SM full-attention
    output equals the all-gather of the two PM per-rank output shards. This is the
    key per-layer step that lets the 24-layer induction proceed: given the
    previous layer's commute (SM q/k/v = allGather of PM q/k/v shards), the
    attention output commutes with the sequence-dim sharding.

    Structure: SM side collapses to plain `fw_attn_varlen` (singleton lemma); PM
    side reconstructs the full output from the two seq-dim chunks
    (`allGather0_reconstruct_chunks_3d`). The two full outputs coincide by the
    bridge hypotheses. Proved separately for `FW_attn_zigzag` and
    `FW_attn_sliding_window` since the two `applyNodeRingAttn_*` defs, while
    structurally identical, are distinct constants. -/

/-- PM-side buddy-pair unfold for `applyNodeRingAttn_zigzag`: a node whose buddy
    list is `[n0, n1]` computes the seq-dim chunk (index `idx = myIdx`) of the
    full attention over the all-gathered q/k/v shards. -/
theorem applyNodeRingAttn_zigzag_pair_eq_chunk
    (g : GraphDecl) (s : Store) (n n0 n1 : NodeDecl)
    (idx : Nat)
    (hbuddy : ringAttnBuddies g n = [n0, n1])
    (hmyIdx : (([n0, n1].findIdx? (fun m => m.rank = n.rank)).getD 0) = idx) :
    applyNodeRingAttn_zigzag g s n =
      chunkPrimDimN 0 2 idx
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 0 0), s (n1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 1 0), s (n1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 2 0), s (n1.ins.getD 2 0)])
          (s (n.ins.getD 3 0)) (s (n.ins.getD 4 0))
          (n.params.getD 0 1) (n.params.getD 1 1) (n.params.getD 2 1) (n.params.getD 3 1)
          (decide (n.params.getD 4 0 ≠ 0)) (n.params.getD 5 0)) := by
  unfold applyNodeRingAttn_zigzag
  rw [hbuddy]
  simp only [List.map, List.length_cons, List.length_nil, hmyIdx]

/-- PM-side buddy-pair unfold for `applyNodeRingAttn_sliding_window` (mirror of
    the zigzag version — identical reconstruction shape). -/
theorem applyNodeRingAttn_sliding_window_pair_eq_chunk
    (g : GraphDecl) (s : Store) (n n0 n1 : NodeDecl)
    (idx : Nat)
    (hbuddy : ringAttnBuddies g n = [n0, n1])
    (hmyIdx : (([n0, n1].findIdx? (fun m => m.rank = n.rank)).getD 0) = idx) :
    applyNodeRingAttn_sliding_window g s n =
      chunkPrimDimN 0 2 idx
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 0 0), s (n1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 1 0), s (n1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 2 0), s (n1.ins.getD 2 0)])
          (s (n.ins.getD 3 0)) (s (n.ins.getD 4 0))
          (n.params.getD 0 1) (n.params.getD 1 1) (n.params.getD 2 1) (n.params.getD 3 1)
          (decide (n.params.getD 4 0 ≠ 0)) (n.params.getD 5 0)) := by
  unfold applyNodeRingAttn_sliding_window
  rw [hbuddy]
  simp only [List.map, List.length_cons, List.length_nil, hmyIdx]

/-- **Per-attention reconstruction (zigzag).** Given an SM ring-attention node
    `n_sm` (singleton buddy, numRanks=1) and its PM buddy pair `n_pm_r0`,
    `n_pm_r1` (numRanks=2), together with the bridge hypotheses that SM's q/k/v
    equal the all-gather of PM's q/k/v shards (from the previous layer's commute),
    the shared cu-seqlens, and matching params, the SM ring-attention output
    equals the all-gather of the two PM per-rank ring-attention outputs. -/
theorem applyNodeRingAttn_zigzag_reconstruction_2_of_buddy_pair
    (g_sm g_pm : GraphDecl) (s_sm s_pm : Store)
    (n_sm n_pm_r0 n_pm_r1 : NodeDecl)
    (Lshard qh vd : Nat)
    (hL : 0 < Lshard) (hqh : 0 < qh) (hvd : 0 < vd)
    (hbuddy_sm : ringAttnBuddies g_sm n_sm = [n_sm])
    (hbuddy_pm : ringAttnBuddies g_pm n_pm_r0 = [n_pm_r0, n_pm_r1])
    (hbuddy_pm' : ringAttnBuddies g_pm n_pm_r1 = [n_pm_r0, n_pm_r1])
    (hmyIdx0 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r0.rank)).getD 0) = 0)
    (hmyIdx1 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r1.rank)).getD 0) = 1)
    (hq_sm : 0 < (s_sm (n_sm.ins.getD 0 0)).shape.length)
    (hk_sm : 0 < (s_sm (n_sm.ins.getD 1 0)).shape.length)
    (hv_sm : 0 < (s_sm (n_sm.ins.getD 2 0)).shape.length)
    (hq_full : s_sm (n_sm.ins.getD 0 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
    (hk_full : s_sm (n_sm.ins.getD 1 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
    (hv_full : s_sm (n_sm.ins.getD 2 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
    (hcuQ_sm_pm : s_sm (n_sm.ins.getD 3 0) = s_pm (n_pm_r0.ins.getD 3 0))
    (hcuK_sm_pm : s_sm (n_sm.ins.getD 4 0) = s_pm (n_pm_r0.ins.getD 4 0))
    (hcuQ_same : s_pm (n_pm_r0.ins.getD 3 0) = s_pm (n_pm_r1.ins.getD 3 0))
    (hcuK_same : s_pm (n_pm_r0.ins.getD 4 0) = s_pm (n_pm_r1.ins.getD 4 0))
    (hparams_sm : n_sm.params = n_pm_r0.params)
    (hparams_same : n_pm_r0.params = n_pm_r1.params)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
          (s_pm (n_pm_r0.ins.getD 3 0)) (s_pm (n_pm_r0.ins.getD 4 0))
          (n_pm_r0.params.getD 0 1) (n_pm_r0.params.getD 1 1) (n_pm_r0.params.getD 2 1)
          (n_pm_r0.params.getD 3 1)
          (decide (n_pm_r0.params.getD 4 0 ≠ 0)) (n_pm_r0.params.getD 5 0)).shape
        = [2 * Lshard, qh, vd]) :
    applyNodeRingAttn_zigzag g_sm s_sm n_sm =
      allGatherPrimDimN 0 2 0
        [applyNodeRingAttn_zigzag g_pm s_pm n_pm_r0,
         applyNodeRingAttn_zigzag g_pm s_pm n_pm_r1] := by
  -- SM full-output shape length > 0 (needed for the singleton chunk collapse).
  have hout_sm : 0 < (fw_attn_varlen (s_sm (n_sm.ins.getD 0 0)) (s_sm (n_sm.ins.getD 1 0))
      (s_sm (n_sm.ins.getD 2 0)) (s_sm (n_sm.ins.getD 3 0)) (s_sm (n_sm.ins.getD 4 0))
      (n_sm.params.getD 0 1) (n_sm.params.getD 1 1) (n_sm.params.getD 2 1) (n_sm.params.getD 3 1)
      (decide (n_sm.params.getD 4 0 ≠ 0)) (n_sm.params.getD 5 0)).shape.length := by
    rw [hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm, hfull_shape]
    simp
  -- SM side: singleton collapse, then bridge SM inputs into the PM full attention.
  rw [applyNodeRingAttn_zigzag_singleton g_sm s_sm n_sm hbuddy_sm hq_sm hk_sm hv_sm hout_sm,
      hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm]
  -- PM side: unfold each rank's node to its seq-dim chunk of the full output.
  rw [applyNodeRingAttn_zigzag_pair_eq_chunk g_pm s_pm n_pm_r0 n_pm_r0 n_pm_r1 0 hbuddy_pm hmyIdx0,
      applyNodeRingAttn_zigzag_pair_eq_chunk g_pm s_pm n_pm_r1 n_pm_r0 n_pm_r1 1 hbuddy_pm' hmyIdx1]
  -- Normalize rank-1's cu-seqlens/params to rank-0's so both chunks share one full output.
  rw [← hcuQ_same, ← hcuK_same, ← hparams_same]
  -- Reconstruct the full output from its two seq-dim chunks.
  rw [allGather0_reconstruct_chunks_3d Lshard qh vd hL hqh hvd _ hfull_shape]

/-- **Per-attention reconstruction (sliding_window).** Mirror of the zigzag
    version for `FW_attn_sliding_window` nodes (identical reconstruction shape;
    the sliding window is a local attention pattern already parameterised by
    `windowLeft`, so gather-then-attend-then-chunk reproduces per-rank shards). -/
theorem applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    (g_sm g_pm : GraphDecl) (s_sm s_pm : Store)
    (n_sm n_pm_r0 n_pm_r1 : NodeDecl)
    (Lshard qh vd : Nat)
    (hL : 0 < Lshard) (hqh : 0 < qh) (hvd : 0 < vd)
    (hbuddy_sm : ringAttnBuddies g_sm n_sm = [n_sm])
    (hbuddy_pm : ringAttnBuddies g_pm n_pm_r0 = [n_pm_r0, n_pm_r1])
    (hbuddy_pm' : ringAttnBuddies g_pm n_pm_r1 = [n_pm_r0, n_pm_r1])
    (hmyIdx0 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r0.rank)).getD 0) = 0)
    (hmyIdx1 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r1.rank)).getD 0) = 1)
    (hq_sm : 0 < (s_sm (n_sm.ins.getD 0 0)).shape.length)
    (hk_sm : 0 < (s_sm (n_sm.ins.getD 1 0)).shape.length)
    (hv_sm : 0 < (s_sm (n_sm.ins.getD 2 0)).shape.length)
    (hq_full : s_sm (n_sm.ins.getD 0 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
    (hk_full : s_sm (n_sm.ins.getD 1 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
    (hv_full : s_sm (n_sm.ins.getD 2 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
    (hcuQ_sm_pm : s_sm (n_sm.ins.getD 3 0) = s_pm (n_pm_r0.ins.getD 3 0))
    (hcuK_sm_pm : s_sm (n_sm.ins.getD 4 0) = s_pm (n_pm_r0.ins.getD 4 0))
    (hcuQ_same : s_pm (n_pm_r0.ins.getD 3 0) = s_pm (n_pm_r1.ins.getD 3 0))
    (hcuK_same : s_pm (n_pm_r0.ins.getD 4 0) = s_pm (n_pm_r1.ins.getD 4 0))
    (hparams_sm : n_sm.params = n_pm_r0.params)
    (hparams_same : n_pm_r0.params = n_pm_r1.params)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
          (s_pm (n_pm_r0.ins.getD 3 0)) (s_pm (n_pm_r0.ins.getD 4 0))
          (n_pm_r0.params.getD 0 1) (n_pm_r0.params.getD 1 1) (n_pm_r0.params.getD 2 1)
          (n_pm_r0.params.getD 3 1)
          (decide (n_pm_r0.params.getD 4 0 ≠ 0)) (n_pm_r0.params.getD 5 0)).shape
        = [2 * Lshard, qh, vd]) :
    applyNodeRingAttn_sliding_window g_sm s_sm n_sm =
      allGatherPrimDimN 0 2 0
        [applyNodeRingAttn_sliding_window g_pm s_pm n_pm_r0,
         applyNodeRingAttn_sliding_window g_pm s_pm n_pm_r1] := by
  have hout_sm : 0 < (fw_attn_varlen (s_sm (n_sm.ins.getD 0 0)) (s_sm (n_sm.ins.getD 1 0))
      (s_sm (n_sm.ins.getD 2 0)) (s_sm (n_sm.ins.getD 3 0)) (s_sm (n_sm.ins.getD 4 0))
      (n_sm.params.getD 0 1) (n_sm.params.getD 1 1) (n_sm.params.getD 2 1) (n_sm.params.getD 3 1)
      (decide (n_sm.params.getD 4 0 ≠ 0)) (n_sm.params.getD 5 0)).shape.length := by
    rw [hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm, hfull_shape]
    simp
  rw [applyNodeRingAttn_sliding_window_singleton g_sm s_sm n_sm hbuddy_sm hq_sm hk_sm hv_sm hout_sm,
      hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm]
  rw [applyNodeRingAttn_sliding_window_pair_eq_chunk g_pm s_pm n_pm_r0 n_pm_r0 n_pm_r1 0
        hbuddy_pm hmyIdx0,
      applyNodeRingAttn_sliding_window_pair_eq_chunk g_pm s_pm n_pm_r1 n_pm_r0 n_pm_r1 1
        hbuddy_pm' hmyIdx1]
  rw [← hcuQ_same, ← hcuK_same, ← hparams_same]
  rw [allGather0_reconstruct_chunks_3d Lshard qh vd hL hqh hvd _ hfull_shape]

/-! ### Deliverable 3 (Approach A): value-level per-layer residual-stream commute.

    These lemmas compose the per-op sharding-commute lemmas (from Pattern_1 and
    Phase C2a) into a single **parametric layer-step commute** at the Tensor value
    level.  They witness that one full Pattern_3 layer (structurally identical
    across all 24 layers — only the attention *kind* differs, and both kinds
    reduce to `fw_attn_varlen` at the value level via the ed31485 reconstruction
    primitives) preserves the residual-stream sharding invariant:

      residual_in_full = allGather0 [residual_in_r0, residual_in_r1]
        ⟹ residual_out_full = allGather0 [residual_out_r0, residual_out_r1].

    The layer is split into two residual sub-blocks (attention, MoE), each proven
    separately and then chained.  Everything is at the value level (no graph
    fold), so a single lemma covers both sliding_window and zigzag layers. -/

/-- Local shape helper: `fw_rms_norm` preserves shape. -/
private theorem rms_norm_shape_p3 (x w : Tensor) :
    (fw_rms_norm x w).shape = x.shape := by
  unfold fw_rms_norm
  cases hrev : x.shape.reverse with
  | nil => simp
  | cons d tl => simp [Tensor.mkShape]

/-- Local shape helper: `fw_per_head_linear` output shape `[b, hW, dW]`. -/
private theorem per_head_linear_shape_p3 (b k hW dW : Nat) (x w : Tensor)
    (hx : x.shape = [b, k]) (hw : w.shape = [hW, dW, k]) :
    (fw_per_head_linear x w).shape = [b, hW, dW] := by
  unfold fw_per_head_linear
  rw [hx, hw]
  simp [Tensor.mkShape]

/-- **Input bridge (Q/K path).** The residual-stream shard-gather commutes through
    the pre-attention `rms_norm → per_head_linear → rotary_apply` chain: the full
    (SM) rotary-applied query (or key) equals the all-gather of the two per-rank
    (PM) rotary-applied shards.  Parametric in the number of heads `nh` so it
    serves both Q (`nh = qh`) and K (`nh = kvh`). -/
theorem norm_perhead_rotary_gather_commute
    (r0 r1 wn wp cs pos0 pos1 : Tensor) (Lshard nh dW : Nat)
    (hL : 0 < Lshard) (hnh : 0 < nh) (hdW : 0 < dW)
    (hr0 : r0.shape = [Lshard, 1024]) (hr1 : r1.shape = [Lshard, 1024])
    (hwn : wn.shape = [1024])
    (hwp : wp.shape = [nh, dW, 1024])
    (hpos0 : pos0.shape = [Lshard, 1]) (hpos1 : pos1.shape = [Lshard, 1]) :
    fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
        (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wp) nh
      = allGatherPrimDimN 0 2 0
          [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wp) nh,
           fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wp) nh] := by
  have hrms0 : (fw_rms_norm r0 wn).shape = [Lshard, 1024] := (rms_norm_shape_p3 r0 wn).trans hr0
  have hrms1 : (fw_rms_norm r1 wn).shape = [Lshard, 1024] := (rms_norm_shape_p3 r1 wn).trans hr1
  have hph0 : (fw_per_head_linear (fw_rms_norm r0 wn) wp).shape = [Lshard, nh, dW] :=
    per_head_linear_shape_p3 Lshard 1024 nh dW _ wp hrms0 hwp
  have hph1 : (fw_per_head_linear (fw_rms_norm r1 wn) wp).shape = [Lshard, nh, dW] :=
    per_head_linear_shape_p3 Lshard 1024 nh dW _ wp hrms1 hwp
  rw [fw_rms_norm_allGather0_commute_2 r0 r1 wn Lshard 1024 hL (by norm_num) hr0 hr1]
  rw [fw_per_head_mix_precision_linear_allGather0_commute_2
        (fw_rms_norm r0 wn) (fw_rms_norm r1 wn) wp Lshard 1024 nh dW
        hL (by norm_num) hnh hdW hrms0 hrms1 hwp]
  rw [fw_rotary_apply_allGather0_commute_2
        (fw_per_head_linear (fw_rms_norm r0 wn) wp) (fw_per_head_linear (fw_rms_norm r1 wn) wp)
        pos0 pos1 cs Lshard nh dW hL hnh hdW hph0 hph1 hpos0 hpos1]

/-- **Input bridge (V path).** The value projection `rms_norm → per_head_linear`
    (no rotary) commutes with the residual-stream shard-gather. -/
theorem norm_perhead_gather_commute
    (r0 r1 wn wp : Tensor) (Lshard nh dW : Nat)
    (hL : 0 < Lshard) (hnh : 0 < nh) (hdW : 0 < dW)
    (hr0 : r0.shape = [Lshard, 1024]) (hr1 : r1.shape = [Lshard, 1024])
    (hwn : wn.shape = [1024])
    (hwp : wp.shape = [nh, dW, 1024]) :
    fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wp
      = allGatherPrimDimN 0 2 0
          [fw_per_head_linear (fw_rms_norm r0 wn) wp,
           fw_per_head_linear (fw_rms_norm r1 wn) wp] := by
  have hrms0 : (fw_rms_norm r0 wn).shape = [Lshard, 1024] := (rms_norm_shape_p3 r0 wn).trans hr0
  have hrms1 : (fw_rms_norm r1 wn).shape = [Lshard, 1024] := (rms_norm_shape_p3 r1 wn).trans hr1
  rw [fw_rms_norm_allGather0_commute_2 r0 r1 wn Lshard 1024 hL (by norm_num) hr0 hr1]
  rw [fw_per_head_mix_precision_linear_allGather0_commute_2
        (fw_rms_norm r0 wn) (fw_rms_norm r1 wn) wp Lshard 1024 nh dW
        hL (by norm_num) hnh hdW hrms0 hrms1 hwp]

/-- Local shape helper: `fw_view` yields exactly its target shape. -/
private theorem view_shape_p3 (s : Shape) (x : Tensor) : (fw_view s x).shape = s := by
  unfold fw_view; simp [Tensor.mkShape]

/-- Local value helper: `fw_view` is buffer-preserving on in-bounds indices. -/
private theorem valAt_fw_view (s : Shape) (x : Tensor) (idx : Nat) (h : idx < prodShape s) :
    valAt (fw_view s x) idx = valAt x idx := by
  have hb : idx < prodShape (fw_view s x).shape := by rw [view_shape_p3]; exact h
  rw [valAt_of_lt _ _ hb]
  unfold fw_view; simp [Tensor.mkShape]

/-- **Reshape/flatten bridge.** Flattening the last two dims of a dim-0-gathered
    `[2L, A, B]` tensor to `[2L, A*B]` commutes with the gather: it equals the
    gather of the per-rank `[L, A*B]` flattenings.  This bridges the attention
    output (3-D `[2L, qh, vd]`) into the 2-D input the output projection expects. -/
theorem view_flatten_gather_2 (L A B : Nat) (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (c0 c1 : Tensor) (hc0 : c0.shape = [L, A, B]) (hc1 : c1.shape = [L, A, B]) :
    fw_view [2 * L, A * B] (allGatherPrimDimN 0 2 0 [c0, c1])
      = allGatherPrimDimN 0 2 0 [fw_view [L, A * B] c0, fw_view [L, A * B] c1] := by
  have hAB : 0 < A * B := Nat.mul_pos hA hB
  have hhead3 : (([c0, c1].head?.map (fun t => t.shape)).getD []) = [L, A, B] := by simp [hc0]
  have hG3 : (allGatherPrimDimN 0 2 0 [c0, c1]).shape = [2 * L, A, B] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, A, B] hhead3]
    simp only [List.set, List.getD_cons_zero]; rw [Nat.mul_comm L 2]
  have hv0 : (fw_view [L, A * B] c0).shape = [L, A * B] := view_shape_p3 _ _
  have hv1 : (fw_view [L, A * B] c1).shape = [L, A * B] := view_shape_p3 _ _
  have hheadv : (([fw_view [L, A * B] c0, fw_view [L, A * B] c1].head?.map
      (fun t => t.shape)).getD []) = [L, A * B] := by simp [hv0]
  have hGv : (allGatherPrimDimN 0 2 0 [fw_view [L, A * B] c0, fw_view [L, A * B] c1]).shape
      = [2 * L, A * B] := by
    rw [allGatherPrimDimN_shape 0 2 _ [L, A * B] hheadv]
    simp only [List.set, List.getD_cons_zero]; rw [Nat.mul_comm L 2]
  apply Tensor.ext
  · rw [hGv, view_shape_p3]
  · intro idx hidx
    rw [view_shape_p3] at hidx
    have hprod : prodShape [2 * L, A * B] = 2 * L * (A * B) := by simp [prodShape, Nat.mul_assoc]
    rw [hprod] at hidx
    set inner := idx % B with hinner_def
    set col := (idx / B) % A with hcol_def
    set fullrow := idx / B / A with hfullrow_def
    have hinner : inner < B := by rw [hinner_def]; exact Nat.mod_lt _ hB
    have hcol : col < A := by rw [hcol_def]; exact Nat.mod_lt _ hA
    have hfullrow_lt : fullrow < 2 * L := by
      rw [hfullrow_def]
      apply Nat.div_lt_of_lt_mul; apply Nat.div_lt_of_lt_mul
      calc idx < 2 * L * (A * B) := hidx
        _ = B * (A * (2 * L)) := by ring
    set r := fullrow / L with hr_def
    set i := fullrow % L with hi_def
    have hi : i < L := by rw [hi_def]; exact Nat.mod_lt _ hL
    have hr : r < 2 := by rw [hr_def]; apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact hfullrow_lt
    have hfullrow_split : fullrow = r * L + i := by
      rw [hr_def, hi_def, Nat.mul_comm]; exact (Nat.div_add_mod fullrow L).symm
    set j := col * B + inner with hj_def
    have hj_lt : j < A * B := by
      rw [hj_def]
      calc col * B + inner < col * B + B := by omega
        _ = (col + 1) * B := by ring
        _ ≤ A * B := Nat.mul_le_mul_right _ (by omega)
    have hidx_3d : idx = ((r * L + i) * A + col) * B + inner := by
      rw [← hfullrow_split, hinner_def, hcol_def, hfullrow_def]
      have e1 : (idx / B / A) * A + (idx / B) % A = idx / B := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod (idx / B) A
      rw [e1, Nat.mul_comm (idx / B) B]; exact (Nat.div_add_mod idx B).symm
    have hidx_2d : idx = (r * L + i) * (A * B) + j := by
      rw [hidx_3d, hj_def]; ring
    have hLval : valAt (fw_view [2 * L, A * B] (allGatherPrimDimN 0 2 0 [c0, c1])) idx
        = valAt ([c0, c1].getD r (zeroTensor [L, A, B])) ((i * A + col) * B + inner) := by
      rw [valAt_fw_view _ _ _ (by rw [hprod]; exact hidx)]
      rw [hidx_3d]
      exact gather0_3d_valAt 2 L A B _ (by omega) hL hA hB hhead3 r hr i hi col hcol inner hinner
    have hRval : valAt (allGatherPrimDimN 0 2 0 [fw_view [L, A * B] c0, fw_view [L, A * B] c1]) idx
        = valAt ([fw_view [L, A * B] c0, fw_view [L, A * B] c1].getD r (zeroTensor [L, A * B]))
            (i * (A * B) + j) := by
      rw [hidx_2d]
      exact allGatherPrimDimN0_valAt 2 L (A * B) _ (by omega) hL hAB hheadv
          (by intro r' hr'; interval_cases r' <;> simp [List.getD, hv0, hv1]) r hr i hi j hj_lt
    rw [hLval, hRval]
    have hgetD3 : [c0, c1].getD r (zeroTensor [L, A, B]) = if r = 0 then c0 else c1 := by
      interval_cases r <;> rfl
    have hgetDv : [fw_view [L, A * B] c0, fw_view [L, A * B] c1].getD r (zeroTensor [L, A * B])
        = if r = 0 then fw_view [L, A * B] c0 else fw_view [L, A * B] c1 := by
      interval_cases r <;> rfl
    rw [hgetD3, hgetDv]
    have hlocal_eq : (i * A + col) * B + inner = i * (A * B) + j := by rw [hj_def]; ring
    rw [hlocal_eq]
    have hview_val : ∀ c : Tensor,
        valAt (fw_view [L, A * B] c) (i * (A * B) + j) = valAt c (i * (A * B) + j) := by
      intro c
      apply valAt_fw_view
      have hp : prodShape [L, A * B] = L * (A * B) := by simp [prodShape, Nat.mul_assoc]
      rw [hp]
      calc i * (A * B) + j < i * (A * B) + A * B := by omega
        _ = (i + 1) * (A * B) := by ring
        _ ≤ L * (A * B) := Nat.mul_le_mul_right _ (by omega)
    clear_value r
    rcases (by omega : r = 0 ∨ r = 1) with hr0' | hr1'
    · simp only [hr0', if_true]; rw [hview_val c0]
    · simp only [hr1', if_false, Nat.one_ne_zero]; rw [hview_val c1]

/-- Local shape helper: 2-D `fw_linear` output shape `[b, o]`. -/
private theorem linear_shape_p3 (b i o : Nat) (x w : Tensor)
    (hx : x.shape = [b, i]) (hw : w.shape = [o, i]) :
    (fw_linear x w).shape = [b, o] := by
  unfold fw_linear; rw [hx, hw]; simp [Tensor.mkShape]

/-- **Reshape/flatten bridge (chunk form).** Flattening `[2L, A, B] → [2L, A*B]` of
    a tensor `T` equals the dim-0 gather of the per-rank flattened seq-chunks of
    `T`.  Direct corollary of `view_flatten_gather_2` composed with the chunk
    reconstruction (`allGather0_reconstruct_chunks_3d`). -/
theorem view_flatten_chunks (L A B : Nat) (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (T : Tensor) (hT : T.shape = [2 * L, A, B]) :
    fw_view [2 * L, A * B] T
      = allGatherPrimDimN 0 2 0
          [fw_view [L, A * B] (chunkPrimDimN 0 2 0 T),
           fw_view [L, A * B] (chunkPrimDimN 0 2 1 T)] := by
  have hchunk : ∀ r, (chunkPrimDimN 0 2 r T).shape = [L, A, B] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r T [2 * L, A, B] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]; rw [show 2 * L / 2 = L from by omega]
  rw [show fw_view [2 * L, A * B] T
        = fw_view [2 * L, A * B]
            (allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T])
      from by rw [allGather0_reconstruct_chunks_3d L A B hL hA hB T hT]]
  exact view_flatten_gather_2 L A B hL hA hB
    (chunkPrimDimN 0 2 0 T) (chunkPrimDimN 0 2 1 T) (hchunk 0) (hchunk 1)

/-- **Output bridge (attention).** The post-attention output projection and
    residual add commute with the residual-stream shard-gather: given the full
    attention output `af : [4096, qh, vd]` (whose per-rank ring shards are its two
    seq-chunks), the full residual output equals the dim-0 gather of the two
    per-rank residual outputs.  Chains `view_flatten_chunks`,
    `fw_mix_precision_linear_allGather0_commute_2`, and the `[2048,1024]` residual
    add commute. -/
theorem attn_output_residual_commute
    (r0 r1 wo af : Tensor) (qh vd : Nat)
    (hqh : 0 < qh) (hvd : 0 < vd)
    (hr0 : r0.shape = [2048, 1024]) (hr1 : r1.shape = [2048, 1024])
    (hwo : wo.shape = [1024, qh * vd])
    (haf : af.shape = [2 * 2048, qh, vd]) :
    elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd] af) wo)
      = allGatherPrimDimN 0 2 0
          [elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 af)) wo),
           elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 af)) wo)] := by
  have hqhvd : 0 < qh * vd := Nat.mul_pos hqh hvd
  have hv0 : (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 af)).shape = [2048, qh * vd] :=
    view_shape_p3 _ _
  have hv1 : (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 af)).shape = [2048, qh * vd] :=
    view_shape_p3 _ _
  have hproj0 : (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 af)) wo).shape
      = [2048, 1024] := linear_shape_p3 2048 (qh * vd) 1024 _ wo hv0 hwo
  have hproj1 : (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 af)) wo).shape
      = [2048, 1024] := linear_shape_p3 2048 (qh * vd) 1024 _ wo hv1 hwo
  rw [view_flatten_chunks 2048 qh vd (by norm_num) hqh hvd af haf]
  rw [fw_mix_precision_linear_allGather0_commute_2
        (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 af))
        (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 af)) wo
        2048 (qh * vd) 1024 (by norm_num) hqhvd (by norm_num) hv0 hv1 hwo]
  rw [fw_add_allGather0_commute_2_2048_1024 r0 r1
        (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0 af)) wo)
        (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1 af)) wo)
        hr0 hr1 hproj0 hproj1]

/-- **Layer attention sub-block residual commute (Approach A, value level).**

    Ties the input bridges (`norm_perhead_rotary_gather_commute` for Q/K,
    `norm_perhead_gather_commute` for V) to the output bridge
    (`attn_output_residual_commute`).  The left-hand side is the SM (full,
    numRanks=1) attention sub-block computed over the gathered residual stream;
    the right-hand side is the dim-0 gather of the two PM (numRanks=2) per-rank
    sub-blocks, whose ring-attention output shard is the corresponding seq-chunk
    of the full attention.  Covers both sliding_window and zigzag layers (both
    reduce to `fw_attn_varlen`).  `qh * vd = 1024` is the model dimension. -/
theorem layer_attn_block_commute
    (r0 r1 wn wq wk wv cs pos0 pos1 wo cuQ cuK : Tensor)
    (qh kh d vd : Nat) (causal : Bool) (windowLeft : Nat)
    (hqh : 0 < qh) (hkh : 0 < kh) (hd : 0 < d) (hvd : 0 < vd)
    (hr0 : r0.shape = [2048, 1024]) (hr1 : r1.shape = [2048, 1024])
    (hwn : wn.shape = [1024])
    (hwq : wq.shape = [qh, d, 1024]) (hwk : wk.shape = [kh, d, 1024])
    (hwv : wv.shape = [kh, vd, 1024])
    (hpos0 : pos0.shape = [2048, 1]) (hpos1 : pos1.shape = [2048, 1])
    (hwo : wo.shape = [1024, qh * vd])
    (haf : (fw_attn_varlen
              (allGatherPrimDimN 0 2 0
                 [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wq) qh,
                  fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wq) qh])
              (allGatherPrimDimN 0 2 0
                 [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wk) kh,
                  fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wk) kh])
              (allGatherPrimDimN 0 2 0
                 [fw_per_head_linear (fw_rms_norm r0 wn) wv,
                  fw_per_head_linear (fw_rms_norm r1 wn) wv])
              cuQ cuK qh kh d vd causal windowLeft).shape = [2 * 2048, qh, vd]) :
    elemwiseAdd (allGatherPrimDimN 0 2 0 [r0, r1])
        (fw_linear (fw_view [2 * 2048, qh * vd]
          (fw_attn_varlen
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wq) qh)
            (fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pos0, pos1])
              (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wk) kh)
            (fw_per_head_linear (fw_rms_norm (allGatherPrimDimN 0 2 0 [r0, r1]) wn) wv)
            cuQ cuK qh kh d vd causal windowLeft)) wo)
      = allGatherPrimDimN 0 2 0
          [elemwiseAdd r0 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 0
              (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn) wv,
                    fw_per_head_linear (fw_rms_norm r1 wn) wv])
                cuQ cuK qh kh d vd causal windowLeft))) wo),
           elemwiseAdd r1 (fw_linear (fw_view [2048, qh * vd] (chunkPrimDimN 0 2 1
              (fw_attn_varlen
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wq) qh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wq) qh])
                (allGatherPrimDimN 0 2 0
                   [fw_rotary_apply cs pos0 (fw_per_head_linear (fw_rms_norm r0 wn) wk) kh,
                    fw_rotary_apply cs pos1 (fw_per_head_linear (fw_rms_norm r1 wn) wk) kh])
                (allGatherPrimDimN 0 2 0
                   [fw_per_head_linear (fw_rms_norm r0 wn) wv,
                    fw_per_head_linear (fw_rms_norm r1 wn) wv])
                cuQ cuK qh kh d vd causal windowLeft))) wo)] := by
  rw [norm_perhead_rotary_gather_commute r0 r1 wn wq cs pos0 pos1 2048 qh d
        (by norm_num) hqh hd hr0 hr1 hwn hwq hpos0 hpos1]
  rw [norm_perhead_rotary_gather_commute r0 r1 wn wk cs pos0 pos1 2048 kh d
        (by norm_num) hkh hd hr0 hr1 hwn hwk hpos0 hpos1]
  rw [norm_perhead_gather_commute r0 r1 wn wv 2048 kh vd
        (by norm_num) hkh hvd hr0 hr1 hwn hwv]
  exact attn_output_residual_commute r0 r1 wo _ qh vd hqh hvd hr0 hr1 hwo haf

end TrainVerify.Denote.GeneratedPatterns
