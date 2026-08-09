import denote.yoco_goals.Goal_1
import denote.yoco_goals.CanonicalKVCacheOrdinaryOps
import denote.ChunkGatherDim0
import denote.DenoteMoE
import denote.MultirefGeneral
import denote.GraphGears
import denote.Gather2Rel

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem l11o_gather0_3d_valAt
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
private theorem l11o_chunk0_3d_valAt
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
theorem l11o_allGather0_reconstruct_chunks_3d
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
    rw [l11o_gather0_3d_valAt 2 Lshard d1 d2 _ (by omega) hL hd1 hd2 hhead r hr row hrow col hcol inner hinner]
    have hgetD : [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].getD r (zeroTensor [Lshard, d1, d2])
        = chunkPrimDimN 0 2 r T := by
      interval_cases r <;> rfl
    rw [hgetD]
    exact l11o_chunk0_3d_valAt Lshard d1 d2 hL hd1 hd2 T hT r hr row hrow col hcol inner hinner

theorem l11o_node_core (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (outTid : Tid)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (_hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      applyNodeDistributedFaithful g
        ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) node outTid :=
  denoteGraphDistributedFaithful_node_core g init k node outTid hk hnode hdrop_nil hdrop

theorem l11o_prefix_read (g : GraphDecl) (init : Store) (k : Nat) (tid : Tid)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, tid ∉ n.outs) :
    ((g.nodes.take k).foldl (applyNodeDistributedFaithful g) init) tid =
      denoteGraphDistributedFaithful g init tid :=
  denoteGraphDistributedFaithful_prefix_read g init k tid hpre_nil hpre

theorem l11o_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid = opfun (s inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid = opfun (denoteGraphDistributedFaithful g init inTid) := by
  rw [l11o_node_core g init k node outTid hk hnode hmoe hdrop_nil hdrop,
    happly, l11o_prefix_read g init k inTid hpre_nil hpre]

theorem l11o_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (in1 in2 outTid : Tid) (opfun : Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid = opfun (s in1) (s in2))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in1) (denoteGraphDistributedFaithful g init in2) := by
  rw [l11o_node_core g init k node outTid hk hnode hmoe hdrop_nil hdrop,
    happly, l11o_prefix_read g init k in1 hpre_nil hpre1,
    l11o_prefix_read g init k in2 hpre_nil hpre2]

theorem l11o_reduce4 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (in0 in1 in2 in3 outTid : Tid)
    (opfun : Tensor → Tensor → Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : ∀ s, applyNodeDistributedFaithful g s node outTid =
      opfun (s in0) (s in1) (s in2) (s in3))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre0 : ∀ n ∈ g.nodes.drop k, in0 ∉ n.outs)
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs)
    (hpre3 : ∀ n ∈ g.nodes.drop k, in3 ∉ n.outs) :
    denoteGraphDistributedFaithful g init outTid =
      opfun (denoteGraphDistributedFaithful g init in0) (denoteGraphDistributedFaithful g init in1)
        (denoteGraphDistributedFaithful g init in2) (denoteGraphDistributedFaithful g init in3) := by
  rw [l11o_node_core g init k node outTid hk hnode hmoe hdrop_nil hdrop,
    happly, l11o_prefix_read g init k in0 hpre_nil hpre0,
    l11o_prefix_read g init k in1 hpre_nil hpre1,
    l11o_prefix_read g init k in2 hpre_nil hpre2,
    l11o_prefix_read g init k in3 hpre_nil hpre3]

theorem l11o_init_value (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ goal_1_full_initGoals) (W : Tid)
    (htp : gW.tps = [{ rank := 0, tid := W }]) (hgd : gW.gatherDim = 0)
    (hrep : gW.replicated = false) (hts : gW.ts = W)
    (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM W = denoteGraphDistributedFaithful pm_goal_1 initPM W := by
  have hg := hInit gW hgW
  unfold InitGoalHolds at hg
  have hv := hg.2.2
  rw [reconstructForGoal_of_not_replicated gW pm_goal_1.numRanks _ hrep, htp, hts, hgd] at hv
  simp only [List.map, reconstructWithDim] at hv
  rw [denoteGraphDistributedFaithful,
    foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM W (by native_decide) hsm,
    denoteGraphDistributedFaithful,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes initPM W (by native_decide) hpm]
  exact hv

theorem l11o_init_shape (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ goal_1_full_initGoals) (W : Tid) (sh : Shape)
    (htsShape : gW.tsShape = sh) (hts : gW.ts = W)
    (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM W).shape = sh := by
  have hg := hInit gW hgW
  unfold InitGoalHolds at hg
  rw [denoteGraphDistributedFaithful,
    foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes initSM W (by native_decide) hsm]
  rw [← hts, ← htsShape]
  exact hg.1

theorem l11o_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_rms_norm", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o =
      fw_rms_norm (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init w) :=
  l11o_reduce2 g init k _ x w o fw_rms_norm hk hn (by simp)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      unfold applyNodeDistributed
      rw [if_neg (by simp)]
      exact applyNode_fw_rms_norm_out_1p g st r x w o)
    hdn hdw hpn hpx hpw

theorem l11o_apply_multiref_at (g : GraphDecl) (s : Store) (rank xTid : Nat)
    (outs : List Tid) (n : Nat) (hn : outs.length = n) (outTid : Tid)
    (hmem : outTid ∈ outs) :
    applyNodeDistributedFaithful g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid], outs := outs, params := [n] }
      outTid = s xTid := by
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by simp) (by simp) (by simp)]
  unfold applyNodeDistributed
  rw [if_neg (by simp)]
  exact applyNode_fw_multiref_at g s rank xTid outs n hn outTid hmem

theorem l11o_apply_per_head (g : GraphDecl) (s : Store) (rank x w o : Nat) :
    applyNodeDistributedFaithful g s
      { rank := rank, op := "OpName.FW_per_head_mix_precision_linear",
        ins := [x, w], outs := [o] } o = fw_per_head_linear (s x) (s w) := by
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by simp) (by simp) (by simp)]
  unfold applyNodeDistributed
  rw [if_neg (by simp), applyNodeRingAttn_eq_applyNode_of_not_ring g s _
    (by simp) (by simp)]
  unfold applyNode
  rw [show ([x, w] : List Tid).map s = [s x, s w] from rfl,
    show evalOp g.numRanks rank "OpName.FW_per_head_mix_precision_linear" [] [s x, s w] =
      [fw_per_head_linear (s x) (s w)] from rfl]
  change storeSet s [(o, fw_per_head_linear (s x) (s w))] o = _
  unfold storeSet
  simp [List.find?]

theorem l11o_per_head (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_per_head_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributedFaithful g init o =
      fw_per_head_linear (denoteGraphDistributedFaithful g init x) (denoteGraphDistributedFaithful g init w) :=
  l11o_reduce2 g init k _ x w o fw_per_head_linear hk hn (by simp)
    (fun st => l11o_apply_per_head g st r x w o)
    hdn hdw hpn hpx hpw

theorem l11o_per_head_shape (x w : Tensor) (b k hW dW : Nat)
    (hx : x.shape = [b, k]) (hw : w.shape = [hW, dW, k]) :
    (fw_per_head_linear x w).shape = [b, hW, dW] := by
  unfold fw_per_head_linear
  rw [hx, hw]
  rfl

theorem l11o_allgather2 (g : GraphDecl) (init : Store) (k r x0 x1 o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.AllGatherPrim", ins := [x0, x1], outs := [o], params := [0] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hp0 : ∀ n ∈ g.nodes.drop k, x0 ∉ n.outs)
    (hp1 : ∀ n ∈ g.nodes.drop k, x1 ∉ n.outs) :
    denoteGraphDistributedFaithful g init o = allGatherPrimDimN 0 g.numRanks r
      [denoteGraphDistributedFaithful g init x0, denoteGraphDistributedFaithful g init x1] :=
  l11o_reduce2 g init k _ x0 x1 o (fun a b => allGatherPrimDimN 0 g.numRanks r [a, b])
    hk hn (by simp)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      unfold applyNodeDistributed
      rw [if_neg (by simp), applyNodeRingAttn_eq_applyNode_of_not_ring g st _
        (by simp) (by simp)]
      exact applyNode_allGatherPrimDimN_out g st r [x0, x1] o 0)
    hdn hdw hpn hp0 hp1

theorem l11o_chunk (g : GraphDecl) (init : Store) (k r x o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.ChunkPrim", ins := [x], outs := [o], params := [0] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs) :
    denoteGraphDistributedFaithful g init o =
      chunkPrimDimN 0 g.numRanks r (denoteGraphDistributedFaithful g init x) :=
  l11o_reduce1 g init k _ x o (fun a => chunkPrimDimN 0 g.numRanks r a)
    hk hn (by simp)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      unfold applyNodeDistributed
      rw [if_neg (by simp), applyNodeRingAttn_eq_applyNode_of_not_ring g st _
        (by simp) (by simp)]
      exact applyNode_chunkPrimDimN_out g st r x o 0)
    hdn hdw hpn hpx

theorem l11o_rotary_pos_congr (cs p p' x : Tensor) (L nh d : Nat)
    (hx : x.shape = [L, nh, d])
    (hpos : ∀ l, l < L → valAt p l = valAt p' l) :
    fw_rotary_apply cs p x nh = fw_rotary_apply cs p' x nh := by
  rw [fw_rotary_apply_reduce_c2a cs p x L nh d hx,
      fw_rotary_apply_reduce_c2a cs p' x L nh d hx]
  apply Tensor.ext
  · simp [Tensor.mkShape]
  · intro outIdx houtIdx
    have hprod : prodShape [L, nh, d] = L * nh * d := by simp [prodShape]
    have hbound : outIdx < L * nh * d := by
      have ht := houtIdx
      simp only [Tensor.mkShape] at ht
      rw [hprod] at ht
      exact ht
    have hd2 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hbound)
    have hnh2 : 0 < nh := Nat.pos_of_ne_zero (by rintro rfl; simp at hbound)
    have hl : outIdx / d / nh < L := by
      rw [Nat.div_lt_iff_lt_mul hnh2, Nat.div_lt_iff_lt_mul hd2]
      simpa [Nat.mul_assoc] using hbound
    rw [valAt_of_lt _ _ (by
          rw [show (Tensor.mkShape [L, nh, d] _).shape = [L, nh, d] from rfl, hprod]
          exact hbound),
        valAt_of_lt _ _ (by
          rw [show (Tensor.mkShape [L, nh, d] _).shape = [L, nh, d] from rfl, hprod]
          exact hbound)]
    simp only [Tensor.mkShape]
    rw [hpos _ hl]

theorem l11o_chunk0_2_1d_valAt (P : Tensor) (L r i : Nat)
    (hP : P.shape = [2 * L]) (hr : r < 2) (hi : i < L) :
    valAt (chunkPrimDimN 0 2 r P) i = valAt P (r * L + i) := by
  have hLpos : 0 < L := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hshard : (2 * L) / 2 = L := by omega
  have hresult_shape : (chunkPrimDimN 0 2 r P).shape = [L] := by
    rw [chunkPrimDimN_shape 0 2 r _ _ hP (by omega)]
    simp [List.set, List.getD, hshard]
  have hprod : i < prodShape (chunkPrimDimN 0 2 r P).shape := by
    rw [hresult_shape]
    simpa [prodShape] using hi
  rw [valAt_of_lt _ _ hprod]
  have hrm : r % 2 = r := Nat.mod_eq_of_lt hr
  have h0 : i / L = 0 := Nat.div_eq_of_lt hi
  have h1 : i % L = i := Nat.mod_eq_of_lt hi
  have hLne : L ≠ 0 := Nat.pos_iff_ne_zero.mp hLpos
  simp only [chunkPrimDimN, Tensor.mkShape, hP, List.getD, List.getElem?_cons_zero,
    Option.getD_some, List.drop, List.foldl, Nat.mod_one, Nat.mul_one,
    Nat.add_zero, Nat.div_one, Nat.zero_add, hshard, hrm, h0, h1, hLne,
    if_false, Nat.reduceEqDiff]
  congr 1
  ring

theorem l11o_rotary_allGather0_1d
    (cs P a b : Tensor) (L nh d : Nat)
    (hL : 0 < L) (hnh : 0 < nh) (hd : 0 < d)
    (hP : P.shape = [2 * L])
    (ha : a.shape = [L, nh, d]) (hb : b.shape = [L, nh, d]) :
    fw_rotary_apply cs P (allGatherPrimDimN 0 2 0 [a, b]) nh =
      allGatherPrimDimN 0 2 0
        [fw_rotary_apply cs (chunkPrimDimN 0 2 0 P) a nh,
         fw_rotary_apply cs (chunkPrimDimN 0 2 1 P) b nh] := by
  set pa := Tensor.mkShape [L, 1] (fun idx => valAt (chunkPrimDimN 0 2 0 P) idx.1)
  set pb := Tensor.mkShape [L, 1] (fun idx => valAt (chunkPrimDimN 0 2 1 P) idx.1)
  have hpa_sh : pa.shape = [L, 1] := rfl
  have hpb_sh : pb.shape = [L, 1] := rfl
  have hpa_val : ∀ i, i < L → valAt pa i = valAt (chunkPrimDimN 0 2 0 P) i := by
    intro i hi
    have hb : i < prodShape ([L, 1] : Shape) := by simp [prodShape]; omega
    show valAt (Tensor.mkShape [L, 1] (fun idx =>
      valAt (chunkPrimDimN 0 2 0 P) idx.1)) i = _
    rw [valAt_of_lt _ i hb]
    rfl
  have hpb_val : ∀ i, i < L → valAt pb i = valAt (chunkPrimDimN 0 2 1 P) i := by
    intro i hi
    have hb : i < prodShape ([L, 1] : Shape) := by simp [prodShape]; omega
    show valAt (Tensor.mkShape [L, 1] (fun idx =>
      valAt (chunkPrimDimN 0 2 1 P) idx.1)) i = _
    rw [valAt_of_lt _ i hb]
    rfl
  have hrank0 : fw_rotary_apply cs pa a nh =
      fw_rotary_apply cs (chunkPrimDimN 0 2 0 P) a nh :=
    l11o_rotary_pos_congr cs pa _ a L nh d ha hpa_val
  have hrank1 : fw_rotary_apply cs pb b nh =
      fw_rotary_apply cs (chunkPrimDimN 0 2 1 P) b nh :=
    l11o_rotary_pos_congr cs pb _ b L nh d hb hpb_val
  have hab_shape : (allGatherPrimDimN 0 2 0 [a, b]).shape = [2 * L, nh, d] := by
    rw [allGatherPrimDimN_shape 0 2 [a, b] [L, nh, d] (by simp [ha])]
    simp only [List.set, List.getD_cons_zero]
    rw [Nat.mul_comm L 2]
  have hgather_pos : ∀ l, l < 2 * L →
      valAt P l = valAt (allGatherPrimDimN 0 2 0 [pa, pb]) l := by
    intro l hl
    obtain ⟨r, i, hr, hi, rfl⟩ : ∃ r i, r < 2 ∧ i < L ∧ l = r * L + i := by
      refine ⟨l / L, l % L, ?_, Nat.mod_lt _ hL, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hL]
        omega
      · rw [Nat.mul_comm]
        exact (Nat.div_add_mod l L).symm
    have hgv := allGatherPrimDimN0_valAt 2 L 1 [pa, pb] (by omega) hL (by omega)
      (by simp [hpa_sh])
      (by intro rr hrr; rcases (by omega : rr = 0 ∨ rr = 1) with h | h <;>
        subst h <;> simp [List.getD, hpa_sh, hpb_sh]) r hr i hi 0 (by omega)
    simp only [Nat.mul_one, Nat.add_zero] at hgv
    rw [hgv]
    rcases (by omega : r = 0 ∨ r = 1) with h | h <;> subst h
    · simp only [List.getD_cons_zero]
      rw [hpa_val i hi, l11o_chunk0_2_1d_valAt P L 0 i hP (by omega) hi]
    · simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      rw [hpb_val i hi, l11o_chunk0_2_1d_valAt P L 1 i hP (by omega) hi]
  have hLHS : fw_rotary_apply cs P (allGatherPrimDimN 0 2 0 [a, b]) nh =
      fw_rotary_apply cs (allGatherPrimDimN 0 2 0 [pa, pb])
        (allGatherPrimDimN 0 2 0 [a, b]) nh :=
    l11o_rotary_pos_congr cs P _ _ (2 * L) nh d hab_shape hgather_pos
  rw [hLHS, fw_rotary_apply_allGather0_commute_2 a b pa pb cs L nh d
      hL hnh hd ha hb hpa_sh hpb_sh, hrank0, hrank1]

/-- L11 ordinary V relation, derived only from the preceding output boundary and init weights. -/
theorem l11o_v5548_rel_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5540)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9558) (denoteGraphDistributedFaithful pm_goal_1 initPM 9559)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5548)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9586) (denoteGraphDistributedFaithful pm_goal_1 initPM 9587)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l11o_reduce1 sm_goal_1 initSM 431
    { rank := 0, op := "OpName.FW_multiref", ins := [5540], outs := [8316, 8320], params := [2] }
    5540 8316 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm_goal_1 st 0 5540 [8316, 8320] 2 rfl 8316 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l11o_reduce1 pm_goal_1 initPM 956
    { rank := 0, op := "OpName.FW_multiref", ins := [9558], outs := [15790, 15794], params := [2] }
    9558 15790 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm_goal_1 st 0 9558 [15790, 15794] 2 rfl 15790 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l11o_reduce1 pm_goal_1 initPM 957
    { rank := 1, op := "OpName.FW_multiref", ins := [9559], outs := [15798, 15802], params := [2] }
    9559 15798 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm_goal_1 st 1 9559 [15798, 15802] 2 rfl 15798 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l11o_init_value initSM initPM hInit initGoal_5541
    (by native_decide) 5541 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l11o_rms sm_goal_1 initSM 432 0 8316 5541 5542
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11o_rms pm_goal_1 initPM 958 0 15790 5541 9562
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11o_rms pm_goal_1 initPM 959 1 15798 5541 9563
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5542)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9562) (denoteGraphDistributedFaithful pm_goal_1 initPM 9563)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)
  have vs := l11o_reduce1 sm_goal_1 initSM 433
    { rank := 0, op := "OpName.FW_multiref", ins := [5542], outs := [8325, 8329, 8333], params := [3] }
    5542 8333 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm_goal_1 st 0 5542 [8325, 8329, 8333] 3 rfl 8333 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v0 := l11o_reduce1 pm_goal_1 initPM 960
    { rank := 0, op := "OpName.FW_multiref", ins := [9562], outs := [15380, 13744, 13752], params := [3] }
    9562 13752 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm_goal_1 st 0 9562 [15380, 13744, 13752] 3 rfl 13752 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v1 := l11o_reduce1 pm_goal_1 initPM 961
    { rank := 1, op := "OpName.FW_multiref", ins := [9563], outs := [15382, 13745, 13753], params := [3] }
    9563 13753 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm_goal_1 st 1 9563 [15382, 13745, 13753] 3 rfl 13753 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at vs v0 v1
  have hw := l11o_init_value initSM initPM hInit initGoal_5547
    (by native_decide) 5547 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l11o_init_shape initSM initPM hInit initGoal_5547
    (by native_decide) 5547 [4, 64, 1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5547).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have ps := l11o_per_head sm_goal_1 initSM 436 0 8333 5547 5548
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p0 := l11o_per_head pm_goal_1 initPM 963 0 13752 5547 9586
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p1 := l11o_per_head pm_goal_1 initPM 966 1 13753 5547 9587
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 13752).shape = [2048, 1024] := by
    rw [v0]; exact rmsRel.shard0_shape
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 13753).shape = [2048, 1024] := by
    rw [v1]; exact rmsRel.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [ps, vs, rmsRel.value, ← v0, ← v1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, p0, p1]
  · rw [ps]; exact l11o_per_head_shape _ _ 4096 1024 4 64
      (by rw [vs]; exact rmsRel.full_shape) hws
  · rw [p0]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs0 hpw
  · rw [p1]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs1 hpw

/-- L11 ordinary rotary Q/K relations.  The only computed relation supplied by
the caller is the preceding residual boundary; RMS, projections, the shared-Q
gather/chunk path, positions chunks, and RoPE are all derived here. -/
theorem l11o_q5550_k5551_rels_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5540)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9558) (denoteGraphDistributedFaithful pm_goal_1 initPM 9559)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5550)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9598) (denoteGraphDistributedFaithful pm_goal_1 initPM 9599)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5551)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9600) (denoteGraphDistributedFaithful pm_goal_1 initPM 9601)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l11o_reduce1 sm_goal_1 initSM 431
    { rank := 0, op := "OpName.FW_multiref", ins := [5540], outs := [8316, 8320], params := [2] }
    5540 8316 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm_goal_1 st 0 5540 [8316, 8320] 2 rfl 8316 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l11o_reduce1 pm_goal_1 initPM 956
    { rank := 0, op := "OpName.FW_multiref", ins := [9558], outs := [15790, 15794], params := [2] }
    9558 15790 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm_goal_1 st 0 9558 [15790, 15794] 2 rfl 15790 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l11o_reduce1 pm_goal_1 initPM 957
    { rank := 1, op := "OpName.FW_multiref", ins := [9559], outs := [15798, 15802], params := [2] }
    9559 15798 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm_goal_1 st 1 9559 [15798, 15802] 2 rfl 15798 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l11o_init_value initSM initPM hInit initGoal_5541
    (by native_decide) 5541 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l11o_rms sm_goal_1 initSM 432 0 8316 5541 5542
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11o_rms pm_goal_1 initPM 958 0 15790 5541 9562
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11o_rms pm_goal_1 initPM 959 1 15798 5541 9563
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5542)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9562) (denoteGraphDistributedFaithful pm_goal_1 initPM 9563)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)

  -- The Q input is gathered first, projected once into the shared tid 5544,
  -- then truly split by the two ChunkPrim nodes.
  have qmS := l11o_reduce1 sm_goal_1 initSM 433
    { rank := 0, op := "OpName.FW_multiref", ins := [5542], outs := [8325, 8329, 8333], params := [3] }
    5542 8325 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm_goal_1 st 0 5542 [8325, 8329, 8333] 3 rfl 8325 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm0 := l11o_reduce1 pm_goal_1 initPM 960
    { rank := 0, op := "OpName.FW_multiref", ins := [9562], outs := [15380, 13744, 13752], params := [3] }
    9562 15380 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm_goal_1 st 0 9562 [15380, 13744, 13752] 3 rfl 15380 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm1 := l11o_reduce1 pm_goal_1 initPM 961
    { rank := 1, op := "OpName.FW_multiref", ins := [9563], outs := [15382, 13745, 13753], params := [3] }
    9563 15382 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm_goal_1 st 1 9563 [15382, 13745, 13753] 3 rfl 15382 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at qmS qm0 qm1
  have qg := l11o_allgather2 pm_goal_1 initPM 964 0 15380 15382 12078
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hwq := l11o_init_value initSM initPM hInit initGoal_5543
    (by native_decide) 5543 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswq := l11o_init_shape initSM initPM hInit initGoal_5543
    (by native_decide) 5543 [16, 64, 1024] rfl rfl (by native_decide)
  have hpwq : (denoteGraphDistributedFaithful pm_goal_1 initPM 5543).shape = [16, 64, 1024] := by
    rw [← hwq]; exact hswq
  have qs := l11o_per_head sm_goal_1 initSM 434 0 8325 5543 5544
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have qp := l11o_per_head pm_goal_1 initPM 968 1 12078 5543 5544
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpmR : pm_goal_1.numRanks = 2 := rfl
  rw [hpmR] at qg
  have qeq : denoteGraphDistributedFaithful sm_goal_1 initSM 5544 = denoteGraphDistributedFaithful pm_goal_1 initPM 5544 := by
    rw [qs, qmS, rmsRel.value, ← qm0, ← qm1, ← qg, hwq, ← qp]
  have hqfullS : (denoteGraphDistributedFaithful sm_goal_1 initSM 5544).shape = [4096, 16, 64] := by
    rw [qs]
    exact l11o_per_head_shape _ _ 4096 1024 16 64
      (by rw [qmS]; exact rmsRel.full_shape) hswq
  have hqfullP : (denoteGraphDistributedFaithful pm_goal_1 initPM 5544).shape = [4096, 16, 64] := by
    rw [← qeq]; exact hqfullS
  have cq0 := l11o_chunk pm_goal_1 initPM 969 0 5544 9564
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have cq1 := l11o_chunk pm_goal_1 initPM 970 1 5544 9565
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at cq0 cq1
  have hq0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 9564).shape = [2048, 16, 64] := by
    rw [cq0, chunkPrimDimN_shape 0 2 0 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have hq1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 9565).shape = [2048, 16, 64] := by
    rw [cq1, chunkPrimDimN_shape 0 2 1 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have qRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5544)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9564) (denoteGraphDistributedFaithful pm_goal_1 initPM 9565)
      [4096, 16, 64] [2048, 16, 64] := by
    refine ⟨?_, hqfullS, hq0, hq1, by decide⟩
    rw [qeq, cq0, cq1]
    exact (l11o_allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5544) (by simpa using hqfullP)).symm

  -- K is projected locally on each shard, so ordinary per-head linear commute
  -- derives its relation directly (no caller-provided computed contract).
  have kmS := l11o_reduce1 sm_goal_1 initSM 433
    { rank := 0, op := "OpName.FW_multiref", ins := [5542], outs := [8325, 8329, 8333], params := [3] }
    5542 8329 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm_goal_1 st 0 5542 [8325, 8329, 8333] 3 rfl 8329 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km0 := l11o_reduce1 pm_goal_1 initPM 960
    { rank := 0, op := "OpName.FW_multiref", ins := [9562], outs := [15380, 13744, 13752], params := [3] }
    9562 13744 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm_goal_1 st 0 9562 [15380, 13744, 13752] 3 rfl 13744 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km1 := l11o_reduce1 pm_goal_1 initPM 961
    { rank := 1, op := "OpName.FW_multiref", ins := [9563], outs := [15382, 13745, 13753], params := [3] }
    9563 13745 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm_goal_1 st 1 9563 [15382, 13745, 13753] 3 rfl 13745 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at kmS km0 km1
  have hwk := l11o_init_value initSM initPM hInit initGoal_5545
    (by native_decide) 5545 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswk := l11o_init_shape initSM initPM hInit initGoal_5545
    (by native_decide) 5545 [4, 64, 1024] rfl rfl (by native_decide)
  have hpwk : (denoteGraphDistributedFaithful pm_goal_1 initPM 5545).shape = [4, 64, 1024] := by
    rw [← hwk]; exact hswk
  have ks := l11o_per_head sm_goal_1 initSM 435 0 8329 5545 5546
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp0 := l11o_per_head pm_goal_1 initPM 962 0 13744 5545 9576
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp1 := l11o_per_head pm_goal_1 initPM 965 1 13745 5545 9577
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5546)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9576) (denoteGraphDistributedFaithful pm_goal_1 initPM 9577)
      [4096, 4, 64] [2048, 4, 64] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [ks, kmS, rmsRel.value, ← km0, ← km1, hwk,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega)
          (by rw [km0]; exact rmsRel.shard0_shape)
          (by rw [km1]; exact rmsRel.shard1_shape) hpwk, kp0, kp1]
    · rw [ks]; exact l11o_per_head_shape _ _ 4096 1024 4 64
        (by rw [kmS]; exact rmsRel.full_shape) hswk
    · rw [kp0]; exact l11o_per_head_shape _ _ 2048 1024 4 64
        (by rw [km0]; exact rmsRel.shard0_shape) hpwk
    · rw [kp1]; exact l11o_per_head_shape _ _ 2048 1024 4 64
        (by rw [km1]; exact rmsRel.shard1_shape) hpwk

  have hcache := l11o_init_value initSM initPM hInit initGoal_4944
    (by native_decide) 4944 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpos := l11o_init_value initSM initPM hInit initGoal_5549
    (by native_decide) 5549 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hspos := l11o_init_shape initSM initPM hInit initGoal_5549
    (by native_decide) 5549 [4096] rfl rfl (by native_decide)
  have pc0 := l11o_chunk pm_goal_1 initPM 12 0 5549 9596
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have pc1 := l11o_chunk pm_goal_1 initPM 26 1 5549 9597
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at pc0 pc1
  have qS := l11o_reduce4 sm_goal_1 initSM 437
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5549, 5544, 5546],
      outs := [5550, 5551], params := [16, 4] }
    4944 5549 5544 5546 5550
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _
        (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out sm_goal_1 st 0 16 4 4944 5549 5544 5546 5550 5551)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have kS := l11o_reduce4 sm_goal_1 initSM 437
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5549, 5544, 5546],
      outs := [5550, 5551], params := [16, 4] }
    4944 5549 5544 5546 5551
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _
        (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out sm_goal_1 st 0 16 4 4944 5549 5544 5546 5550 5551 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q0 := l11o_reduce4 pm_goal_1 initPM 971
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 9596, 9564, 9576],
      outs := [9598, 9600], params := [16, 4] }
    4944 9596 9564 9576 9598
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _
        (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 0 16 4 4944 9596 9564 9576 9598 9600)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k0 := l11o_reduce4 pm_goal_1 initPM 971
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 9596, 9564, 9576],
      outs := [9598, 9600], params := [16, 4] }
    4944 9596 9564 9576 9600
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _
        (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 0 16 4 4944 9596 9564 9576 9598 9600 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q1 := l11o_reduce4 pm_goal_1 initPM 972
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 9597, 9565, 9577],
      outs := [9599, 9601], params := [16, 4] }
    4944 9597 9565 9577 9599
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _
        (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 1 16 4 4944 9597 9565 9577 9599 9601)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k1 := l11o_reduce4 pm_goal_1 initPM 972
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 9597, 9565, 9577],
      outs := [9599, 9601], params := [16, 4] }
    4944 9597 9565 9577 9601
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _
        (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 1 16 4 4944 9597 9565 9577 9599 9601 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qval : denoteGraphDistributedFaithful sm_goal_1 initSM 5550 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 9598, denoteGraphDistributedFaithful pm_goal_1 initPM 9599] := by
    rw [qS]
    simp only [fw_rotary_embedding]
    rw [qRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5549) (denoteGraphDistributedFaithful pm_goal_1 initPM 9564)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9565) 2048 16 64 (by omega) (by omega) (by omega)
      hspos qRel.shard0_shape qRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributedFaithful sm_goal_1 initSM 5551 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 9600, denoteGraphDistributedFaithful pm_goal_1 initPM 9601] := by
    rw [kS]
    simp only [fw_rotary_embedding]
    rw [kRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5549) (denoteGraphDistributedFaithful pm_goal_1 initPM 9576)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9577) 2048 4 64 (by omega) (by omega) (by omega)
      hspos kRel.shard0_shape kRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 9598).shape = [2048, 16, 64] := by
    rw [q0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard0_shape
  have qs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 9599).shape = [2048, 16, 64] := by
    rw [q1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard1_shape
  have ks0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 9600).shape = [2048, 4, 64] := by
    rw [k0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard0_shape
  have ks1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 9601).shape = [2048, 4, 64] := by
    rw [k1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]
    rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]
    rfl

end TrainVerify.Denote.GeneratedPatterns
