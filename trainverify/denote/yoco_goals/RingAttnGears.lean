/- Shared ring-attention node-reduction gears (Worker #12).

   Home for the GENERIC, graph-generic machinery used by the residual/MoE/L1
   reconstruction cascade (Worker #12) and available to the sliding-window/zigzag
   cascade (Worker #13). Everything is stated over an arbitrary `g : GraphDecl`,
   imports only `denote.GraphSlicing`, and uses UNIQUE names (all suffixed
   `_g12` or otherwise disjoint from `IntermediateReconstruction`/`Pattern_3`), so
   it can be imported ALONGSIDE those modules with zero name collisions.

   Contents:
   - `foldl_prefix_ring_g12` — ring-fold prefix reduction (own copy so this file
     needs no `IntermediateReconstruction` dependency).
   - `valAt_fw_view_lt`, `fw_view_id_shape` — reshape value lemmas (the `<`-hyp
     variant + own-shape identity; distinct from Pattern_3's versions).
   - `fw_view_allGather0_reshape_16_64_2_g12` — row-preserving reshape / dim-0
     allGather commute.
   - `ringAttn_reshape_reduce_g12` — ring node reduction for a params `FW_reshape`.
   - `ringAttn_reduce1` / `ringAttn_reduce2` — GENERIC ring node reductions for
     any non-ring single-output unary/binary op, given the op's `applyNode`
     reduction as a hypothesis. -/
import denote.GraphSlicing

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote

/-- Ring-fold prefix reduction: the ring value at `tid` equals its value after
    the prefix `take k`, when the suffix `drop k` never writes `tid`. Own copy
    (matches `IntermediateReconstruction.foldl_prefix_eq_full_ringAttn'`) so this
    module stays standalone. -/
theorem foldl_prefix_ring_g12 (g : GraphDecl) (nodes : List NodeDecl)
    (s : Store) (tid : Tid) (k : Nat)
    (hnil : ∀ n ∈ nodes.drop k, n.outs ≠ [])
    (h : ∀ n ∈ nodes.drop k, tid ∉ n.outs) :
    nodes.foldl (applyNodeRingAttn g) s tid =
      (nodes.take k).foldl (applyNodeRingAttn g) s tid := by
  conv_lhs => rw [← List.take_append_drop k nodes, List.foldl_append]
  exact foldl_applyNodeRingAttn_at_not_written g _ _ tid hnil h

/-! ### Row-preserving reshape / dim-0 allGather commute -/

/-- `valAt` is invariant under `fw_view` (pure shape relabel over flat data),
    `<`-hypothesis variant. -/
theorem valAt_fw_view_lt (sh : Shape) (x : Tensor) (k : Nat) (h : k < prodShape sh) :
    valAt (fw_view sh x) k = valAt x k := by
  have hs : (fw_view sh x).shape = sh := rfl
  rw [valAt_of_lt (fw_view sh x) k (by rw [hs]; exact h)]
  rfl

/-- A `fw_view` to a tensor's OWN shape is the identity (shape unchanged, flat
    data preserved). Used for the identity `FW_reshape`/`FW_view` nodes that the
    emitter inserts (e.g. `[4096,1024] → [4096,1024]`). -/
theorem fw_view_id_shape (sh : Shape) (x : Tensor) (hx : x.shape = sh) :
    fw_view sh x = x := by
  apply Tensor.ext
  · show sh = x.shape; exact hx.symm
  · intro idx hidx
    have hlt : idx < prodShape sh := by
      have : (fw_view sh x).shape = sh := rfl
      rw [← this] at hidx; exact hidx
    rw [valAt_fw_view_lt sh x idx hlt]

set_option maxHeartbeats 1600000 in
-- index decomposition + valAt unfolds are heartbeat-heavy
theorem fw_view_allGather0_reshape_16_64_2_g12
    (a b : Tensor) (ha : a.shape = [2048, 16, 64]) (hb : b.shape = [2048, 16, 64]) :
    fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [a, b])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] a, fw_view [2048, 1024] b] := by
  have hheadL : (([a, b] : List Tensor).head?.map (fun t => t.shape)).getD [] = [2048, 16, 64] := by
    simp [ha]
  have hheadR : (([fw_view [2048, 1024] a, fw_view [2048, 1024] b] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [2048, 1024] := rfl
  have hRshape : (allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] a, fw_view [2048, 1024] b]).shape
      = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] hheadR]; rfl
  apply Tensor.ext
  · rw [hRshape]; rfl
  · intro idx hidx
    have hidx' : idx < prodShape ([4096, 1024] : Shape) := hidx
    have hprod : prodShape ([4096, 1024] : Shape) = 4096 * 1024 := by simp [prodShape]
    have hidxlt : idx < 4096 * 1024 := by rw [hprod] at hidx'; exact hidx'
    rw [valAt_fw_view_lt [4096, 1024] _ idx hidx']
    set R := idx / 1024 with hR
    set c := idx % 1024 with hc
    have hc_lt : c < 1024 := Nat.mod_lt _ (by norm_num)
    have hR_lt : R < 4096 := by
      rw [hR]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hidxlt)
    have hidx_eq : idx = R * 1024 + c := by rw [hR, hc]; omega
    set r := R / 2048 with hr
    set i := R % 2048 with hi
    have hi_lt : i < 2048 := Nat.mod_lt _ (by norm_num)
    have hr_lt : r < 2 := by rw [hr]; exact Nat.div_lt_of_lt_mul (by omega)
    have hR_eq : R = r * 2048 + i := by rw [hr, hi]; omega
    set j := c / 64 with hj
    set k := c % 64 with hk
    have hk_lt : k < 64 := Nat.mod_lt _ (by norm_num)
    have hj_lt : j < 16 := by rw [hj]; exact Nat.div_lt_of_lt_mul (by omega)
    have hc_eq : c = j * 64 + k := by rw [hj, hk]; omega
    have hidx_3d : idx = ((r * 2048 + i) * 16 + j) * 64 + k := by
      rw [hidx_eq, hR_eq, hc_eq]; ring
    have hidx_2d : idx = (r * 2048 + i) * 1024 + c := by rw [hidx_eq, hR_eq]
    have hLHS : valAt (allGatherPrimDimN 0 2 0 [a, b]) idx
        = valAt (([a, b] : List Tensor).getD r (zeroTensor [2048, 16, 64])) ((i * 16 + j) * 64 + k) := by
      rw [hidx_3d]
      exact allGatherPrimDimN0_valAt_3D 2 2048 16 64 [a, b] (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hheadL
        (by intro rr hrr; interval_cases rr <;> simp [List.getD, ha, hb]) r hr_lt i hi_lt j hj_lt k hk_lt
    have hRHS : valAt (allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] a, fw_view [2048, 1024] b]) idx
        = valAt (([fw_view [2048, 1024] a, fw_view [2048, 1024] b] : List Tensor).getD r
            (zeroTensor [2048, 1024])) (i * 1024 + c) := by
      rw [hidx_2d]
      exact allGatherPrimDimN0_valAt 2 2048 1024 [fw_view [2048, 1024] a, fw_view [2048, 1024] b]
        (by norm_num) (by norm_num) (by norm_num) hheadR
        (by intro rr hrr; interval_cases rr <;> rfl) r hr_lt i hi_lt c hc_lt
    rw [hLHS, hRHS]
    have hbound : i * 1024 + c < prodShape ([2048, 1024] : Shape) := by
      have hp : prodShape ([2048, 1024] : Shape) = 2097152 := by decide
      rw [hp]; omega
    have hpiece_a : valAt (fw_view [2048, 1024] a) (i * 1024 + c) = valAt a (i * 1024 + c) :=
      valAt_fw_view_lt [2048, 1024] a (i * 1024 + c) hbound
    have hpiece_b : valAt (fw_view [2048, 1024] b) (i * 1024 + c) = valAt b (i * 1024 + c) :=
      valAt_fw_view_lt [2048, 1024] b (i * 1024 + c) hbound
    have hoff : (i * 16 + j) * 64 + k = i * 1024 + c := by rw [hc_eq]; ring
    interval_cases r <;>
      simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;>
      rw [hoff] <;>
      first
        | rw [hpiece_a]
        | rw [hpiece_b]

/-! ### Generic ring node reductions -/

/-- **Ring-denotation node reduction for a non-empty-params `FW_reshape` node.** -/
theorem ringAttn_reshape_reduce_g12 (g : GraphDecl) (init : Store) (k : Nat)
    (rank inTid outTid : Tid) (tshape : List Nat)
    (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk =
      { rank := rank, op := "OpName.FW_reshape", ins := [inTid], outs := [outTid], params := tshape })
    (htne : tshape ≠ [])
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraph_ringAttn g init outTid = fw_view tshape (denoteGraph_ringAttn g init inTid) := by
  have hstep := congrFun (foldl_take_succ (applyNodeRingAttn g) g.nodes init k hk) outTid
  rw [denoteGraph_ringAttn,
      foldl_prefix_ring_g12 g g.nodes init outTid (k + 1) hdrop_nil hdrop, hstep, hnode,
      applyNodeRingAttn_eq_applyNode_of_not_ring g _ _
        (show ¬ (("OpName.FW_reshape" : String) = "OpName.FW_attn_zigzag") by decide)
        (show ¬ (("OpName.FW_reshape" : String) = "OpName.FW_attn_sliding_window") by decide),
      applyNode_fw_reshape_out]
  cases tshape with
  | nil => exact absurd rfl htne
  | cons hd tl =>
    show fw_view (hd :: tl) ((g.nodes.take k).foldl (applyNodeRingAttn g) init inTid) = _
    congr 1
    exact (foldl_prefix_ring_g12 g g.nodes init inTid k hpre_nil hpre).symm

/-- **Generic ring node reduction, single-input single-output.** For a non-ring
    op node at position `k` whose `applyNode` reduces to `opfun` applied to its
    single input's store value, the ring value at the output equals `opfun`
    applied to the ring value at the input. The `applyNode` reduction is supplied
    as `happly` (e.g. `fun s => applyNode_fw_float_out g s rank inTid outTid ps`). -/
theorem ringAttn_reduce1 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk = node)
    (hnr1 : node.op ≠ "OpName.FW_attn_zigzag")
    (hnr2 : node.op ≠ "OpName.FW_attn_sliding_window")
    (happly : ∀ (s : Store), applyNode g s node outTid = opfun (s inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraph_ringAttn g init outTid = opfun (denoteGraph_ringAttn g init inTid) := by
  have hstep := congrFun (foldl_take_succ (applyNodeRingAttn g) g.nodes init k hk) outTid
  rw [denoteGraph_ringAttn,
      foldl_prefix_ring_g12 g g.nodes init outTid (k + 1) hdrop_nil hdrop, hstep, hnode,
      applyNodeRingAttn_eq_applyNode_of_not_ring g _ _ hnr1 hnr2, happly]
  congr 1
  exact (foldl_prefix_ring_g12 g g.nodes init inTid k hpre_nil hpre).symm

/-- **Generic ring node reduction, two-input single-output.** As `ringAttn_reduce1`
    but for a binary op. Requires each input to be unwritten by the suffix. -/
theorem ringAttn_reduce2 (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (in1 in2 outTid : Tid) (opfun : Tensor → Tensor → Tensor)
    (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk = node)
    (hnr1 : node.op ≠ "OpName.FW_attn_zigzag")
    (hnr2 : node.op ≠ "OpName.FW_attn_sliding_window")
    (happly : ∀ (s : Store), applyNode g s node outTid = opfun (s in1) (s in2))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre1 : ∀ n ∈ g.nodes.drop k, in1 ∉ n.outs)
    (hpre2 : ∀ n ∈ g.nodes.drop k, in2 ∉ n.outs) :
    denoteGraph_ringAttn g init outTid
      = opfun (denoteGraph_ringAttn g init in1) (denoteGraph_ringAttn g init in2) := by
  have hstep := congrFun (foldl_take_succ (applyNodeRingAttn g) g.nodes init k hk) outTid
  rw [denoteGraph_ringAttn,
      foldl_prefix_ring_g12 g g.nodes init outTid (k + 1) hdrop_nil hdrop, hstep, hnode,
      applyNodeRingAttn_eq_applyNode_of_not_ring g _ _ hnr1 hnr2, happly]
  congr 1
  · exact (foldl_prefix_ring_g12 g g.nodes init in1 k hpre_nil hpre1).symm
  · exact (foldl_prefix_ring_g12 g g.nodes init in2 k hpre_nil hpre2).symm

end TrainVerify.Denote.GeneratedPatterns
