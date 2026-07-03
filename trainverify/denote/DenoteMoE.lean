/-
DenoteMoE — unfolding + applyNode lemmas for the MoE / YOCO primitives that
were registered in `Denote.lean` (see the "MoE / YOCO algebraic primitives"
block).

These mirror exactly the layernorm / gelu pair `evalOp_fw_layernorm` /
`applyNode_fw_layernorm_out` etc., so generated bridges can rewrite a node's
denotation the same way the existing 312 bridges do for legacy ops.

The lemmas are intentionally *pure unfolding* (no semantic reasoning) — the
mathematical content lives in the corresponding `fw_X` / `bw_X` definitions.
-/

import denote.Denote

set_option linter.style.longLine false

open TrainVerify.Denote

namespace TrainVerify.Denote

/-! ## evalOp unfolding lemmas (one per registered MoE/YOCO branch) -/

theorem evalOp_fw_rms_norm (numParts rank : Nat) (params : List Nat) (x w : Tensor) :
    evalOp numParts rank "OpName.FW_rms_norm" params [x, w] = [fw_rms_norm x w] := by
  rfl

theorem evalOp_bw_rms_norm (numParts rank : Nat) (params : List Nat) (g x w : Tensor) :
    evalOp numParts rank "OpName.BW_rms_norm" params [g, x, w] =
      [ (bw_rms_norm g x w).1, (bw_rms_norm g x w).2 ] := by
  rfl

theorem evalOp_fw_sigmoid (numParts rank : Nat) (params : List Nat) (x : Tensor) :
    evalOp numParts rank "OpName.FW_sigmoid" params [x] = [fw_sigmoid x] := by
  rfl

theorem evalOp_bw_sigmoid (numParts rank : Nat) (params : List Nat) (g x : Tensor) :
    evalOp numParts rank "OpName.BW_sigmoid" params [g, x] = [bw_sigmoid g x] := by
  rfl

theorem evalOp_fw_silu (numParts rank : Nat) (params : List Nat) (x : Tensor) :
    evalOp numParts rank "OpName.FW_silu" params [x] = [fw_silu x] := by
  rfl

theorem evalOp_bw_silu (numParts rank : Nat) (params : List Nat) (g x : Tensor) :
    evalOp numParts rank "OpName.BW_silu" params [g, x] = [bw_silu g x] := by
  rfl

theorem evalOp_fw_swiglu (numParts rank : Nat) (params : List Nat) (gate up : Tensor) :
    evalOp numParts rank "OpName.FW_swiglu" params [gate, up] = [fw_swiglu gate up] := by
  rfl

theorem evalOp_bw_swiglu (numParts rank : Nat) (params : List Nat) (g gate up : Tensor) :
    evalOp numParts rank "OpName.BW_swiglu" params [g, gate, up] =
      [ (bw_swiglu g gate up).1, (bw_swiglu g gate up).2 ] := by
  rfl

theorem evalOp_fw_glu (numParts rank : Nat) (params : List Nat) (x gate : Tensor) :
    evalOp numParts rank "OpName.FW_glu" params [x, gate] = [fw_glu x gate] := by
  rfl

theorem evalOp_bw_glu (numParts rank : Nat) (params : List Nat) (g x gate : Tensor) :
    evalOp numParts rank "OpName.BW_glu" params [g, x, gate] =
      [ (bw_glu g x gate).1, (bw_glu g x gate).2 ] := by
  rfl

/-! ## `applyNode` lemmas: singleton-out forms used by bridge generation

    The shape `applyNode g s {..., ins := [...], outs := [outTid], ...} outTid`
    reduces (by definitional unfolding + `storeSet` lookup) to the corresponding
    `fw_X (s xTid) ...` expression, mirroring `applyNode_fw_layernorm_out`. -/

theorem applyNode_fw_rms_norm_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid wTid outTid : Tid)
    (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_rms_norm",
                    ins := [xTid, wTid], outs := [outTid], params := params } outTid =
      fw_rms_norm (s xTid) (s wTid) := by
  unfold applyNode
  rw [show ([xTid, wTid] : List Tid).map s = [s xTid, s wTid] from rfl,
      evalOp_fw_rms_norm]
  change storeSet s [(outTid, fw_rms_norm (s xTid) (s wTid))] outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_fw_sigmoid_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid outTid : Tid) (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_sigmoid",
                    ins := [xTid], outs := [outTid], params := params } outTid =
      fw_sigmoid (s xTid) := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_sigmoid]
  change storeSet s [(outTid, fw_sigmoid (s xTid))] outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_sigmoid_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid outTid : Tid) (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.BW_sigmoid",
                    ins := [gTid, xTid], outs := [outTid], params := params } outTid =
      bw_sigmoid (s gTid) (s xTid) := by
  unfold applyNode
  rw [show ([gTid, xTid] : List Tid).map s = [s gTid, s xTid] from rfl,
      evalOp_bw_sigmoid]
  change storeSet s [(outTid, bw_sigmoid (s gTid) (s xTid))] outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_fw_silu_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid outTid : Tid) (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_silu",
                    ins := [xTid], outs := [outTid], params := params } outTid =
      fw_silu (s xTid) := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_silu]
  change storeSet s [(outTid, fw_silu (s xTid))] outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_silu_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid outTid : Tid) (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.BW_silu",
                    ins := [gTid, xTid], outs := [outTid], params := params } outTid =
      bw_silu (s gTid) (s xTid) := by
  unfold applyNode
  rw [show ([gTid, xTid] : List Tid).map s = [s gTid, s xTid] from rfl,
      evalOp_bw_silu]
  change storeSet s [(outTid, bw_silu (s gTid) (s xTid))] outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_fw_swiglu_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gateTid upTid outTid : Tid) (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_swiglu",
                    ins := [gateTid, upTid], outs := [outTid], params := params } outTid =
      fw_swiglu (s gateTid) (s upTid) := by
  unfold applyNode
  rw [show ([gateTid, upTid] : List Tid).map s = [s gateTid, s upTid] from rfl,
      evalOp_fw_swiglu]
  change storeSet s [(outTid, fw_swiglu (s gateTid) (s upTid))] outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_fw_glu_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid gateTid outTid : Tid) (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_glu",
                    ins := [xTid, gateTid], outs := [outTid], params := params } outTid =
      fw_glu (s xTid) (s gateTid) := by
  unfold applyNode
  rw [show ([xTid, gateTid] : List Tid).map s = [s xTid, s gateTid] from rfl,
      evalOp_fw_glu]
  change storeSet s [(outTid, fw_glu (s xTid) (s gateTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-! ### Two-output forms: BW_rms_norm and BW_swiglu

    These return `(dx, dw)` / `(dg_gate, dg_up)`. We provide first-out and
    second-out lemmas in the style of `applyNode_bw_layernorm_*_out` (see
    Denote.lean). The pattern: `outs := [t1, t2]` and the lookup picks the
    component by index. -/

theorem applyNode_bw_rms_norm_fst_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid t1 t2 : Tid)
    (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.BW_rms_norm",
                    ins := [gTid, xTid, wTid], outs := [t1, t2], params := params } t1 =
      (bw_rms_norm (s gTid) (s xTid) (s wTid)).1 := by
  unfold applyNode
  rw [show ([gTid, xTid, wTid] : List Tid).map s = [s gTid, s xTid, s wTid] from rfl,
      evalOp_bw_rms_norm]
  -- outs.zip outs = [(t1, dx), (t2, dw)]; storeSet picks t1's entry
  change storeSet s [(t1, (bw_rms_norm (s gTid) (s xTid) (s wTid)).1),
                     (t2, (bw_rms_norm (s gTid) (s xTid) (s wTid)).2)] t1 = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_rms_norm_snd_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid t1 t2 : Tid)
    (params : List Nat)
    (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.BW_rms_norm",
                    ins := [gTid, xTid, wTid], outs := [t1, t2], params := params } t2 =
      (bw_rms_norm (s gTid) (s xTid) (s wTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, wTid] : List Tid).map s = [s gTid, s xTid, s wTid] from rfl,
      evalOp_bw_rms_norm]
  change storeSet s [(t1, (bw_rms_norm (s gTid) (s xTid) (s wTid)).1),
                     (t2, (bw_rms_norm (s gTid) (s xTid) (s wTid)).2)] t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne]

theorem applyNode_bw_swiglu_fst_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid gateTid upTid t1 t2 : Tid)
    (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.BW_swiglu",
                    ins := [gTid, gateTid, upTid], outs := [t1, t2], params := params } t1 =
      (bw_swiglu (s gTid) (s gateTid) (s upTid)).1 := by
  unfold applyNode
  rw [show ([gTid, gateTid, upTid] : List Tid).map s = [s gTid, s gateTid, s upTid] from rfl,
      evalOp_bw_swiglu]
  change storeSet s [(t1, (bw_swiglu (s gTid) (s gateTid) (s upTid)).1),
                     (t2, (bw_swiglu (s gTid) (s gateTid) (s upTid)).2)] t1 = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_swiglu_snd_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid gateTid upTid t1 t2 : Tid)
    (params : List Nat)
    (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.BW_swiglu",
                    ins := [gTid, gateTid, upTid], outs := [t1, t2], params := params } t2 =
      (bw_swiglu (s gTid) (s gateTid) (s upTid)).2 := by
  unfold applyNode
  rw [show ([gTid, gateTid, upTid] : List Tid).map s = [s gTid, s gateTid, s upTid] from rfl,
      evalOp_bw_swiglu]
  change storeSet s [(t1, (bw_swiglu (s gTid) (s gateTid) (s upTid)).1),
                     (t2, (bw_swiglu (s gTid) (s gateTid) (s upTid)).2)] t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne]

/-! ### RoPE: evalOp unfolding + applyNode lemmas (two-output forms)

    Each RoPE node carries `params := [qh, kh]`; bridge proofs rely on this
    layout to recover the head-count arguments to `fw_rotary_embedding`. -/

theorem evalOp_fw_rotary_embedding
    (numParts rank qh kh : Nat) (csCache positions q k : Tensor) :
    evalOp numParts rank "OpName.FW_rotary_embedding" [qh, kh]
        [csCache, positions, q, k] =
      [ (fw_rotary_embedding csCache positions q k qh kh).1,
        (fw_rotary_embedding csCache positions q k qh kh).2 ] := by
  rfl

theorem evalOp_bw_rotary_embedding
    (numParts rank qh kh : Nat) (csCache positions gq gk : Tensor) :
    evalOp numParts rank "OpName.BW_rotary_embedding" [qh, kh]
        [csCache, positions, gq, gk] =
      [ (bw_rotary_embedding csCache positions gq gk qh kh).1,
        (bw_rotary_embedding csCache positions gq gk qh kh).2 ] := by
  rfl

theorem applyNode_fw_rotary_embedding_fst_out
    (g : GraphDecl) (s : Store) (rank qh kh : Nat)
    (csTid posTid qTid kTid t1 t2 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_rotary_embedding",
                    ins := [csTid, posTid, qTid, kTid],
                    outs := [t1, t2], params := [qh, kh] } t1 =
      (fw_rotary_embedding (s csTid) (s posTid) (s qTid) (s kTid) qh kh).1 := by
  unfold applyNode
  rw [show ([csTid, posTid, qTid, kTid] : List Tid).map s =
            [s csTid, s posTid, s qTid, s kTid] from rfl,
      evalOp_fw_rotary_embedding]
  change storeSet s
    [(t1, (fw_rotary_embedding (s csTid) (s posTid) (s qTid) (s kTid) qh kh).1),
     (t2, (fw_rotary_embedding (s csTid) (s posTid) (s qTid) (s kTid) qh kh).2)]
    t1 = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_fw_rotary_embedding_snd_out
    (g : GraphDecl) (s : Store) (rank qh kh : Nat)
    (csTid posTid qTid kTid t1 t2 : Tid)
    (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.FW_rotary_embedding",
                    ins := [csTid, posTid, qTid, kTid],
                    outs := [t1, t2], params := [qh, kh] } t2 =
      (fw_rotary_embedding (s csTid) (s posTid) (s qTid) (s kTid) qh kh).2 := by
  unfold applyNode
  rw [show ([csTid, posTid, qTid, kTid] : List Tid).map s =
            [s csTid, s posTid, s qTid, s kTid] from rfl,
      evalOp_fw_rotary_embedding]
  change storeSet s
    [(t1, (fw_rotary_embedding (s csTid) (s posTid) (s qTid) (s kTid) qh kh).1),
     (t2, (fw_rotary_embedding (s csTid) (s posTid) (s qTid) (s kTid) qh kh).2)]
    t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne]

theorem applyNode_bw_rotary_embedding_fst_out
    (g : GraphDecl) (s : Store) (rank qh kh : Nat)
    (csTid posTid gqTid gkTid t1 t2 : Tid) :
    applyNode g s { rank := rank, op := "OpName.BW_rotary_embedding",
                    ins := [csTid, posTid, gqTid, gkTid],
                    outs := [t1, t2], params := [qh, kh] } t1 =
      (bw_rotary_embedding (s csTid) (s posTid) (s gqTid) (s gkTid) qh kh).1 := by
  unfold applyNode
  rw [show ([csTid, posTid, gqTid, gkTid] : List Tid).map s =
            [s csTid, s posTid, s gqTid, s gkTid] from rfl,
      evalOp_bw_rotary_embedding]
  change storeSet s
    [(t1, (bw_rotary_embedding (s csTid) (s posTid) (s gqTid) (s gkTid) qh kh).1),
     (t2, (bw_rotary_embedding (s csTid) (s posTid) (s gqTid) (s gkTid) qh kh).2)]
    t1 = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_rotary_embedding_snd_out
    (g : GraphDecl) (s : Store) (rank qh kh : Nat)
    (csTid posTid gqTid gkTid t1 t2 : Tid)
    (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.BW_rotary_embedding",
                    ins := [csTid, posTid, gqTid, gkTid],
                    outs := [t1, t2], params := [qh, kh] } t2 =
      (bw_rotary_embedding (s csTid) (s posTid) (s gqTid) (s gkTid) qh kh).2 := by
  unfold applyNode
  rw [show ([csTid, posTid, gqTid, gkTid] : List Tid).map s =
            [s csTid, s posTid, s gqTid, s gkTid] from rfl,
      evalOp_bw_rotary_embedding]
  change storeSet s
    [(t1, (bw_rotary_embedding (s csTid) (s posTid) (s gqTid) (s gkTid) qh kh).1),
     (t2, (bw_rotary_embedding (s csTid) (s posTid) (s gqTid) (s gkTid) qh kh).2)]
    t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne]

/-! ### Shuffle / unshuffle: evalOp unfolding + applyNode lemmas

    Shuffle/unshuffle nodes take `cpSize + 1` inputs (one `cu_seqlens` plus
    one tensor per CP rank) and a single output, with `params := [cpSize, cpRank]`.
    The evalOp/applyNode lemmas mirror the `allToAllPrim` pattern. -/

theorem evalOp_fw_maybe_shuffle
    (numParts rank cpSize cpRank : Nat) (data cu : Tensor) :
    evalOp numParts rank "OpName.FW_maybe_shuffle" [cpSize, cpRank] [data, cu] =
      [fw_maybe_shuffle data cu cpSize cpRank] := by
  rfl

theorem evalOp_fw_maybe_unshuffle
    (numParts rank cpSize cpRank : Nat) (data cu : Tensor) :
    evalOp numParts rank "OpName.FW_maybe_unshuffle" [cpSize, cpRank] [data, cu] =
      [fw_maybe_unshuffle data cu cpSize cpRank] := by
  rfl

theorem evalOp_bw_maybe_shuffle
    (numParts rank cpSize cpRank : Nat) (grad cu : Tensor) :
    evalOp numParts rank "OpName.BW_maybe_shuffle" [cpSize, cpRank] [grad, cu] =
      [bw_maybe_shuffle grad cu cpSize cpRank] := by
  rfl

theorem evalOp_bw_maybe_unshuffle
    (numParts rank cpSize cpRank : Nat) (grad cu : Tensor) :
    evalOp numParts rank "OpName.BW_maybe_unshuffle" [cpSize, cpRank] [grad, cu] =
      [bw_maybe_unshuffle grad cu cpSize cpRank] := by
  rfl

/-- `applyNode` for `FW_maybe_shuffle`: inputs `[dataTid, cuTid]`, output `outTid`. -/
theorem applyNode_fw_maybe_shuffle_out
    (g : GraphDecl) (s : Store) (rank cpSize cpRank : Nat)
    (dataTid cuTid : Tid) (outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_maybe_shuffle",
                    ins := [dataTid, cuTid],
                    outs := [outTid], params := [cpSize, cpRank] } outTid =
      fw_maybe_shuffle (s dataTid) (s cuTid) cpSize cpRank := by
  unfold applyNode
  rw [show ([dataTid, cuTid] : List Tid).map s = [s dataTid, s cuTid] from rfl,
      evalOp_fw_maybe_shuffle]
  change storeSet s [(outTid, fw_maybe_shuffle (s dataTid) (s cuTid) cpSize cpRank)]
    outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_fw_maybe_unshuffle_out
    (g : GraphDecl) (s : Store) (rank cpSize cpRank : Nat)
    (dataTid cuTid : Tid) (outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_maybe_unshuffle",
                    ins := [dataTid, cuTid],
                    outs := [outTid], params := [cpSize, cpRank] } outTid =
      fw_maybe_unshuffle (s dataTid) (s cuTid) cpSize cpRank := by
  unfold applyNode
  rw [show ([dataTid, cuTid] : List Tid).map s = [s dataTid, s cuTid] from rfl,
      evalOp_fw_maybe_unshuffle]
  change storeSet s [(outTid, fw_maybe_unshuffle (s dataTid) (s cuTid) cpSize cpRank)]
    outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_maybe_shuffle_out
    (g : GraphDecl) (s : Store) (rank cpSize cpRank : Nat)
    (gradTid cuTid : Tid) (outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.BW_maybe_shuffle",
                    ins := [gradTid, cuTid],
                    outs := [outTid], params := [cpSize, cpRank] } outTid =
      bw_maybe_shuffle (s gradTid) (s cuTid) cpSize cpRank := by
  unfold applyNode
  rw [show ([gradTid, cuTid] : List Tid).map s = [s gradTid, s cuTid] from rfl,
      evalOp_bw_maybe_shuffle]
  change storeSet s [(outTid, bw_maybe_shuffle (s gradTid) (s cuTid) cpSize cpRank)]
    outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_maybe_unshuffle_out
    (g : GraphDecl) (s : Store) (rank cpSize cpRank : Nat)
    (gradTid cuTid : Tid) (outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.BW_maybe_unshuffle",
                    ins := [gradTid, cuTid],
                    outs := [outTid], params := [cpSize, cpRank] } outTid =
      bw_maybe_unshuffle (s gradTid) (s cuTid) cpSize cpRank := by
  unfold applyNode
  rw [show ([gradTid, cuTid] : List Tid).map s = [s gradTid, s cuTid] from rfl,
      evalOp_bw_maybe_unshuffle]
  change storeSet s [(outTid, bw_maybe_unshuffle (s gradTid) (s cuTid) cpSize cpRank)]
    outTid = _
  unfold storeSet
  simp [List.find?]

/-! ### Attention: evalOp unfolding + applyNode lemmas

    `FW_attn_varlen` takes 5 inputs `(q, k, v, cuQ, cuK)` and 1 output;
    `BW_attn_varlen` takes 6 inputs `(gO, q, k, v, cuQ, cuK)` and 3 outputs
    `(dQ, dK, dV)`. Params encode `[qh, kvh, d, vd, causalNat, windowLeft]`. -/

theorem evalOp_fw_attn_varlen
    (numParts rank qh kvh d vd causalNat windowLeft : Nat)
    (q k v cuQ cuK : Tensor) :
    evalOp numParts rank "OpName.FW_attn_varlen"
        [qh, kvh, d, vd, causalNat, windowLeft] [q, k, v, cuQ, cuK] =
      [fw_attn_varlen q k v cuQ cuK qh kvh d vd
        (decide (causalNat ≠ 0)) windowLeft] := by
  rfl

theorem evalOp_bw_attn_varlen
    (numParts rank qh kvh d vd causalNat windowLeft : Nat)
    (gO q k v cuQ cuK : Tensor) :
    evalOp numParts rank "OpName.BW_attn_varlen"
        [qh, kvh, d, vd, causalNat, windowLeft] [gO, q, k, v, cuQ, cuK] =
      [ (bw_attn_varlen gO q k v cuQ cuK qh kvh d vd
          (decide (causalNat ≠ 0)) windowLeft).1,
        (bw_attn_varlen gO q k v cuQ cuK qh kvh d vd
          (decide (causalNat ≠ 0)) windowLeft).2.1,
        (bw_attn_varlen gO q k v cuQ cuK qh kvh d vd
          (decide (causalNat ≠ 0)) windowLeft).2.2 ] := by
  rfl

/-- `applyNode` for `FW_attn_varlen`: inputs `[qTid, kTid, vTid, cuQTid, cuKTid]`,
    single output. -/
theorem applyNode_fw_attn_varlen_out
    (g : GraphDecl) (s : Store) (rank qh kvh d vd causalNat windowLeft : Nat)
    (qTid kTid vTid cuQTid cuKTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_attn_varlen",
                    ins := [qTid, kTid, vTid, cuQTid, cuKTid],
                    outs := [outTid],
                    params := [qh, kvh, d, vd, causalNat, windowLeft] } outTid =
      fw_attn_varlen (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
        qh kvh d vd (decide (causalNat ≠ 0)) windowLeft := by
  unfold applyNode
  rw [show ([qTid, kTid, vTid, cuQTid, cuKTid] : List Tid).map s =
            [s qTid, s kTid, s vTid, s cuQTid, s cuKTid] from rfl,
      evalOp_fw_attn_varlen]
  change storeSet s
    [(outTid, fw_attn_varlen (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
        qh kvh d vd (decide (causalNat ≠ 0)) windowLeft)] outTid = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `BW_attn_varlen` first output (dQ). -/
theorem applyNode_bw_attn_varlen_dq_out
    (g : GraphDecl) (s : Store) (rank qh kvh d vd causalNat windowLeft : Nat)
    (gOTid qTid kTid vTid cuQTid cuKTid t1 t2 t3 : Tid) :
    applyNode g s { rank := rank, op := "OpName.BW_attn_varlen",
                    ins := [gOTid, qTid, kTid, vTid, cuQTid, cuKTid],
                    outs := [t1, t2, t3],
                    params := [qh, kvh, d, vd, causalNat, windowLeft] } t1 =
      (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
        qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).1 := by
  unfold applyNode
  rw [show ([gOTid, qTid, kTid, vTid, cuQTid, cuKTid] : List Tid).map s =
            [s gOTid, s qTid, s kTid, s vTid, s cuQTid, s cuKTid] from rfl,
      evalOp_bw_attn_varlen]
  change storeSet s
    [(t1, (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
            qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).1),
     (t2, (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
            qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).2.1),
     (t3, (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
            qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).2.2)] t1 = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `BW_attn_varlen` second output (dK). -/
theorem applyNode_bw_attn_varlen_dk_out
    (g : GraphDecl) (s : Store) (rank qh kvh d vd causalNat windowLeft : Nat)
    (gOTid qTid kTid vTid cuQTid cuKTid t1 t2 t3 : Tid)
    (hne12 : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.BW_attn_varlen",
                    ins := [gOTid, qTid, kTid, vTid, cuQTid, cuKTid],
                    outs := [t1, t2, t3],
                    params := [qh, kvh, d, vd, causalNat, windowLeft] } t2 =
      (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
        qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).2.1 := by
  unfold applyNode
  rw [show ([gOTid, qTid, kTid, vTid, cuQTid, cuKTid] : List Tid).map s =
            [s gOTid, s qTid, s kTid, s vTid, s cuQTid, s cuKTid] from rfl,
      evalOp_bw_attn_varlen]
  change storeSet s
    [(t1, (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
            qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).1),
     (t2, (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
            qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).2.1),
     (t3, (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
            qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).2.2)] t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne12]

/-- `applyNode` for `BW_attn_varlen` third output (dV). -/
theorem applyNode_bw_attn_varlen_dv_out
    (g : GraphDecl) (s : Store) (rank qh kvh d vd causalNat windowLeft : Nat)
    (gOTid qTid kTid vTid cuQTid cuKTid t1 t2 t3 : Tid)
    (hne13 : t1 ≠ t3) (hne23 : t2 ≠ t3) :
    applyNode g s { rank := rank, op := "OpName.BW_attn_varlen",
                    ins := [gOTid, qTid, kTid, vTid, cuQTid, cuKTid],
                    outs := [t1, t2, t3],
                    params := [qh, kvh, d, vd, causalNat, windowLeft] } t3 =
      (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
        qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).2.2 := by
  unfold applyNode
  rw [show ([gOTid, qTid, kTid, vTid, cuQTid, cuKTid] : List Tid).map s =
            [s gOTid, s qTid, s kTid, s vTid, s cuQTid, s cuKTid] from rfl,
      evalOp_bw_attn_varlen]
  change storeSet s
    [(t1, (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
            qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).1),
     (t2, (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
            qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).2.1),
     (t3, (bw_attn_varlen (s gOTid) (s qTid) (s kTid) (s vTid) (s cuQTid) (s cuKTid)
            qh kvh d vd (decide (causalNat ≠ 0)) windowLeft).2.2)] t3 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t3) from hne13, show ¬ (t2 = t3) from hne23]

/-! ## Shape preservation (used in shape-obligation proofs) -/

theorem fw_sigmoid_shape (x : Tensor) : (fw_sigmoid x).shape = x.shape := by
  unfold fw_sigmoid
  simp [Tensor.mkShape]

theorem fw_silu_shape (x : Tensor) : (fw_silu x).shape = x.shape := by
  unfold fw_silu
  simp [Tensor.mkShape]

theorem fw_swiglu_shape (gate up : Tensor) :
    (fw_swiglu gate up).shape = up.shape := by
  unfold fw_swiglu
  simp [Tensor.mkShape]

theorem fw_glu_shape (x gate : Tensor) :
    (fw_glu x gate).shape = x.shape := by
  unfold fw_glu
  simp [Tensor.mkShape]

theorem bw_sigmoid_shape (g x : Tensor) : (bw_sigmoid g x).shape = x.shape := by
  unfold bw_sigmoid
  simp [Tensor.mkShape]

theorem bw_silu_shape (g x : Tensor) : (bw_silu g x).shape = x.shape := by
  unfold bw_silu
  simp [Tensor.mkShape]

theorem fw_rms_norm_shape (x w : Tensor) : (fw_rms_norm x w).shape = x.shape := by
  unfold fw_rms_norm
  cases h : x.shape.reverse with
  | nil => simp
  | cons d _ => simp [Tensor.mkShape]

/-! ### RoPE shape preservation -/

theorem fw_rotary_apply_shape (csCache positions x : Tensor) (numHeads : Nat) :
    (fw_rotary_apply csCache positions x numHeads).shape = x.shape := by
  unfold fw_rotary_apply
  cases h : x.shape.reverse with
  | nil => simp
  | cons d _ => simp [Tensor.mkShape]

theorem bw_rotary_apply_shape (csCache positions g : Tensor) (numHeads : Nat) :
    (bw_rotary_apply csCache positions g numHeads).shape = g.shape := by
  unfold bw_rotary_apply
  cases h : g.shape.reverse with
  | nil => simp
  | cons d _ => simp [Tensor.mkShape]

theorem fw_rotary_embedding_fst_shape
    (csCache positions q k : Tensor) (qh kh : Nat) :
    (fw_rotary_embedding csCache positions q k qh kh).1.shape = q.shape := by
  unfold fw_rotary_embedding
  exact fw_rotary_apply_shape csCache positions q qh

theorem fw_rotary_embedding_snd_shape
    (csCache positions q k : Tensor) (qh kh : Nat) :
    (fw_rotary_embedding csCache positions q k qh kh).2.shape = k.shape := by
  unfold fw_rotary_embedding
  exact fw_rotary_apply_shape csCache positions k kh

theorem bw_rotary_embedding_fst_shape
    (csCache positions gq gk : Tensor) (qh kh : Nat) :
    (bw_rotary_embedding csCache positions gq gk qh kh).1.shape = gq.shape := by
  unfold bw_rotary_embedding
  exact bw_rotary_apply_shape csCache positions gq qh

theorem bw_rotary_embedding_snd_shape
    (csCache positions gq gk : Tensor) (qh kh : Nat) :
    (bw_rotary_embedding csCache positions gq gk qh kh).2.shape = gk.shape := by
  unfold bw_rotary_embedding
  exact bw_rotary_apply_shape csCache positions gk kh

/-! ### Shuffle / unshuffle shape preservation

    Under the identity model (2026-07-03 audit), all four variants are literally
    `id` on the data tensor, so shape preservation is `rfl`. -/

theorem fw_maybe_shuffle_shape
    (data cu : Tensor) (cpSize cpRank : Nat) :
    (fw_maybe_shuffle data cu cpSize cpRank).shape = data.shape := by
  unfold fw_maybe_shuffle; rfl

theorem fw_maybe_unshuffle_shape
    (data cu : Tensor) (cpSize cpRank : Nat) :
    (fw_maybe_unshuffle data cu cpSize cpRank).shape = data.shape := by
  unfold fw_maybe_unshuffle; rfl

theorem bw_maybe_shuffle_shape
    (grad cu : Tensor) (cpSize cpRank : Nat) :
    (bw_maybe_shuffle grad cu cpSize cpRank).shape = grad.shape := by
  unfold bw_maybe_shuffle; rfl

theorem bw_maybe_unshuffle_shape
    (grad cu : Tensor) (cpSize cpRank : Nat) :
    (bw_maybe_unshuffle grad cu cpSize cpRank).shape = grad.shape := by
  unfold bw_maybe_unshuffle; rfl

/-! ### Attention shape preservation

    Forward: `fw_attn_varlen` produces `[L_q, qh, vd]` where `L_q = q.shape.head`.
    Backward components: dQ matches q.shape, dK matches k.shape, dV matches
    `[L_k, kvh, vd]`. The shape lemmas state these explicitly. -/

theorem fw_attn_varlen_shape
    (q k v cuQ cuK : Tensor) (qh kvh d vd : Nat)
    (causal : Bool) (windowLeft : Nat) (lQ : Nat)
    (hQ : q.shape.head? = some lQ) :
    (fw_attn_varlen q k v cuQ cuK qh kvh d vd causal windowLeft).shape =
      [lQ, qh, vd] := by
  unfold fw_attn_varlen
  have hh : (q.shape.head?).getD 0 = lQ := by rw [hQ]; rfl
  simp [hh, Tensor.mkShape]

theorem bw_attn_dq_shape
    (gO q k v cuQ cuK : Tensor) (qh kvh d vd : Nat)
    (causal : Bool) (windowLeft : Nat) (lQ : Nat)
    (hQ : q.shape.head? = some lQ) :
    (bw_attn_dq gO q k v cuQ cuK qh kvh d vd causal windowLeft).shape =
      [lQ, qh, d] := by
  unfold bw_attn_dq
  have hh : (q.shape.head?).getD 0 = lQ := by rw [hQ]; rfl
  simp [hh, Tensor.mkShape]

theorem bw_attn_dk_shape
    (gO q k v cuQ cuK : Tensor) (qh kvh d vd lQ : Nat)
    (causal : Bool) (windowLeft : Nat) (lK : Nat)
    (hK : k.shape.head? = some lK) :
    (bw_attn_dk gO q k v cuQ cuK qh kvh d vd lQ causal windowLeft).shape =
      [lK, kvh, d] := by
  unfold bw_attn_dk
  have hh : (k.shape.head?).getD 0 = lK := by rw [hK]; rfl
  simp [hh, Tensor.mkShape]

theorem bw_attn_dv_shape
    (gO q k cuQ cuK : Tensor) (qh kvh d vd lQ : Nat)
    (causal : Bool) (windowLeft : Nat) (lK : Nat)
    (hK : k.shape.head? = some lK) :
    (bw_attn_dv gO q k cuQ cuK qh kvh d vd lQ causal windowLeft).shape =
      [lK, kvh, vd] := by
  unfold bw_attn_dv
  have hh : (k.shape.head?).getD 0 = lK := by rw [hK]; rfl
  simp [hh, Tensor.mkShape]

/-! ## Mix-precision linear (P2-A)

    `mix_precision_linear` is mathematically `fw_linear`; the evalOp branch is
    a direct alias, so the unfolding lemmas reduce to `fw_linear` / `bw_linear`
    in exactly the same shape as `applyNode_fw_linear_out` in `Denote.lean`. -/

theorem evalOp_fw_mix_precision_linear
    (numParts rank : Nat) (params : List Nat) (x w : Tensor) :
    evalOp numParts rank "OpName.FW_mix_precision_linear" params [x, w] =
      [fw_linear x w] := by
  rfl

theorem evalOp_bw_mix_precision_linear
    (numParts rank : Nat) (params : List Nat) (g x w : Tensor) :
    evalOp numParts rank "OpName.BW_mix_precision_linear" params [g, x, w] =
      [ (bw_linear g x w).1, (bw_linear g x w).2 ] := by
  rfl

theorem applyNode_fw_mix_precision_linear_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid wTid outTid : Tid)
    (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_mix_precision_linear",
                    ins := [xTid, wTid], outs := [outTid], params := params } outTid =
      fw_linear (s xTid) (s wTid) := by
  unfold applyNode
  rw [show ([xTid, wTid] : List Tid).map s = [s xTid, s wTid] from rfl,
      evalOp_fw_mix_precision_linear]
  change storeSet s [(outTid, fw_linear (s xTid) (s wTid))] outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_mix_precision_linear_fst_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid t1 t2 : Tid)
    (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.BW_mix_precision_linear",
                    ins := [gTid, xTid, wTid], outs := [t1, t2], params := params } t1 =
      (bw_linear (s gTid) (s xTid) (s wTid)).1 := by
  unfold applyNode
  rw [show ([gTid, xTid, wTid] : List Tid).map s = [s gTid, s xTid, s wTid] from rfl,
      evalOp_bw_mix_precision_linear]
  change storeSet s [(t1, (bw_linear (s gTid) (s xTid) (s wTid)).1),
                     (t2, (bw_linear (s gTid) (s xTid) (s wTid)).2)] t1 = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_mix_precision_linear_snd_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid t1 t2 : Tid)
    (params : List Nat)
    (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.BW_mix_precision_linear",
                    ins := [gTid, xTid, wTid], outs := [t1, t2], params := params } t2 =
      (bw_linear (s gTid) (s xTid) (s wTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, wTid] : List Tid).map s = [s gTid, s xTid, s wTid] from rfl,
      evalOp_bw_mix_precision_linear]
  change storeSet s [(t1, (bw_linear (s gTid) (s xTid) (s wTid)).1),
                     (t2, (bw_linear (s gTid) (s xTid) (s wTid)).2)] t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne]

/-! ## Per-head mix-precision linear (P2-A) -/

theorem evalOp_fw_per_head_mix_precision_linear
    (numParts rank : Nat) (params : List Nat) (x w : Tensor) :
    evalOp numParts rank "OpName.FW_per_head_mix_precision_linear" params [x, w] =
      [fw_per_head_linear x w] := by
  rfl

theorem evalOp_bw_per_head_mix_precision_linear
    (numParts rank : Nat) (params : List Nat) (g x w : Tensor) :
    evalOp numParts rank "OpName.BW_per_head_mix_precision_linear" params [g, x, w] =
      [ (bw_per_head_linear g x w).1, (bw_per_head_linear g x w).2 ] := by
  rfl

theorem applyNode_fw_per_head_mix_precision_linear_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid wTid outTid : Tid)
    (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_per_head_mix_precision_linear",
                    ins := [xTid, wTid], outs := [outTid], params := params } outTid =
      fw_per_head_linear (s xTid) (s wTid) := by
  unfold applyNode
  rw [show ([xTid, wTid] : List Tid).map s = [s xTid, s wTid] from rfl,
      evalOp_fw_per_head_mix_precision_linear]
  change storeSet s [(outTid, fw_per_head_linear (s xTid) (s wTid))] outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_per_head_mix_precision_linear_fst_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid t1 t2 : Tid)
    (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.BW_per_head_mix_precision_linear",
                    ins := [gTid, xTid, wTid], outs := [t1, t2], params := params } t1 =
      (bw_per_head_linear (s gTid) (s xTid) (s wTid)).1 := by
  unfold applyNode
  rw [show ([gTid, xTid, wTid] : List Tid).map s = [s gTid, s xTid, s wTid] from rfl,
      evalOp_bw_per_head_mix_precision_linear]
  change storeSet s [(t1, (bw_per_head_linear (s gTid) (s xTid) (s wTid)).1),
                     (t2, (bw_per_head_linear (s gTid) (s xTid) (s wTid)).2)] t1 = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_per_head_mix_precision_linear_snd_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid t1 t2 : Tid)
    (params : List Nat)
    (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.BW_per_head_mix_precision_linear",
                    ins := [gTid, xTid, wTid], outs := [t1, t2], params := params } t2 =
      (bw_per_head_linear (s gTid) (s xTid) (s wTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, wTid] : List Tid).map s = [s gTid, s xTid, s wTid] from rfl,
      evalOp_bw_per_head_mix_precision_linear]
  change storeSet s [(t1, (bw_per_head_linear (s gTid) (s xTid) (s wTid)).1),
                     (t2, (bw_per_head_linear (s gTid) (s xTid) (s wTid)).2)] t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne]

/-! ## Norm linear (P2-A) -/

theorem evalOp_fw_norm_linear
    (numParts rank : Nat) (params : List Nat) (x w : Tensor) :
    evalOp numParts rank "OpName.FW_norm_linear" params [x, w] =
      [fw_norm_linear x w] := by
  rfl

theorem evalOp_bw_norm_linear
    (numParts rank : Nat) (params : List Nat) (g x w : Tensor) :
    evalOp numParts rank "OpName.BW_norm_linear" params [g, x, w] =
      [ (bw_norm_linear g x w).1, (bw_norm_linear g x w).2 ] := by
  rfl

theorem applyNode_fw_norm_linear_out
    (g : GraphDecl) (s : Store) (rank : Nat) (xTid wTid outTid : Tid)
    (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.FW_norm_linear",
                    ins := [xTid, wTid], outs := [outTid], params := params } outTid =
      fw_norm_linear (s xTid) (s wTid) := by
  unfold applyNode
  rw [show ([xTid, wTid] : List Tid).map s = [s xTid, s wTid] from rfl,
      evalOp_fw_norm_linear]
  change storeSet s [(outTid, fw_norm_linear (s xTid) (s wTid))] outTid = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_norm_linear_fst_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid t1 t2 : Tid)
    (params : List Nat) :
    applyNode g s { rank := rank, op := "OpName.BW_norm_linear",
                    ins := [gTid, xTid, wTid], outs := [t1, t2], params := params } t1 =
      (bw_norm_linear (s gTid) (s xTid) (s wTid)).1 := by
  unfold applyNode
  rw [show ([gTid, xTid, wTid] : List Tid).map s = [s gTid, s xTid, s wTid] from rfl,
      evalOp_bw_norm_linear]
  change storeSet s [(t1, (bw_norm_linear (s gTid) (s xTid) (s wTid)).1),
                     (t2, (bw_norm_linear (s gTid) (s xTid) (s wTid)).2)] t1 = _
  unfold storeSet
  simp [List.find?]

theorem applyNode_bw_norm_linear_snd_out
    (g : GraphDecl) (s : Store) (rank : Nat) (gTid xTid wTid t1 t2 : Tid)
    (params : List Nat)
    (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.BW_norm_linear",
                    ins := [gTid, xTid, wTid], outs := [t1, t2], params := params } t2 =
      (bw_norm_linear (s gTid) (s xTid) (s wTid)).2 := by
  unfold applyNode
  rw [show ([gTid, xTid, wTid] : List Tid).map s = [s gTid, s xTid, s wTid] from rfl,
      evalOp_bw_norm_linear]
  change storeSet s [(t1, (bw_norm_linear (s gTid) (s xTid) (s wTid)).1),
                     (t2, (bw_norm_linear (s gTid) (s xTid) (s wTid)).2)] t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne]

/-! ### Shape preservation for P2-A linear kernels

    All three operators produce concretely-derived output shapes from the
    `Tensor.mkShape` head; the lemmas state them as functions of the input
    shapes. -/

theorem fw_per_head_linear_shape
    (x w : Tensor) (hW dW kw : Nat) (rest : List Nat)
    (hx : x.shape.reverse = (kw :: rest))
    (hw : w.shape = [hW, dW, kw]) :
    (fw_per_head_linear x w).shape = rest.reverse ++ [hW, dW] := by
  unfold fw_per_head_linear
  -- w.shape.reverse = [kw, dW, hW]
  have hwr : w.shape.reverse = [kw, dW, hW] := by rw [hw]; rfl
  rw [hx, hwr]
  simp [Tensor.mkShape]

theorem bw_per_head_linear_fst_shape
    (g x w : Tensor) (hW dW kw : Nat) (rest : List Nat)
    (hx : x.shape.reverse = (kw :: rest))
    (hw : w.shape = [hW, dW, kw]) :
    (bw_per_head_linear g x w).1.shape = x.shape := by
  unfold bw_per_head_linear
  have hwr : w.shape.reverse = [kw, dW, hW] := by rw [hw]; rfl
  rw [hx, hwr]
  simp [Tensor.mkShape]

theorem bw_per_head_linear_snd_shape
    (g x w : Tensor) (hW dW kw : Nat) (rest : List Nat)
    (hx : x.shape.reverse = (kw :: rest))
    (hw : w.shape = [hW, dW, kw]) :
    (bw_per_head_linear g x w).2.shape = w.shape := by
  unfold bw_per_head_linear
  have hwr : w.shape.reverse = [kw, dW, hW] := by rw [hw]; rfl
  rw [hx, hwr]
  simp [Tensor.mkShape]

theorem fw_norm_linear_shape
    (x w : Tensor) (n kw : Nat) (rest : List Nat)
    (hx : x.shape.reverse = (kw :: rest))
    (hw : w.shape = [n, kw]) :
    (fw_norm_linear x w).shape = rest.reverse ++ [n] := by
  unfold fw_norm_linear
  have hwr : w.shape.reverse = [kw, n] := by rw [hw]; rfl
  rw [hx, hwr]
  simp [Tensor.mkShape]

theorem bw_norm_linear_fst_shape
    (g x w : Tensor) (n kw : Nat) (rest : List Nat)
    (hx : x.shape.reverse = (kw :: rest))
    (hw : w.shape = [n, kw]) :
    (bw_norm_linear g x w).1.shape = x.shape := by
  unfold bw_norm_linear
  have hwr : w.shape.reverse = [kw, n] := by rw [hw]; rfl
  rw [hx, hwr]
  simp [Tensor.mkShape]

theorem bw_norm_linear_snd_shape
    (g x w : Tensor) (n kw : Nat) (rest : List Nat)
    (hx : x.shape.reverse = (kw :: rest))
    (hw : w.shape = [n, kw]) :
    (bw_norm_linear g x w).2.shape = w.shape := by
  unfold bw_norm_linear
  have hwr : w.shape.reverse = [kw, n] := by rw [hw]; rfl
  rw [hx, hwr]
  simp [Tensor.mkShape]
/-! ### MoE: top-k routing — evalOp unfolding + applyNode lemmas

    `FW_topk_routing` has 1 input (`logits`) and 3 outputs
    `(routing_probs, routing_map, gate_scores)`, all sharing the shape
    `[l, e]`. Params encode `[top_k, numExperts]`. -/

theorem evalOp_fw_topk_routing
    (numParts rank top_k numExperts : Nat) (logits : Tensor) :
    evalOp numParts rank "OpName.FW_topk_routing" [top_k, numExperts] [logits] =
      [ (fw_topk_routing logits top_k numExperts).1,
        (fw_topk_routing logits top_k numExperts).2.1,
        (fw_topk_routing logits top_k numExperts).2.2 ] := by
  rfl

/-- `applyNode` for `FW_topk_routing` 1st output (`routing_probs`). -/
theorem applyNode_fw_topk_routing_fst_out
    (g : GraphDecl) (s : Store) (rank top_k numExperts : Nat)
    (logitsTid t1 t2 t3 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_topk_routing",
                    ins := [logitsTid], outs := [t1, t2, t3],
                    params := [top_k, numExperts] } t1 =
      (fw_topk_routing (s logitsTid) top_k numExperts).1 := by
  unfold applyNode
  rw [show ([logitsTid] : List Tid).map s = [s logitsTid] from rfl,
      evalOp_fw_topk_routing]
  change storeSet s
    [(t1, (fw_topk_routing (s logitsTid) top_k numExperts).1),
     (t2, (fw_topk_routing (s logitsTid) top_k numExperts).2.1),
     (t3, (fw_topk_routing (s logitsTid) top_k numExperts).2.2)] t1 = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `FW_topk_routing` 2nd output (`routing_map`). -/
theorem applyNode_fw_topk_routing_snd_out
    (g : GraphDecl) (s : Store) (rank top_k numExperts : Nat)
    (logitsTid t1 t2 t3 : Tid) (hne12 : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.FW_topk_routing",
                    ins := [logitsTid], outs := [t1, t2, t3],
                    params := [top_k, numExperts] } t2 =
      (fw_topk_routing (s logitsTid) top_k numExperts).2.1 := by
  unfold applyNode
  rw [show ([logitsTid] : List Tid).map s = [s logitsTid] from rfl,
      evalOp_fw_topk_routing]
  change storeSet s
    [(t1, (fw_topk_routing (s logitsTid) top_k numExperts).1),
     (t2, (fw_topk_routing (s logitsTid) top_k numExperts).2.1),
     (t3, (fw_topk_routing (s logitsTid) top_k numExperts).2.2)] t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne12]

/-- `applyNode` for `FW_topk_routing` 3rd output (`gate_scores`). -/
theorem applyNode_fw_topk_routing_thd_out
    (g : GraphDecl) (s : Store) (rank top_k numExperts : Nat)
    (logitsTid t1 t2 t3 : Tid) (hne13 : t1 ≠ t3) (hne23 : t2 ≠ t3) :
    applyNode g s { rank := rank, op := "OpName.FW_topk_routing",
                    ins := [logitsTid], outs := [t1, t2, t3],
                    params := [top_k, numExperts] } t3 =
      (fw_topk_routing (s logitsTid) top_k numExperts).2.2 := by
  unfold applyNode
  rw [show ([logitsTid] : List Tid).map s = [s logitsTid] from rfl,
      evalOp_fw_topk_routing]
  change storeSet s
    [(t1, (fw_topk_routing (s logitsTid) top_k numExperts).1),
     (t2, (fw_topk_routing (s logitsTid) top_k numExperts).2.1),
     (t3, (fw_topk_routing (s logitsTid) top_k numExperts).2.2)] t3 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t3) from hne13, show ¬ (t2 = t3) from hne23]

/-! ### MoE: all2all + grouped MM expert layer — evalOp unfolding + applyNode

    `FW_all2all_moe_gmm` has 5 inputs `(input, routing_probs, routing_map,
    w13, w2)` and 1 output `[l, h_model]`. Params encode
    `[num_experts, local_expert_start, local_expert_end, top_k,
      swiglu_limit_int]`.

    Note: `fw_all2all_moe_gmm` currently has a `zeroTensor` stub body — see
    Denote.lean. The evalOp/applyNode/shape lemmas here are real proofs and
    will keep working when the body is replaced with the full expansion. -/

theorem evalOp_fw_all2all_moe_gmm
    (numParts rank numExperts localExpertStart localExpertEnd topK
     swigluLimitInt : Nat)
    (input rp rm w13 w2 : Tensor) :
    evalOp numParts rank "OpName.FW_all2all_moe_gmm"
        [numExperts, localExpertStart, localExpertEnd, topK, swigluLimitInt]
        [input, rp, rm, w13, w2] =
      [ fw_all2all_moe_gmm input rp rm w13 w2 numExperts localExpertStart
          localExpertEnd topK ((swigluLimitInt : Nat) : Scalar) ] := by
  rfl

theorem applyNode_fw_all2all_moe_gmm_out
    (g : GraphDecl) (s : Store)
    (rank numExperts localExpertStart localExpertEnd topK swigluLimitInt : Nat)
    (inputTid rpTid rmTid w13Tid w2Tid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_all2all_moe_gmm",
                    ins := [inputTid, rpTid, rmTid, w13Tid, w2Tid],
                    outs := [outTid],
                    params := [numExperts, localExpertStart, localExpertEnd,
                               topK, swigluLimitInt] } outTid =
      fw_all2all_moe_gmm (s inputTid) (s rpTid) (s rmTid) (s w13Tid) (s w2Tid)
        numExperts localExpertStart localExpertEnd topK
        ((swigluLimitInt : Nat) : Scalar) := by
  unfold applyNode
  rw [show ([inputTid, rpTid, rmTid, w13Tid, w2Tid] : List Tid).map s =
            [s inputTid, s rpTid, s rmTid, s w13Tid, s w2Tid] from rfl,
      evalOp_fw_all2all_moe_gmm]
  change storeSet s
    [(outTid, fw_all2all_moe_gmm (s inputTid) (s rpTid) (s rmTid) (s w13Tid)
        (s w2Tid) numExperts localExpertStart localExpertEnd topK
        ((swigluLimitInt : Nat) : Scalar))] outTid = _
  unfold storeSet
  simp [List.find?]

/-! ### MoE shape preservation

    Both outputs of `fw_topk_routing` and `fw_all2all_moe_gmm` have shapes
    that depend only on the input shapes (`lDim`, `numExperts`, `hModel`),
    so the shape lemmas are direct rewrites of `Tensor.mkShape`. -/

/-- `fw_topk_routing` 1st output (`routing_probs`) has shape `[lDim, numExperts]`
    where `lDim = logits.shape.head`. -/
theorem fw_topk_routing_fst_shape
    (logits : Tensor) (top_k numExperts : Nat) (lDim : Nat)
    (hL : logits.shape.head? = some lDim) :
    (fw_topk_routing logits top_k numExperts).1.shape = [lDim, numExperts] := by
  unfold fw_topk_routing
  have hh : (logits.shape.head?).getD 0 = lDim := by rw [hL]; rfl
  simp [hh, Tensor.mkShape]

/-- `fw_topk_routing` 2nd output (`routing_map`) has shape `[lDim, numExperts]`. -/
theorem fw_topk_routing_snd_shape
    (logits : Tensor) (top_k numExperts : Nat) (lDim : Nat)
    (hL : logits.shape.head? = some lDim) :
    (fw_topk_routing logits top_k numExperts).2.1.shape = [lDim, numExperts] := by
  unfold fw_topk_routing
  have hh : (logits.shape.head?).getD 0 = lDim := by rw [hL]; rfl
  simp [hh, Tensor.mkShape]

/-- `fw_topk_routing` 3rd output (`gate_scores`) has the same shape as `logits`
    (it's the unmodified softmax output). -/
theorem fw_topk_routing_thd_shape
    (logits : Tensor) (top_k numExperts : Nat) :
    (fw_topk_routing logits top_k numExperts).2.2.shape = logits.shape := by
  unfold fw_topk_routing
  -- gate_scores = softmax logits, which preserves shape.
  unfold softmax
  cases h : logits.shape.reverse with
  | nil => simp
  | cons d rest => simp [Tensor.mkShape]

/-- `fw_all2all_moe_gmm` output has shape `[lDim, hModel]` where
    `lDim = input.shape.head` and `hModel = w2.shape.last`. -/
theorem fw_all2all_moe_gmm_shape
    (input rp rm w13 w2 : Tensor)
    (numExperts localExpertStart localExpertEnd topK : Nat)
    (swigluLimit : Scalar)
    (lDim hModel : Nat)
    (hL : input.shape.head? = some lDim)
    (hH : w2.shape.reverse.head? = some hModel) :
    (fw_all2all_moe_gmm input rp rm w13 w2 numExperts localExpertStart
        localExpertEnd topK swigluLimit).shape = [lDim, hModel] := by
  unfold fw_all2all_moe_gmm
  have hl : (input.shape.head?).getD 0 = lDim := by rw [hL]; rfl
  have hh : (w2.shape.reverse.head?).getD 0 = hModel := by rw [hH]; rfl
  show (zeroTensor [(input.shape.head?).getD 0,
                    (w2.shape.reverse.head?).getD 0]).shape = [lDim, hModel]
  rw [hl, hh]
  simp [zeroTensor, Tensor.mkShape]

/-! ### YOCO loss kernel: `inner_chunk_linear_cross_entropy`

    `FW_inner_chunk_ce` has 3 inputs `(x, w, y)` and 2 outputs `(losses, z_losses)`,
    both of shape `[L]` where `L = x.shape.head`.  Params layout is
    `[chunkSize, zLossScaleInt]` (where `chunkSize` is engineering-only and
    `zLossScaleInt` is the integer encoding of the bf16 z-loss scale; defaults to
    `0` when absent, matching the PM trace). -/

theorem evalOp_fw_inner_chunk_ce
    (numParts rank chunkSize zLossScaleInt : Nat) (x w y : Tensor) :
    evalOp numParts rank "OpName.FW_inner_chunk_ce" [chunkSize, zLossScaleInt]
        [x, w, y] =
      [ (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0)
            ((zLossScaleInt : Nat) : Scalar)).1,
        (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0)
            ((zLossScaleInt : Nat) : Scalar)).2 ] := by
  rfl

/-- `applyNode` for `FW_inner_chunk_ce` 1st output (`losses`). -/
theorem applyNode_fw_inner_chunk_ce_fst_out
    (g : GraphDecl) (s : Store) (rank chunkSize zLossScaleInt : Nat)
    (xTid wTid yTid t1 t2 : Tid) :
    applyNode g s { rank := rank, op := "OpName.FW_inner_chunk_ce",
                    ins := [xTid, wTid, yTid], outs := [t1, t2],
                    params := [chunkSize, zLossScaleInt] } t1 =
      (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid)
          (((s wTid).shape.head?).getD 0)
          ((zLossScaleInt : Nat) : Scalar)).1 := by
  unfold applyNode
  rw [show ([xTid, wTid, yTid] : List Tid).map s =
            [s xTid, s wTid, s yTid] from rfl,
      evalOp_fw_inner_chunk_ce]
  change storeSet s
    [(t1, (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid)
              (((s wTid).shape.head?).getD 0)
              ((zLossScaleInt : Nat) : Scalar)).1),
     (t2, (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid)
              (((s wTid).shape.head?).getD 0)
              ((zLossScaleInt : Nat) : Scalar)).2)] t1 = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for `FW_inner_chunk_ce` 2nd output (`z_losses`). -/
theorem applyNode_fw_inner_chunk_ce_snd_out
    (g : GraphDecl) (s : Store) (rank chunkSize zLossScaleInt : Nat)
    (xTid wTid yTid t1 t2 : Tid)
    (hne : t1 ≠ t2) :
    applyNode g s { rank := rank, op := "OpName.FW_inner_chunk_ce",
                    ins := [xTid, wTid, yTid], outs := [t1, t2],
                    params := [chunkSize, zLossScaleInt] } t2 =
      (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid)
          (((s wTid).shape.head?).getD 0)
          ((zLossScaleInt : Nat) : Scalar)).2 := by
  unfold applyNode
  rw [show ([xTid, wTid, yTid] : List Tid).map s =
            [s xTid, s wTid, s yTid] from rfl,
      evalOp_fw_inner_chunk_ce]
  change storeSet s
    [(t1, (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid)
              (((s wTid).shape.head?).getD 0)
              ((zLossScaleInt : Nat) : Scalar)).1),
     (t2, (fw_inner_chunk_ce (s xTid) (s wTid) (s yTid)
              (((s wTid).shape.head?).getD 0)
              ((zLossScaleInt : Nat) : Scalar)).2)] t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne]

/-- `fw_inner_chunk_ce` 1st output (`losses`) has shape `[lDim]` where
    `lDim = x.shape.head`. -/
theorem fw_inner_chunk_ce_fst_shape
    (x w y : Tensor) (vocab : Nat) (zLossScale : Scalar) (lDim : Nat)
    (hL : x.shape.head? = some lDim) :
    (fw_inner_chunk_ce x w y vocab zLossScale).1.shape = [lDim] := by
  unfold fw_inner_chunk_ce
  have hh : (x.shape.head?).getD 0 = lDim := by rw [hL]; rfl
  simp [hh, Tensor.mkShape]

/-- `fw_inner_chunk_ce` 2nd output (`z_losses`) has shape `[lDim]`. -/
theorem fw_inner_chunk_ce_snd_shape
    (x w y : Tensor) (vocab : Nat) (zLossScale : Scalar) (lDim : Nat)
    (hL : x.shape.head? = some lDim) :
    (fw_inner_chunk_ce x w y vocab zLossScale).2.shape = [lDim] := by
  unfold fw_inner_chunk_ce
  have hh : (x.shape.head?).getD 0 = lDim := by rw [hL]; rfl
  simp [hh, Tensor.mkShape]

end TrainVerify.Denote
