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

end TrainVerify.Denote
