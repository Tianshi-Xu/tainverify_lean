/-
AttnPlainZeroWitness — rigorous negative-result witness (Worker #8, 2026-07-15).

CLAIM (proved below, zero sorry / zero user axiom):
Under the PLAIN `denoteGraph` denotation with `numParts = pm.numRanks = 2`, the
per-rank `FW_attn_sliding_window` output is the VALUE-INDEPENDENT all-zero tensor
(the AGENTS.md #24 "identity/zero model" — Denote.lean:3924-3927 `else` branch).

CONSEQUENCE:
`intermediateGoal_4696` (layer-0 attention output, 2-tp `[[2048,16,64]×2]`)
CANNOT be discharged over plain `denoteGraph`:
  * SM side (numParts = sm.numRanks = 1) = `fw_attn_varlen q k v …`  (value-faithful,
    input-DEPENDENT).
  * PM shards 7437/7438 (numParts = 2) = all-zero tensors  (input-INDEPENDENT).
  * reconstruction goal `sm 4696 = allGatherPrimDimN 0 2 0 [pm 7437, pm 7438]`
    would force `fw_attn_varlen q k v … = zeroTensor`, which is false for generic
    (nonzero) q/k/v — so the ∀-quantified `InitGoalHolds` is FALSE.

The value-FAITHFUL reconstruction of the very same node already exists and is
zero-sorry, but ONLY over the RING-ATTN denotation:
`applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair`
(Pattern_3.lean:3838), consumed by Goal_3 (Pattern_3.lean:4930) under
`denoteGraph_ringAttn`. See `~/ATTENTION_ANALYSIS.md`.

Per ground rules R2 / AGENTS.md #25 we do NOT patch Denote.lean; this file only
DOCUMENTS the plain-denotation gap with a checkable proof.
-/

import denote.Denote

set_option linter.style.longLine false

open TrainVerify.Denote

namespace TrainVerify.Denote

/-- The per-rank `FW_attn_sliding_window` evalOp with `numParts = 2` (the PM
    context-parallel case) is the value-INDEPENDENT all-zero tensor of the
    output shape `[lQ, qh, vd]` — regardless of the q/k/v inputs. This is the
    literal `else` branch of Denote.lean:3924-3927. -/
theorem evalOp_fw_attn_sliding_window_numParts2_zero
    (rank : Nat) (q k v cuQ cuK : Tensor) :
    evalOp 2 rank "OpName.FW_attn_sliding_window"
        [16, 4, 64, 64, 1, 512] [q, k, v, cuQ, cuK] =
      [Tensor.mkShape [(q.shape.head?).getD 0, 16, 64] (fun _ => 0)] := by
  rfl

/-- The all-zero attention shard is INDEPENDENT of its k/v inputs: feeding two
    DIFFERENT key/value tensors (same q, hence same output shape) yields the
    IDENTICAL output. This is the crisp statement that the plain-denotation PM
    attention output carries no attention information (value-lossy, AGENTS.md
    #24). A value-faithful `fw_attn_varlen` cannot satisfy this. -/
theorem attn_sliding_window_numParts2_value_independent
    (rank : Nat) (q k1 v1 k2 v2 cuQ cuK : Tensor) :
    evalOp 2 rank "OpName.FW_attn_sliding_window"
        [16, 4, 64, 64, 1, 512] [q, k1, v1, cuQ, cuK] =
    evalOp 2 rank "OpName.FW_attn_sliding_window"
        [16, 4, 64, 64, 1, 512] [q, k2, v2, cuQ, cuK] := by
  rw [evalOp_fw_attn_sliding_window_numParts2_zero,
      evalOp_fw_attn_sliding_window_numParts2_zero]

/-- By contrast, the SM side (`numParts = 1`) is the value-FAITHFUL
    `fw_attn_varlen`, which DOES depend on k/v. The two branches are therefore
    semantically distinct: no plain-denotation reconstruction can equate them. -/
theorem evalOp_fw_attn_sliding_window_numParts1_faithful
    (rank : Nat) (q k v cuQ cuK : Tensor) :
    evalOp 1 rank "OpName.FW_attn_sliding_window"
        [16, 4, 64, 64, 1, 512] [q, k, v, cuQ, cuK] =
      [fw_attn_varlen q k v cuQ cuK 16 4 64 64 (decide ((1 : Nat) ≠ 0)) 512] := by
  rfl

end TrainVerify.Denote
