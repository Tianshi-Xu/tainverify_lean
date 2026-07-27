/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.ChunkGatherDim0

/-!
# A view that changes nothing

Several generated `FW_reshape` / `FW_view` nodes target exactly the shape their
input already has. On the PM side of the MoE branch this happens because each
rank reshapes its own `[2048, 512]` shard to `[2048, 512]`. Recognising these as
the identity avoids having to prove a commutation lemma for them.
-/

namespace TrainVerify.Denote

-- `fw_view` to a tensor's own shape is the identity.
set_option maxRecDepth 1000000 in
theorem fw_view_self (x : Tensor) (sh : Shape) (hx : x.shape = sh) :
    fw_view sh x = x := by
  unfold fw_view
  refine Tensor.ext (by rw [hx]; rfl) ?_
  intro idx hidx
  -- LHS is a `mkShape` whose value function is `fun i => valAt x i.1`, so the
  -- read at `idx` is literally `valAt x idx`.
  have hb : idx < prodShape (Tensor.mkShape sh (fun i => valAt x i.1)).shape := hidx
  rw [valAt_of_lt _ _ hb]
  rfl

end TrainVerify.Denote
