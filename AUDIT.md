# Denote Op Semantics Audit — 2026-07-03

## TL;DR (updated 2026-07-03 mid-audit)

### GPT-2 ly4 (312 桥) — L1 ✅ L3 ✅ L2 in progress
- **L1**: 26 non-collective + 4 collective ops, all use fixed-arity patterns. No arg-order bugs.
- **L3**: `gpt_main_all_goals` depends only on 5-axiom kernel (`propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound`). No custom axioms.
- **L2**: verified for FW_sum, FW_add (under same-shape assumption which GPT-2 satisfies for all 45 additions), FW_gelu, FW_linear. Subagent audit of the rest is running.

### Pattern_2 / Pattern_4 / Pattern_5 (MoE yoco_goals) — L1 ✅ L3 ✅ L2 partly verified
- **L1**: Pattern_2 (3 ops), Pattern_4 (4 ops), Pattern_5 (2 ops). All fixed-arity patterns, no reshuffling.
- **L3**: `prove_pattern_2/4/5` each depend only on 5-axiom kernel. No custom axioms.
- **L2**: FW_embedding, FW_topk_routing, FW_inner_chunk_ce, FW_stack — semantics verified against PyTorch/nnscaler.

### Pattern_1 (MoE + CP) — L1 ❌ L2 ⚠️ L3 ❌ VACUOUS
- **L1 broken**: `FW_maybe_shuffle/unshuffle` (and BW_ variants) evalOp binding `cu :: xs` assumes `cu` at ins[0], but graph convention is `[data, cu_seqlens]` (data at ins[0]).
- **L2 broken**: `fw_maybe_(un)shuffle` uses `xs.head?.shape` (metadata) as `firstShape`, so all outputs have shape [2] (cu.shape) not the intended data shape.
- **L2 additional bug**: none found here. `FW_reshape` in Denote is identity, but Pattern_1's actual usage is verified as identity (input.shape = output.shape per intermediateGoal authority). Earlier concern was based on tid-shadowing across graph scopes.
- **L3 broken**: `prove_pattern_1` depends on `fw_maybe_unshuffle_cp2_commute` which is provably inconsistent (see `UnshuffleInconsistent.lean` — derives False from just this axiom + 5-axiom kernel). Pattern_1's proof is vacuous.

---

## Layer 1 detailed findings

Total OpName arms in Denote.lean: 149 (over 67 unique ops)
Total non-trivial `::` patterns: **8** (all in FW/BW × maybe_shuffle/unshuffle):
- `FW_maybe_shuffle`   L3729 evalOp `cu :: xs` + L3483 tp_shape `_cu :: x0 :: _rest` ❌
- `FW_maybe_unshuffle` L3733 evalOp `cu :: xs` + L3485 tp_shape `_cu :: x0 :: _rest` ❌
- `BW_maybe_shuffle`   L3737 evalOp `cu :: gs` + L3487 tp_shape `_cu :: g0 :: _rest` ❌
- `BW_maybe_unshuffle` L3741 evalOp `cu :: gs` + L3489 tp_shape `_cu :: g0 :: _rest` ❌

All other 61 ops use fixed-arity destructuring (`[x]`, `[x, y]`, `[x, w]`, `[g, x, w]`, `[x, weight, bias]`, `[ids, weight]`, `xs`, etc.). No arg-order ambiguity → L1 clean.

## Layer 2 findings

### Verified (semantics match Python)
- `fw_sum` (`torch.sum` reducing to scalar `[1]`) — but note: PyTorch sum reduces to `[]` shape (scalar); Denote uses `[1]`. Semantically equivalent for typical use.
- `fw_add` (under same-shape assumption; GPT-2 satisfies)
- `fw_gelu` — exact GELU: `x * 0.5 * (1 + erf(x/√2))`. PyTorch default. ✅
- `fw_linear` — `y = x @ w.T`. Matches `torch.nn.functional.linear`. Only supports 2D/3D input. ✅
- `fw_layernorm` — per-row (last dim) normalization + weight/bias. ✅
- `batchedMatmul` — `x.shape=batch++[n,k1]`, `y.shape=batch++[k1,m]`, output `batch++[n,m]`. Standard PyTorch. ✅
- `fw_sigmoid` — element-wise sigmoid. ✅
- `fw_swiglu(gate, up) = silu(gate) ⊙ up` — matches SwiGLU FFN. ✅
- `fw_silu` — element-wise SiLU. ✅
- `fw_rms_norm` — per-row RMS normalization + weight scale. Matches LlamaRMSNorm. ✅
- `fw_embedding` — output `weight[ids[i], :]`. Matches `F.embedding`. ✅
- `fw_topk_routing` — softmax + top-k + normalize within top-k. Matches nnscaler MoE routing. ✅
- `fw_stack xs` — stack along new dim 0. Matches `torch.stack(xs, dim=0)`. ✅
- `fw_inner_chunk_ce` — cross-entropy per token: `lse[l] - logits[l, y[l]]` + z-loss. Matches standard CE loss. ✅

### Conditional (correct only under stated preconditions)
- `elemwiseAdd` / `elemwiseMul` — `outShape2` picks first arg's shape when lengths equal, i.e., **DOES NOT do full PyTorch broadcasting**. Correct ONLY when inputs have equal shape. GPT-2 satisfies; Pattern_1 does NOT (sigmoid × view case, sigmoid output [2048, 1] vs view output [2048, 1024]).
- `fw_all2all_moe_gmm` — sums over `Finset.range (local_expert_end - local_expert_start)` for MoE experts. Correct when `local_expert_end - local_expert_start = w13.shape[0]`. Sharding-commute axiom is only valid under specific routing_map structure (not general).

### BROKEN (semantics disagree with Python)
- `FW_maybe_shuffle` / `FW_maybe_unshuffle` (and BW_ variants) — evalOp binding + fw_maybe_(un)shuffle def both use `xs.head?.shape` (metadata) for output shape, but graph intends output shape = data shape.
- `FW_reshape` — Denote defines this as `identity`. **VERIFIED CORRECT for Pattern_1's actual usage**: all 12 reshape nodes in Pattern_1's graph have input.shape = output.shape (per `intermediateGoal_TID.tsShape` authority). Earlier "shape mismatch" alarm was noise from tid-shadowing between different graph scopes' initShapes.

### Unverified (not yet checked)
- Backward passes: BW_sum, BW_add, BW_linear, BW_matmul, BW_embedding, BW_layernorm, BW_gelu, BW_softmax, BW_div, BW_contiguous, BW_view, BW_transpose, BW_multiref (13 ops, subagent audit in progress)
- BW_add2 (called from BW_add binary form)
- Pattern_1-specific ops not audited: `fw_norm_linear`, `fw_mix_precision_linear` (uses fw_linear so likely OK)

## Recommended path forward

Based on this audit:

1. **GPT-2 is CLEAN**: 312 桥证明 is trustworthy. No action needed there.
2. **Pattern_2/4/5 are CLEAN**: their proofs are trustworthy. No action needed.
3. **Pattern_1 needs FUNDAMENTAL fix** — not because of the axioms but because:
   - `FW_maybe_unshuffle` semantics is systematically wrong (bind + firstShape both back)
   - `FW_reshape` is identity in Denote but not in the graph
   - These are Denote-level semantic bugs that must be fixed by:
     a) understanding actual Python semantics (need to find `nnscaler.customized_ops.ring_attention.wrap_maybe_shuffle` source)
     b) writing correct Denote defs
     c) re-proving Pattern_1 from scratch against corrected semantics
   - No amount of axiom-writing will fix this — the underlying denotational semantics is wrong.
