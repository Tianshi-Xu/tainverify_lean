#  Copyright (c) Microsoft Corporation.
#  Licensed under the MIT License.

from enum import Enum

"""If an operator is injected (not an aligned operator), and is uni-directonal (can only appear in either forward or backward pass), then set `None` for the isfw field."""


class OpName(Enum):
    # UNI DIRECTIONAL OPERATOR

    DATALOADER = ("dataloader", True)

    # BI DIRECTIONAL OPERATOR

    FW_linear = ("linear", True)
    BW_linear = ("linear", False)

    FW_sum = ("sum", True)
    BW_sum = ("sum", False)

    FW_add = ("add", True)
    BW_add = ("add", False)

    FW_transpose = ("transpose", True)
    BW_transpose = ("transpose", False)

    FW_layernorm = ("layernorm", True)
    BW_layernorm = ("layernorm", False)

    FW_self_attention = ("self_attention", True)
    BW_self_attention = ("self_attention", False)

    FW_dropout = ("dropout", True)
    BW_dropout = ("dropout", False)

    FW_feedforward = ("feedforward", True)
    BW_feedforward = ("feedforward", False)

    FW_identity = ("identity", True)
    BW_identity = ("identity", False)

    FW_multiref = ("multiref", True)
    BW_multiref = ("multiref", False)

    FW_embedding = ("embedding", True)
    BW_embedding = ("embedding", False)

    FW_float = ("float", True)
    BW_float = ("float", False)

    FW_to = ("to", True)
    BW_to = ("to", False)

    FW_contiguous = ("contiguous", True)
    BW_contiguous = ("contiguous", False)

    FW_create_mask = ("create_mask", True)
    BW_create_mask = ("create_mask", False)

    FW_pow = ("pow", True)
    BW_pow = ("pow", False)

    FW_mean = ("mean", True)
    BW_mean = ("mean", False)

    FW_rsqrt = ("rsqrt", True)
    BW_rsqrt = ("rsqrt", False)

    FW_mul = ("mul", True)
    BW_mul = ("mul", False)

    FW_view = ("view", True)
    BW_view = ("view", False)

    FW_apply_rotary_emb = ("apply_rotary_emb", True)
    BW_apply_rotary_emb = ("apply_rotary_emb", False)

    FW_matmul = ("matmul", True)
    BW_matmul = ("matmul", False)

    FW_div = ("div", True)
    BW_div = ("div", False)

    FW_apply_mask = ("apply_mask", True)
    BW_apply_mask = ("apply_mask", False)

    FW_softmax = ("softmax", True)
    BW_softmax = ("softmax", False)

    FW_silu = ("silu", True)
    BW_silu = ("silu", False)

    FW_gelu = ("gelu", True)
    BW_gelu = ("gelu", False)
    
    FW_nns_moe_gate = ("gate_fw", True)
    BW_nns_moe_gate = ("gate_fw", False)
    
    FW_nns_moe_gmm = ("nnscaler_moe_gmm", True)
    BW_nns_moe_gmm = ("nnscaler_moe_gmm", False)

    # ── YOCO-MoE-A0.4B novel ops (added 2026-06-30 for llm-train audit) ──

    # P0: scalar / elementwise primitives
    FW_sigmoid = ("sigmoid", True)
    BW_sigmoid = ("sigmoid", False)
    FW_rms_norm = ("rms_norm_func", True)
    BW_rms_norm = ("rms_norm_func", False)
    FW_swiglu = ("swiglu", True)
    BW_swiglu = ("swiglu", False)

    # P1 RoPE: chunk-style rotary embedding (llm-train arch.rotary_embedding)
    FW_rotary_embedding = ("rotary_embedding_func", True)
    BW_rotary_embedding = ("rotary_embedding_func", False)

    # P1 D-1: zigzag CP sequence shuffle (varlen)
    FW_maybe_shuffle = ("wrap_maybe_shuffle", True)
    BW_maybe_shuffle = ("wrap_maybe_shuffle", False)
    FW_maybe_unshuffle = ("wrap_maybe_unshuffle", True)
    BW_maybe_unshuffle = ("wrap_maybe_unshuffle", False)

    # P1 D-2: varlen attention with causal + (optional) sliding window
    # sliding_window_attn_func (self-attn, window=(W,0)) and
    # zigzag_allgather_attn_varlen_func (cross-attn, window=(-1,-1)) share the
    # same fw_attn_varlen Lean op; the difference is just (causal, windowLeft)
    # params.
    FW_attn_sliding_window = ("wrap_sliding_window_attn_func", True)
    BW_attn_sliding_window = ("wrap_sliding_window_attn_func", False)
    FW_attn_zigzag = ("wrap_zigzag_allgather_attn_varlen_func", True)
    BW_attn_zigzag = ("wrap_zigzag_allgather_attn_varlen_func", False)

    # P2-A linear variants (datawise equivalent to FW_linear but with a
    # distinct op name in the nnscaler trace; share the same denotation)
    FW_mix_precision_linear = ("mix_precision_linear", True)
    BW_mix_precision_linear = ("mix_precision_linear", False)
    FW_per_head_mix_precision_linear = ("per_head_mix_precision_linear", True)
    BW_per_head_mix_precision_linear = ("per_head_mix_precision_linear", False)
    FW_norm_linear = ("norm_linear", True)
    BW_norm_linear = ("norm_linear", False)

    # P2-B MoE: top-k routing + fused MoE GMM
    FW_topk_routing = ("topk_routing", True)
    BW_topk_routing = ("topk_routing", False)
    FW_all2all_moe_gmm = ("nnscaler_all2all_moe_gmm", True)
    BW_all2all_moe_gmm = ("nnscaler_all2all_moe_gmm", False)

    # P2-C: vocab-parallel chunked cross-entropy loss
    FW_inner_chunk_ce = ("inner_chunk_linear_cross_entropy", True)
    BW_inner_chunk_ce = ("inner_chunk_linear_cross_entropy", False)

    # ── nnscaler dataloader-side Python helper ops ──
    # IRPyFunc cells (e.g. `getitem` extracting tensor entries from the sample
    # dict). Treated as identity-like / not subject to audit equivalence checks
    # (these are pre-graph data shuffling, not learned transformations).
    FW_pyfunc = ("pyfunc", True)
    BW_pyfunc = ("pyfunc", False)

    # ── nnscaler graph-internal ops not yet covered (no Lean denotation yet) ──
    # Reshape: like view but allowed non-contiguous; same input/output element
    # count, shape change only. Stack: concat-along-new-axis of N tensors.
    FW_reshape = ("reshape", True)
    BW_reshape = ("reshape", False)
    FW_stack = ("stack", True)
    BW_stack = ("stack", False)
    

    # COMMUNICATION PRIM

    # comm primitives are shared for fw and bw, so set None for isfw
    ChunkPrim = ("ChunkPrim", None)
    MovePrim = ("MovePrim", None)
    AllGatherPrim = ("AllGatherPrim", None)
    AllReducePrim = ("AllReducePrim", None)
    BroadcastPrim = ("BroadcastPrim", None)
    AllToAllPrim = ("AllToAllPrim", None)
    IdentityPrim = ("IdentityPrim", None)

    # VERDICT OP

    LOCAL_GRAD_ACCUM = ("local_grad_accumulation", None)
    CROSS_DP_WRED = ("reducer", None)
