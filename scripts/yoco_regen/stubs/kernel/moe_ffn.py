"""Shape-only fused MoE FFN for CPU tracing."""
import torch
TIMING_LOGGER=lambda *_a,**_kw:None
def fused_moe_ffn(hidden_states,*_args,**_kwargs): return torch.zeros_like(hidden_states)
