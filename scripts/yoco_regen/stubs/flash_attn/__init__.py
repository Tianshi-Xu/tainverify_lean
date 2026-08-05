"""Shape-only flash-attn stubs for CPU graph tracing."""
import torch
def flash_attn_func(q,*_a,**_kw): return torch.zeros_like(q)
def flash_attn_varlen_func(q,*_a,**kw):
    out=torch.zeros_like(q)
    if kw.get('return_attn_probs') or kw.get('return_lse'):
        return out, torch.zeros(q.shape[1],q.shape[0],dtype=torch.float32,device=q.device), None
    return out
def flash_attn_with_kvcache(q,*_a,**_kw): return torch.zeros_like(q)
