"""Shape-only low-level flash-attn stubs."""
import torch
def _fwd(q,*_a,**_kw):
    return torch.zeros_like(q), torch.zeros(q.shape[1],q.shape[0],dtype=torch.float32,device=q.device)
def _bwd(*args,**_kw):
    ts=[x for x in args if isinstance(x,torch.Tensor)]
    return tuple(torch.zeros_like(x) for x in ts[:3])
_flash_attn_forward=_flash_attn_varlen_forward=_fwd
_flash_attn_backward=_flash_attn_varlen_backward=_bwd
