"""Shape-only grouped GEMM for CPU tracing."""
import torch
def gmm(a,b,batch_sizes=None,trans_a=False,trans_b=False,*_args,**_kwargs):
    n=b.shape[-2] if trans_b else b.shape[-1]
    return torch.zeros((a.shape[0],n),dtype=a.dtype,device=a.device)
