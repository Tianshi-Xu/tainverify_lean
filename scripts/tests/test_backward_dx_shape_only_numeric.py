"""CPU torch.nn.functional.linear controls for the Lean dX contract.

Not distributed execution, capture validation, or a Torch-refinement proof.
Independent saved-X values are legal for dX, not for dW reconstruction.
"""
import torch
from torch.nn.functional import linear


def backward(x,w,g):
    x=x.clone().requires_grad_();w=w.clone().requires_grad_()
    return torch.autograd.grad(linear(x,w),(x,w),grad_outputs=g)


def test_dp2_tp3_shape_only_dx_and_discriminating_controls():
    g=torch.arange(1,13,dtype=torch.float64).reshape(2,2,3)
    w=torch.stack([torch.arange(b,b+4,dtype=torch.float64) for b in (1,11,21)])
    x=torch.full((2,2,4),19.,dtype=torch.float64)
    full_dx,_=backward(x,w,g)
    local_xs=[torch.full((1,2,4),float(v),dtype=torch.float64) for v in (11,13,17)]
    local_gs=[g[1:2,:,j:j+1] for j in range(3)]
    local_ws=[w[j:j+1] for j in range(3)]
    grads=[backward(a,b,c) for a,b,c in zip(local_xs,local_ws,local_gs,strict=True)]
    reduced=torch.stack([a for a,_ in grads]).sum(0)
    assert torch.equal(reduced,full_dx[1:2])
    assert not torch.equal(reduced,full_dx[0:1])  # wrong DP unit
    assert not torch.equal(reduced/3,full_dx[1:2])  # invented mean
    assert not torch.equal(torch.stack([a for a,_ in grads[:-1]]).sum(0),full_dx[1:2])
    wrong_pairs=[backward(a,b,c)[0] for a,b,c in zip(local_xs,reversed(local_ws),local_gs,strict=True)]
    assert not torch.equal(torch.stack(wrong_pairs).sum(0),full_dx[1:2])
    _,reference_dw=backward(x[1:2],w,g[1:2])
    assert not torch.equal(torch.cat([b for _,b in grads]),reference_dw)
    shared=[backward(x[1:2],b,c)[1] for b,c in zip(local_ws,local_gs,strict=True)]
    assert torch.equal(torch.cat(shared),reference_dw)
