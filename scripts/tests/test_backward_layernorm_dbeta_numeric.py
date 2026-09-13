"""CPU source-operator check: dβ needs gradient values and shapes, not X values."""
import pytest


def test_layernorm_dbeta_dp_tp_without_saved_value_equality():
    torch=pytest.importorskip('torch')
    torch.manual_seed(37)
    dtype=torch.float64
    D,T,B,S,H=3,3,2,3,2
    x=torch.randn(B*D,S*T,H,dtype=dtype,requires_grad=True)
    gamma=torch.randn(H,dtype=dtype,requires_grad=True)
    beta=torch.randn(H,dtype=dtype,requires_grad=True)
    g=torch.arange(x.numel(),dtype=dtype).reshape_as(x)/7+1
    y=torch.nn.functional.layer_norm(x,(H,),gamma,beta,1e-5)
    _,dgamma,dbeta=torch.autograd.grad(y,(x,gamma,beta),g)
    torch.testing.assert_close(dbeta,g.sum((0,1)))
    local=[]
    for u in range(D):
        for r in range(T):
            gu=g[u*B:(u+1)*B,r*S:(r+1)*S]
            xu=(torch.randn(B,S,H,dtype=dtype)+u+r*3).requires_grad_()
            ga=torch.randn(H,dtype=dtype,requires_grad=True)
            be=torch.randn(H,dtype=dtype,requires_grad=True)
            out=torch.nn.functional.layer_norm(xu,(H,),ga,be,1e-5)
            _,_,db=torch.autograd.grad(out,(xu,ga,be),gu)
            torch.testing.assert_close(db,gu.sum((0,1)))
            local.append(db)
    total=torch.stack(local).sum(0)
    torch.testing.assert_close(total,dbeta)
    assert not torch.allclose(total/(D*T),dbeta)
    assert not torch.allclose(torch.stack(local[:-1]).sum(0),dbeta)
    wrong=torch.stack(local[:T]+local[:T]+local[2*T:]).sum(0)
    assert not torch.allclose(wrong,dbeta)
    # The same relaxation is not valid for dgamma.
    alternate=torch.randn_like(x).requires_grad_()
    out=torch.nn.functional.layer_norm(alternate,(H,),gamma,beta,1e-5)
    different_dgamma,unchanged_dbeta=torch.autograd.grad(out,(gamma,beta),g)
    torch.testing.assert_close(unchanged_dbeta,dbeta)
    assert not torch.allclose(different_dgamma,dgamma)
