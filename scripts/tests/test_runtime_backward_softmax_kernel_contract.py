from pathlib import Path


def test_joint_softmax_witness_contract():
    root = Path(__file__).resolve().parents[2]
    p = root / 'iroha-tasks/trainverify-backward/SoftmaxReadWitness.lean'
    assert p.exists(), 'missing joint softmax successful-run witness'
    text = p.read_text()
    for name in ('caller_nonvacuous','run_success','saved_nonconstant','seed_nonconstant',
                 'pointwise_derivative','not_cotangent','not_saved','not_missing_dot'):
        assert name in text
    assert not any(s in text for s in ('sorry', 'axiom ', 'native_decide'))


def test_exact_nonconstant_logits_witness_cpu():
    import torch
    x = torch.tensor([2.,3.,2.,3.],dtype=torch.float64).log().reshape(1,2,1,2).requires_grad_()
    g = torch.tensor([1.,3.,2.,6.],dtype=torch.float64).reshape(x.shape)
    p = torch.softmax(x,dim=-1)
    dx, = torch.autograd.grad(p,x,g)
    expected = torch.tensor([-12/25,12/25,-24/25,24/25],dtype=torch.float64).reshape(x.shape)
    torch.testing.assert_close(dx,expected,rtol=1e-14,atol=1e-14)
    torch.testing.assert_close(p,torch.tensor([2/5,3/5,2/5,3/5],dtype=torch.float64).reshape(x.shape))
    assert torch.count_nonzero(dx)==4 and dx[0,0,0,0]!=dx[0,1,0,0]
    assert not torch.allclose(dx,p*g)
    assert not torch.allclose(dx,x.detach()) and not torch.allclose(dx,g)
    wrong_p=torch.softmax(p.detach(),dim=-1)
    wrong=wrong_p*(g-(wrong_p*g).sum(dim=-1,keepdim=True))
    assert not torch.allclose(dx,wrong)  # storing output instead of INPUT logits
