from pathlib import Path


def test_joint_original_matmul_dv_reduction_witness():
    root = Path(__file__).resolve().parents[2]
    p = root/'iroha-tasks/trainverify-backward/MatmulDVReduceScatterWitness.lean'
    assert p.exists(), 'missing joint matmul second-output reduction witness'
    text = p.read_text()
    for name in ('caller_nonvacuous','run_success','caller_read','output_pointwise','contributions_distinct','not_average'):
        assert name in text
    assert not any(s in text for s in ('sorry','native_decide','axiom '))


def test_exact_two_matmul_dv_contributions_sum_then_chunk_cpu():
    import torch
    import ast
    import re
    shape = (1,2,2,2)
    contributions = []
    wrong_first = []
    for scale in (1,2):
        x = torch.arange(1,9,dtype=torch.float64).reshape(shape).requires_grad_()
        y = torch.arange(11,19,dtype=torch.float64).reshape(shape).requires_grad_()
        g = scale*torch.arange(3,11,dtype=torch.float64).reshape(shape)
        dx,dy = torch.autograd.grad(torch.matmul(x,y),(x,y),g)
        contributions.append(dy);wrong_first.append(dx)
    full = sum(contributions)
    result = full.chunk(2,dim=2)[[0,2].index(2)]
    reference = sum(t.chunk(2,dim=2)[1] for t in contributions)
    torch.testing.assert_close(result,reference,rtol=0,atol=0)
    root = Path(__file__).resolve().parents[2]
    text = (root/'iroha-tasks/trainverify-backward/MatmulDVReduceScatterWitness.lean').read_text()
    for name,t in [('dv0Expected',contributions[0]),('dv2Expected',contributions[1]),('outputExpected',result)]:
        table=ast.literal_eval(re.search(r'def '+name+r'.*?:= \((\[[^]]+\])',text)[1])
        assert t.flatten().tolist()==table
    assert not torch.equal(contributions[0],contributions[1])
    assert not torch.equal(result,reference/2)
    assert not torch.equal(result,sum(wrong_first).chunk(2,dim=2)[1])
    assert torch.count_nonzero(result)==4 and result.unique().numel()>1
