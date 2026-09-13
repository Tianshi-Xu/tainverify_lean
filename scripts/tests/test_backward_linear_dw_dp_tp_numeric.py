"""CPU operator check: DP SUM per output-row TP shard, then gather dim0.

Input values are constructed, not asserted as an established original forward
saved-X bridge. This is not a distributed runtime/storage refinement.
"""
import pytest


def test_linear_dw_dp_sum_then_tp_output_row_gather_requires_saved_x():
    torch = pytest.importorskip('torch')
    rng = torch.Generator().manual_seed(857)
    D, T, B, S, I, O = 3, 2, 2, 3, 4, 5
    rand = lambda *shape: torch.randn(*shape, dtype=torch.float64, generator=rng)
    x = rand(B * D, S, I)
    w = rand(O * T, I)
    g = rand(B * D, S, O * T)

    def dw(xv, wv, gv):
        weight = wv.detach().clone().requires_grad_()
        y = torch.nn.functional.linear(xv, weight)
        return torch.autograd.grad(y, weight, gv)[0]

    expected = dw(x, w, g)
    pieces = [[] for _ in range(T)]
    for r in range(T):
        wr = w[r * O:(r + 1) * O]
        for u in range(D):
            xu = x[u * B:(u + 1) * B]
            gu = g[u * B:(u + 1) * B, :, r * O:(r + 1) * O]
            local = dw(xu, wr, gu)
            pieces[r].append(local)
            # W values are irrelevant to dW, but its O/I shape is not.
            torch.testing.assert_close(local, dw(xu, wr + 7, gu))
            assert not torch.allclose(local, dw(xu.flip(-1), wr, gu))
            wrong_u = (u + 1) % D
            assert not torch.allclose(local, dw(x[wrong_u * B:(wrong_u + 1) * B], wr, gu))
        full_shard = torch.stack(pieces[r]).sum(0)
        torch.testing.assert_close(full_shard, expected[r * O:(r + 1) * O])
        assert not torch.allclose(full_shard / D, expected[r * O:(r + 1) * O])
        assert not torch.allclose(torch.stack(pieces[r][:-1]).sum(0), full_shard)
    reconstructed = torch.cat([torch.stack(rows).sum(0) for rows in pieces], dim=0)
    torch.testing.assert_close(reconstructed, expected)
    assert not torch.allclose(reconstructed, torch.cat([torch.stack(rows).sum(0) for rows in reversed(pieces)], dim=0))
