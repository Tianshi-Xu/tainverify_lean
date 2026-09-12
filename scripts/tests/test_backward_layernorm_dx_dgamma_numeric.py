"""CPU operator check of the actual sequence-within-batch LN partition.

This exercises the input contract needed after the forward saved-X value bridge;
it does not claim that bridge or distributed Torch runtime refinement is proved.
"""
import pytest


def test_layernorm_dx_dgamma_dp_tp_requires_corresponding_saved_values():
    torch = pytest.importorskip('torch')
    rng = torch.Generator().manual_seed(431)
    D, T, B, S, H = 2, 3, 2, 3, 5
    rand = lambda *shape: torch.randn(*shape, dtype=torch.float64, generator=rng)
    x = rand(D * B, T * S, H)
    g = rand(D * B, T * S, H)
    gamma, beta = rand(H), rand(H)

    def backward(saved, cotangent, weight=gamma):
        saved = saved.detach().clone().requires_grad_()
        weight = weight.detach().clone().requires_grad_()
        bias = beta.detach().clone().requires_grad_()
        y = torch.nn.functional.layer_norm(saved, (H,), weight, bias, 1e-5)
        return torch.autograd.grad(y, (saved, weight, bias), cotangent)

    dx, dg, db = backward(x, g)
    contributions = []
    for u in range(D):
        for r in range(T):
            partition = (slice(u * B, (u + 1) * B), slice(r * S, (r + 1) * S))
            lx, lg, lb = backward(x[partition], g[partition])
            torch.testing.assert_close(lx, dx[partition])
            contributions.append(lg)
            # Altering X is not the dβ-only relaxation for dX or dgamma.
            wrong_x, wrong_g, same_b = backward(x[partition].flip(-1), g[partition])
            assert not torch.allclose(wrong_x, lx)
            assert not torch.allclose(wrong_g, lg)
            torch.testing.assert_close(same_b, lb)
            # Equal shapes do not certify DP ownership or G/X correspondence.
            wrong_dp = ((u + 1) % D) * B
            other_x = x[wrong_dp:wrong_dp + B, r * S:(r + 1) * S]
            wx, wg, _ = backward(other_x, g[partition])
            assert not torch.allclose(wx, lx)
            assert not torch.allclose(wg, lg)
            # Gamma replication is required for dX (unlike dgamma/dbeta).
            wx, same_g, same_b = backward(x[partition], g[partition], gamma + 1)
            assert not torch.allclose(wx, lx)
            torch.testing.assert_close(same_g, lg)
            torch.testing.assert_close(same_b, lb)
    total = torch.stack(contributions).sum(0)
    torch.testing.assert_close(total, dg)
    torch.testing.assert_close(db, g.sum((0, 1)))
    assert not torch.allclose(total / (D * T), dg)
    assert not torch.allclose(torch.stack(contributions[:-1]).sum(0), dg)
    duplicate_dp = contributions[:T] + contributions[:T]
    assert not torch.allclose(torch.stack(duplicate_dp).sum(0), dg)
