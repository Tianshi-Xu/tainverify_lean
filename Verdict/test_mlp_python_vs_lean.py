"""Deterministic single-machine MLP test using the original MLP class.

We mirror the Lean interpreter's pseudo-random init for the single-machine path:
- randFloat(state) = ((state % 1000) / 1000.0) * 2 - 1
- makeMatrix(rows, cols, seed) uses seed + i + j per element
- dataloader tensor (tid 20) uses seed = tid + 7 = 27
- shared weight uses seed = 123 with shape 128 x 128

We load these values into the original genmodel.model.mlp.MLP (no PM shards) and
assert the loss matches the Lean run (737067.139072).
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import torch

# Allow import of genmodel.model.mlp when executed from repo root.
ROOT = Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT))

from genmodel.model.mlp import MLP


def rand_float(state: int) -> float:
    v = (state % 1000) / 1000.0
    return v * 2.0 - 1.0


def make_matrix(rows: int, cols: int, seed: int) -> np.ndarray:
    m = np.empty((rows, cols), dtype=np.float64)
    for i in range(rows):
        for j in range(cols):
            m[i, j] = rand_float(seed + i + j)
    return m


def sm_forward_with_original_mlp() -> float:
    torch.set_default_dtype(torch.float64)
    model = MLP(dim=128, nlayers=1)

    x_np = make_matrix(128, 128, seed=27)  # dataloader tid 20 => seed 27
    w_np = make_matrix(128, 128, seed=123)  # shared base weight

    with torch.no_grad():
        model.layers[0].weight.copy_(torch.from_numpy(w_np))

    x = torch.from_numpy(x_np)
    loss = model(x)
    return float(loss.item())


def main() -> None:
    sm = sm_forward_with_original_mlp()
    print(f"sm_loss={sm:.6f}")
    assert np.isclose(sm, 737067.139072, rtol=1e-9, atol=1e-6), "Loss differs from Lean"


if __name__ == "__main__":
    main()
