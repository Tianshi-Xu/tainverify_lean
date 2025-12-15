from __future__ import annotations

import torch
from torch import Tensor, nn

# ---------------------------------------------------------------------------
# Model dimensions copied from Verdict/scripts/analyze_graph.sh.
# ---------------------------------------------------------------------------

ROW_WIDTH: int = 128
EXPECTED_VALUE: int = 98767132430434304


# ---------------------------------------------------------------------------
# Dataset construction (LoadData).
# ---------------------------------------------------------------------------

DATASET: Tensor = torch.arange(ROW_WIDTH * ROW_WIDTH, dtype=torch.int64).view(ROW_WIDTH, ROW_WIDTH)


# ---------------------------------------------------------------------------
# Deterministic weight matrices derived from the Lean model.
# ---------------------------------------------------------------------------

def build_weight_matrix0() -> Tensor:
    """First linear layer: weight_{i,j} = i + j + 1."""
    in_idx = torch.arange(ROW_WIDTH, dtype=torch.int64).view(-1, 1)
    out_idx = torch.arange(ROW_WIDTH, dtype=torch.int64).view(1, -1)
    return in_idx + out_idx + 1


def build_weight_matrix1() -> Tensor:
    """Second linear layer: weight_{i,j} = 2*j + 3*i + 1 (matches Lean encoding)."""
    in_idx = torch.arange(ROW_WIDTH, dtype=torch.int64).view(-1, 1)
    out_idx = torch.arange(ROW_WIDTH, dtype=torch.int64).view(1, -1)
    return 2 * out_idx + 3 * in_idx + 1


# ---------------------------------------------------------------------------
# Torch module implementing the two linear stages.
# ---------------------------------------------------------------------------

class TwoLayerMLP(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        weight0 = build_weight_matrix0()
        weight1 = build_weight_matrix1()
        self.register_buffer("weight0", weight0, persistent=False)
        self.register_buffer("weight1", weight1, persistent=False)

    def forward(self, row: Tensor) -> Tensor:
        """Apply the two linear stages to a single 128-wide row."""
        row_vec = row.to(dtype=torch.int64).view(-1)
        stage0 = torch.matmul(row_vec, self.weight0)
        stage1 = torch.matmul(stage0, self.weight1)
        return stage1


MODEL = TwoLayerMLP()


# ---------------------------------------------------------------------------
# Workflow evaluation mirroring the Lean sequential semantics.
# ---------------------------------------------------------------------------

def sequential_eval(data: Tensor) -> int:
    """Single-device execution: apply both linear layers, then Sum."""
    total = torch.tensor(0, dtype=torch.int64)
    for row in data:
        total += MODEL(row).sum()
    return int(total.item())


BASELINE_VALUE: int = sequential_eval(DATASET)


def main() -> None:
    print(f"baseline_value={BASELINE_VALUE}")
    if BASELINE_VALUE != EXPECTED_VALUE:
        raise SystemExit(
            "Computed value does not match the Lean proof artifact: "
            f"expected {EXPECTED_VALUE}"
        )


if __name__ == "__main__":
    main()
