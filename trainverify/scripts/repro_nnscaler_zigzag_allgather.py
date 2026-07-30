#!/usr/bin/env python3
"""Two-GPU reproduction for nnScaler zigzag-shuffle + naive all-gather.

Run inside an nnScaler checkout with two visible GPUs:

    torchrun --standalone --nproc-per-node=2 \
      trainverify/scripts/repro_nnscaler_zigzag_allgather.py

The script uses nnScaler's real `shuffle_varlen` and runtime adapter
`all_gather`. It starts from a globally ordered tensor, splits it contiguously,
shuffles it with cp=2, then applies the exact all-gather implementation behind
`AllGatherPrim`.

Expected result for a nontrivial sequence:

* shuffle -> unshuffle -> all_gather equals the original full tensor;
* shuffle -> plain all_gather does NOT equal the original full tensor.

Exit 0 means the reproduction succeeded (the mismatch was observed and the
unshuffle control recovered the reference). Any unexpected equality or failure
of the control path exits nonzero.
"""

from __future__ import annotations

import importlib.util
import os
import sys
import types
from pathlib import Path

import torch
import torch.distributed as dist


def _load_module_from_source(module_name: str, path: Path):
    """Load one nnScaler source file without importing its heavyweight package.

    Importing `nnscaler.customized_ops.ring_attention.varlen_utils` normally
    executes `ring_attention/__init__.py`, which imports `flash_attn`. The
    reproduction itself needs neither flash-attn nor the rest of nnScaler, so a
    source checkout can set `NNSCALER_SOURCE_ROOT` and load the two audited files
    directly. On a fully provisioned GPU host the ordinary package imports are
    used instead.
    """
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {module_name} from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_source_root = os.environ.get("NNSCALER_SOURCE_ROOT")
if _source_root:
    root = Path(_source_root)
    _varlen = _load_module_from_source(
        "nnscaler_repro_varlen_utils",
        root / "nnscaler/customized_ops/ring_attention/varlen_utils.py",
    )

    # `collectives.py` itself is the audited implementation, but its timer,
    # device-group and async-handler imports pull in the full nnScaler package.
    # Install tiny API-compatible stubs so we still execute the REAL `all_gather`
    # function from that source file without unrelated flash-attn dependencies.
    class _Timer:
        def start(self, **_kwargs):
            return None

        def stop(self, **_kwargs):
            return None

    class _DeviceGroup:
        def get_group(self, _ranks):
            return dist.group.WORLD

    class _AsyncHandler:
        def submit(self, *_args, **_kwargs):
            raise AssertionError("reproduction uses synchronous all_gather")

    modules = {
        "nnscaler": types.ModuleType("nnscaler"),
        "nnscaler.runtime": types.ModuleType("nnscaler.runtime"),
        "nnscaler.runtime.device": types.ModuleType("nnscaler.runtime.device"),
        "nnscaler.profiler": types.ModuleType("nnscaler.profiler"),
        "nnscaler.profiler.timer": types.ModuleType("nnscaler.profiler.timer"),
        "nnscaler.runtime.executor": types.ModuleType("nnscaler.runtime.executor"),
    }
    setattr(modules["nnscaler.runtime.device"], "DeviceGroup", _DeviceGroup)
    setattr(modules["nnscaler.profiler.timer"], "CudaTimer", _Timer)
    setattr(modules["nnscaler.runtime.executor"], "AsyncCommHandler", _AsyncHandler)
    sys.modules.update(modules)

    _collectives = _load_module_from_source(
        "nnscaler_repro_collectives",
        root / "nnscaler/runtime/adapter/collectives.py",
    )
    shuffle_varlen = _varlen.shuffle_varlen
    unshuffle_varlen = _varlen.unshuffle_varlen
    all_gather = _collectives.all_gather
else:
    from nnscaler.customized_ops.ring_attention.varlen_utils import (
        shuffle_varlen,
        unshuffle_varlen,
    )
    from nnscaler.runtime.adapter.collectives import all_gather


def main() -> None:
    rank = int(os.environ["RANK"])
    local_rank = int(os.environ["LOCAL_RANK"])
    world_size = int(os.environ["WORLD_SIZE"])
    if world_size != 2:
        raise RuntimeError(f"this reproduction requires exactly 2 ranks, got {world_size}")

    if torch.cuda.is_available():
        torch.cuda.set_device(local_rank)
        device = torch.device("cuda", local_rank)
        backend = "nccl"
    else:
        # CPU fallback exercises the same nnScaler shuffle permutation and
        # runtime all_gather implementation through Gloo. It is useful when the
        # GPU hosts are temporarily unreachable; the final upstream report still
        # requests a CUDA/NCCL rerun on two real GPUs.
        device = torch.device("cpu")
        backend = "gloo"
    dist.init_process_group(backend)
    group = dist.group.WORLD
    ranks = tuple(range(world_size))

    # Two sequences, padded to a global length divisible by 2*cp_size. Distinct
    # scalar values expose the ownership order directly.
    full = torch.arange(16, dtype=torch.float32, device=device)
    cu_seqlens = torch.tensor([0, 8, 16], dtype=torch.int32, device=device)
    chunk = full.numel() // world_size
    local = full[rank * chunk : (rank + 1) * chunk].clone()

    shuffled = shuffle_varlen(local, cu_seqlens, list(ranks), group)
    naive = all_gather(shuffled, dim=0, ranks=ranks)

    restored_local = unshuffle_varlen(shuffled, cu_seqlens, list(ranks), group)
    control = all_gather(restored_local, dim=0, ranks=ranks)

    gathered_shards = [torch.empty_like(shuffled) for _ in ranks]
    dist.all_gather(gathered_shards, shuffled, group=group)

    mismatch = not torch.equal(naive, full)
    control_ok = torch.equal(control, full)
    local_roundtrip_ok = torch.equal(restored_local, local)

    if rank == 0:
        print("REFERENCE_FULL       =", full.cpu().tolist())
        for r, shard in enumerate(gathered_shards):
            print(f"SHUFFLED_RANK_{r}      =", shard.cpu().tolist())
        print("NAIVE_ALLGATHER      =", naive.cpu().tolist())
        print("UNSHUFFLE_ALLGATHER  =", control.cpu().tolist())
        print("NAIVE_EQUALS_FULL    =", not mismatch)
        print("CONTROL_EQUALS_FULL  =", control_ok)
        print("LOCAL_ROUNDTRIP_OK   =", local_roundtrip_ok)

    verdict = torch.tensor(
        [int(mismatch and control_ok and local_roundtrip_ok)],
        dtype=torch.int32,
        device=device,
    )
    dist.all_reduce(verdict, op=dist.ReduceOp.MIN, group=group)
    dist.destroy_process_group()
    if verdict.item() != 1:
        raise AssertionError(
            "reproduction failed: expected naive gather mismatch and correct "
            "unshuffle control on every rank"
        )


if __name__ == "__main__":
    main()
