#!/usr/bin/env python3
"""Regenerate YOCO-MoE A0.4B using the archived CPU-compatible environment.

Run with the historical ``verdict`` Python environment. Output paths are
explicit so proof files in ``denote/yoco_goals`` are never overwritten.
"""

from __future__ import annotations

import argparse
import multiprocessing.pool
import os
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_AUTHORITY = Path(
    os.environ.get(
        "YOCO_A04B_AUTHORITY_DIR",
        "/home/argustest/.openclaw/workspace/iroha-tasks/trainverify-llm-train/from-egpu1/yoco_moe_a04b",
    )
)
LLM_TRAIN = Path(os.environ.get("YOCO_LLM_TRAIN_REPO", "/home/argustest/.openclaw/workspace/llm-train"))
NNSCALER = Path(os.environ.get(
    "YOCO_NNSCALER_REPO",
    "/home/argustest/.openclaw/workspace/iroha-tasks/trainverify-llm-train/nnscaler",
))
STUBS = NNSCALER.parent / "stubs"


def ensure_torch_recompile_limit(torch_module, entry_factory=None) -> bool:
    """Install Torch 2.6's missing Dynamo key; return whether it was added."""
    config = torch_module._dynamo.config._config
    if "recompile_limit" in config:
        return False
    if entry_factory is None:
        from torch.utils._config_module import Config, _ConfigEntry
        entry_factory = lambda: _ConfigEntry(Config(default=32, value_type=int))
    config["recompile_limit"] = entry_factory()
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--manifest-out", type=Path, required=True)
    parser.add_argument("--goals-out-dir", type=Path, required=True)
    args = parser.parse_args()

    for path in (STUBS, LLM_TRAIN / "llm", ROOT, ROOT / "Verdict"):
        sys.path.insert(0, str(path))
    # The PKLs were archived with this exact nnScaler revision; it defines the
    # bound methods referenced by dill (notably Sign2EmitRule.emit_self_getattr).
    sys.path.insert(0, str(NNSCALER))

    import triton_shim  # noqa: F401
    import torch
    # The archived graph only needs this import-time knob to exist. Torch 2.6
    # predates the public key used by the pinned llm-train checkout.
    ensure_torch_recompile_limit(torch)
    from triton.runtime.driver import driver as driver_config

    class CPUDriver:
        def get_benchmarker(self): return lambda *a, **kw: 0.0
        def get_current_target(self):
            class Target: backend = "cpu"
            return Target()
        def __getattr__(self, _name): return lambda *a, **kw: None

    type(driver_config).active = property(lambda _self: CPUDriver())

    class SequentialPool:
        def __init__(self, processes=None, initializer=None, initargs=()):
            if initializer:
                initializer(*initargs)
        def __enter__(self): return self
        def __exit__(self, *_args): return False
        def map(self, function, values): return [function(value) for value in values]

    multiprocessing.pool.Pool = SequentialPool
    import nnscaler_backend.build_graph as build_graph
    build_graph.Pool = SequentialPool

    import dill as pickle_dill
    import nnscaler_backend.load_graph as load_graph
    load_graph.pickle = pickle_dill

    from verdict.log import setup_logger
    setup_logger("ERROR")

    sm = DEFAULT_AUTHORITY / "sm_mgener.pkl"
    pm = DEFAULT_AUTHORITY / "pm_mgener.pkl"
    metadata = [DEFAULT_AUTHORITY / name for name in (
        "gen_args.json", "sm_mgener.json", "pm_mgener.json"
    )]
    sys.argv = [
        "graph_to_lean", "--sm-pkl", str(sm), "--pm-pkl", str(pm),
        "--out", str(args.out), "--module", "denote.GeneratedYOCOMoE",
        "--max-goals", "5", "--split-goals",
        "--goals-out-dir", str(args.goals_out_dir),
        "--manifest-out", str(args.manifest_out),
        "--llm-train-repo", str(LLM_TRAIN),
        "--llm-train-revision", "30b80f546d46aacbf8316c983550c50a56bcd1ac",
        "--nnscaler-repo", str(NNSCALER),
        "--nnscaler-revision", "1102e629ee68ab6f8f4a7c2e721ea894e5962131",
        "--sm-pkl-sha256", "cc29dde6f21bff4a8dabfdc1acb97f0043b8ae23d42c91fd7b95346b4facb0ce",
        "--pm-pkl-sha256", "bdadb2b52acf0c41b6aef4e1f16c4a64b62603eabb46bb1665296abc57082c58",
    ]
    for path in metadata:
        sys.argv.extend(["--metadata-json", str(path)])
    for name, digest in {
        "gen_args.json": "eec8988999798a9c37a4709c3303244a50a7bea667d028aa31fd71cb9f0ac3d3",
        "sm_mgener.json": "82e5c370a8434b1f27f25f86e650857ef6dbeb45549d00e8f771d3a1e3901400",
        "pm_mgener.json": "07be10e9547b40485e118390743f1584ce3ec3be84a0ea0d12ec597daa1fc3a6",
    }.items():
        sys.argv.extend(["--metadata-sha256", f"{name}={digest}"])

    os.chdir(ROOT)
    import graph_to_lean
    graph_to_lean.main()


if __name__ == "__main__":
    main()
