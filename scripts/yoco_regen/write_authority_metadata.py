#!/usr/bin/env python3
"""Validate trusted production pickles and write authority metadata."""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
import platform
import sys
import subprocess
from pathlib import Path

from .comm_profile import profile_sha256
from .comp_profile import validate_artifact as validate_comp_profile_artifact
from .patch_llm_cc12_gemm import patch_source as patch_llm_gemm_source
from .patch_mgener_dump import patch_source

EXPECTED_LLM = "9a1be1d5fd1c063d80be82797692cdc7d23cfbef"
EXPECTED_NNS = "d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf"
ALLOWED_POLICY_IDENTITIES = {
    "__main__.main.<locals>.autodist_wrapper",
    "__mp_main__.main.<locals>.autodist_wrapper",
    "nnscaler_train.main.<locals>.autodist_wrapper",
}


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def git_head(path: Path) -> str:
    return subprocess.check_output(
        ["git", "-C", str(path), "rev-parse", "HEAD"], text=True
    ).strip()


def git_status(path: Path) -> list[str]:
    return subprocess.check_output(
        ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"],
        text=True,
    ).splitlines()


def git_blob(path: Path, revision: str, relative_path: str) -> bytes:
    return subprocess.check_output(
        ["git", "-C", str(path), "show", f"{revision}:{relative_path}"]
    )


def git_archive_digest(path: Path, revision: str) -> str:
    archive = subprocess.check_output(
        ["git", "-C", str(path), "archive", "--format=tar", revision]
    )
    return digest_bytes(archive)


def digest_bytes(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def atomic_json(path: Path, value) -> None:
    tmp = path.with_suffix(path.suffix + f".tmp.{os.getpid()}")
    try:
        with tmp.open("w", encoding="utf-8") as handle:
            json.dump(value, handle, indent=2, sort_keys=True)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(tmp, path)
        path.chmod(0o644)
    finally:
        tmp.unlink(missing_ok=True)


def configure_imports(llm_train: Path, nnscaler_repo: Path):
    sys.path[:0] = [str(nnscaler_repo), str(llm_train / "llm")]
    import nnscaler

    imported = Path(nnscaler.__file__).resolve()
    if not imported.is_relative_to(nnscaler_repo):
        raise RuntimeError(f"imported nnScaler is outside pinned checkout: {imported}")
    return nnscaler


def validate_graph(mg, kind: str, plan: int, receipt: dict):
    devices = getattr(mg, "devices", None)
    runtime_ndevs = getattr(mg, "runtime_ndevs", None)
    if (
        not isinstance(devices, (list, tuple))
        or any(type(device) is not int for device in devices)
        or list(devices) != list(range(plan))
        or type(runtime_ndevs) is not int
        or runtime_ndevs != plan
    ):
        raise RuntimeError(f"{kind} topology mismatch")
    if receipt != {
        "policy": receipt.get("policy"),
        "plan_ngpus": plan,
        "runtime_ngpus": plan,
        "pkl_sha256": receipt.get("pkl_sha256"),
        "patched_parallel_py_sha256": receipt.get("patched_parallel_py_sha256"),
        "patched_llm_gemm_py_sha256": receipt.get("patched_llm_gemm_py_sha256"),
        "comm_profile_sha256": receipt.get("comm_profile_sha256"),
        "comp_profile_sha256": receipt.get("comp_profile_sha256"),
        "dp_solver_extension_sha256": receipt.get("dp_solver_extension_sha256"),
        "canonicalized_comment_count": receipt.get("canonicalized_comment_count"),
        "canonicalized_code_count": receipt.get("canonicalized_code_count"),
    }:
        raise RuntimeError(f"{kind} receipt has unexpected fields or values")
    for field in ("canonicalized_comment_count", "canonicalized_code_count"):
        if type(receipt[field]) is not int or receipt[field] < 0:
            raise RuntimeError(f"{kind} receipt has invalid {field}")
    llm_patch_hash = receipt.get("patched_llm_gemm_py_sha256")
    if (
        not isinstance(llm_patch_hash, str)
        or len(llm_patch_hash) != 64
        or any(c not in "0123456789abcdef" for c in llm_patch_hash)
    ):
        raise RuntimeError(f"{kind} receipt has invalid llm GEMM patch hash")
    policy = receipt.get("policy")
    if policy not in ALLOWED_POLICY_IDENTITIES:
        raise RuntimeError(f"{kind} receipt is not from llm-train autodist_wrapper")
    def node_signature(node) -> str:
        signature = getattr(node, "signature", None)
        return signature if isinstance(signature, str) and signature else type(node).__name__

    counts = collections.Counter(node_signature(node) for node in mg.execplan.graph.nodes())
    minimum = {
        "nnscaler.customized_ops.ring_attention.maybe_shuffle.wrap_maybe_shuffle": 1,
        "nnscaler.customized_ops.ring_attention.maybe_shuffle.wrap_maybe_unshuffle": 25,
        "nnscaler.customized_ops.ring_attention.sliding_window_attn.wrap_sliding_window_attn_func": 12,
        "nnscaler.customized_ops.ring_attention.zigzag_allgather_attn_varlen.wrap_zigzag_allgather_attn_varlen_func": 12,
        "arch.all2all_moe.topk_routing": 24,
        "arch.all2all_moe.nnscaler_all2all_moe_gmm": 24,
        "nnscaler.runtime.function.stack": 2,
    }
    for signature, count in minimum.items():
        if counts[signature] < count:
            raise RuntimeError(
                f"{kind} signature count below structural minimum for {signature}: "
                f"expected at least {count}, got {counts[signature]}"
            )
    shapes = set()
    for node in mg.execplan.graph.nodes():
        for tensor in list(node.inputs()) + list(node.outputs()):
            shape = getattr(tensor, "shape", None)
            if shape is not None:
                shapes.add(tuple(shape))
    if not any(
        shape and type(shape[0]) is int and shape[0] == 4096
        for shape in shapes
    ):
        raise RuntimeError(f"{kind} does not contain the expected flattened seq4096 axis")
    return counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--authority-dir", type=Path, required=True)
    parser.add_argument("--llm-train", type=Path, required=True)
    parser.add_argument("--nnscaler", type=Path, required=True)
    parser.add_argument("--comm-profile", type=Path, required=True)
    parser.add_argument("--comp-profile", type=Path, required=True)
    parser.add_argument("--dp-solver-extension", type=Path, required=True)
    parser.add_argument("--trainverify-revision", required=True)
    parser.add_argument("--trust-local-pickle", action="store_true")
    args = parser.parse_args()
    if not args.trust_local_pickle:
        parser.error("--trust-local-pickle is required because dill input is executable")
    authority = args.authority_dir.resolve()
    llm_train = args.llm_train.resolve()
    nnscaler_repo = args.nnscaler.resolve()
    trainverify_root = Path(__file__).resolve().parents[2]
    if (
        len(args.trainverify_revision) != 40
        or any(character not in "0123456789abcdef" for character in args.trainverify_revision)
        or git_head(trainverify_root) != args.trainverify_revision
        or git_status(trainverify_root)
    ):
        raise RuntimeError("TrainVerify private materialization mismatch")
    if git_head(llm_train) != EXPECTED_LLM or git_head(nnscaler_repo) != EXPECTED_NNS:
        raise RuntimeError("source revision mismatch")
    if git_status(llm_train) != [" M llm/kernel/gemm.py"]:
        raise RuntimeError("llm-train generation clone has unexpected modifications")
    dp_solver_extension = args.dp_solver_extension.resolve()
    expected_dp_solver = (
        nnscaler_repo / "nnscaler" / "autodist" /
        ("dp_solver" + __import__("sysconfig").get_config_var("EXT_SUFFIX"))
    ).resolve()
    if dp_solver_extension != expected_dp_solver or not dp_solver_extension.is_file():
        raise RuntimeError("unexpected dp solver extension path")
    if list((nnscaler_repo / "nnscaler" / "autodist").glob("dp_solver*.so")) != [
        dp_solver_extension
    ] or (nnscaler_repo / "build").exists():
        raise RuntimeError("unexpected dp solver build artifacts")
    if git_status(nnscaler_repo) != [" M nnscaler/parallel.py"]:
        raise RuntimeError("nnScaler generation clone has unexpected modifications")
    clean_parallel = git_blob(
        nnscaler_repo, EXPECTED_NNS, "nnscaler/parallel.py").decode("utf-8")
    expected_patched_hash = digest_bytes(patch_source(clean_parallel).encode("utf-8"))
    if digest(nnscaler_repo / "nnscaler" / "parallel.py") != expected_patched_hash:
        raise RuntimeError("nnScaler generation patch does not match canonical patch")
    clean_llm_gemm = git_blob(
        llm_train, EXPECTED_LLM, "llm/kernel/gemm.py").decode("utf-8")
    expected_llm_gemm_hash = digest_bytes(
        patch_llm_gemm_source(clean_llm_gemm).encode("utf-8"))
    if digest(llm_train / "llm" / "kernel" / "gemm.py") != expected_llm_gemm_hash:
        raise RuntimeError("llm GEMM generation patch does not match canonical patch")
    nnscaler = configure_imports(llm_train, nnscaler_repo)
    authority_dp_solver = authority / "nnscaler_dp_solver.so"
    if not authority_dp_solver.is_file() or not os.path.samestat(
        dp_solver_extension.stat(), authority_dp_solver.stat()
    ):
        raise RuntimeError("authority dp solver is not the private-build inode")
    dp_solver_hash = digest(dp_solver_extension)
    comm_profile_hash = profile_sha256(args.comm_profile.resolve())
    comp_profile = args.comp_profile.resolve()
    if comp_profile != authority / "comp_profile.json":
        raise RuntimeError("unexpected computation profile artifact path")
    comp_profile_hash = validate_comp_profile_artifact(comp_profile)
    import dill
    import torch

    patched_parallel_hash = expected_patched_hash
    gpu_inventory = []
    for index in range(torch.cuda.device_count()):
        properties = torch.cuda.get_device_properties(index)
        gpu_inventory.append({
            "index": index,
            "name": properties.name,
            "total_memory_bytes": properties.total_memory,
            "compute_capability": list(torch.cuda.get_device_capability(index)),
        })
    if len(gpu_inventory) != 2:
        raise RuntimeError(f"production authority requires exactly two GPUs, got {len(gpu_inventory)}")
    driver_versions = set(
        subprocess.check_output(
            [
                "nvidia-smi", "--query-gpu=driver_version",
                "--format=csv,noheader,nounits",
            ],
            text=True,
        ).splitlines()
    )
    if len(driver_versions) != 1:
        raise RuntimeError(f"inconsistent NVIDIA driver inventory: {sorted(driver_versions)}")
    hardware = {
        "cuda_runtime_version": torch.version.cuda,
        "nccl_version": list(torch.cuda.nccl.version()),
        "nvidia_driver_version": next(iter(driver_versions)),
        "gpu_inventory": gpu_inventory,
        "trainverify_regen_commit": args.trainverify_revision,
        "comm_profile_sha256": comm_profile_hash,
        "comp_profile_sha256": comp_profile_hash,
    }
    hardware_hash = hashlib.sha256(
        json.dumps(
            hardware, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
        ).encode("utf-8")
    ).hexdigest()
    records = {}
    worlds = {}
    for kind, plan in (("sm", 1), ("pm", 2)):
        pkl = authority / f"{kind}_mgener.pkl"
        receipt_path = authority / f"{kind}_mgener.pkl.receipt.json"
        if not pkl.is_file() or not receipt_path.is_file():
            raise FileNotFoundError(pkl if not pkl.is_file() else receipt_path)
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        if receipt.get("pkl_sha256") != digest(pkl):
            raise RuntimeError(f"{kind} receipt/pickle hash mismatch")
        if receipt.get("patched_parallel_py_sha256") != patched_parallel_hash:
            raise RuntimeError(f"{kind} receipt/source hash mismatch")
        if receipt.get("patched_llm_gemm_py_sha256") != expected_llm_gemm_hash:
            raise RuntimeError(f"{kind} receipt/llm GEMM source hash mismatch")
        if receipt.get("comm_profile_sha256") != comm_profile_hash:
            raise RuntimeError(f"{kind} receipt/communication profile hash mismatch")
        if receipt.get("comp_profile_sha256") != comp_profile_hash:
            raise RuntimeError(f"{kind} receipt/computation profile hash mismatch")
        if receipt.get("dp_solver_extension_sha256") != dp_solver_hash:
            raise RuntimeError(f"{kind} receipt/dp solver extension hash mismatch")
        if receipt.get("plan_ngpus") != plan or receipt.get("runtime_ngpus") != plan:
            raise RuntimeError(f"{kind} receipt topology mismatch")
        if receipt.get("policy") not in ALLOWED_POLICY_IDENTITIES:
            raise RuntimeError(f"{kind} receipt policy mismatch")
        with pkl.open("rb") as handle:
            mg = dill.load(handle)
        counts = validate_graph(mg, kind, plan, receipt)
        records[kind] = {
            "authority": True,
            "policy": "pas_autodist",
            "plan_ngpus": plan,
            "runtime_ngpus": plan,
            "zero_group_size": plan,
            "cp_size_runtime": plan,
            "ep_size_runtime": plan,
            "cp_size_codegen_sentinel": 0,
            "pkl_sha256": digest(pkl),
            "receipt_sha256": digest(receipt_path),
            "patched_parallel_py_sha256": patched_parallel_hash,
            "patched_llm_gemm_py_sha256": expected_llm_gemm_hash,
            "comm_profile_sha256": comm_profile_hash,
            "comp_profile_sha256": comp_profile_hash,
            "dp_solver_extension_sha256": dp_solver_hash,
            "canonicalized_comment_count": receipt["canonicalized_comment_count"],
            "canonicalized_code_count": receipt["canonicalized_code_count"],
            "node_count": len(mg.execplan.graph.nodes()),
            "signature_counts": dict(sorted(counts.items())),
        }
        worlds[kind] = {
            "model_name": "YOCO-MoE-A0.4B",
            "num_dp": 1, "num_tp": plan, "num_pp": 1, "num_mb": 1, "gbs": 1,
            "num_layers": 12, "num_heads": 16, "hidden_size": 1024,
            "seqlen": 4096, "n_activated_experts": 8, "n_routed_experts": 64,
        }
    source_hashes = {
        "nnscaler/fixed_commit_archive.tar": git_archive_digest(
            nnscaler_repo, EXPECTED_NNS),
        "nnscaler/setup.py": digest_bytes(git_blob(nnscaler_repo, EXPECTED_NNS, "setup.py")),
        "nnscaler/autodist/dp_solver.cpp": digest_bytes(
            git_blob(nnscaler_repo, EXPECTED_NNS, "nnscaler/autodist/dp_solver.cpp")),
        "nnscaler/autodist/dp_solver.h": digest_bytes(
            git_blob(nnscaler_repo, EXPECTED_NNS, "nnscaler/autodist/dp_solver.h")),
        "llm/arch/model.py": digest_bytes(
            git_blob(llm_train, EXPECTED_LLM, "llm/arch/model.py")),
        "llm/pcs/all2all_moe.yaml": digest_bytes(
            git_blob(llm_train, EXPECTED_LLM, "llm/pcs/all2all_moe.yaml")),
        "llm/kernel/gemm.py.patched_cc12_fallback": expected_llm_gemm_hash,
        "nnscaler/parallel.py.patched": patched_parallel_hash,
        "nnscaler/customized_ops/ring_attention/maybe_shuffle.py": digest_bytes(
            git_blob(
                nnscaler_repo, EXPECTED_NNS,
                "nnscaler/customized_ops/ring_attention/maybe_shuffle.py")),
    }
    metadata = {
        "authority": True,
        "model": "YOCO-MoE-A0.4B",
        "max_seq_len": 4096,
        "layers": 24,
        "cross_layers": 12,
        "precision": "fp32",
        "partition_constraints": "llm/pcs/all2all_moe.yaml",
        "llm_train_commit": EXPECTED_LLM,
        "llm_hardware_patch": "cc12_generic_triton_fallback_v1",
        "nnscaler_commit": EXPECTED_NNS,
        "nnscaler_version": nnscaler.__version__,
        "torch_version": torch.__version__,
        "python_version": platform.python_version(),
        "host": platform.node(),
        "dp_solver_extension_sha256": dp_solver_hash,
        "comp_profile_sha256": comp_profile_hash,
        "hardware_sha256": hardware_hash,
        **hardware,
        "source_sha256": source_hashes,
        "sm": records["sm"],
        "pm": records["pm"],
    }
    atomic_json(authority / "sm_mgener.json", worlds["sm"])
    atomic_json(authority / "pm_mgener.json", worlds["pm"])
    atomic_json(authority / "sm_provenance.json", records["sm"])
    atomic_json(authority / "pm_provenance.json", records["pm"])
    atomic_json(authority / "gen_args.json", metadata)
    print(json.dumps(metadata, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
