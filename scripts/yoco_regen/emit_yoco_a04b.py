#!/usr/bin/env python3
"""Emit an atomic YOCO-MoE Lean refresh snapshot from trusted authority artifacts."""
from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import multiprocessing.pool
import os
import shutil
import stat
import subprocess
import sys
from pathlib import Path

from scripts.yoco_regen.safe_cleanup import create_owned_stage, cleanup_owned_stage

ROOT = Path(__file__).resolve().parents[2]
STUBS = Path(__file__).resolve().parent / "stubs"
LLM_REVISION = "9a1be1d5fd1c063d80be82797692cdc7d23cfbef"
NNSCALER_REVISION = "d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf"
ALLOWED_POLICY_IDENTITIES = {
    "__main__.main.<locals>.autodist_wrapper",
    "__mp_main__.main.<locals>.autodist_wrapper",
    "nnscaler_train.main.<locals>.autodist_wrapper",
}
WORLD_KEYS = {
    "model_name", "num_dp", "num_tp", "num_pp", "num_mb", "gbs",
    "num_layers", "num_heads", "hidden_size", "seqlen",
    "n_activated_experts", "n_routed_experts",
}
AUTHORITY_NAMES = (
    "sm_mgener.pkl", "pm_mgener.pkl", "gen_args.json",
    "comm_profile_intra_2.json",
    "sm_mgener.json", "pm_mgener.json",
    "sm_provenance.json", "pm_provenance.json",
    "sm_mgener.pkl.receipt.json", "pm_mgener.pkl.receipt.json",
)
RECEIPT_KEYS = {
    "policy", "plan_ngpus", "runtime_ngpus", "pkl_sha256",
    "patched_parallel_py_sha256", "patched_llm_gemm_py_sha256",
    "comm_profile_sha256",
}
RECORD_KEYS = {
    "authority", "policy", "plan_ngpus", "runtime_ngpus", "zero_group_size",
    "cp_size_runtime", "ep_size_runtime", "cp_size_codegen_sentinel",
    "pkl_sha256", "receipt_sha256", "patched_parallel_py_sha256",
    "patched_llm_gemm_py_sha256", "node_count", "signature_counts",
    "comm_profile_sha256",
}
HARDWARE_KEYS = {
    "cuda_runtime_version", "nccl_version", "nvidia_driver_version",
    "gpu_inventory", "trainverify_regen_commit",
    "comm_profile_sha256",
}
GPU_KEYS = {"index", "name", "total_memory_bytes", "compute_capability"}
META_KEYS = {
    "authority", "model", "max_seq_len", "layers", "cross_layers",
    "precision", "partition_constraints", "llm_train_commit",
    "llm_hardware_patch", "nnscaler_commit", "nnscaler_version",
    "torch_version", "cuda_runtime_version", "nccl_version",
    "nvidia_driver_version", "gpu_inventory", "python_version", "host",
    "trainverify_regen_commit", "comm_profile_sha256", "hardware_sha256",
    "source_sha256", "sm", "pm",
}


def _strict_int(value, *, minimum: int = 0) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= minimum


def _is_lower_hex(value, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(c in "0123456789abcdef" for c in value)
    )


def _require_exact_keys(value, expected: set[str], label: str) -> None:
    if not isinstance(value, dict) or set(value) != expected:
        actual = set(value) if isinstance(value, dict) else type(value).__name__
        raise RuntimeError(f"{label} schema mismatch: {actual}")


def validate_receipt_schema(receipt: dict, plan: int) -> None:
    _require_exact_keys(receipt, RECEIPT_KEYS, "receipt")
    if (
        receipt["policy"] not in ALLOWED_POLICY_IDENTITIES
        or not _strict_int(receipt["plan_ngpus"], minimum=1)
        or not _strict_int(receipt["runtime_ngpus"], minimum=1)
        or receipt["plan_ngpus"] != plan
        or receipt["runtime_ngpus"] != plan
        or not _is_lower_hex(receipt["pkl_sha256"], 64)
        or not _is_lower_hex(receipt["patched_parallel_py_sha256"], 64)
        or not _is_lower_hex(receipt["patched_llm_gemm_py_sha256"], 64)
        or not _is_lower_hex(receipt["comm_profile_sha256"], 64)
    ):
        raise RuntimeError("receipt schema values mismatch")


def validate_record_schema(record: dict, plan: int) -> None:
    _require_exact_keys(record, RECORD_KEYS, "provenance record")
    if (
        record["authority"] is not True
        or record["policy"] != "pas_autodist"
        or any(
            not _strict_int(record[key], minimum=1) or record[key] != plan
            for key in (
            "plan_ngpus", "runtime_ngpus", "zero_group_size",
            "cp_size_runtime", "ep_size_runtime",
        ))
        or not _strict_int(record["cp_size_codegen_sentinel"], minimum=0)
        or record["cp_size_codegen_sentinel"] != 0
        or not _is_lower_hex(record["pkl_sha256"], 64)
        or not _is_lower_hex(record["receipt_sha256"], 64)
        or not _is_lower_hex(record["patched_parallel_py_sha256"], 64)
        or not _is_lower_hex(record["patched_llm_gemm_py_sha256"], 64)
        or not _is_lower_hex(record["comm_profile_sha256"], 64)
        or not _strict_int(record["node_count"], minimum=1)
        or not isinstance(record["signature_counts"], dict)
        or not record["signature_counts"]
        or any(
            not isinstance(key, str) or not key
            or not _strict_int(count, minimum=0)
            for key, count in record["signature_counts"].items()
        )
    ):
        raise RuntimeError("provenance record schema values mismatch")


def validate_hardware_schema(hardware: dict) -> None:
    _require_exact_keys(hardware, HARDWARE_KEYS, "hardware metadata")
    inventory = hardware["gpu_inventory"]
    if not isinstance(inventory, list) or len(inventory) != 2:
        raise RuntimeError("GPU inventory must contain exactly two devices")
    normalized = []
    for expected_index, gpu in enumerate(inventory):
        _require_exact_keys(gpu, GPU_KEYS, "GPU inventory entry")
        capability = gpu["compute_capability"]
        if (
            not _strict_int(gpu["index"], minimum=0)
            or gpu["index"] != expected_index
            or not isinstance(gpu["name"], str) or not gpu["name"]
            or not _strict_int(gpu["total_memory_bytes"], minimum=1)
            or not isinstance(capability, list) or len(capability) != 2
            or not _strict_int(capability[0], minimum=8)
            or not _strict_int(capability[1], minimum=0)
        ):
            raise RuntimeError("GPU inventory values mismatch")
        normalized.append((gpu["name"], gpu["total_memory_bytes"], capability))
    if normalized[0] != normalized[1]:
        raise RuntimeError("GPU inventory is not homogeneous")
    for key in ("cuda_runtime_version", "nvidia_driver_version"):
        value = hardware[key]
        if not isinstance(value, str) or not value or any(c not in "0123456789." for c in value):
            raise RuntimeError(f"hardware metadata {key} is invalid")
    nccl = hardware["nccl_version"]
    if (
        not isinstance(nccl, list) or len(nccl) != 3
        or any(not _strict_int(part, minimum=0) for part in nccl)
    ):
        raise RuntimeError("hardware metadata NCCL version is invalid")
    if not _is_lower_hex(hardware["trainverify_regen_commit"], 40):
        raise RuntimeError("hardware metadata regen commit is invalid")
    if not _is_lower_hex(hardware["comm_profile_sha256"], 64):
        raise RuntimeError("hardware metadata communication profile hash is invalid")


def hardware_sha256(hardware: dict) -> str:
    validate_hardware_schema(hardware)
    payload = json.dumps(
        hardware, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def validate_expected_hardware(hardware: dict, expected_sha256: str) -> None:
    if not _is_lower_hex(expected_sha256, 64):
        raise RuntimeError("trusted hardware SHA-256 is malformed")
    actual = hardware_sha256(hardware)
    if not hmac.compare_digest(actual, expected_sha256):
        raise RuntimeError("trusted hardware SHA-256 mismatch")


def validate_meta_schema(meta: dict) -> None:
    _require_exact_keys(meta, META_KEYS, "gen_args")
    if (
        meta["authority"] is not True
        or meta["model"] != "YOCO-MoE-A0.4B"
        or not _strict_int(meta["max_seq_len"], minimum=1)
        or meta["max_seq_len"] != 4096
        or not _strict_int(meta["layers"], minimum=1)
        or meta["layers"] != 24
        or not _strict_int(meta["cross_layers"], minimum=1)
        or meta["cross_layers"] != 12
        or meta["precision"] != "fp32"
        or meta["partition_constraints"] != "llm/pcs/all2all_moe.yaml"
        or meta["llm_train_commit"] != LLM_REVISION
        or meta["nnscaler_commit"] != NNSCALER_REVISION
        or meta["llm_hardware_patch"] != "cc12_generic_triton_fallback_v1"
        or any(
            not isinstance(meta[key], str) or not meta[key]
            for key in ("nnscaler_version", "torch_version", "python_version", "host")
        )
        or not _is_lower_hex(meta["hardware_sha256"], 64)
        or not isinstance(meta["source_sha256"], dict)
    ):
        raise RuntimeError("gen_args schema values mismatch")
    hardware = {key: meta[key] for key in HARDWARE_KEYS}
    validate_hardware_schema(hardware)
    if not hmac.compare_digest(meta["hardware_sha256"], hardware_sha256(hardware)):
        raise RuntimeError("gen_args hardware SHA-256 mismatch")
    validate_record_schema(meta["sm"], 1)
    validate_record_schema(meta["pm"], 2)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def digest_bytes(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def git_head(path: Path) -> str:
    return subprocess.check_output(
        ["git", "-C", str(path), "rev-parse", "HEAD"], text=True
    ).strip()


def git_clean(path: Path) -> bool:
    return not subprocess.check_output(
        ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"],
        text=True,
    ).strip()


def git_blob(path: Path, revision: str, relative_path: str) -> bytes:
    return subprocess.check_output(
        ["git", "-C", str(path), "show", f"{revision}:{relative_path}"]
    )


def validate_source_checkouts(llm_train: Path, nnscaler: Path) -> None:
    if git_head(llm_train) != LLM_REVISION or git_head(nnscaler) != NNSCALER_REVISION:
        raise RuntimeError("source revision mismatch")
    if not git_clean(llm_train) or not git_clean(nnscaler):
        raise RuntimeError("source checkout is dirty")


def materialize_source(source: Path, revision: str, target: Path) -> None:
    subprocess.run(
        ["git", "clone", "--quiet", "--no-hardlinks", str(source), str(target)],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(target), "checkout", "--quiet", revision],
        check=True,
    )
    if git_head(target) != revision or not git_clean(target):
        raise RuntimeError(f"private source materialization failed: {target}")


def secure_copy_authority(source: Path, target: Path) -> None:
    """Copy from one locked directory inode; never reopen source paths by name."""
    target.mkdir(mode=0o700)
    directory_fd = os.open(source, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for name in AUTHORITY_NAMES:
            source_fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=directory_fd)
            try:
                info = os.fstat(source_fd)
                if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid():
                    raise PermissionError(f"untrusted authority inode: {name}")
                if stat.S_IMODE(info.st_mode) & 0o022:
                    raise PermissionError(f"authority inode is group/world writable: {name}")
                destination_fd = os.open(
                    target / name, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o400)
                try:
                    with os.fdopen(os.dup(source_fd), "rb") as src, os.fdopen(
                        os.dup(destination_fd), "wb") as dst:
                        shutil.copyfileobj(src, dst, length=1 << 20)
                        dst.flush()
                        os.fsync(dst.fileno())
                finally:
                    os.close(destination_fd)
            finally:
                os.close(source_fd)
    finally:
        os.close(directory_fd)


def validate_authority(
    authority: Path,
    llm_train: Path,
    nnscaler: Path,
    expected_hardware_sha256: str,
):
    files = {name: authority / name for name in AUTHORITY_NAMES}
    meta = json.loads(files["gen_args.json"].read_text(encoding="utf-8"))
    validate_meta_schema(meta)
    validate_expected_hardware(
        {key: meta[key] for key in HARDWARE_KEYS}, expected_hardware_sha256,
    )
    if meta.get("authority") is not True:
        raise RuntimeError("gen_args.json is not marked as production authority")
    if meta.get("llm_train_commit") != LLM_REVISION:
        raise RuntimeError("gen_args llm-train revision mismatch")
    if meta.get("nnscaler_commit") != NNSCALER_REVISION:
        raise RuntimeError("gen_args nnScaler revision mismatch")
    if meta.get("llm_hardware_patch") != "cc12_generic_triton_fallback_v1":
        raise RuntimeError("gen_args llm hardware patch mismatch")

    from scripts.yoco_regen.patch_mgener_dump import patch_source
    from scripts.yoco_regen.patch_llm_cc12_gemm import (
        patch_source as patch_llm_gemm_source,
    )
    from scripts.yoco_regen.comm_profile import profile_sha256

    comm_profile_hash = profile_sha256(files["comm_profile_intra_2.json"])
    if comm_profile_hash != meta["comm_profile_sha256"]:
        raise RuntimeError("communication profile hash mismatch")

    clean_parallel = git_blob(
        nnscaler, NNSCALER_REVISION, "nnscaler/parallel.py").decode("utf-8")
    patched_parallel_hash = digest_bytes(patch_source(clean_parallel).encode("utf-8"))
    clean_llm_gemm = git_blob(
        llm_train, LLM_REVISION, "llm/kernel/gemm.py").decode("utf-8")
    patched_llm_gemm_hash = digest_bytes(
        patch_llm_gemm_source(clean_llm_gemm).encode("utf-8"))
    expected_source_hashes = {
        "llm/arch/model.py": digest_bytes(
            git_blob(llm_train, LLM_REVISION, "llm/arch/model.py")),
        "llm/pcs/all2all_moe.yaml": digest_bytes(
            git_blob(llm_train, LLM_REVISION, "llm/pcs/all2all_moe.yaml")),
        "llm/kernel/gemm.py.patched_cc12_fallback": patched_llm_gemm_hash,
        "nnscaler/parallel.py.patched": patched_parallel_hash,
        "nnscaler/customized_ops/ring_attention/maybe_shuffle.py": digest_bytes(
            git_blob(
                nnscaler, NNSCALER_REVISION,
                "nnscaler/customized_ops/ring_attention/maybe_shuffle.py")),
    }
    if meta.get("source_sha256") != expected_source_hashes:
        raise RuntimeError("authority source hash ledger mismatch")

    for kind, plan in (("sm", 1), ("pm", 2)):
        record = meta.get(kind, {})
        actual = sha256(files[f"{kind}_mgener.pkl"])
        if record.get("pkl_sha256") != actual:
            raise RuntimeError(f"{kind} pickle hash mismatch")
        if record.get("policy") != "pas_autodist":
            raise RuntimeError(f"{kind} is not a pas_autodist artifact")
        if record.get("plan_ngpus") != plan or record.get("runtime_ngpus") != plan:
            raise RuntimeError(f"{kind} topology mismatch")
        if record.get("patched_parallel_py_sha256") != patched_parallel_hash:
            raise RuntimeError(f"{kind} patched-source hash mismatch")
        if record.get("patched_llm_gemm_py_sha256") != patched_llm_gemm_hash:
            raise RuntimeError(f"{kind} patched llm GEMM source hash mismatch")
        if record.get("comm_profile_sha256") != comm_profile_hash:
            raise RuntimeError(f"{kind} communication profile hash mismatch")
        receipt_path = files[f"{kind}_mgener.pkl.receipt.json"]
        if record.get("receipt_sha256") != sha256(receipt_path):
            raise RuntimeError(f"{kind} receipt hash mismatch")
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        validate_receipt_schema(receipt, plan)
        if (
            receipt.get("pkl_sha256") != actual
            or receipt.get("policy") not in ALLOWED_POLICY_IDENTITIES
            or receipt.get("patched_parallel_py_sha256") != patched_parallel_hash
            or receipt.get("patched_llm_gemm_py_sha256") != patched_llm_gemm_hash
            or receipt.get("comm_profile_sha256") != comm_profile_hash
        ):
            raise RuntimeError(f"{kind} receipt semantics mismatch")
        provenance = json.loads(
            files[f"{kind}_provenance.json"].read_text(encoding="utf-8"))
        if provenance != record:
            raise RuntimeError(f"{kind} provenance disagrees with gen_args")
        world = json.loads(files[f"{kind}_mgener.json"].read_text(encoding="utf-8"))
        if set(world) != WORLD_KEYS:
            raise RuntimeError(f"{kind} world metadata has unexpected fields")
        expected_world = {
            "model_name": "YOCO-MoE-A0.4B", "num_dp": 1, "num_tp": plan,
            "num_pp": 1, "num_mb": 1, "gbs": 1, "num_layers": 12,
            "num_heads": 16, "hidden_size": 1024, "seqlen": 4096,
            "n_activated_experts": 8, "n_routed_experts": 64,
        }
        if world != expected_world:
            raise RuntimeError(f"{kind} world metadata mismatch")
    return meta, files


class SequentialPool:
    def __init__(self, processes=None, initializer=None, initargs=()):
        if initializer:
            initializer(*initargs)

    def __enter__(self):
        return self

    def __exit__(self, *_args):
        return False

    def map(self, function, values):
        return [function(value) for value in values]


def configure_runtime(llm_train: Path, nnscaler_repo: Path):
    os.environ["YOCO_LLM_TRAIN_REPO"] = str(llm_train)
    sys.path[:0] = [
        str(STUBS), str(nnscaler_repo), str(llm_train / "llm"),
        str(ROOT), str(ROOT / "Verdict"),
    ]
    import triton_shim  # noqa: F401
    import arch.model as llm_model
    import nnscaler
    import torch

    imported_nnscaler = Path(nnscaler.__file__).resolve()
    imported_llm = Path(llm_model.__file__).resolve()
    if not imported_nnscaler.is_relative_to(nnscaler_repo):
        raise RuntimeError(f"runtime nnScaler is outside pinned checkout: {imported_nnscaler}")
    if not imported_llm.is_relative_to(llm_train / "llm"):
        raise RuntimeError(f"runtime llm-train model is outside pinned checkout: {imported_llm}")
    config = torch._dynamo.config._config
    if "recompile_limit" not in config:
        from torch.utils._config_module import Config, _ConfigEntry

        config["recompile_limit"] = _ConfigEntry(Config(default=32, value_type=int))
    multiprocessing.pool.Pool = SequentialPool
    import dill
    import nnscaler_backend.build_graph as build_graph
    import nnscaler_backend.load_graph as load_graph

    build_graph.Pool = SequentialPool
    load_graph.pickle = dill


def graph_to_lean_argv(llm_train, nnscaler, files, stage):
    command = [
        "graph_to_lean",
        "--sm-pkl", str(files["sm_mgener.pkl"]),
        "--pm-pkl", str(files["pm_mgener.pkl"]),
        "--out", str(stage / "GeneratedYOCOMoE.lean"),
        "--module", "denote.GeneratedYOCOMoE",
        "--max-goals", "5", "--split-goals", "--assume-cp-dim0-shuffle",
        "--goals-out-dir", str(stage / "goals"),
        "--manifest-out", str(stage / "GeneratedYOCOMoE.manifest.json"),
        "--llm-train-repo", str(llm_train),
        "--llm-train-revision", LLM_REVISION,
        "--nnscaler-repo", str(nnscaler),
        "--nnscaler-revision", NNSCALER_REVISION,
        "--sm-pkl-sha256", sha256(files["sm_mgener.pkl"]),
        "--pm-pkl-sha256", sha256(files["pm_mgener.pkl"]),
    ]
    for name in AUTHORITY_NAMES[2:]:
        command += ["--metadata-json", str(files[name])]
        command += ["--metadata-sha256", f"{name}={sha256(files[name])}"]
    return command


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--authority-dir", type=Path, required=True)
    parser.add_argument("--llm-train", type=Path, required=True)
    parser.add_argument("--nnscaler", type=Path, required=True)
    parser.add_argument("--snapshot-dir", type=Path, required=True)
    parser.add_argument(
        "--expected-hardware-sha256", required=True,
        help="SHA-256 captured out-of-band from the trusted GPU generation session",
    )
    parser.add_argument(
        "--trust-new-authority", action="store_true",
        help="acknowledge that pinned local pickle generation is the trust root",
    )
    args = parser.parse_args()
    if not args.trust_new_authority:
        parser.error("--trust-new-authority is required before pickle deserialization")
    authority_source = args.authority_dir.resolve()
    llm_source = args.llm_train.resolve()
    nnscaler_source = args.nnscaler.resolve()
    snapshot = args.snapshot_dir.absolute()
    validate_source_checkouts(llm_source, nnscaler_source)
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    stage, stage_marker, stage_dev, stage_ino = create_owned_stage(
        snapshot.parent, f".{snapshot.name}.staged-")
    try:
        (stage / "goals").mkdir()
        llm_train = stage / ".llm-train-source"
        nnscaler = stage / ".nnscaler-source"
        materialize_source(llm_source, LLM_REVISION, llm_train)
        materialize_source(nnscaler_source, NNSCALER_REVISION, nnscaler)
        authority = stage / "authority"
        secure_copy_authority(authority_source, authority)
        _, files = validate_authority(
            authority, llm_train, nnscaler, args.expected_hardware_sha256,
        )
        configure_runtime(llm_train, nnscaler)
        sys.argv = graph_to_lean_argv(llm_train, nnscaler, files, stage)
        from verdict.log import setup_logger
        import graph_to_lean

        setup_logger("ERROR")
        graph_to_lean.main()
        required_files = (
            stage / "GeneratedYOCOMoE.lean",
            stage / "GeneratedYOCOMoE.manifest.json",
        )
        if any(not path.is_file() or path.stat().st_size == 0 for path in required_files):
            raise RuntimeError("emitter did not create nonempty Lean and manifest files")
        if not any((stage / "goals").iterdir()):
            raise RuntimeError("emitter created an empty goals directory")
        shutil.rmtree(llm_train)
        shutil.rmtree(nnscaler)
        shutil.rmtree(authority)
        from scripts.yoco_regen.atomic_publish import rename_noreplace

        rename_noreplace(stage, snapshot)
    except BaseException:
        cleanup_owned_stage(stage, stage_marker, stage_dev, stage_ino)
        raise
    print(f"wrote atomic refresh snapshot: {snapshot}")


if __name__ == "__main__":
    main()
