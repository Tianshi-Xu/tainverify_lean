from pathlib import Path
from functools import partial
import fcntl
import hashlib
import importlib
import io
import json
import os
import pickle
import stat
import subprocess
import sys
import tarfile
import types
import zipfile
import zipimport

import pytest

from scripts.yoco_regen.patch_mgener_dump import MARKER, patch_source
from scripts.check_yoco_a04b_regen import _validate_candidate_manifest
from scripts.yoco_regen.comm_profile import EXPECTED_SIZES_MB, validate_profile
from scripts.yoco_regen.check_publication_allowlist import (
    EXPECTED as PUBLICATION_FILES,
    validate as validate_publication,
)
from scripts.yoco_regen.patch_llm_cc12_gemm import (
    MARKER as CC12_MARKER,
    patch_source as patch_cc12_source,
)
from scripts.yoco_regen.atomic_publish import publish_authority, rename_noreplace
from scripts.yoco_regen.sealed_extension_exec import (
    CLEAN_TOOL_ENV,
    _FULL_SEALS,
    _runtime_zip,
    _sealed_memfd,
    allowlisted_runtime_environment,
)
import scripts.yoco_regen.emit_yoco_a04b as emitter
from scripts.yoco_regen.safe_cleanup import create_owned_stage, cleanup_owned_stage
from scripts.yoco_regen.write_authority_metadata import validate_graph


def _clear_zip_import_caches(path: str) -> None:
    sys.path_importer_cache.pop(path, None)
    getattr(zipimport, "_zip_directory_cache").pop(path, None)


def test_dump_patch_is_idempotent_and_atomic():
    source = "def build(pas_policy, compute_config):\n    mgener = ModuleCodeGen(execplan, 2)\n    return mgener\n"
    patched = patch_source(source)
    assert MARKER in patched
    assert "_tv_dst + '.tmp.'" in patched
    assert "_tv_os.replace(_tv_tmp, _tv_dst)" in patched
    assert "_tv_os.chmod(_tv_dst, 0o444)" in patched
    assert "_tv_os.unlink(_tv_leftover)" in patched
    assert "setrecursionlimit(100000)" in patched
    assert patch_source(patched) == patched


def test_cc12_gemm_patch_is_exact_and_idempotent():
    source = """def _pick_mgemm_configs():
    if (_cuda_compute_capability_major() or 0) >= 10:
        return B200_Mgemm_configs
    return A100_H100_Mgemm_configs

def _pick_kgemm_configs():
    if (_cuda_compute_capability_major() or 0) >= 10:
        return B200_Kgemm_configs
    return A100_H100_Kgemm_configs
"""
    patched = patch_cc12_source(source)
    assert CC12_MARKER in patched
    assert patched.count("== 10") == 2
    assert ">= 10" not in patched
    assert patch_cc12_source(patched) == patched


def test_cc12_gemm_patch_rejects_partial_source():
    with pytest.raises(RuntimeError, match="exactly two"):
        patch_cc12_source(
            "if (_cuda_compute_capability_major() or 0) >= 10:\n    pass\n"
        )


def test_communication_profile_schema_is_closed_and_finite():
    profile = {
        primitive: [EXPECTED_SIZES_MB, [0.001 * (index + 1) for index in range(12)]]
        for primitive in ("all gather", "all reduce", "reduce scatter", "all to all")
    }
    validate_profile(profile)
    with pytest.raises(RuntimeError, match="primitive schema"):
        validate_profile({**profile, "attacker": profile["all gather"]})
    invalid = {**profile, "all gather": [EXPECTED_SIZES_MB, [True] * 12]}
    with pytest.raises(RuntimeError, match="invalid timing"):
        validate_profile(invalid)
    boolean_sizes = list(EXPECTED_SIZES_MB)
    boolean_sizes[2] = True
    with pytest.raises(RuntimeError, match="sizes mismatch"):
        validate_profile({**profile, "all gather": [boolean_sizes, [0.001] * 12]})


def _run_patched_dump(
    tmp_path, monkeypatch, local_rank, dump_function, llm_patch_hash: str | None = "c" * 64
):
    source = "def build(pas_policy, compute_config):\n    mgener = ModuleCodeGen(execplan, 2)\n    return mgener\n"
    patched = patch_source(source)
    source_path = tmp_path / "parallel.py"
    source_path.write_text(patched, encoding="utf-8")
    fake_dill = types.ModuleType("dill")
    setattr(fake_dill, "dump", dump_function)
    monkeypatch.setitem(sys.modules, "dill", fake_dill)
    destination = tmp_path / f"rank{local_rank}.pkl"
    monkeypatch.setenv("MGENER_DUMP_PATH", str(destination))
    monkeypatch.setenv("LOCAL_RANK", str(local_rank))
    monkeypatch.setenv("TRAINVERIFY_EXPECTED_POLICY", "autodist_wrapper")
    if llm_patch_hash is None:
        monkeypatch.delenv("TRAINVERIFY_PATCHED_LLM_GEMM_SHA256", raising=False)
    else:
        monkeypatch.setenv("TRAINVERIFY_PATCHED_LLM_GEMM_SHA256", llm_patch_hash)
    monkeypatch.setenv("TRAINVERIFY_COMM_PROFILE_SHA256", "e" * 64)
    monkeypatch.setenv("TRAINVERIFY_DP_SOLVER_SHA256", "f" * 64)
    namespace = {
        "__file__": str(source_path),
        "__loader__": types.SimpleNamespace(get_data=lambda path: Path(path).read_bytes()),
        "ModuleCodeGen": lambda *_args: {"ok": True},
        "execplan": object(),
    }
    exec(compile(patched, str(source_path), "exec"), namespace)
    def autodist_wrapper(*_args):
        return None

    autodist_wrapper.__module__ = "__main__"
    autodist_wrapper.__qualname__ = "main.<locals>.autodist_wrapper"
    wrapped_policy = partial(lambda *_args, **_kwargs: None, policy=autodist_wrapper)
    config = types.SimpleNamespace(
        plan_ngpus=2,
        runtime_ngpus=2,
        pas_config={"__pas_name": "__main__.main.<locals>.autodist_wrapper"},
    )
    namespace["build"](wrapped_policy, config)
    return destination


def test_dump_patch_only_rank_zero_writes_receipt(tmp_path, monkeypatch):
    rank1 = _run_patched_dump(tmp_path, monkeypatch, 1, pickle.dump)
    assert not rank1.exists()
    rank0 = _run_patched_dump(tmp_path, monkeypatch, 0, pickle.dump)
    receipt = Path(str(rank0) + ".receipt.json")
    assert rank0.is_file() and receipt.is_file()
    assert stat.S_IMODE(rank0.stat().st_mode) == 0o444
    data = json.loads(receipt.read_text(encoding="utf-8"))
    assert data["policy"] == "__main__.main.<locals>.autodist_wrapper"
    assert data["plan_ngpus"] == 2 and data["runtime_ngpus"] == 2
    assert data["patched_llm_gemm_py_sha256"] == "c" * 64
    assert data["comm_profile_sha256"] == "e" * 64
    assert data["dp_solver_extension_sha256"] == "f" * 64


def test_dump_patch_rejects_missing_or_invalid_llm_patch_hash(tmp_path, monkeypatch):
    with pytest.raises(RuntimeError, match="llm GEMM source hash"):
        _run_patched_dump(tmp_path, monkeypatch, 0, pickle.dump, None)
    with pytest.raises(RuntimeError, match="llm GEMM source hash"):
        _run_patched_dump(tmp_path, monkeypatch, 0, pickle.dump, "not-a-hash")
    assert not list(tmp_path.glob("*.pkl"))


def test_dump_patch_cleans_temporary_files_on_failure(tmp_path, monkeypatch):
    def broken_dump(*_args):
        raise RuntimeError("interrupted")

    with pytest.raises(RuntimeError, match="interrupted"):
        _run_patched_dump(tmp_path, monkeypatch, 0, broken_dump)
    assert not list(tmp_path.glob("*.tmp.*"))


def test_dump_patch_fails_closed_without_codegen_anchor():
    with pytest.raises(RuntimeError, match="ModuleCodeGen"):
        patch_source("def unrelated():\n    return None\n")


def test_atomic_publish_never_replaces_existing_target(tmp_path):
    source = tmp_path / "source"
    source.mkdir()
    (source / "value").write_text("new", encoding="utf-8")
    target = tmp_path / "target"
    target.mkdir()
    (target / "value").write_text("old", encoding="utf-8")
    with pytest.raises(FileExistsError):
        rename_noreplace(source, target)
    assert source.is_dir()
    assert (target / "value").read_text(encoding="utf-8") == "old"
    target.rename(tmp_path / "old-target")
    rename_noreplace(source, target)
    assert not source.exists()
    assert (target / "value").read_text(encoding="utf-8") == "new"


def test_secure_authority_copy_rejects_symlinks(tmp_path, monkeypatch):
    monkeypatch.setattr(emitter, "AUTHORITY_NAMES", ("payload",))
    source = tmp_path / "authority"
    source.mkdir()
    (source / "payload").write_text("trusted", encoding="utf-8")
    (source / "payload").chmod(0o444)
    target = tmp_path / "copy"
    emitter.secure_copy_authority(source, target)
    assert (target / "payload").read_text(encoding="utf-8") == "trusted"

    bad_source = tmp_path / "bad-authority"
    bad_source.mkdir()
    (bad_source / "real").write_text("other", encoding="utf-8")
    (bad_source / "real").chmod(0o444)
    (bad_source / "payload").symlink_to("real")
    with pytest.raises(OSError):
        emitter.secure_copy_authority(bad_source, tmp_path / "bad-copy")


def test_candidate_manifest_requires_schema_v3_solver_artifact():
    with pytest.raises(RuntimeError, match="schema v3"):
        _validate_candidate_manifest({"schema_version": 2})
    with pytest.raises(RuntimeError, match="dp solver"):
        _validate_candidate_manifest({"schema_version": 3, "artifact_sha256": {}})
    _validate_candidate_manifest({
        "schema_version": 3,
        "artifact_sha256": {"nnscaler_dp_solver.so": "a" * 64},
    })
    optimized = subprocess.run(
        [
            sys.executable, "-O", "-c",
            "from scripts.check_yoco_a04b_regen import _validate_candidate_manifest; "
            "_validate_candidate_manifest({'schema_version': 2})",
        ],
        cwd=Path(__file__).resolve().parents[2],
        text=True,
        capture_output=True,
        check=False,
    )
    assert optimized.returncode != 0
    assert "candidate manifest is not schema v3" in optimized.stderr


def test_publication_allowlist_rejects_private_or_symlink_entries(tmp_path):
    stage = tmp_path / "stage"
    stage.mkdir()
    for name in PUBLICATION_FILES:
        (stage / name).write_bytes(b"artifact")
        (stage / name).chmod(0o444)
    validate_publication(stage)
    private = stage / ".dp-solver-build-output"
    private.mkdir()
    with pytest.raises(RuntimeError, match="allowlist"):
        validate_publication(stage)
    private.rmdir()
    victim = stage / "gen_args.json"
    victim.unlink()
    victim.symlink_to("sm_mgener.json")
    with pytest.raises(PermissionError, match="untrusted"):
        validate_publication(stage)


def test_atomic_publication_validates_the_same_directory_inode(tmp_path):
    stage = tmp_path / "stage"
    stage.mkdir()
    for name in PUBLICATION_FILES:
        (stage / name).write_bytes(b"artifact")
        (stage / name).chmod(0o444)
    target = tmp_path / "authority"
    publish_authority(stage, target)
    assert not stage.exists()
    validate_publication(target)

    rejected = tmp_path / "rejected"
    rejected.mkdir()
    for name in PUBLICATION_FILES:
        (rejected / name).write_bytes(b"artifact")
        (rejected / name).chmod(0o444)
    (rejected / ".private-build").mkdir()
    with pytest.raises(RuntimeError, match="allowlist"):
        publish_authority(rejected, tmp_path / "must-not-exist")
    assert rejected.exists()
    assert not (tmp_path / "must-not-exist").exists()

    unsafe_parent = tmp_path / "unsafe-parent"
    unsafe_parent.mkdir(mode=0o777)
    unsafe_parent.chmod(0o777)
    unsafe_stage = unsafe_parent / "stage"
    unsafe_stage.mkdir()
    for name in PUBLICATION_FILES:
        (unsafe_stage / name).write_bytes(b"artifact")
        (unsafe_stage / name).chmod(0o444)
    with pytest.raises(PermissionError, match="owner-controlled"):
        publish_authority(unsafe_stage, unsafe_parent / "authority")

    unsafe_ancestor = tmp_path / "unsafe-ancestor"
    unsafe_ancestor.mkdir(mode=0o777)
    unsafe_ancestor.chmod(0o777)
    trusted_immediate = unsafe_ancestor / "trusted-immediate"
    trusted_immediate.mkdir(mode=0o700)
    nested_stage = trusted_immediate / "stage"
    nested_stage.mkdir()
    for name in PUBLICATION_FILES:
        (nested_stage / name).write_bytes(b"artifact")
        (nested_stage / name).chmod(0o444)
    with pytest.raises(PermissionError, match="ancestor"):
        publish_authority(nested_stage, trusted_immediate / "authority")


def test_runtime_and_tar_environments_are_closed(monkeypatch):
    required = {
        "HOME": "/private/home",
        "MGENER_DUMP_PATH": "/stage/sm.pkl",
        "TRAINVERIFY_EXPECTED_POLICY": "policy",
        "TRAINVERIFY_PATCHED_LLM_GEMM_SHA256": "a" * 64,
        "TRAINVERIFY_COMM_PROFILE_SHA256": "b" * 64,
    }
    poisoned = {
        **required,
        "LD_AUDIT": "/evil/audit.so",
        "TAR_OPTIONS": "--checkpoint-action=exec=evil",
        "DISABLE_COMM_FUSION": "1",
        "DISABLE_INTRA_RVD": "1",
        "TRACE_STRATEGY": "evil",
    }
    environment = allowlisted_runtime_environment(poisoned)
    assert environment == required
    assert set(CLEAN_TOOL_ENV) == {"LANG", "LC_ALL", "PATH"}
    assert "TAR_OPTIONS" not in CLEAN_TOOL_ENV


def test_memfd_runtime_is_fully_sealed_and_archive_links_cannot_escape():
    descriptor = _sealed_memfd("test-runtime", b"sealed")
    try:
        assert fcntl.fcntl(descriptor, getattr(fcntl, "F_GET_SEALS", 1034)) == _FULL_SEALS
        with pytest.raises(OSError):
            os.write(descriptor, b"mutation")
    finally:
        os.close(descriptor)

    archive = io.BytesIO()
    with tarfile.open(fileobj=archive, mode="w") as handle:
        parallel = tarfile.TarInfo("nnscaler/parallel.py")
        parallel.size = len(b"old")
        handle.addfile(parallel, io.BytesIO(b"old"))
        package = tarfile.TarInfo("nnscaler/__init__.py")
        package.size = 0
        handle.addfile(package, io.BytesIO())
        for name in ("namespace_probe", "namespace_probe/sub"):
            directory = tarfile.TarInfo(name)
            directory.type = tarfile.DIRTYPE
            handle.addfile(directory)
        module = tarfile.TarInfo("namespace_probe/sub/mod.py")
        module.size = len(b"VALUE = 1729\n")
        handle.addfile(module, io.BytesIO(b"VALUE = 1729\n"))
    runtime = _runtime_zip(archive.getvalue(), b"patched", b"guard")
    with zipfile.ZipFile(io.BytesIO(runtime)) as handle:
        assert handle.read("nnscaler/parallel.py") == b"patched"
        assert handle.read("sitecustomize.py") == b"guard"
        assert "namespace_probe/sub/" in handle.namelist()
    runtime_descriptor = _sealed_memfd("namespace-runtime.zip", runtime)
    runtime_path = f"/proc/{os.getpid()}/fd/{runtime_descriptor}"
    _clear_zip_import_caches(runtime_path)
    sys.path.insert(0, runtime_path)
    try:
        assert importlib.import_module("namespace_probe.sub.mod").VALUE == 1729
    finally:
        sys.path.remove(runtime_path)
        _clear_zip_import_caches(runtime_path)
        for name in ("namespace_probe.sub.mod", "namespace_probe.sub", "namespace_probe"):
            sys.modules.pop(name, None)
        os.close(runtime_descriptor)

    escaping = io.BytesIO()
    with tarfile.open(fileobj=escaping, mode="w") as handle:
        link = tarfile.TarInfo("nnscaler/parallel.py")
        link.type = tarfile.SYMTYPE
        link.linkname = "../../outside"
        handle.addfile(link)
    with pytest.raises(RuntimeError, match="escaping"):
        _runtime_zip(escaping.getvalue(), b"patched", b"guard")


def test_dump_receipt_hashes_parallel_source_loaded_from_memfd_zip(tmp_path, monkeypatch):
    source = """class Config:
    plan_ngpus = 2
    runtime_ngpus = 2
    pas_config = {}
compute_config = Config()
pas_policy = "policy"
def ModuleCodeGen():
    return {"authority": True}
mgener_probe = ModuleCodeGen()
"""
    patched = patch_source(source)
    archive = io.BytesIO()
    with zipfile.ZipFile(archive, mode="w", compression=zipfile.ZIP_STORED) as handle:
        handle.writestr("receipt_probe.py", patched)
    descriptor = _sealed_memfd("receipt-probe.zip", archive.getvalue())
    destination = tmp_path / "authority.pkl"
    monkeypatch.setenv("MGENER_DUMP_PATH", str(destination))
    monkeypatch.setenv("LOCAL_RANK", "0")
    monkeypatch.setenv("TRAINVERIFY_EXPECTED_POLICY", "policy")
    monkeypatch.setenv("TRAINVERIFY_PATCHED_LLM_GEMM_SHA256", "a" * 64)
    monkeypatch.setenv("TRAINVERIFY_COMM_PROFILE_SHA256", "b" * 64)
    monkeypatch.setenv("TRAINVERIFY_DP_SOLVER_SHA256", "c" * 64)
    monkeypatch.setitem(sys.modules, "dill", pickle)
    runtime_path = f"/proc/{os.getpid()}/fd/{descriptor}"
    _clear_zip_import_caches(runtime_path)
    sys.path.insert(0, runtime_path)
    try:
        importlib.import_module("receipt_probe")
    finally:
        sys.path.remove(runtime_path)
        _clear_zip_import_caches(runtime_path)
        sys.modules.pop("receipt_probe", None)
        os.close(descriptor)
    receipt = json.loads((tmp_path / "authority.pkl.receipt.json").read_text())
    assert receipt["patched_parallel_py_sha256"] == hashlib.sha256(
        patched.encode("utf-8")
    ).hexdigest()


def test_generator_requires_external_clean_environment():
    script = Path(__file__).resolve().parents[1] / "yoco_regen" / "generate_authority.sh"
    result = subprocess.run(
        ["/bin/bash", "--noprofile", "--norc", str(script)],
        env={"YOCO_PYTHON": sys.executable},
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 2
    assert "TRAINVERIFY_CLEAN_ENV" in result.stderr

    poisoned = subprocess.run(
        ["/bin/bash", "--noprofile", "--norc", str(script)],
        env={
            "HOME": "/tmp",
            "TRAINVERIFY_CLEAN_ENV": "1",
            "YOCO_PYTHON": sys.executable,
            "YOCO_LLM_TRAIN_REPO": "/missing/llm",
            "YOCO_NNSCALER_REPO": "/missing/nns",
            "YOCO_AUTHORITY_OUT": "/missing/out",
            "TRACE_STRATEGY": "ambient-control",
        },
        text=True,
        capture_output=True,
        check=False,
    )
    assert poisoned.returncode == 2
    assert "unexpected inherited environment: TRACE_STRATEGY" in poisoned.stderr


def test_safe_path_package_entrypoints_import_siblings():
    root = Path(__file__).resolve().parents[2]
    environment = {
        "PATH": "/usr/bin:/bin",
        "PYTHONNOUSERSITE": "1",
        "PYTHONPATH": str(root),
        "PYTHONSAFEPATH": "1",
    }
    for module in (
        "scripts.yoco_regen.write_authority_metadata",
        "scripts.yoco_regen.atomic_publish",
    ):
        result = subprocess.run(
            [sys.executable, "-S", "-m", module, "--help"],
            cwd=root,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )
        assert result.returncode == 0, (module, result.stderr)
    imports = subprocess.run(
        [
            sys.executable, "-S", "-c",
            "from scripts.yoco_regen import write_authority_metadata as w; "
            "from scripts.yoco_regen import patch_mgener_dump, patch_llm_cc12_gemm, comm_profile",
        ],
        cwd=root,
        env=environment,
        text=True,
        capture_output=True,
        check=False,
    )
    assert imports.returncode == 0, imports.stderr


def test_owned_stage_cleanup_requires_matching_marker(tmp_path):
    stage, real_marker, dev, ino = create_owned_stage(tmp_path, "stage-")
    (stage / "valuable").write_text("keep", encoding="utf-8")
    nested = stage / "nested"
    nested.mkdir()
    (nested / "payload").write_text("nested", encoding="utf-8")
    (stage / "payload-link").symlink_to("nested/payload")
    assert cleanup_owned_stage(stage, "owner-b", dev, ino) is False
    assert (stage / "valuable").read_text(encoding="utf-8") == "keep"
    cleanup_script = Path(__file__).resolve().parents[1] / "yoco_regen" / "safe_cleanup.py"
    rejected = subprocess.run(
        [sys.executable, str(cleanup_script), "cleanup", str(stage), "owner-b", str(dev), str(ino)],
        check=False,
    )
    assert rejected.returncode != 0
    assert (stage / "valuable").read_text(encoding="utf-8") == "keep"
    assert cleanup_owned_stage(stage, real_marker, dev, ino) is True
    assert not stage.exists()


def test_owned_stage_cleanup_rejects_replaced_inode_even_with_marker(tmp_path):
    stage, marker, dev, ino = create_owned_stage(tmp_path, "stage-")
    original = tmp_path / "original"
    stage.rename(original)
    stage.mkdir()
    (stage / ".trainverify-stage-owner").write_text(marker + "\n", encoding="utf-8")
    valuable = stage / "valuable"
    valuable.write_text("unrelated", encoding="utf-8")
    assert cleanup_owned_stage(stage, marker, dev, ino) is False
    assert valuable.read_text(encoding="utf-8") == "unrelated"
    assert cleanup_owned_stage(original, marker, dev, ino) is True


def test_stage_cleanup_has_no_path_recursive_delete():
    source = (
        Path(__file__).resolve().parents[1] / "yoco_regen" / "safe_cleanup.py"
    ).read_text(encoding="utf-8")
    assert "shutil.rmtree" not in source
    assert "dir_fd=" in source


def test_cpu_smoke_refuses_existing_output_before_import(tmp_path):
    output = tmp_path / "existing"
    output.mkdir()
    valuable = output / "sm_mgener.pkl"
    valuable.write_bytes(b"do-not-delete")
    script = Path(__file__).resolve().parents[1] / "yoco_regen" / "compile_cpu_smoke.py"
    result = subprocess.run(
        [
            sys.executable, str(script),
            "--llm-train", str(tmp_path / "missing-llm"),
            "--out-dir", str(output),
        ],
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode != 0
    assert valuable.read_bytes() == b"do-not-delete"


def _fake_authority_graph(plan=1, missing_unshuffle=False, token_shape=(4096, 1024)):
    counts = {
        "nnscaler.customized_ops.ring_attention.maybe_shuffle.wrap_maybe_shuffle": plan,
        "nnscaler.customized_ops.ring_attention.maybe_shuffle.wrap_maybe_unshuffle": 25 * plan,
        "nnscaler.customized_ops.ring_attention.sliding_window_attn.wrap_sliding_window_attn_func": 12 * plan,
        "nnscaler.customized_ops.ring_attention.zigzag_allgather_attn_varlen.wrap_zigzag_allgather_attn_varlen_func": 12 * plan,
        "arch.all2all_moe.topk_routing": 24 * plan,
        "arch.all2all_moe.nnscaler_all2all_moe_gmm": 24 * plan,
        "nnscaler.runtime.function.stack": 2 * plan,
    }
    if missing_unshuffle:
        counts["nnscaler.customized_ops.ring_attention.maybe_shuffle.wrap_maybe_unshuffle"] -= 1

    class Node:
        def __init__(self, signature, with_shape=False):
            self.signature = signature
            self._values = [types.SimpleNamespace(shape=token_shape)] if with_shape else []

        def inputs(self):
            return self._values

        def outputs(self):
            return []

    nodes = []
    for signature, count in counts.items():
        nodes.extend(Node(signature, not nodes and index == 0) for index in range(count))
    nodes.append(Node(None))
    graph = types.SimpleNamespace(nodes=lambda: nodes)
    return types.SimpleNamespace(
        devices=list(range(plan)),
        runtime_ndevs=plan,
        execplan=types.SimpleNamespace(graph=graph),
    )


def _receipt(plan=1, policy="nnscaler_train.main.<locals>.autodist_wrapper"):
    return {
        "policy": policy,
        "plan_ngpus": plan,
        "runtime_ngpus": plan,
        "pkl_sha256": "a" * 64,
        "patched_parallel_py_sha256": "b" * 64,
        "patched_llm_gemm_py_sha256": "c" * 64,
        "comm_profile_sha256": "e" * 64,
        "dp_solver_extension_sha256": "f" * 64,
    }


def _authority_record(plan=1):
    return {
        "authority": True,
        "policy": "pas_autodist",
        "plan_ngpus": plan,
        "runtime_ngpus": plan,
        "zero_group_size": plan,
        "cp_size_runtime": plan,
        "ep_size_runtime": plan,
        "cp_size_codegen_sentinel": 0,
        "pkl_sha256": "a" * 64,
        "receipt_sha256": "d" * 64,
        "patched_parallel_py_sha256": "b" * 64,
        "patched_llm_gemm_py_sha256": "c" * 64,
        "comm_profile_sha256": "e" * 64,
        "dp_solver_extension_sha256": "f" * 64,
        "node_count": 1,
        "signature_counts": {"op": 1},
    }


def _hardware_meta():
    gpu = {
        "index": 0,
        "name": "GPU",
        "total_memory_bytes": 1024,
        "compute_capability": [12, 0],
    }
    return {
        "cuda_runtime_version": "12.8",
        "nccl_version": [2, 27, 3],
        "nvidia_driver_version": "595.71.05",
        "gpu_inventory": [gpu, {**gpu, "index": 1}],
        "trainverify_regen_commit": "e" * 40,
        "comm_profile_sha256": "f" * 64,
    }


def _full_meta():
    hardware = _hardware_meta()
    return {
        "authority": True,
        "model": "YOCO-MoE-A0.4B",
        "max_seq_len": 4096,
        "layers": 24,
        "cross_layers": 12,
        "precision": "fp32",
        "partition_constraints": "llm/pcs/all2all_moe.yaml",
        "llm_train_commit": emitter.LLM_REVISION,
        "llm_hardware_patch": "cc12_generic_triton_fallback_v1",
        "nnscaler_commit": emitter.NNSCALER_REVISION,
        "nnscaler_version": "0.9",
        "torch_version": "2.8.0+cu128",
        "python_version": "3.12.3",
        "host": "host",
        "dp_solver_extension_sha256": "1" * 64,
        "hardware_sha256": emitter.hardware_sha256(hardware),
        "source_sha256": {"source": "a" * 64},
        "sm": _authority_record(1),
        "pm": _authority_record(2),
        **hardware,
    }


def test_trusted_emitter_receipt_and_record_schemas_are_closed():
    emitter.validate_receipt_schema(_receipt(), 1)
    emitter.validate_record_schema(_authority_record(), 1)
    for value, validator in (
        (_receipt(), lambda x: emitter.validate_receipt_schema(x, 1)),
        (_authority_record(), lambda x: emitter.validate_record_schema(x, 1)),
    ):
        missing = dict(value)
        del missing["plan_ngpus"]
        with pytest.raises(RuntimeError, match="schema"):
            validator(missing)
        extra = {**value, "attacker": True}
        with pytest.raises(RuntimeError, match="schema"):
            validator(extra)


def test_trusted_emitter_hardware_schema_rejects_forgery_and_extras():
    meta = _hardware_meta()
    emitter.validate_hardware_schema(meta)
    forged = {**meta, "gpu_inventory": [{
        "index": 999,
        "name": "FORGED",
        "total_memory_bytes": 1,
        "compute_capability": [0, 0],
    }]}
    with pytest.raises(RuntimeError, match="GPU"):
        emitter.validate_hardware_schema(forged)
    with pytest.raises(RuntimeError, match="schema"):
        emitter.validate_hardware_schema({**meta, "attacker": True})
    boolean_indices = {**meta, "gpu_inventory": [
        {**meta["gpu_inventory"][0], "index": False},
        {**meta["gpu_inventory"][1], "index": True},
    ]}
    with pytest.raises(RuntimeError, match="GPU"):
        emitter.validate_hardware_schema(boolean_indices)


def test_trusted_hardware_digest_rejects_coordinated_plausible_forgery():
    original = _hardware_meta()
    expected = emitter.hardware_sha256(original)
    forged = {
        **original,
        "nvidia_driver_version": "999.999",
        "cuda_runtime_version": "99.9",
        "nccl_version": [99, 99, 99],
        "trainverify_regen_commit": "f" * 40,
        "gpu_inventory": [
            {**gpu, "name": "FORGED", "compute_capability": [99, 9]}
            for gpu in original["gpu_inventory"]
        ],
    }
    emitter.validate_hardware_schema(forged)
    with pytest.raises(RuntimeError, match="trusted hardware"):
        emitter.validate_expected_hardware(forged, expected)


def test_trusted_emitter_gen_args_schema_is_closed():
    meta = _full_meta()
    emitter.validate_meta_schema(meta)
    with pytest.raises(RuntimeError, match="schema"):
        emitter.validate_meta_schema({**meta, "attacker": True})
    missing = dict(meta)
    del missing["nvidia_driver_version"]
    with pytest.raises(RuntimeError, match="schema"):
        emitter.validate_meta_schema(missing)


def test_dp_solver_binary_is_hashed_but_not_passed_as_json(tmp_path):
    files = {}
    for name in emitter.AUTHORITY_NAMES:
        path = tmp_path / name
        path.write_bytes(b"\x7fELF" if name == "nnscaler_dp_solver.so" else b"{}")
        files[name] = path
    argv = emitter.graph_to_lean_argv(tmp_path, tmp_path, files, tmp_path)
    metadata_json_values = [
        argv[index + 1] for index, value in enumerate(argv) if value == "--metadata-json"
    ]
    assert str(files["nnscaler_dp_solver.so"]) not in metadata_json_values
    assert any(
        isinstance(value, str) and value.startswith("nnscaler_dp_solver.so=")
        for value in argv
    )


def test_authority_graph_gate_accepts_only_full_autodist_graph():
    counts = validate_graph(_fake_authority_graph(), "sm", 1, _receipt())
    assert counts["Node"] == 1
    assert all(isinstance(signature, str) for signature in counts)
    assert counts[
        "nnscaler.customized_ops.ring_attention.maybe_shuffle.wrap_maybe_unshuffle"
    ] == 25
    with pytest.raises(RuntimeError, match="structural minimum"):
        validate_graph(_fake_authority_graph(missing_unshuffle=True), "sm", 1, _receipt())
    with pytest.raises(RuntimeError, match="autodist_wrapper"):
        validate_graph(_fake_authority_graph(), "sm", 1, _receipt(policy="partial"))
    with pytest.raises(RuntimeError, match="flattened seq4096"):
        validate_graph(_fake_authority_graph(token_shape=(1, 4096)), "sm", 1, _receipt())
    wrong_runtime = _fake_authority_graph()
    wrong_runtime.runtime_ndevs = 2
    with pytest.raises(RuntimeError, match="topology"):
        validate_graph(wrong_runtime, "sm", 1, _receipt())
    missing_runtime = _fake_authority_graph()
    del missing_runtime.runtime_ndevs
    with pytest.raises(RuntimeError, match="topology"):
        validate_graph(missing_runtime, "sm", 1, _receipt())


def test_authority_script_pins_reviewed_llm_revision():
    script = (
        Path(__file__).resolve().parents[1]
        / "yoco_regen"
        / "generate_authority.sh"
    ).read_text(encoding="utf-8")
    assert "9a1be1d5fd1c063d80be82797692cdc7d23cfbef" in script
    assert "d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf" in script
    assert "MGENER_DUMP_PATH" in script
    assert "--plan_ngpus \"$plan\"" in script
    assert "--partition_constraints_path ./pcs/all2all_moe.yaml" in script
    assert "TRAINVERIFY_EXPECTED_POLICY='main.<locals>.autodist_wrapper'" in script
    assert "umask 077" in script
    assert "YOCO_PYTHON" in script
    assert 'unset LD_AUDIT LD_PRELOAD LD_LIBRARY_PATH CC CXX' in script
    assert '"$PYTHON" -S' in script
    assert "git clone --quiet --no-hardlinks" in script
    assert "patch_llm_cc12_gemm.py" in script
    assert "TRAINVERIFY_PATCHED_LLM_GEMM_SHA256" in script
    assert "TRAINVERIFY_COMM_PROFILE_SHA256" in script
    assert "comm_profile.py" in script
    assert "build_dp_solver.py" in script
    assert "sealed_extension_exec.py" in script
    assert "TRAINVERIFY_DP_SOLVER_SHA256" in script
    assert 'HOME="$PROFILE_HOME" MGENER_DUMP_PATH="$dump"' in script
    assert '"$TRAINVERIFY_DP_SOLVER_SHA256" "$NNS_WORK"' in script
    assert '"$DP_SOLVER_SITE_GUARD/sitecustomize.py" "$LLM_WORK/llm" -- torchrun' in script
    assert 'ln "$PRIVATE_COMM_DIR/intra_2.json" "$STAGE/comm_profile_intra_2.json"' in script
    assert 'safe_cleanup.py" cleanup' in script
    assert "dp_solver_sitecustomize.py" in script
    assert "export PYTHONSAFEPATH=1" in script
    assert "git -C \"$NNS_SOURCE\" status" in script
    assert "git -C \"$NNS\" restore" not in script
    assert "scripts.yoco_regen.atomic_publish" in script
    assert "trap - EXIT" in script
    sealed = (
        Path(__file__).resolve().parents[1]
        / "yoco_regen" / "sealed_extension_exec.py"
    ).read_text(encoding="utf-8")
    assert '"-S"' in sealed
    assert "PYTHONNOUSERSITE" in sealed
    assert "TRAINVERIFY_WORKER_SHIM" in sealed
    assert "NNSCALER_ARCHIVE_SHA256" in sealed
    assert "memfd_create" in sealed
    assert "F_ADD_SEALS" in sealed
    assert "TRAINVERIFY_RUNTIME_ZIP_SHA256" in sealed
    assert "unshare" not in sealed
    assert "mount(" not in sealed
    builder = (
        Path(__file__).resolve().parents[1] / "yoco_regen" / "build_dp_solver.py"
    ).read_text(encoding="utf-8")
    assert "EXPECTED_EXTENSION_SHA256" in builder
    assert 'sys.executable, "-S"' in builder
    assert '"PATH": "/usr/bin:/bin"' in builder
    assert "env=CLEAN_TOOL_ENV" in builder
    assert "NNSCALER_ARCHIVE_SHA256" in builder
    assert "unshare" not in builder
    emitter = (
        Path(__file__).resolve().parents[1] / "yoco_regen" / "emit_yoco_a04b.py"
    ).read_text(encoding="utf-8")
    assert '"--verifier-cache-dir", str(stage / "verifier-cache")' in emitter
    assert 'shutil.rmtree(stage / "verifier-cache")' in emitter
    assert '"mount"' not in builder


def test_cpu_smoke_is_explicitly_non_authoritative():
    script = (
        Path(__file__).resolve().parents[1]
        / "yoco_regen"
        / "compile_cpu_smoke.py"
    ).read_text(encoding="utf-8")
    assert "'authority': False" in script
    assert "'policy': 'tp-smoke'" in script
    assert "codegen_args.cp_size = 0" in script


def test_compatibility_entrypoint_imports_from_any_cwd(tmp_path):
    script = Path(__file__).resolve().parents[1] / "regenerate_yoco_a04b.py"
    result = subprocess.run(
        [sys.executable, str(script), "--help"],
        cwd=tmp_path,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert "--snapshot-dir" in result.stdout
    assert "--trust-new-authority" in result.stdout
