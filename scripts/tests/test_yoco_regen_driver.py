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
from scripts.yoco_regen.comp_profile import (
    copy_artifact as copy_comp_profile_artifact,
    create_artifact as create_comp_profile_artifact,
    extract_artifact as extract_comp_profile_artifact,
)
from scripts.yoco_regen.check_publication_allowlist import (
    EXPECTED as PUBLICATION_FILES,
    validate as validate_publication,
)
from scripts.yoco_regen.patch_llm_cc12_gemm import (
    MARKER as CC12_MARKER,
    patch_source as patch_cc12_source,
)
from scripts.yoco_regen.atomic_publish import (
    publish_authority, publish_validated_directory, rename_noreplace,
)
from scripts.yoco_regen.build_dp_solver import _validate_build_output
from scripts.yoco_regen.sealed_extension_exec import (
    CLEAN_TOOL_ENV,
    _FULL_SEALS,
    _runtime_zip,
    _sealed_memfd,
    _worker_shim_content,
    _parse_args as parse_sealed_exec_args,
    allowlisted_runtime_environment,
)
import scripts.yoco_regen.emit_yoco_a04b as emitter
import scripts.yoco_regen.atomic_publish as atomic_publish
import scripts.yoco_regen.safe_cleanup as safe_cleanup
from scripts.yoco_regen.safe_cleanup import create_owned_stage, cleanup_owned_stage
from scripts.yoco_regen.write_authority_metadata import validate_graph


PROOF_TARGETS = [
    f"TrainVerify.Denote.GeneratedPatterns.prove_pattern_{index}"
    for index in range(1, 6)
]


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


def test_comp_profile_artifact_round_trip_and_rejects_ambiguous_inputs(tmp_path):
    source = tmp_path / "comp"
    source.mkdir()
    original = json.dumps({
        "shape : torch.float32 : True": {
            "in_mem_info": [4], "param_mem_info": [], "buffer_mem_info": [],
            "fw_span": 1.25, "bw_span": 2.5, "infer_memory": 4,
            "train_mem_info": [4], "train_mem2in_idx": [0],
        }
    }, separators=(",", ":")).encode()
    profile_file = source / "torch.add.json"
    profile_file.write_bytes(original)
    profile_file.chmod(0o400)
    artifact = tmp_path / "comp_profile.json"
    create_comp_profile_artifact(source, artifact)

    extracted = tmp_path / "extracted"
    extract_comp_profile_artifact(artifact, extracted)
    assert (extracted / "torch.add.json").read_bytes() == original
    assert create_comp_profile_artifact(extracted, tmp_path / "again.json") == artifact.read_bytes()
    copied = tmp_path / "copied.json"
    assert copy_comp_profile_artifact(artifact, copied) == hashlib.sha256(
        artifact.read_bytes()
    ).hexdigest()
    assert copied.read_bytes() == artifact.read_bytes()
    alias = tmp_path / "alias.json"
    alias.symlink_to(artifact)
    with pytest.raises(OSError):
        copy_comp_profile_artifact(alias, tmp_path / "copy-from-alias.json")

    (source / "rogue").symlink_to("missing")
    with pytest.raises(RuntimeError, match="regular JSON files"):
        create_comp_profile_artifact(source, tmp_path / "bad.json")
    (source / "rogue").unlink()
    (source / "nested").mkdir()
    with pytest.raises(RuntimeError, match="regular JSON files"):
        create_comp_profile_artifact(source, tmp_path / "bad.json")


def test_comp_profile_artifact_rejects_noncanonical_json_and_tampering(tmp_path):
    source = tmp_path / "comp"
    source.mkdir()
    artifact = tmp_path / "comp_profile.json"
    profile_file = source / "torch.add.json"
    for invalid in (b'{"a":1,"a":2}', b'{"a":NaN}', b'[]'):
        if profile_file.exists():
            profile_file.chmod(0o600)
        profile_file.write_bytes(invalid)
        profile_file.chmod(0o400)
        with pytest.raises(RuntimeError):
            create_comp_profile_artifact(source, artifact)

    base_metrics = {
        "in_mem_info": [], "param_mem_info": [], "buffer_mem_info": [],
        "fw_span": 1.0, "bw_span": 2.0, "infer_memory": 0,
        "train_mem_info": [], "train_mem2in_idx": [],
    }
    for bad_metrics in (
        {**base_metrics, "train_mem_info": [4], "train_mem2in_idx": []},
        {**base_metrics, "train_mem_info": [4], "train_mem2in_idx": [-2]},
    ):
        profile_file.chmod(0o600)
        profile_file.write_text(json.dumps({"shape": bad_metrics}), encoding="utf-8")
        profile_file.chmod(0o400)
        with pytest.raises(RuntimeError):
            create_comp_profile_artifact(source, artifact)

    valid = {"shape": base_metrics}
    profile_file.chmod(0o600)
    profile_file.write_text(json.dumps(valid), encoding="utf-8")
    profile_file.chmod(0o400)
    create_comp_profile_artifact(source, artifact)
    payload = json.loads(artifact.read_text(encoding="utf-8"))
    payload["files"][0]["content_base64"] = "e30="
    artifact.chmod(0o600)
    artifact.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(RuntimeError, match="content hash mismatch"):
        extract_comp_profile_artifact(artifact, tmp_path / "out")


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
    tmp_path, monkeypatch, local_rank, dump_function, llm_patch_hash: str | None = "c" * 64,
    module_codegen=None,
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
    monkeypatch.setenv("TRAINVERIFY_COMP_PROFILE_SHA256", "d" * 64)
    monkeypatch.setenv("TRAINVERIFY_LLM_SOURCE_ROOT", "/trusted/llm")
    monkeypatch.setenv("TRAINVERIFY_DP_SOLVER_SHA256", "f" * 64)
    namespace = {
        "__file__": str(source_path),
        "__loader__": types.SimpleNamespace(get_data=lambda path: Path(path).read_bytes()),
        "ModuleCodeGen": module_codegen or (lambda *_args: {"ok": True}),
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


def test_dump_patch_canonicalizes_only_dynamic_provenance_paths(tmp_path, monkeypatch):
    def dynamic_function():
        return None

    dynamic_function.__code__ = dynamic_function.__code__.replace(
        co_filename="/proc/123456/fd/3/nnscaler/graph/parser/register.py"
    )
    authority = types.SimpleNamespace(
        _comment='File "/trusted/llm/arch/model.py", line 1, in forward',
        callback=dynamic_function,
    )
    captured = {}
    def capture_dump(obj, handle):
        captured["comment"] = obj._comment
        captured["filename"] = obj.callback.__code__.co_filename
        pickle.dump({"captured": True}, handle)

    destination = _run_patched_dump(
        tmp_path, monkeypatch, 0, capture_dump,
        module_codegen=lambda *_args: authority,
    )
    assert captured["comment"].startswith('File "/trainverify/llm/arch/model.py"')
    assert captured["filename"] == "/trainverify/nnscaler/graph/parser/register.py"
    receipt = json.loads(Path(str(destination) + ".receipt.json").read_text())
    assert receipt["canonicalized_comment_count"] == 1
    assert receipt["canonicalized_code_count"] == 1


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
    assert data["comp_profile_sha256"] == "d" * 64
    assert data["canonicalized_comment_count"] == 0
    assert data["canonicalized_code_count"] == 0
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


def test_candidate_manifest_requires_schema_v3_solver_and_comp_profile_artifacts():
    with pytest.raises(RuntimeError, match="schema v3"):
        _validate_candidate_manifest({"schema_version": 2})
    with pytest.raises(RuntimeError, match="computation profile"):
        _validate_candidate_manifest({
            "schema_version": 3,
            "artifact_sha256": {"nnscaler_dp_solver.so": "a" * 64},
        })
    _validate_candidate_manifest({
        "schema_version": 3,
        "artifact_sha256": {
            "nnscaler_dp_solver.so": "a" * 64,
            "comp_profile.json": "b" * 64,
        },
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


def test_sealed_executor_parses_profile_options_before_remainder():
    prefix = ["run", "solver.so", "a" * 64, "nnscaler", "guard.py", "llm"]
    live = parse_sealed_exec_args(["--allow-live-comp-profile", *prefix, "--", "torchrun", "x"])
    assert live.allow_live_comp_profile is True
    assert live.command == ["torchrun", "x"]
    frozen = parse_sealed_exec_args([
        "--comp-profile", "comp_profile.json",
        "--comp-profile-sha256", "b" * 64,
        *prefix, "--", "torchrun", "x",
    ])
    assert frozen.comp_profile == Path("comp_profile.json")
    assert frozen.comp_profile_sha256 == "b" * 64
    assert frozen.command == ["torchrun", "x"]


def test_worker_shim_supports_real_multiprocessing_spawn(tmp_path):
    (tmp_path / "sitecustomize.py").write_text("READY = True\n", encoding="utf-8")
    descriptor = _sealed_memfd(
        "spawn-worker-shim", _worker_shim_content(Path(sys.executable)), executable=True,
    )
    shim_path = f"/proc/{os.getpid()}/fd/{descriptor}"
    code = (
        "import multiprocessing as mp, os\n"
        "if __name__ == '__main__':\n"
        "  mp.set_executable(os.environ['TRAINVERIFY_WORKER_SHIM'])\n"
        "  p=mp.get_context('spawn').Process(target=os.getpid)\n"
        "  p.start(); p.join(30)\n"
        "  assert not p.is_alive() and p.exitcode == 0, (p.is_alive(), p.exitcode)\n"
    )
    environment = {
        **os.environ,
        "PYTHONPATH": str(tmp_path),
        "PYTHONDONTWRITEBYTECODE": "1",
        "TRAINVERIFY_WORKER_SHIM": shim_path,
    }
    try:
        result = subprocess.run(
            [sys.executable, "-S", "-c", code],
            env=environment,
            pass_fds=(descriptor,),
            text=True,
            capture_output=True,
            timeout=60,
        )
        assert result.returncode == 0, result.stderr
    finally:
        os.close(descriptor)


def test_runtime_and_tar_environments_are_closed(monkeypatch):
    required = {
        "HOME": "/private/home",
        "MGENER_DUMP_PATH": "/stage/sm.pkl",
        "TRAINVERIFY_EXPECTED_POLICY": "policy",
        "TRAINVERIFY_PATCHED_LLM_GEMM_SHA256": "a" * 64,
        "TRAINVERIFY_COMM_PROFILE_SHA256": "b" * 64,
        "TRAINVERIFY_COMP_PROFILE_SHA256": "c" * 64,
        "TRAINVERIFY_LLM_SOURCE_ROOT": "/trusted/llm",
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

    duplicate = io.BytesIO()
    with tarfile.open(fileobj=duplicate, mode="w") as handle:
        for content in (b"first", b"second"):
            member = tarfile.TarInfo("nnscaler/parallel.py")
            member.size = len(content)
            handle.addfile(member, io.BytesIO(content))
    with pytest.raises(RuntimeError, match="duplicate"):
        _runtime_zip(duplicate.getvalue(), b"patched", b"guard")

    guard_collision = io.BytesIO()
    with tarfile.open(fileobj=guard_collision, mode="w") as handle:
        for name in ("nnscaler/parallel.py", "sitecustomize.py"):
            member = tarfile.TarInfo(name)
            member.size = 1
            handle.addfile(member, io.BytesIO(b"x"))
    with pytest.raises(RuntimeError, match="startup guard"):
        _runtime_zip(guard_collision.getvalue(), b"patched", b"guard")

    alias = io.BytesIO()
    with tarfile.open(fileobj=alias, mode="w") as handle:
        member = tarfile.TarInfo("./nnscaler/parallel.py")
        member.size = 1
        handle.addfile(member, io.BytesIO(b"x"))
    with pytest.raises(RuntimeError, match="non-canonical"):
        _runtime_zip(alias.getvalue(), b"patched", b"guard")


def test_dp_solver_build_output_rejects_unknown_inodes(tmp_path):
    output = tmp_path / "output"
    extension = output / "nnscaler" / "autodist" / "dp_solver.so"
    extension.parent.mkdir(parents=True)
    extension.write_bytes(b"ELF")
    _validate_build_output(output, extension)

    rogue = output / "rogue"
    rogue.symlink_to("missing")
    with pytest.raises(RuntimeError, match="unexpected"):
        _validate_build_output(output, extension)
    rogue.unlink()

    os.mkfifo(rogue)
    with pytest.raises(RuntimeError, match="unexpected"):
        _validate_build_output(output, extension)
    rogue.unlink()

    outside_link = tmp_path / "outside-link.so"
    os.link(extension, outside_link)
    with pytest.raises(RuntimeError, match="unique regular file"):
        _validate_build_output(output, extension)


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
    monkeypatch.setenv("TRAINVERIFY_COMP_PROFILE_SHA256", "d" * 64)
    monkeypatch.setenv("TRAINVERIFY_LLM_SOURCE_ROOT", "/trusted/llm")
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


def test_safe_cleanup_direct_script_runs_under_python_s(tmp_path):
    root = Path(__file__).resolve().parents[2]
    cleanup_script = root / "scripts" / "yoco_regen" / "safe_cleanup.py"
    result = subprocess.run(
        [sys.executable, "-S", str(cleanup_script), "create", str(tmp_path), "direct-"],
        cwd=root,
        env={
            "HOME": str(tmp_path),
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "PYTHONPATH": str(root),
        },
        text=True,
        capture_output=True,
        check=True,
    )
    stage_text, marker, dev, ino = result.stdout.strip().split("\t")
    assert cleanup_owned_stage(Path(stage_text), marker, int(dev), int(ino)) is True


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


def test_owned_stage_cleanup_restores_replacement_after_rename_race(
    tmp_path, monkeypatch,
):
    stage, marker, dev, ino = create_owned_stage(tmp_path, "stage-")
    preserved = tmp_path / "trusted-preserved"
    replacement = tmp_path / "replacement"
    replacement.mkdir()
    (replacement / "unrelated").write_text("keep", encoding="utf-8")
    real_renameat2 = safe_cleanup._renameat2
    calls = {"count": 0}

    def swap_then_rename(source_fd, source_name, target_fd, target_name):
        calls["count"] += 1
        if calls["count"] == 1:
            stage.rename(preserved)
            replacement.rename(stage)
        return real_renameat2(source_fd, source_name, target_fd, target_name)

    monkeypatch.setattr(safe_cleanup, "_renameat2", swap_then_rename)
    with pytest.raises(RuntimeError, match="stage inode changed"):
        cleanup_owned_stage(stage, marker, dev, ino)
    quarantine = next(tmp_path.glob(".*.cleanup-*"))
    assert (quarantine / "unrelated").read_text(encoding="utf-8") == "keep"
    assert preserved.is_dir()
    assert not stage.exists()
    assert calls["count"] == 1


def test_owned_stage_cleanup_rollback_never_moves_replacement(
    tmp_path, monkeypatch,
):
    stage, marker, dev, ino = create_owned_stage(tmp_path, "stage-")
    replacement = tmp_path / "replacement"
    replacement.mkdir()
    (replacement / "unrelated").write_text("keep", encoding="utf-8")
    preserved = tmp_path / "trusted-preserved"
    real_renameat2 = safe_cleanup._renameat2
    calls = {"count": 0}

    def replace_after_quarantine(source_fd, source_name, target_fd, target_name):
        calls["count"] += 1
        result = real_renameat2(source_fd, source_name, target_fd, target_name)
        if calls["count"] == 1:
            quarantine = tmp_path / target_name
            quarantine.rename(preserved)
            replacement.rename(quarantine)
        return result

    monkeypatch.setattr(safe_cleanup, "_renameat2", replace_after_quarantine)
    with pytest.raises(RuntimeError, match="stage inode changed"):
        cleanup_owned_stage(stage, marker, dev, ino)
    quarantine = next(tmp_path.glob(".*.cleanup-*"))
    assert (quarantine / "unrelated").read_text(encoding="utf-8") == "keep"
    assert preserved.is_dir()
    assert not stage.exists()
    assert calls["count"] == 1


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
        "comp_profile_sha256": "d" * 64,
        "dp_solver_extension_sha256": "f" * 64,
        "canonicalized_comment_count": 1,
        "canonicalized_code_count": 1,
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
        "comp_profile_sha256": "d" * 64,
        "dp_solver_extension_sha256": "f" * 64,
        "canonicalized_comment_count": 1,
        "canonicalized_code_count": 1,
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
        "comp_profile_sha256": "d" * 64,
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
        "comp_profile_sha256": "d" * 64,
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
    comp_forged = {**original, "comp_profile_sha256": "0" * 64}
    emitter.validate_hardware_schema(comp_forged)
    with pytest.raises(RuntimeError, match="trusted hardware"):
        emitter.validate_expected_hardware(comp_forged, expected)


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


def _write_snapshot_stage(root: Path) -> Path:
    stage = root / "stage"
    goals = stage / "yoco_goals"
    goals.mkdir(parents=True, mode=0o700)
    goals.chmod(0o700)
    marker = stage / ".trainverify-stage-owner"
    marker.write_text("owned", encoding="utf-8")
    marker.chmod(0o400)
    files = {"GeneratedYOCOMoE.lean": b"def generated : Nat := 1\n"}
    for name in sorted(emitter.REGISTERED_TOP_LEVEL_MODULES):
        files[name] = f"-- {name}\n".encode()
    for name in sorted(emitter.EXPECTED_GOAL_MODULES):
        files[f"yoco_goals/{name}"] = f"-- {name}\n".encode()
    for relative, content in files.items():
        path = stage / relative
        path.write_bytes(content)
        path.chmod(0o400)
    manifest = {
        "snapshot_sha256": {
            relative: hashlib.sha256(content).hexdigest()
            for relative, content in files.items()
        }
    }
    manifest_path = stage / "GeneratedYOCOMoE.manifest.json"
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
    manifest_path.chmod(0o400)
    return stage


def test_emitter_snapshot_stage_ledger_is_exact_and_fail_closed(tmp_path):
    stage = _write_snapshot_stage(tmp_path / "valid")
    emitter.verify_snapshot_stage(stage)

    missing_helper = _write_snapshot_stage(tmp_path / "missing-helper")
    (missing_helper / "EmbeddingHiddenShard.lean").unlink()
    with pytest.raises(RuntimeError, match="unexpected snapshot top-level paths"):
        emitter.verify_snapshot_stage(missing_helper)

    missing = _write_snapshot_stage(tmp_path / "missing")
    (missing / "yoco_goals" / "Goal_1.lean").unlink()
    with pytest.raises(RuntimeError, match="unexpected yoco_goals paths"):
        emitter.verify_snapshot_stage(missing)

    extra = _write_snapshot_stage(tmp_path / "extra")
    (extra / "yoco_goals" / "attacker.lean").write_text("axiom bad : False")
    with pytest.raises(RuntimeError, match="unexpected yoco_goals paths"):
        emitter.verify_snapshot_stage(extra)

    tampered = _write_snapshot_stage(tmp_path / "tampered")
    target = tampered / "yoco_goals" / "Goal_2.lean"
    target.chmod(0o600)
    target.write_text("-- changed\n", encoding="utf-8")
    target.chmod(0o400)
    with pytest.raises(RuntimeError, match="digest mismatch"):
        emitter.verify_snapshot_stage(tampered)

    linked = _write_snapshot_stage(tmp_path / "linked")
    target = linked / "yoco_goals" / "Goal_3.lean"
    target.unlink()
    target.symlink_to("Goal_2.lean")
    with pytest.raises(RuntimeError, match="untrusted snapshot inode"):
        emitter.verify_snapshot_stage(linked)


def test_snapshot_publish_binds_validated_stage_inode(tmp_path):
    source = _write_snapshot_stage(tmp_path / "source")
    replacement = _write_snapshot_stage(tmp_path / "replacement")
    source.parent.chmod(0o700)
    replacement.parent.chmod(0o700)
    target = tmp_path / "published"
    preserved = source.with_name("verified-preserved")
    calls = {"count": 0}

    def attack_after_validation(stage_fd):
        emitter.verify_snapshot_fd(stage_fd)
        calls["count"] += 1
        if calls["count"] == 1:
            source.rename(preserved)
            replacement.rename(source)

    with pytest.raises(RuntimeError, match="source entry differs"):
        publish_validated_directory(source, target, attack_after_validation)
    assert not target.exists()
    assert preserved.is_dir()
    assert source.is_dir()


def test_snapshot_publish_rollback_never_moves_replacement(tmp_path, monkeypatch):
    source = _write_snapshot_stage(tmp_path / "source")
    source.parent.chmod(0o700)
    target = tmp_path / "published"
    preserved = tmp_path / "trusted-preserved"
    calls = {"validator": 0, "rename": 0}
    real_renameat2 = atomic_publish._renameat2

    def counted_rename(*args):
        calls["rename"] += 1
        return real_renameat2(*args)

    def replace_after_publish(stage_fd):
        emitter.verify_snapshot_fd(stage_fd)
        calls["validator"] += 1
        if calls["validator"] == 2:
            target.rename(preserved)
            target.mkdir(mode=0o700)
            (target / "attacker").write_text("replacement", encoding="utf-8")

    monkeypatch.setattr(atomic_publish, "_renameat2", counted_rename)
    with pytest.raises(RuntimeError, match="target changed"):
        publish_validated_directory(source, target, replace_after_publish)
    assert not source.exists()
    assert (target / "attacker").read_text(encoding="utf-8") == "replacement"
    assert preserved.is_dir()
    assert calls["rename"] == 1


def test_emitter_main_sets_private_umask_before_parsing(monkeypatch):
    events = []

    class StopParser:
        def __init__(self, *args, **kwargs):
            events.append("parser")

        def add_argument(self, *args, **kwargs):
            return None

        def parse_args(self):
            raise RuntimeError("stop after parse")

    monkeypatch.setattr(emitter.os, "umask", lambda mode: events.append(("umask", mode)))
    monkeypatch.setattr(emitter.argparse, "ArgumentParser", StopParser)
    with pytest.raises(RuntimeError, match="stop after parse"):
        emitter.main()
    assert events[0] == ("umask", 0o077)


def test_emitter_lean_gate_uses_private_revision_and_propagates_failure(
    tmp_path, monkeypatch,
):
    stage = _write_snapshot_stage(tmp_path / "snapshot")
    cache_project = tmp_path / "cache-project"
    packages = cache_project / ".lake" / "packages"
    packages.mkdir(parents=True, mode=0o700)
    packages.chmod(0o700)
    revision = "a" * 40
    build_commands = []
    direct_build_calls = []
    fail_build = {"value": False}
    replace_cleanup = {"value": False, "replacement": None, "preserved": None}

    def fake_run(command, **kwargs):
        if command[:3] == ["git", "clone", "--quiet"]:
            repo = Path(command[-1])
            goals = repo / "trainverify" / "denote" / "yoco_goals"
            goals.mkdir(parents=True)
            (goals / "old.lean").write_text("-- old\n")
        elif command[0] == "/trusted/lake":
            build_commands.append(command)
            if command[1:3] == ["env", "lean"]:
                audit_text = (Path(kwargs["cwd"]) / "AxiomAudit.lean").read_text()
                assert audit_text.startswith("import denote.yoco_goals.Instances\n")
                assert "import denote.yoco_goals.Pattern_1\n" not in audit_text
                if replace_cleanup["value"]:
                    validation_root = Path(kwargs["cwd"]).parents[1]
                    preserved = validation_root.with_name(validation_root.name + "-preserved")
                    validation_root.rename(preserved)
                    validation_root.mkdir()
                    (validation_root / "unrelated").write_text("keep", encoding="utf-8")
                    replace_cleanup["replacement"] = validation_root
                    replace_cleanup["preserved"] = preserved
                output = "".join(
                    f"'{target}' does not depend on any axioms\n"
                    for target in PROOF_TARGETS
                )
                return types.SimpleNamespace(returncode=0, stdout=output, stderr="")
        return types.SimpleNamespace(returncode=0, stdout="", stderr="")

    def fake_direct_build(project, lake, targets, clean_env):
        direct_build_calls.append((project, lake, targets, clean_env))
        if fail_build["value"]:
            raise subprocess.CalledProcessError(1, [lake, "env", "lean"])

    monkeypatch.setattr(emitter.subprocess, "run", fake_run)
    monkeypatch.setattr(emitter, "direct_lean_build", fake_direct_build)
    monkeypatch.setattr(emitter, "git_head", lambda _repo: revision)
    monkeypatch.setattr(emitter, "git_clean", lambda _repo: True)
    monkeypatch.setattr(emitter.shutil, "which", lambda _name: "/trusted/lake")
    emitter.validate_lean_snapshot(stage, cache_project, revision, PROOF_TARGETS)
    assert len(direct_build_calls) == 1
    expected_direct_targets = tuple(sorted(
        set(emitter.LEAN_TARGETS)
        | {"denote.GeneratedYOCOMoE"}
        | {
            f"denote.yoco_goals.{path.stem}"
            for path in (stage / "yoco_goals").glob("*.lean")
        }
        | {
            f"denote.{Path(name).stem}"
            for name in emitter.REGISTERED_TOP_LEVEL_MODULES
        }
    ))
    assert direct_build_calls[0][1:] == (
        "/trusted/lake", expected_direct_targets,
        {
            "HOME": os.environ["HOME"], "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8",
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        },
    )
    assert build_commands == [
        ["/trusted/lake", "env", "lean", "AxiomAudit.lean"],
    ]
    assert all("build" not in command for command in build_commands)
    assert not list(stage.parent.glob(".trainverify-lean-validation-*"))

    fail_build["value"] = True
    with pytest.raises(subprocess.CalledProcessError):
        emitter.validate_lean_snapshot(stage, cache_project, revision, PROOF_TARGETS)
    assert not list(stage.parent.glob(".trainverify-lean-validation-*"))

    fail_build["value"] = False
    replace_cleanup["value"] = True
    with pytest.raises(RuntimeError, match="identity changed"):
        emitter.validate_lean_snapshot(stage, cache_project, revision, PROOF_TARGETS)
    assert (replace_cleanup["replacement"] / "unrelated").read_text() == "keep"
    assert replace_cleanup["preserved"].is_dir()


def test_direct_lean_build_respects_import_dag_and_four_worker_limit(
    tmp_path, monkeypatch,
):
    import threading
    import time

    project = tmp_path / "project"
    project.mkdir()
    dependencies = [f"Dep{index}" for index in range(6)]
    for module in dependencies:
        (project / f"{module}.lean").write_text("import Mathlib\n", encoding="utf-8")
    (project / "Target.lean").write_text(
        "import " + " ".join(dependencies) + "\n", encoding="utf-8",
    )
    calls = []
    lock = threading.Lock()
    active = 0
    peak = 0

    def fake_run(command, **kwargs):
        nonlocal active, peak
        assert command[:3] == ["/trusted/lake", "env", "lean"]
        assert "build" not in command
        assert kwargs["env"]["LEAN_NUM_THREADS"] == "1"
        with lock:
            active += 1
            peak = max(peak, active)
            calls.append(command[-1])
        time.sleep(0.02)
        output = Path(kwargs["cwd"]) / command[command.index("-o") + 1]
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(b"olean")
        output.chmod(0o600)
        with lock:
            active -= 1
        return types.SimpleNamespace(returncode=0)

    monkeypatch.setattr(emitter.subprocess, "run", fake_run)
    emitter.direct_lean_build(
        project, "/trusted/lake", ("Target",),
        {"HOME": os.environ["HOME"], "PATH": os.environ.get("PATH", "")},
    )
    assert peak == 4
    assert set(calls[:-1]) == {f"{module}.lean" for module in dependencies}
    assert calls[-1] == "Target.lean"

    local = project / "Local"
    local.mkdir()
    (local / "Broken.lean").write_text("import Local.Missing\n", encoding="utf-8")
    with pytest.raises(RuntimeError, match="missing project-local Lean imports"):
        emitter.direct_lean_build(
            project, "/trusted/lake", ("Local.Broken",),
            {"HOME": os.environ["HOME"], "PATH": os.environ.get("PATH", "")},
        )


def test_emitter_proof_registry_binds_exact_generated_statements_and_blobs(
    tmp_path, monkeypatch,
):
    stage = tmp_path / "stage"
    goals = stage / "yoco_goals"
    goals.mkdir(parents=True)
    generated = b"generated"
    generated_path = stage / "GeneratedYOCOMoE.lean"
    generated_path.write_bytes(generated)
    generated_path.chmod(0o600)
    goal_bytes = {}
    for index in range(1, 6):
        content = f"goal-{index}".encode()
        goal_bytes[f"Goal_{index}.lean"] = content
        goal_path = goals / f"Goal_{index}.lean"
        goal_path.write_bytes(content)
        goal_path.chmod(0o600)
    proof = b"proof without placeholders"
    registry = {
        "schema_version": 1,
        "generated_lean_sha256": emitter.digest_bytes(generated),
        "goal_sha256": {
            name: emitter.digest_bytes(content) for name, content in goal_bytes.items()
        },
        "modules": {
            "Pattern_2.lean": {
                "source": "trainverify/denote/yoco_goals/Pattern_2.lean",
                "sha256": emitter.digest_bytes(proof),
            }
        },
        "proof_targets": PROOF_TARGETS,
    }
    for helper_destination in sorted(emitter.REGISTERED_TOP_LEVEL_MODULES):
        registry["modules"][helper_destination] = {
            "source": f"trainverify/denote/{helper_destination}",
            "sha256": emitter.digest_bytes(proof),
        }
    for goal_destination in sorted(
        emitter.PROOF_REGISTRY_GOALS
        | emitter.REGISTERED_LEGACY_CUT_MODULES
        | emitter.REGISTERED_SEALED_DEPENDENCY_MODULES
    ):
        registry["modules"][goal_destination] = {
            "source": f"trainverify/denote/yoco_goals/{goal_destination}",
            "sha256": emitter.digest_bytes(proof),
        }
    monkeypatch.setattr(
        emitter, "git_blob", lambda _repo, _rev, path: proof
        if path.endswith("Pattern_2.lean") else b"",
    )
    loaded = emitter.validate_proof_registry(registry, stage)
    assert loaded == registry["modules"]

    missing_goal_overlay = json.loads(json.dumps(registry))
    del missing_goal_overlay["modules"]["Goal_1.lean"]
    with pytest.raises(RuntimeError, match="generated goal overlays"):
        emitter.validate_proof_registry(missing_goal_overlay, stage)

    missing_cut_overlay = json.loads(json.dumps(registry))
    del missing_cut_overlay["modules"]["Goal_1_Cut.lean"]
    with pytest.raises(RuntimeError, match="legacy cut overlays"):
        emitter.validate_proof_registry(missing_cut_overlay, stage)

    missing_sealed_dependency = json.loads(json.dumps(registry))
    del missing_sealed_dependency["modules"]["GatherOpGears.lean"]
    with pytest.raises(RuntimeError, match="sealed dependency modules"):
        emitter.validate_proof_registry(missing_sealed_dependency, stage)

    # A registry destination is a snapshot module name; its authenticated Git
    # source may be a differently named public theorem module.
    remapped = json.loads(json.dumps(registry))
    remapped["modules"]["Pattern_2.lean"]["source"] = (
        "trainverify/denote/yoco_goals/Goal2FaithfulFull.lean"
    )
    assert emitter.validate_proof_registry(remapped, stage) == remapped["modules"]

    bad = json.loads(json.dumps(registry))
    bad["goal_sha256"]["Goal_1.lean"] = "0" * 64
    with pytest.raises(RuntimeError, match="goal digest mismatch"):
        emitter.validate_proof_registry(bad, stage)
    bad = json.loads(json.dumps(registry))
    bad["unknown"] = 1
    with pytest.raises(RuntimeError, match="schema mismatch"):
        emitter.validate_proof_registry(bad, stage)
    bad = json.loads(json.dumps(registry))
    bad["modules"]["../escape.lean"] = bad["modules"].pop("Pattern_2.lean")
    with pytest.raises(RuntimeError, match="destination"):
        emitter.validate_proof_registry(bad, stage)
    bad = json.loads(json.dumps(registry))
    bad["proof_targets"][0] = "bad target"
    with pytest.raises(RuntimeError, match="targets"):
        emitter.validate_proof_registry(bad, stage)


def test_emitter_materializes_registered_proofs_atomically_and_refreshes_ledger(
    tmp_path, monkeypatch,
):
    stage = tmp_path / "stage"
    goals = stage / "yoco_goals"
    goals.mkdir(parents=True)
    generated = stage / "GeneratedYOCOMoE.lean"
    generated.write_bytes(b"generated")
    generated.chmod(0o600)
    goal_digests = {}
    for index in range(1, 6):
        path = goals / f"Goal_{index}.lean"
        path.write_bytes(f"goal-{index}".encode())
        path.chmod(0o600)
        goal_digests[path.name] = emitter.sha256(path)
    deprecated_generated_auxiliaries = {
        *(f"Goal_{index}_CutToFull.lean" for index in range(1, 6)),
        "Patterns.lean", "ProofObligations.lean",
    }
    for name in deprecated_generated_auxiliaries:
        path = goals / name
        path.write_text("theorem bogus_cut_to_full : True := by trivial\n", encoding="utf-8")
        path.chmod(0o600)
    patterns = {}
    blobs = {}
    modules = {}
    for index in (1, 2):
        destination = f"Pattern_{index}.lean"
        path = goals / destination
        path.write_bytes(f"old-{index}".encode())
        path.chmod(0o600)
        patterns[destination] = path
        source = f"trainverify/denote/yoco_goals/{destination}"
        blobs[source] = f"theorem proof_{index} : True := by trivial\n".encode()
        modules[destination] = {
            "source": source,
            "sha256": emitter.digest_bytes(blobs[source]),
        }
    for destination in sorted(
        emitter.PROOF_REGISTRY_GOALS
        | emitter.REGISTERED_LEGACY_CUT_MODULES
        | emitter.REGISTERED_SEALED_DEPENDENCY_MODULES
    ):
        if destination in emitter.REGISTERED_SEALED_DEPENDENCY_MODULES:
            static_path = goals / destination
            static_path.write_bytes(b"old-static")
            static_path.chmod(0o600)
        source = f"trainverify/denote/yoco_goals/{destination}"
        theorem_name = destination.removesuffix(".lean").lower()
        blobs[source] = f"theorem {theorem_name}_overlay : True := by trivial\n".encode()
        modules[destination] = {
            "source": source,
            "sha256": emitter.digest_bytes(blobs[source]),
        }
    for helper_destination in sorted(emitter.REGISTERED_TOP_LEVEL_MODULES):
        helper_source = f"trainverify/denote/{helper_destination}"
        blobs[helper_source] = (
            f"theorem helper_{helper_destination.removesuffix('.lean')} : True := by trivial\n"
        ).encode()
        modules[helper_destination] = {
            "source": helper_source,
            "sha256": emitter.digest_bytes(blobs[helper_source]),
        }
    manifest_path = stage / "GeneratedYOCOMoE.manifest.json"
    manifest = {
        "snapshot_sha256": {
            "GeneratedYOCOMoE.lean": emitter.sha256(generated),
            **{
                f"yoco_goals/{name}": emitter.sha256(path)
                for name, path in patterns.items()
                if name == "Pattern_1.lean"
            },
        }
    }
    manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
    manifest_path.chmod(0o600)
    registry = {
        "schema_version": 1,
        "generated_lean_sha256": emitter.sha256(generated),
        "goal_sha256": goal_digests,
        "modules": modules,
        "proof_targets": PROOF_TARGETS,
    }
    monkeypatch.setattr(emitter, "git_blob", lambda _repo, _rev, path: blobs[path])
    emitter.materialize_registered_proofs(tmp_path, "a" * 40, stage, registry)
    for destination, entry in modules.items():
        if destination in emitter.REGISTERED_TOP_LEVEL_MODULES:
            continue
        assert (goals / destination).read_bytes() == blobs[entry["source"]]
    helper_paths = {}
    for helper_destination in sorted(emitter.REGISTERED_TOP_LEVEL_MODULES):
        helper_source = modules[helper_destination]["source"]
        helper_path = stage / helper_destination
        helper_paths[helper_destination] = helper_path
        assert helper_path.read_bytes() == blobs[helper_source]
    refreshed = json.loads(manifest_path.read_text())
    for name in deprecated_generated_auxiliaries:
        assert not (goals / name).exists()
        assert f"yoco_goals/{name}" not in refreshed["snapshot_sha256"]
    for destination, path in patterns.items():
        assert refreshed["snapshot_sha256"][f"yoco_goals/{destination}"] == emitter.sha256(path)
    for destination in emitter.REGISTERED_LEGACY_CUT_MODULES:
        relative = f"yoco_goals/{destination}"
        assert refreshed["snapshot_sha256"][relative] == emitter.sha256(goals / destination)
    for helper_destination, helper_path in helper_paths.items():
        assert refreshed["snapshot_sha256"][helper_destination] == emitter.sha256(helper_path)

    before = {name: path.read_bytes() for name, path in patterns.items()}
    for destination in emitter.REGISTERED_LEGACY_CUT_MODULES:
        (goals / destination).unlink()
    registry["goal_sha256"] = {
        name: emitter.sha256(goals / name) for name in emitter.PROOF_REGISTRY_GOALS
    }
    with pytest.raises(RuntimeError, match="top-level destination already exists"):
        emitter.materialize_registered_proofs(tmp_path, "a" * 40, stage, registry)
    assert {name: path.read_bytes() for name, path in patterns.items()} == before
    for helper_path in helper_paths.values():
        helper_path.unlink()
    bad = json.loads(json.dumps(registry))
    bad["modules"]["Pattern_2.lean"]["sha256"] = "0" * 64
    with pytest.raises(RuntimeError, match="blob digest mismatch"):
        emitter.materialize_registered_proofs(tmp_path, "a" * 40, stage, bad)
    assert {name: path.read_bytes() for name, path in patterns.items()} == before

    proof2_source = modules["Pattern_2.lean"]["source"]
    for token in (b"sorry", b"sorryAx", b"axiom", b"unsafe"):
        blobs[proof2_source] = b"theorem x : True := by exact " + token + b"\n"
        bad = json.loads(json.dumps(registry))
        bad["modules"]["Pattern_2.lean"]["sha256"] = emitter.digest_bytes(
            blobs[proof2_source]
        )
        with pytest.raises(RuntimeError, match="forbidden proof token"):
            emitter.materialize_registered_proofs(tmp_path, "a" * 40, stage, bad)
        assert {name: path.read_bytes() for name, path in patterns.items()} == before


def test_emitter_rejects_nonbaseline_print_axioms_output():
    target = PROOF_TARGETS[0]
    baseline = (
        f"'{target}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound,\n "
        f"{target}._native.native_decide.ax_1_2]\n"
    )
    emitter.validate_print_axioms_output(baseline, [target])
    emitter.validate_print_axioms_output(
        f"'{target}' depends on axioms: "
        f"[{target}._native.native_decide.ax_1_2✝]\n",
        [target],
    )
    emitter.validate_print_axioms_output(
        f"'{target}' does not depend on any axioms\n", [target]
    )
    for bad in (
        "sorryAx", "Bad.customAxiom", "Bad.native_decide.ax_evil",
        "Bad.native_decide.ax_1", "Bad.customAxiom✝",
        "Bad.native_decide.ax_evil✝",
    ):
        with pytest.raises(RuntimeError, match="untrusted axioms"):
            emitter.validate_print_axioms_output(
                f"'{target}' depends on axioms: [{bad}]\n", [target]
            )
    with pytest.raises(RuntimeError, match="missing #print axioms"):
        emitter.validate_print_axioms_output("", [target])


def test_emitter_proof_registry_loader_requires_canonical_git_blob(monkeypatch):
    registry = {
        "schema_version": 1,
        "generated_lean_sha256": "a" * 64,
        "goal_sha256": {},
        "modules": {},
        "proof_targets": PROOF_TARGETS,
    }
    canonical = (
        json.dumps(registry, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode()
    monkeypatch.setattr(emitter, "git_blob", lambda *_args: canonical)
    assert emitter.load_proof_registry(Path("/unused"), "b" * 40) == registry
    monkeypatch.setattr(emitter, "git_blob", lambda *_args: json.dumps(registry).encode())
    with pytest.raises(RuntimeError, match="canonical JSON"):
        emitter.load_proof_registry(Path("/unused"), "b" * 40)


def test_emitter_materializes_static_goal_modules_from_git_blob_no_replace(tmp_path):
    target = tmp_path / "yoco_goals"
    target.mkdir()
    revision = emitter.git_head(emitter.ROOT)
    emitter.materialize_static_goal_modules(emitter.ROOT, revision, target)
    for relative_path in emitter.STATIC_GOAL_MODULES:
        destination = target / Path(relative_path).name
        assert destination.read_bytes() == emitter.git_blob(
            emitter.ROOT, revision, relative_path,
        )
    with pytest.raises(FileExistsError):
        emitter.materialize_static_goal_modules(emitter.ROOT, revision, target)


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
    assert '"$DP_SOLVER_SITE_GUARD/sitecustomize.py" "$LLM_WORK/llm"' in script
    assert "--allow-live-comp-profile" in script
    assert "scripts.yoco_regen.comp_profile create" in script
    assert "scripts.yoco_regen.comp_profile copy" in script
    assert "YOCO_COMP_PROFILE_ARTIFACT" in script
    assert "TRAINVERIFY_PRIVATE_MATERIALIZATION" in script
    assert '--trainverify-revision "$TRAINVERIFY_REV"' in script
    assert '--comp-profile "$STAGE/comp_profile.json"' in script
    assert "live computation profile directory survived freezing" in script
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
    assert '"PYTHONHASHSEED": "0"' in sealed
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
    assert '"PATH": "/usr/bin:/bin"' in builder
    assert "env=CLEAN_TOOL_ENV" in builder
    assert "NNSCALER_ARCHIVE_SHA256" in builder
    assert "memfd_create" in builder
    assert "F_ADD_SEALS" in builder
    assert '"-x", "c++"' in builder
    assert 'source_root / "setup.py"' not in builder
    assert '"build_ext"' not in builder
    assert "unshare" not in builder
    emitter = (
        Path(__file__).resolve().parents[1] / "yoco_regen" / "emit_yoco_a04b.py"
    ).read_text(encoding="utf-8")
    assert '"--verifier-cache-dir", str(stage / "verifier-cache")' in emitter
    assert 'shutil.rmtree(stage / "verifier-cache")' in emitter
    assert 'str(stage / "yoco_goals")' in emitter
    assert '(stage / "yoco_goals").mkdir()' in emitter
    assert '"--lean-project", type=Path, required=True' in emitter
    assert "validate_lean_snapshot(" in emitter
    assert 'proof_registry["proof_targets"]' in emitter
    assert "validate_print_axioms_output" in emitter
    assert "verify_snapshot_stage(stage)" in emitter
    assert "TRAINVERIFY_PRIVATE_MATERIALIZATION" in emitter
    assert 'stage / "goals"' not in emitter

    generator = (
        Path(__file__).resolve().parents[2] / "Verdict" / "graph_to_lean.py"
    ).read_text(encoding="utf-8")
    assert 'goal_lines.append("set_option maxRecDepth 100000")' in generator
    assert 'pattern_file_lines.append(f"import {goals_module_prefix}.Goal_{gid}")' in generator
    assert 'pattern_file_lines.append("open TrainVerify.Denote.GeneratedGoals")' in generator
    assert 'instance_lines.append("open TrainVerify.Denote.GeneratedGoals")' in generator
    assert "cut_to_full bridge omitted from this bounded snapshot" in generator
    assert "Main full-goal composition omitted" in generator
    assert 'goal_{gid}_cut_to_full prove_goal_{gid}_from_pattern_{pid}' in generator
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
