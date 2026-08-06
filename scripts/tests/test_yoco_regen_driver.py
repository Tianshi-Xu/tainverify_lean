from pathlib import Path
from functools import partial
import json
import pickle
import stat
import subprocess
import sys
import types

import pytest

from scripts.yoco_regen.patch_mgener_dump import MARKER, patch_source
from scripts.yoco_regen.patch_llm_cc12_gemm import (
    MARKER as CC12_MARKER,
    patch_source as patch_cc12_source,
)
from scripts.yoco_regen.atomic_publish import rename_noreplace
import scripts.yoco_regen.emit_yoco_a04b as emitter
from scripts.yoco_regen.safe_cleanup import create_owned_stage, cleanup_owned_stage
from scripts.yoco_regen.write_authority_metadata import validate_graph


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
    namespace = {
        "__file__": str(source_path),
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


def test_owned_stage_cleanup_requires_matching_marker(tmp_path):
    stage, real_marker, dev, ino = create_owned_stage(tmp_path, "stage-")
    (stage / "valuable").write_text("keep", encoding="utf-8")
    nested = stage / "nested"
    nested.mkdir()
    (nested / "payload").write_text("nested", encoding="utf-8")
    (stage / "payload-link").symlink_to("nested/payload")
    assert cleanup_owned_stage(stage, "owner-b", dev, ino) is False
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


def _fake_authority_graph(plan=1, missing_unshuffle=False):
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
            self._values = [types.SimpleNamespace(shape=(1, 4096))] if with_shape else []

        def inputs(self):
            return self._values

        def outputs(self):
            return []

    nodes = []
    for signature, count in counts.items():
        nodes.extend(Node(signature, not nodes and index == 0) for index in range(count))
    graph = types.SimpleNamespace(nodes=lambda: nodes)
    return types.SimpleNamespace(
        devices=list(range(plan)),
        compute_config=types.SimpleNamespace(plan_ngpus=plan, runtime_ngpus=plan),
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


def test_authority_graph_gate_accepts_only_full_autodist_graph():
    counts = validate_graph(_fake_authority_graph(), "sm", 1, _receipt())
    assert counts[
        "nnscaler.customized_ops.ring_attention.maybe_shuffle.wrap_maybe_unshuffle"
    ] == 25
    with pytest.raises(RuntimeError, match="structural minimum"):
        validate_graph(_fake_authority_graph(missing_unshuffle=True), "sm", 1, _receipt())
    with pytest.raises(RuntimeError, match="autodist_wrapper"):
        validate_graph(_fake_authority_graph(), "sm", 1, _receipt(policy="partial"))


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
    assert "git clone --quiet --no-hardlinks" in script
    assert "patch_llm_cc12_gemm.py" in script
    assert "TRAINVERIFY_PATCHED_LLM_GEMM_SHA256" in script
    assert 'export PYTHONPATH="$NNS_WORK:$LLM_WORK/llm:${PYTHONPATH:-}"' in script
    assert "export PYTHONSAFEPATH=1" in script
    assert "git -C \"$NNS_SOURCE\" status" in script
    assert "git -C \"$NNS\" restore" not in script
    assert "atomic_publish.py" in script
    assert "trap - EXIT" in script


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
