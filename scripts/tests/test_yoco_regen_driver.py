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


def _run_patched_dump(tmp_path, monkeypatch, local_rank, dump_function):
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
    }


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
