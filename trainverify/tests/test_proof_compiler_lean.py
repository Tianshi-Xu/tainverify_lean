from __future__ import annotations

import hashlib
import json
import copy
import subprocess
import sys
from pathlib import Path

import pytest

from trainverify.proof_compiler import compile_job
from trainverify.proof_compiler.lean_emitter import LeanEmissionError, emit_lean_certificate


REPO_ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = REPO_ROOT / "trainverify"


def _target_sha(observables: list[dict]) -> str:
    payload = json.dumps(observables, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def _authority_provenance() -> dict:
    mapping = [{"rank": 0, "tid": 201}]
    return {
        "kind": "authority_input",
        "source": "kernel-fixture",
        "authority_sha256": "a" * 64,
        "value_witness": {
            "kind": "authority_tensor_mapping",
            "sm_tid": 101,
            "pm_tids": mapping,
        },
        "ownership_witness": {"kind": "exact_rank_set", "ranks": [0]},
    }


def _fixture(*, theorem: str = "TrainVerify.Denote.ProofCompiler.fw_contiguous_equal") -> tuple[dict, dict, dict]:
    observables = [{"sm_tid": 102, "pm_tids": [{"rank": 0, "tid": 202}]}]
    job = {
        "schema_version": 1,
        "num_ranks": 1,
        "target_manifest_sha256": _target_sha(observables),
        "sm_nodes": [{
            "logical_id": "unseen_identity",
            "rank": 0,
            "op": "OpName.FW_contiguous",
            "ins": [101],
            "outs": [102],
        }],
        "pm_nodes": [{
            "logical_id": "unseen_identity",
            "rank": 0,
            "op": "OpName.FW_contiguous",
            "ins": [201],
            "outs": [202],
        }],
        "input_relations": [{
            "sm_tid": 101,
            "pm_tids": [{"rank": 0, "tid": 201}],
            "relation": {"kind": "equal"},
            "provenance": _authority_provenance(),
        }],
        "observables": observables,
    }
    library = {
        "denotations": [{
            "op": "OpName.FW_contiguous",
            "lean_definition": "TrainVerify.Denote.fw_contiguous",
        }],
        "rules": [{
            "name": "fw_contiguous_equal",
            "sm_op": "OpName.FW_contiguous",
            "pm_op": "OpName.FW_contiguous",
            "input_relations": [{"kind": "equal"}],
            "output_relations": [{"from_input": 0}],
            "lean_theorem": theorem,
            "kernel_semantics": {"kind": "unary_map"},
        }],
    }
    result = compile_job(job, library)
    return job, library, result


def _replicated_fixture() -> tuple[dict, dict, dict]:
    output_mapping = [{"rank": 0, "tid": 202}, {"rank": 1, "tid": 302}]
    observables = [{"sm_tid": 102, "pm_tids": output_mapping}]
    input_mapping = [{"rank": 0, "tid": 201}, {"rank": 1, "tid": 301}]
    job = {
        "schema_version": 1,
        "num_ranks": 2,
        "target_manifest_sha256": _target_sha(observables),
        "sm_nodes": [{
            "logical_id": "replicated_identity", "rank": 0,
            "op": "OpName.FW_contiguous", "ins": [101], "outs": [102],
        }],
        "pm_nodes": [
            {"logical_id": "replicated_identity", "rank": 0,
             "op": "OpName.FW_contiguous", "ins": [201], "outs": [202]},
            {"logical_id": "replicated_identity", "rank": 1,
             "op": "OpName.FW_contiguous", "ins": [301], "outs": [302]},
        ],
        "input_relations": [{
            "sm_tid": 101, "pm_tids": input_mapping,
            "relation": {"kind": "replicated"},
            "provenance": {
                "kind": "authority_input", "source": "replicated-fixture",
                "authority_sha256": "b" * 64,
                "value_witness": {"kind": "same_authority_tensor", "sm_tid": 101},
                "ownership_witness": {"kind": "exact_rank_set", "ranks": [0, 1]},
            },
        }],
        "observables": observables,
    }
    library = {
        "denotations": [{
            "op": "OpName.FW_contiguous",
            "lean_definition": "TrainVerify.Denote.fw_contiguous",
        }],
        "rules": [{
            "name": "fw_contiguous_replicated",
            "sm_op": "OpName.FW_contiguous",
            "pm_op": "OpName.FW_contiguous",
            "input_relations": [{"kind": "replicated"}],
            "output_relations": [{"from_input": 0}],
            "lean_theorem": "TrainVerify.Denote.ProofCompiler.fw_contiguous_replicated",
            "kernel_semantics": {"kind": "unary_map"},
        }],
    }
    result = compile_job(job, library)
    return job, library, result


def _run_lean(path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=LEAN_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )


def test_emits_kernel_checked_unseen_unary_dag(tmp_path: Path) -> None:
    job, library, result = _fixture()
    assert result["status"] == "certificate"
    source = emit_lean_certificate(job, library, result, namespace="GeneratedUnseen")
    output = tmp_path / "GeneratedUnseen.lean"
    output.write_text(source)
    checked = _run_lean(output)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert "axiom" not in source
    assert "sorry" not in source
    assert "theorem compiledCertificate" in source


def test_emits_kernel_checked_two_rank_replication(tmp_path: Path) -> None:
    job, library, result = _replicated_fixture()
    assert result["status"] == "certificate"
    source = emit_lean_certificate(job, library, result, namespace="GeneratedReplicated")
    output = tmp_path / "GeneratedReplicated.lean"
    output.write_text(source)
    checked = _run_lean(output)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    assert "numRanks := 1" in source
    assert "numRanks := 2" in source


def test_forged_lean_theorem_fails_kernel(tmp_path: Path) -> None:
    job, library, result = _fixture(theorem="Attacker.Forged.theorem")
    assert result["status"] == "certificate"
    source = emit_lean_certificate(job, library, result, namespace="GeneratedForged")
    output = tmp_path / "GeneratedForged.lean"
    output.write_text(source)
    checked = _run_lean(output)
    assert checked.returncode != 0
    assert "unknownIdentifier" in checked.stdout + checked.stderr


def test_emitter_rejects_rule_without_closed_kernel_semantics() -> None:
    job, library, result = _fixture()
    del library["rules"][0]["kernel_semantics"]
    with pytest.raises(LeanEmissionError, match="kernel_semantics"):
        emit_lean_certificate(job, library, result)


def test_emitter_rejects_certificate_from_different_job() -> None:
    job, library, result = _fixture()
    stale_job = copy.deepcopy(job)
    stale_job["pm_nodes"][0]["ins"] = [999]
    with pytest.raises(LeanEmissionError, match="does not exactly match"):
        emit_lean_certificate(stale_job, library, result)


def test_emitter_rejects_unsupported_relation() -> None:
    job, library, _ = _fixture()
    zigzag = {"kind": "zigzag", "dim": 0, "parts": 1, "block_size": 1}
    job["observables"][0]["relation"] = zigzag
    job["target_manifest_sha256"] = _target_sha(job["observables"])
    library["rules"][0]["output_relations"] = [{"relation": zigzag}]
    result = compile_job(job, library)
    assert result["status"] == "certificate"
    with pytest.raises(LeanEmissionError, match="unsupported kernel relation"):
        emit_lean_certificate(job, library, result)


def _run_cli(
    job: dict, library: dict, output: Path, tmp_path: Path
) -> subprocess.CompletedProcess[str]:
    job_path = tmp_path / "job.json"
    library_path = tmp_path / "library.json"
    job_path.write_text(json.dumps(job))
    library_path.write_text(json.dumps(library))
    return subprocess.run(
        [
            sys.executable,
            str(REPO_ROOT / "trainverify/scripts/proof_compile_lean.py"),
            "--job", str(job_path),
            "--library", str(library_path),
            "--output", str(output),
            "--namespace", "GeneratedCli",
            "--check",
            "--lean-root", str(LEAN_ROOT),
        ],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )


def test_one_command_kernel_checks_and_publishes_no_replace(tmp_path: Path) -> None:
    job, library, _ = _fixture()
    output = tmp_path / "GeneratedCli.lean"
    first = _run_cli(job, library, output, tmp_path)
    assert first.returncode == 0, first.stdout + first.stderr
    assert json.loads(first.stdout)["status"] == "kernel_certificate"
    assert output.exists()

    second = _run_cli(job, library, output, tmp_path)
    assert second.returncode == 2
    assert json.loads(second.stdout)["failure"]["reason"] == "output_already_exists"


def test_one_command_rejects_broken_output_symlink(tmp_path: Path) -> None:
    job, library, _ = _fixture()
    target = tmp_path / "redirected.lean"
    output = tmp_path / "GeneratedCli.lean"
    output.symlink_to(target)
    checked = _run_cli(job, library, output, tmp_path)
    assert checked.returncode == 2
    assert json.loads(checked.stdout)["failure"]["reason"] == "output_already_exists"
    assert output.is_symlink()
    assert not target.exists()


def test_one_command_rejects_untrusted_output_directory(tmp_path: Path) -> None:
    job, library, _ = _fixture()
    unsafe = tmp_path / "unsafe"
    unsafe.mkdir()
    unsafe.chmod(0o777)
    checked = _run_cli(job, library, unsafe / "Generated.lean", tmp_path)
    assert checked.returncode == 2
    assert json.loads(checked.stdout)["failure"]["reason"] == "insecure_output_directory"


def test_one_command_path_setup_failure_is_structured(tmp_path: Path) -> None:
    job, library, _ = _fixture()
    not_directory = tmp_path / "not-directory"
    not_directory.write_text("x")
    checked = _run_cli(job, library, not_directory / "Generated.lean", tmp_path)
    assert checked.returncode == 2
    assert json.loads(checked.stdout)["failure"]["reason"] == "output_path_invalid"
    assert checked.stderr == ""


def test_one_command_does_not_publish_kernel_rejection(tmp_path: Path) -> None:
    job, library, _ = _fixture(theorem="Attacker.Forged.theorem")
    output = tmp_path / "Rejected.lean"
    checked = _run_cli(job, library, output, tmp_path)
    assert checked.returncode == 2
    assert json.loads(checked.stdout)["failure"]["reason"] == "lean_kernel_rejected"
    assert checked.stderr == ""
    assert not output.exists()

    repeated = _run_cli(job, library, output, tmp_path)
    assert repeated.returncode == 2
    assert repeated.stdout == checked.stdout
