"""Deterministic, immutable provenance records for generated Lean snapshots."""

from __future__ import annotations

import hashlib
import json
import platform
import re
import subprocess
from importlib import metadata
from pathlib import Path, PurePosixPath
from typing import Any, Iterable, Mapping, Sequence


_COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
_PATH_FLAGS = {
    "--sm-pkl": "$AUTHORITY_DIR",
    "--pm-pkl": "$AUTHORITY_DIR",
    "--metadata-json": "$AUTHORITY_DIR",
    "--out": "$OUTPUT_DIR",
    "--manifest-out": "$OUTPUT_DIR",
    "--goals-out-dir": "$OUTPUT_DIR",
    "--spec-out": "$OUTPUT_DIR",
    "--verifier-cache-dir": "$OUTPUT_DIR",
    "--llm-train-repo": "$LLM_TRAIN_REPO",
    "--nnscaler-repo": "$NNSCALER_REPO",
}


class ProvenanceError(ValueError):
    """The requested provenance record is incomplete or inconsistent."""


def sha256_file(path: str | Path, chunk_size: int = 1024 * 1024) -> str:
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        while chunk := stream.read(chunk_size):
            digest.update(chunk)
    return digest.hexdigest()


def git_revision(repo: str | Path) -> str:
    path = Path(repo)
    try:
        revision = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            check=True, capture_output=True, text=True,
        ).stdout.strip().lower()
    except (OSError, subprocess.CalledProcessError) as exc:
        raise ProvenanceError(f"cannot resolve git revision for {path}: {exc}") from exc
    _validate_commit("revision", revision)
    return revision


def installed_package_versions(names: Iterable[str]) -> dict[str, str]:
    versions: dict[str, str] = {}
    for name in sorted(set(names)):
        try:
            versions[name] = metadata.version(name)
        except metadata.PackageNotFoundError as exc:
            raise ProvenanceError(f"required package version unavailable: {name}") from exc
    return versions


def normalize_command(command: Sequence[str]) -> list[str]:
    """Remove checkout-specific absolute paths while retaining reproducible operands."""
    normalized: list[str] = []
    path_prefix: str | None = None
    artifact_file = False
    for token in command:
        if artifact_file:
            name, separator, raw_path = str(token).partition("=")
            if not separator or not name or not raw_path:
                raise ProvenanceError("--artifact-file must be NAME=PATH")
            artifact_name = Path(raw_path.replace("\\", "/")).name
            normalized.append(f"{name}=$AUTHORITY_DIR/{artifact_name}")
            artifact_file = False
            continue
        if path_prefix is not None:
            normalized.append(f"{path_prefix}/{Path(token).name}")
            path_prefix = None
            continue
        normalized.append(str(token).replace("\\", "/"))
        artifact_file = str(token) == "--artifact-file"
        path_prefix = _PATH_FLAGS.get(str(token))
    if artifact_file or path_prefix is not None:
        raise ProvenanceError("path-bearing command flag is missing its operand")
    return normalized


def deterministic_json_bytes(value: Mapping[str, Any]) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, separators=(",", ": ")) + "\n").encode("utf-8")


def _validate_commit(field: str, revision: str) -> None:
    if not revision:
        raise ProvenanceError(f"missing authority revision: {field}")
    if not _COMMIT_RE.fullmatch(revision.lower()):
        raise ProvenanceError(f"{field} must be a full 40-character git commit")


def _check_expected(field: str, actual: str, expected: Mapping[str, str]) -> None:
    declared = expected.get(field)
    if declared is not None and declared.lower() != actual:
        raise ProvenanceError(f"{field} mismatch: declared {declared}, computed {actual}")


def build_manifest(
    *, model: str, sm_pkl: str | Path, pm_pkl: str | Path,
    metadata_files: Sequence[str | Path], llm_train_commit: str,
    nnscaler_commit: str, emitter: str | Path, generated_lean: str | Path,
    command: Sequence[str], packages: Mapping[str, str],
    deduplicated_intermediate_tids: Sequence[int], final_goal_tids: Sequence[int],
    intermediate_goal_tids: Sequence[int], expected_hashes: Mapping[str, str] | None = None,
    artifact_files: Mapping[str, str | Path] | None = None,
    input_value_classes: Mapping[str, Sequence[tuple[str, Sequence[int]]]] | None = None,
    snapshot_files: Mapping[str, str | Path] | None = None,
) -> dict[str, Any]:
    _validate_commit("llm_train_commit", llm_train_commit)
    _validate_commit("nnscaler_commit", nnscaler_commit)
    if not model:
        raise ProvenanceError("model is required")
    expected = expected_hashes or {}
    sm_hash = sha256_file(sm_pkl)
    pm_hash = sha256_file(pm_pkl)
    _check_expected("sm_pkl_sha256", sm_hash, expected)
    _check_expected("pm_pkl_sha256", pm_hash, expected)
    metadata_hashes: dict[str, str] = {}
    for source in metadata_files:
        name = Path(source).name
        if name in metadata_hashes:
            raise ProvenanceError(f"duplicate metadata basename: {name}")
        metadata_hashes[name] = sha256_file(source)
        _check_expected(f"metadata_sha256.{name}", metadata_hashes[name], expected)
    artifact_hashes: dict[str, str] = {}
    for name, source in sorted((artifact_files or {}).items()):
        if not name or Path(name).name != name:
            raise ProvenanceError(f"invalid artifact name: {name}")
        if name in artifact_hashes:
            raise ProvenanceError(f"duplicate artifact name: {name}")
        artifact_hashes[name] = sha256_file(source)
        expected_field = f"artifact_sha256.{name}"
        if expected_field not in expected:
            raise ProvenanceError(f"missing expected artifact hash: {name}")
        _check_expected(expected_field, artifact_hashes[name], expected)
    consumed_expected = {"sm_pkl_sha256", "pm_pkl_sha256"}
    consumed_expected.update(f"metadata_sha256.{name}" for name in metadata_hashes)
    consumed_expected.update(f"artifact_sha256.{name}" for name in artifact_hashes)
    unexpected = set(expected) - consumed_expected
    if unexpected:
        raise ProvenanceError(f"unconsumed expected hashes: {sorted(unexpected)}")
    class_data = {
        side: [
            {"source": str(source), "tids": sorted(set(map(int, tids)))}
            for source, tids in sorted(classes)
        ]
        for side, classes in sorted((input_value_classes or {}).items())
    }
    snapshot_hashes: dict[str, str] = {}
    for name, source in sorted((snapshot_files or {}).items()):
        normalized = str(name).replace("\\", "/")
        path = PurePosixPath(normalized)
        if (
            not normalized or path.is_absolute() or normalized != path.as_posix()
            or any(part in {"", ".", ".."} for part in path.parts)
            or path.suffix != ".lean"
        ):
            raise ProvenanceError(f"invalid snapshot path: {name}")
        if normalized in snapshot_hashes:
            raise ProvenanceError(f"duplicate snapshot path: {normalized}")
        snapshot_hashes[normalized] = sha256_file(source)
    return {
        "artifact_sha256": dict(sorted(artifact_hashes.items())),
        "command": normalize_command(command),
        "deduplicated_intermediate_tids": sorted(set(map(int, deduplicated_intermediate_tids))),
        "emitter_sha256": sha256_file(emitter),
        "final_goal_count": len(set(map(int, final_goal_tids))),
        "final_goal_tids": sorted(set(map(int, final_goal_tids))),
        "generated_lean_sha256": sha256_file(generated_lean),
        "intermediate_goal_count": len(set(map(int, intermediate_goal_tids))),
        "intermediate_goal_tids": sorted(set(map(int, intermediate_goal_tids))),
        "input_value_class_count": sum(len(classes) for classes in class_data.values()),
        "input_value_classes": class_data,
        "llm_train_commit": llm_train_commit.lower(),
        "metadata_sha256": dict(sorted(metadata_hashes.items())),
        "model": model,
        "nnscaler_commit": nnscaler_commit.lower(),
        "packages": dict(sorted((str(k), str(v)) for k, v in packages.items())),
        "pm_pkl_sha256": pm_hash,
        "python": platform.python_version(),
        "schema_version": 3,
        "sm_pkl_sha256": sm_hash,
        "snapshot_sha256": dict(sorted(snapshot_hashes.items())),
    }


def write_manifest(path: str | Path, manifest: Mapping[str, Any]) -> None:
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(deterministic_json_bytes(manifest))
