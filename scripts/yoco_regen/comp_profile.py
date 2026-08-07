#!/usr/bin/env python3
"""Create, extract, and verify an authenticated nnScaler computation profile."""
from __future__ import annotations

import argparse
import base64
import binascii
import hashlib
import hmac
import json
import math
import os
import stat
from pathlib import Path
from typing import Any

_SCHEMA_VERSION = 1
_FILE_KEYS = {"name", "sha256", "content_base64"}
_METRIC_KEYS = {
    "in_mem_info", "param_mem_info", "buffer_mem_info", "fw_span", "bw_span",
    "infer_memory", "train_mem_info", "train_mem2in_idx",
}


def _reject_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON constant: {value}")


def _reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _strict_json(content: bytes, label: str) -> Any:
    try:
        return json.loads(
            content.decode("utf-8"),
            object_pairs_hook=_reject_duplicate_pairs,
            parse_constant=_reject_constant,
        )
    except (UnicodeDecodeError, ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"invalid JSON in {label}: {exc}") from exc


def _is_nonnegative_int(value: Any) -> bool:
    return type(value) is int and value >= 0


def _is_nonnegative_finite_number(value: Any) -> bool:
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


def _validate_metric_list(value: Any, label: str, *, signed: bool = False) -> None:
    if not isinstance(value, list) or any(
        type(item) is not int or (item < -1 if signed else item < 0) for item in value
    ):
        raise RuntimeError(f"invalid computation profile metric list: {label}")


def _validate_profile_json(content: bytes, name: str) -> None:
    profile = _strict_json(content, name)
    if not isinstance(profile, dict) or not profile:
        raise RuntimeError(f"computation profile file must contain a nonempty object: {name}")
    for serialized, metrics in profile.items():
        if not isinstance(serialized, str) or not serialized:
            raise RuntimeError(f"invalid serialized operation key in {name}")
        if not isinstance(metrics, dict) or set(metrics) != _METRIC_KEYS:
            raise RuntimeError(f"computation profile metric schema mismatch in {name}")
        for field in (
            "in_mem_info", "param_mem_info", "buffer_mem_info", "train_mem_info",
        ):
            _validate_metric_list(metrics[field], f"{name}:{field}")
        _validate_metric_list(
            metrics["train_mem2in_idx"], f"{name}:train_mem2in_idx", signed=True,
        )
        if len(metrics["train_mem_info"]) != len(metrics["train_mem2in_idx"]):
            raise RuntimeError(f"computation profile saved-tensor schema mismatch in {name}")
        if not _is_nonnegative_finite_number(metrics["fw_span"]):
            raise RuntimeError(f"invalid forward span in {name}")
        if not _is_nonnegative_finite_number(metrics["bw_span"]):
            raise RuntimeError(f"invalid backward span in {name}")
        if not _is_nonnegative_int(metrics["infer_memory"]):
            raise RuntimeError(f"invalid inference memory in {name}")


def _profile_files(source: Path) -> list[tuple[str, bytes]]:
    source = source.resolve()
    if not source.is_dir():
        raise RuntimeError("computation profile source is not a directory")
    entries = list(source.iterdir())
    if not entries:
        raise RuntimeError("computation profile is empty")
    files: list[tuple[str, bytes]] = []
    for path in entries:
        info = path.lstat()
        name = path.name
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.getuid()
            or stat.S_IMODE(info.st_mode) & 0o022
            or path.parent != source
            or Path(name).name != name
            or "\\" in name
            or not name.endswith(".json")
        ):
            raise RuntimeError("computation profile must contain only owned regular JSON files")
        content = path.read_bytes()
        _validate_profile_json(content, name)
        files.append((name, content))
    files.sort(key=lambda item: item[0].encode("utf-8"))
    if len({name for name, _ in files}) != len(files):
        raise RuntimeError("duplicate computation profile filename")
    return files


def artifact_bytes(source: Path) -> bytes:
    files = [
        {
            "name": name,
            "sha256": hashlib.sha256(content).hexdigest(),
            "content_base64": base64.b64encode(content).decode("ascii"),
        }
        for name, content in _profile_files(source)
    ]
    value = {"schema_version": _SCHEMA_VERSION, "files": files}
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")


def create_artifact(source: Path, output: Path) -> bytes:
    content = artifact_bytes(source)
    output = output.absolute()
    output.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(output, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o400)
    try:
        with os.fdopen(fd, "wb", closefd=False) as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
    finally:
        os.close(fd)
    return content


def _decode_artifact_bytes(raw: bytes, label: str) -> list[tuple[str, bytes]]:
    value = _strict_json(raw, label)
    if not isinstance(value, dict) or set(value) != {"schema_version", "files"}:
        raise RuntimeError("computation profile artifact schema mismatch")
    if value["schema_version"] != _SCHEMA_VERSION or not isinstance(value["files"], list):
        raise RuntimeError("computation profile artifact version mismatch")
    if not value["files"]:
        raise RuntimeError("computation profile artifact is empty")
    result: list[tuple[str, bytes]] = []
    prior: bytes | None = None
    for record in value["files"]:
        if not isinstance(record, dict) or set(record) != _FILE_KEYS:
            raise RuntimeError("computation profile artifact file schema mismatch")
        name = record["name"]
        encoded = record["content_base64"]
        expected = record["sha256"]
        if (
            not isinstance(name, str)
            or Path(name).name != name
            or "\\" in name
            or not name.endswith(".json")
            or not isinstance(encoded, str)
            or not isinstance(expected, str)
            or len(expected) != 64
            or any(char not in "0123456789abcdef" for char in expected)
        ):
            raise RuntimeError("invalid computation profile artifact file record")
        ordering = name.encode("utf-8")
        if prior is not None and ordering <= prior:
            raise RuntimeError("computation profile artifact filenames are not unique and sorted")
        prior = ordering
        try:
            content = base64.b64decode(encoded, validate=True)
        except (ValueError, binascii.Error) as exc:
            raise RuntimeError("invalid computation profile base64") from exc
        if not hmac.compare_digest(hashlib.sha256(content).hexdigest(), expected):
            raise RuntimeError("computation profile content hash mismatch")
        _validate_profile_json(content, name)
        result.append((name, content))
    canonical = {
        "schema_version": _SCHEMA_VERSION,
        "files": [
            {
                "name": name,
                "sha256": hashlib.sha256(content).hexdigest(),
                "content_base64": base64.b64encode(content).decode("ascii"),
            }
            for name, content in result
        ],
    }
    canonical_bytes = (
        json.dumps(canonical, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("utf-8")
    if not hmac.compare_digest(raw, canonical_bytes):
        raise RuntimeError("computation profile artifact encoding is not canonical")
    return result


def _decode_artifact(artifact: Path) -> list[tuple[str, bytes]]:
    return _decode_artifact_bytes(artifact.read_bytes(), artifact.name)


def extract_artifact(artifact: Path, target: Path) -> None:
    files = _decode_artifact(artifact.resolve())
    target = target.absolute()
    target.mkdir(mode=0o700, parents=False, exist_ok=False)
    directory_fd = os.open(target, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for name, content in files:
            fd = os.open(
                name,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                0o400,
                dir_fd=directory_fd,
            )
            try:
                with os.fdopen(fd, "wb", closefd=False) as handle:
                    handle.write(content)
                    handle.flush()
                    os.fsync(handle.fileno())
            finally:
                os.close(fd)
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)


def verify_artifact(source: Path, artifact: Path) -> None:
    expected = artifact.resolve().read_bytes()
    _decode_artifact(artifact.resolve())
    actual = artifact_bytes(source)
    if not hmac.compare_digest(actual, expected):
        raise RuntimeError("consumed computation profile changed from authenticated artifact")


def validate_artifact(artifact: Path) -> str:
    artifact = artifact.resolve()
    _decode_artifact(artifact)
    return hashlib.sha256(artifact.read_bytes()).hexdigest()


def copy_artifact(source: Path, output: Path) -> str:
    descriptor = os.open(source.absolute(), os.O_RDONLY | os.O_NOFOLLOW)
    try:
        info = os.fstat(descriptor)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.getuid()
            or stat.S_IMODE(info.st_mode) & 0o022
        ):
            raise PermissionError("untrusted computation profile artifact inode")
        chunks = []
        while chunk := os.read(descriptor, 1 << 20):
            chunks.append(chunk)
        content = b"".join(chunks)
    finally:
        os.close(descriptor)
    _decode_artifact_bytes(content, source.name)
    output = output.absolute()
    target = os.open(
        output, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o400,
    )
    try:
        with os.fdopen(target, "wb", closefd=False) as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
    finally:
        os.close(target)
    return hashlib.sha256(content).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="action", required=True)
    create = subparsers.add_parser("create")
    create.add_argument("source", type=Path)
    create.add_argument("artifact", type=Path)
    extract = subparsers.add_parser("extract")
    extract.add_argument("artifact", type=Path)
    extract.add_argument("target", type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("source", type=Path)
    verify.add_argument("artifact", type=Path)
    copy = subparsers.add_parser("copy")
    copy.add_argument("source", type=Path)
    copy.add_argument("artifact", type=Path)
    args = parser.parse_args()
    if args.action == "create":
        create_artifact(args.source, args.artifact)
    elif args.action == "extract":
        extract_artifact(args.artifact, args.target)
    elif args.action == "verify":
        verify_artifact(args.source, args.artifact)
    else:
        print(copy_artifact(args.source, args.artifact))


if __name__ == "__main__":
    main()
