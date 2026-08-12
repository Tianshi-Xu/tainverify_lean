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
import secrets
import stat
from pathlib import Path
from typing import Any

if __package__:
    from .atomic_publish import _renameat2
    from .cleanup_errors import closing_fd, raise_failures
    from .strict_json import loads_strict_json
else:
    from atomic_publish import _renameat2
    from cleanup_errors import closing_fd, raise_failures
    from strict_json import loads_strict_json

_SCHEMA_VERSION = 1
_FILE_KEYS = {"name", "sha256", "content_base64"}
_METRIC_KEYS = {
    "in_mem_info", "param_mem_info", "buffer_mem_info", "fw_span", "bw_span",
    "infer_memory", "train_mem_info", "train_mem2in_idx",
}


def _is_nonnegative_int(value: Any) -> bool:
    return type(value) is int and value >= 0


def _is_nonnegative_finite_number(value: Any) -> bool:
    if type(value) is int:
        return value >= 0
    return type(value) is float and math.isfinite(value) and value >= 0


def _validate_metric_list(value: Any, label: str, *, signed: bool = False) -> None:
    if not isinstance(value, list) or any(
        type(item) is not int or (item < -1 if signed else item < 0) for item in value
    ):
        raise RuntimeError(f"invalid computation profile metric list: {label}")


def _validate_profile_json(content: bytes, name: str) -> None:
    profile = loads_strict_json(content, name)
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


def _read_fd_all(descriptor: int) -> bytes:
    chunks: list[bytes] = []
    while chunk := os.read(descriptor, 1 << 20):
        chunks.append(chunk)
    return b"".join(chunks)


def _read_owned_regular(path: Path, label: str) -> bytes:
    descriptor = os.open(path.absolute(), os.O_RDONLY | os.O_NOFOLLOW)
    with closing_fd(descriptor, "read and computation-profile close both failed"):
        info = os.fstat(descriptor)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.getuid()
            or stat.S_IMODE(info.st_mode) & 0o022
        ):
            raise PermissionError(f"untrusted computation profile inode: {label}")
        return _read_fd_all(descriptor)


def _profile_files(source: Path) -> list[tuple[str, bytes]]:
    source = source.absolute()
    directory_fd = os.open(source, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    with closing_fd(directory_fd, "profile scan and directory close both failed"):
        names = os.listdir(directory_fd)
        if not names:
            raise RuntimeError("computation profile is empty")
        files: list[tuple[str, bytes]] = []
        for name in names:
            if Path(name).name != name or "\\" in name or not name.endswith(".json"):
                raise RuntimeError(
                    "computation profile must contain only owned regular JSON files"
                )
            descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=directory_fd)
            with closing_fd(descriptor, "profile read and file close both failed"):
                info = os.fstat(descriptor)
                if (
                    not stat.S_ISREG(info.st_mode)
                    or info.st_uid != os.getuid()
                    or stat.S_IMODE(info.st_mode) & 0o022
                ):
                    raise RuntimeError(
                        "computation profile must contain only owned regular JSON files"
                    )
                content = _read_fd_all(descriptor)
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
    with closing_fd(fd, "artifact write and file close both failed"):
        with os.fdopen(fd, "wb", closefd=False) as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
    return content


def _decode_artifact_bytes(raw: bytes, label: str) -> list[tuple[str, bytes]]:
    value = loads_strict_json(raw, label)
    if not isinstance(value, dict) or set(value) != {"schema_version", "files"}:
        raise RuntimeError("computation profile artifact schema mismatch")
    if (
        type(value["schema_version"]) is not int
        or value["schema_version"] != _SCHEMA_VERSION
        or not isinstance(value["files"], list)
    ):
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
    return _decode_artifact_bytes(
        _read_owned_regular(artifact, artifact.name), artifact.name,
    )


def _validate_extracted_directory(
    directory_fd: int, files: list[tuple[str, bytes]],
) -> None:
    expected_names = {name for name, _content in files}
    actual_names = set(os.listdir(directory_fd))
    if actual_names != expected_names:
        raise RuntimeError(
            f"unexpected extracted profile entries: {sorted(actual_names ^ expected_names)}"
        )
    for name, expected_content in files:
        entry = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
        if (
            not stat.S_ISREG(entry.st_mode)
            or entry.st_uid != os.getuid()
            or stat.S_IMODE(entry.st_mode) != 0o400
        ):
            raise PermissionError(f"untrusted extracted computation profile: {name}")
        descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=directory_fd)
        with closing_fd(descriptor, "extracted validation and close both failed"):
            opened = os.fstat(descriptor)
            if opened.st_dev != entry.st_dev or opened.st_ino != entry.st_ino:
                raise RuntimeError(f"extracted computation profile changed: {name}")
            actual_content = _read_fd_all(descriptor)
        if not hmac.compare_digest(actual_content, expected_content):
            raise RuntimeError(f"extracted computation profile content changed: {name}")


def _cleanup_extraction_stage(
    parent_fd: int,
    directory_fd: int,
    stage_name: str,
    created_info: os.stat_result | None,
    written_names: list[str],
) -> None:
    """Quarantine and remove only an empty stage bound to the held inode."""
    if created_info is None:
        raise RuntimeError("stage identity unavailable for failure cleanup")
    if directory_fd >= 0:
        opened = os.fstat(directory_fd)
        if (
            opened.st_dev != created_info.st_dev
            or opened.st_ino != created_info.st_ino
        ):
            raise RuntimeError("stage identity changed before failure cleanup")
        for name in written_names:
            try:
                os.unlink(name, dir_fd=directory_fd)
            except FileNotFoundError:
                pass
        if os.listdir(directory_fd):
            raise RuntimeError("unexpected entries prevented failure cleanup")

    current = os.stat(stage_name, dir_fd=parent_fd, follow_symlinks=False)
    if (
        current.st_dev != created_info.st_dev
        or current.st_ino != created_info.st_ino
    ):
        raise RuntimeError("stage identity changed before failure cleanup")

    quarantine_name = f".{stage_name}.cleanup-{secrets.token_hex(16)}"
    _renameat2(parent_fd, stage_name, parent_fd, quarantine_name)
    quarantine_failure: BaseException | None = None
    try:
        quarantine_fd = os.open(
            quarantine_name,
            os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
            dir_fd=parent_fd,
        )
        with closing_fd(quarantine_fd, "quarantine validation and close both failed"):
            quarantined = os.fstat(quarantine_fd)
            if (
                quarantined.st_dev != created_info.st_dev
                or quarantined.st_ino != created_info.st_ino
            ):
                raise RuntimeError("stage identity changed during failure cleanup")
            if os.listdir(quarantine_fd):
                raise RuntimeError("unexpected entries prevented failure cleanup")
    except BaseException as error:
        quarantine_failure = error
    if quarantine_failure is not None:
        rollback_failures: list[BaseException] = []
        try:
            _renameat2(parent_fd, quarantine_name, parent_fd, stage_name)
        except BaseException as rollback_error:
            rollback_failures.append(rollback_error)
        raise_failures(
            "quarantine validation and namespace rollback both failed",
            quarantine_failure,
            rollback_failures,
        )
    try:
        os.rmdir(quarantine_name, dir_fd=parent_fd)
    except BaseException as remove_error:
        rollback_failures = []
        try:
            _renameat2(parent_fd, quarantine_name, parent_fd, stage_name)
        except BaseException as rollback_error:
            rollback_failures.append(rollback_error)
        raise_failures(
            "quarantine removal and namespace rollback both failed",
            remove_error,
            rollback_failures,
        )


def extract_artifact(artifact: Path, target: Path) -> None:
    """Extract through an exact, private stage and publish it without replacement.

    The current UID is the trust principal throughout the regeneration pipeline;
    a hostile process running under that same UID is outside the security boundary.
    Exact entry/content checks on both sides of publication still reject accidental
    same-UID namespace replacement and prevent extra files from being accepted.
    """
    files = _decode_artifact(artifact)
    target = target.absolute()
    parent_fd = os.open(
        target.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
    )
    directory_fd = -1
    stage_name: str | None = None
    created_info = None
    stage_info = None
    published = False
    written_names: list[str] = []
    primary: BaseException | None = None
    try:
        parent_info = os.fstat(parent_fd)
        if (
            not stat.S_ISDIR(parent_info.st_mode)
            or parent_info.st_uid != os.getuid()
            or stat.S_IMODE(parent_info.st_mode) & 0o022
        ):
            raise PermissionError("untrusted computation profile extraction parent")
        for _attempt in range(128):
            candidate = f".{target.name}.extract-{secrets.token_hex(16)}"
            try:
                os.mkdir(candidate, mode=0o700, dir_fd=parent_fd)
            except FileExistsError:
                continue
            stage_name = candidate
            created_info = os.stat(
                stage_name, dir_fd=parent_fd, follow_symlinks=False,
            )
            break
        if stage_name is None or created_info is None:
            raise RuntimeError("unable to allocate private computation profile stage")
        directory_fd = os.open(
            stage_name,
            os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
            dir_fd=parent_fd,
        )
        stage_info = os.fstat(directory_fd)
        if (
            not stat.S_ISDIR(stage_info.st_mode)
            or stage_info.st_uid != os.getuid()
            or stat.S_IMODE(stage_info.st_mode) != 0o700
        ):
            raise PermissionError("untrusted computation profile extraction stage")
        if (
            stage_info.st_dev != created_info.st_dev
            or stage_info.st_ino != created_info.st_ino
        ):
            raise RuntimeError("computation profile extraction stage was replaced")
        stage_entry = os.stat(stage_name, dir_fd=parent_fd, follow_symlinks=False)
        if (
            stage_entry.st_dev != stage_info.st_dev
            or stage_entry.st_ino != stage_info.st_ino
        ):
            raise RuntimeError("computation profile extraction stage was replaced")
        for name, content in files:
            fd = os.open(
                name,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                0o400,
                dir_fd=directory_fd,
            )
            written_names.append(name)
            with closing_fd(fd, "profile write and file close both failed"):
                with os.fdopen(fd, "wb", closefd=False) as handle:
                    handle.write(content)
                    handle.flush()
                    os.fsync(handle.fileno())
        os.fsync(directory_fd)
        _validate_extracted_directory(directory_fd, files)
        source_entry = os.stat(stage_name, dir_fd=parent_fd, follow_symlinks=False)
        if (
            source_entry.st_dev != stage_info.st_dev
            or source_entry.st_ino != stage_info.st_ino
        ):
            raise RuntimeError("computation profile extraction stage changed")
        _renameat2(parent_fd, stage_name, parent_fd, target.name)
        published = True
        target_entry = os.stat(target.name, dir_fd=parent_fd, follow_symlinks=False)
        if (
            target_entry.st_dev != stage_info.st_dev
            or target_entry.st_ino != stage_info.st_ino
        ):
            raise RuntimeError("published computation profile directory changed")
        _validate_extracted_directory(directory_fd, files)
        os.fsync(parent_fd)
    except BaseException as error:
        primary = error
    finally:
        cleanup_failures: list[BaseException] = []
        if stage_name is not None and not published:
            try:
                _cleanup_extraction_stage(
                    parent_fd, directory_fd, stage_name, created_info, written_names,
                )
            except BaseException as cleanup_error:
                cleanup_failures.append(cleanup_error)
        if directory_fd >= 0:
            try:
                os.close(directory_fd)
            except BaseException as close_error:
                cleanup_failures.append(close_error)
        try:
            os.close(parent_fd)
        except BaseException as close_error:
            cleanup_failures.append(close_error)
        raise_failures(
            "operation and computation-profile cleanup both failed",
            primary,
            cleanup_failures,
        )


def verify_artifact(source: Path, artifact: Path) -> None:
    expected = _read_owned_regular(artifact, artifact.name)
    _decode_artifact_bytes(expected, artifact.name)
    actual = artifact_bytes(source)
    if not hmac.compare_digest(actual, expected):
        raise RuntimeError("consumed computation profile changed from authenticated artifact")


def validate_artifact(artifact: Path) -> str:
    content = _read_owned_regular(artifact, artifact.name)
    _decode_artifact_bytes(content, artifact.name)
    return hashlib.sha256(content).hexdigest()


def copy_artifact(source: Path, output: Path) -> str:
    content = _read_owned_regular(source, source.name)
    _decode_artifact_bytes(content, source.name)
    output = output.absolute()
    target = os.open(
        output, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o400,
    )
    with closing_fd(target, "artifact copy and file close both failed"):
        with os.fdopen(target, "wb", closefd=False) as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
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
