#!/usr/bin/env python3
"""Compile certificate IR, emit Lean, and optionally kernel-check before publication."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import stat
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[2]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from trainverify.proof_compiler import compile_job
from trainverify.proof_compiler.lean_emitter import LeanEmissionError, emit_lean_certificate


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> Any:
    raise ValueError(f"non-finite JSON number: {value}")


def _load(path: Path) -> Any:
    with path.open(encoding="utf-8") as handle:
        return json.load(
            handle,
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_constant,
        )


def _failure(reason: str, *, detail: str | None = None) -> dict[str, Any]:
    failure: dict[str, Any] = {
        "category": "certificate_bug",
        "stage": "lean_kernel_check",
        "reason": reason,
    }
    if detail is not None:
        failure["detail"] = detail
    return {"schema_version": 1, "status": "failure", "failure": failure}


def _print(payload: dict[str, Any]) -> None:
    print(json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--job", required=True, type=Path)
    parser.add_argument("--library", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--namespace", default="GeneratedCertificate")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--lean-root", type=Path, default=REPO_ROOT / "trainverify")
    args = parser.parse_args()

    try:
        job = _load(args.job)
        library = _load(args.library)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        _print(_failure("invalid_json", detail=str(error)))
        return 2

    result = compile_job(job, library)
    if result.get("status") != "certificate":
        _print(result)
        return 2
    try:
        source = emit_lean_certificate(job, library, result, namespace=args.namespace)
    except (LeanEmissionError, KeyError, TypeError, ValueError) as error:
        _print(_failure("lean_emission_failed", detail=str(error)))
        return 2

    requested_output = args.output.absolute()
    if requested_output.suffix != ".lean":
        _print(_failure("output_must_have_lean_suffix"))
        return 2
    try:
        requested_output.parent.mkdir(parents=True, exist_ok=True)
        if os.path.lexists(requested_output):
            _print(_failure("output_already_exists"))
            return 2
        output = requested_output.parent.resolve(strict=True) / requested_output.name
        if os.path.lexists(output):
            _print(_failure("output_already_exists"))
            return 2
        parent_stat = output.parent.stat()
    except OSError as error:
        _print(_failure("output_path_invalid", detail=str(error)))
        return 2
    if (
        not stat.S_ISDIR(parent_stat.st_mode)
        or parent_stat.st_uid != os.geteuid()
        or parent_stat.st_mode & 0o022
    ):
        _print(_failure("insecure_output_directory"))
        return 2

    temporary: Path | None = None
    temporary_fd: int | None = None
    trusted_stat: os.stat_result | None = None
    publication_complete = False
    source_bytes = source.encode("utf-8")
    try:
        with tempfile.NamedTemporaryFile(
            mode="wb", suffix=".lean", prefix=f".{output.stem}.",
            dir=output.parent, delete=False,
        ) as handle:
            handle.write(source_bytes)
            handle.flush()
            os.fsync(handle.fileno())
            temporary = Path(handle.name)

        temporary_fd = os.open(temporary, os.O_RDONLY | os.O_NOFOLLOW)
        trusted_stat = os.fstat(temporary_fd)
        if trusted_stat.st_size != len(source_bytes):
            _print(_failure("temporary_artifact_changed"))
            return 2
        if args.check:
            checked = subprocess.run(
                ["lake", "env", "lean", str(temporary)],
                cwd=args.lean_root.resolve(),
                text=True,
                capture_output=True,
                check=False,
            )
            if checked.returncode != 0:
                detail = (checked.stdout + checked.stderr).strip()
                detail = detail.replace(str(temporary), str(output))
                _print(_failure("lean_kernel_rejected", detail=detail[-8000:]))
                return 2

        path_stat = os.stat(temporary, follow_symlinks=False)
        os.lseek(temporary_fd, 0, os.SEEK_SET)
        checked_bytes = bytearray()
        while True:
            chunk = os.read(temporary_fd, 65536)
            if not chunk:
                break
            checked_bytes.extend(chunk)
        if (
            (path_stat.st_dev, path_stat.st_ino, path_stat.st_size)
            != (trusted_stat.st_dev, trusted_stat.st_ino, trusted_stat.st_size)
            or bytes(checked_bytes) != source_bytes
        ):
            _print(_failure("temporary_artifact_changed"))
            return 2

        # Atomic no-replace publication from the checked inode's trusted path.
        os.link(temporary, output, follow_symlinks=False)
        temporary.unlink()
        temporary = None
        directory_fd = os.open(output.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
        publication_complete = True
    except FileExistsError:
        _print(_failure("output_already_exists"))
        return 2
    except (OSError, subprocess.SubprocessError) as error:
        _print(_failure("lean_toolchain_failed", detail=str(error)))
        return 2
    finally:
        if not publication_complete and trusted_stat is not None:
            try:
                published = os.stat(output, follow_symlinks=False)
                if (published.st_dev, published.st_ino) == (
                    trusted_stat.st_dev, trusted_stat.st_ino
                ):
                    output.unlink()
            except FileNotFoundError:
                pass
        if temporary_fd is not None:
            os.close(temporary_fd)
        if temporary is not None and trusted_stat is not None:
            try:
                current = os.stat(temporary, follow_symlinks=False)
                if (current.st_dev, current.st_ino) == (trusted_stat.st_dev, trusted_stat.st_ino):
                    temporary.unlink()
            except FileNotFoundError:
                pass

    _print({
        "schema_version": 1,
        "status": "kernel_certificate" if args.check else "lean_source",
        "checked": args.check,
        "output": str(args.output),
        "target_manifest_sha256": result["target_manifest_sha256"],
    })
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
