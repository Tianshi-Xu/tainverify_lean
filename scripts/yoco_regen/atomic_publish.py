#!/usr/bin/env python3
"""Atomically publish a validated authority without replacing a target (Linux)."""
from __future__ import annotations

import argparse
import ctypes
import errno
import os
import stat
from collections.abc import Callable
from pathlib import Path

try:
    from .check_publication_allowlist import validate_fd
except ImportError:  # Direct script execution.
    from check_publication_allowlist import validate_fd

RENAME_NOREPLACE = 1


def _require_trusted_parent(directory_fd: int, label: str) -> None:
    info = os.fstat(directory_fd)
    if info.st_uid != os.getuid() or stat.S_IMODE(info.st_mode) & 0o022:
        raise PermissionError(f"{label} parent is not owner-controlled")


def _require_trusted_ancestor_chain(directory: Path, label: str) -> None:
    current = directory.absolute()
    while True:
        info = os.lstat(current)
        mode = stat.S_IMODE(info.st_mode)
        if not stat.S_ISDIR(info.st_mode) or stat.S_ISLNK(info.st_mode):
            raise PermissionError(f"{label} ancestor is not a real directory: {current}")
        if info.st_uid not in {0, os.getuid()}:
            raise PermissionError(f"{label} ancestor has an untrusted owner: {current}")
        if mode & 0o022 and not mode & stat.S_ISVTX:
            raise PermissionError(f"{label} ancestor is non-sticky writable: {current}")
        parent = current.parent
        if parent == current:
            return
        current = parent


def _renameat2(source_fd: int, source_name: str, target_fd: int, target_name: str) -> None:
    libc = ctypes.CDLL(None, use_errno=True)
    renameat2 = getattr(libc, "renameat2", None)
    if renameat2 is None:
        raise RuntimeError("renameat2 is unavailable; refusing non-atomic publication")
    renameat2.argtypes = [
        ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint,
    ]
    renameat2.restype = ctypes.c_int
    if renameat2(
        source_fd, os.fsencode(source_name), target_fd, os.fsencode(target_name),
        RENAME_NOREPLACE,
    ) != 0:
        error = ctypes.get_errno()
        if error == errno.EEXIST:
            raise FileExistsError(error, os.strerror(error), target_name)
        raise OSError(error, os.strerror(error), f"{source_name} -> {target_name}")


def rename_noreplace(source: Path, target: Path) -> None:
    source = source.absolute()
    target = target.absolute()
    source_parent = os.open(source.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    target_parent = os.open(target.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        _renameat2(source_parent, source.name, target_parent, target.name)
        os.fsync(target_parent)
    finally:
        os.close(target_parent)
        os.close(source_parent)


def publish_validated_directory(
    source: Path, target: Path, validator: Callable[[int], None],
) -> None:
    source = source.absolute()
    target = target.absolute()
    source_parent = os.open(source.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    target_parent = os.open(target.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    stage_fd = -1
    try:
        _require_trusted_parent(source_parent, "source")
        _require_trusted_parent(target_parent, "target")
        _require_trusted_ancestor_chain(source.parent.parent, "source")
        _require_trusted_ancestor_chain(target.parent.parent, "target")
        stage_fd = os.open(
            source.name,
            os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
            dir_fd=source_parent,
        )
        expected = os.fstat(stage_fd)
        validator(stage_fd)
        source_entry = os.stat(
            source.name, dir_fd=source_parent, follow_symlinks=False,
        )
        if (source_entry.st_dev, source_entry.st_ino) != (expected.st_dev, expected.st_ino):
            raise RuntimeError("source entry differs from validated stage")
        _renameat2(source_parent, source.name, target_parent, target.name)
        actual = os.stat(target.name, dir_fd=target_parent, follow_symlinks=False)
        if (actual.st_dev, actual.st_ino) != (expected.st_dev, expected.st_ino):
            raise RuntimeError("published authority inode differs from validated stage")
        validator(stage_fd)
        os.fsync(stage_fd)
        os.fsync(target_parent)
        final = os.stat(target.name, dir_fd=target_parent, follow_symlinks=False)
        if (final.st_dev, final.st_ino) != (expected.st_dev, expected.st_ino):
            raise RuntimeError("target changed before publication completed")
    except BaseException:
        # There is no Linux rename primitive that conditionally moves a directory
        # entry by (dev, ino).  A stat-then-rename rollback would reopen the same
        # TOCTOU window publication just closed.  Fail closed and leave the
        # post-rename namespace untouched for explicit inspection/recovery.
        raise
    finally:
        if stage_fd >= 0:
            os.close(stage_fd)
        os.close(target_parent)
        os.close(source_parent)


def publish_authority(source: Path, target: Path) -> None:
    publish_validated_directory(source, target, validate_fd)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("target", type=Path)
    args = parser.parse_args()
    publish_authority(args.source, args.target)


if __name__ == "__main__":
    main()
