#!/usr/bin/env python3
"""Create and clean private stages bound to an unguessable marker and inode."""
from __future__ import annotations

import argparse
import os
import secrets
import stat
import tempfile
import uuid
from pathlib import Path

MARKER_NAME = ".trainverify-stage-owner"


def create_owned_stage(parent: Path, prefix: str) -> tuple[Path, str, int, int]:
    parent = parent.absolute()
    parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=prefix, dir=parent))
    marker = secrets.token_hex(32)
    marker_path = stage / MARKER_NAME
    marker_path.write_text(marker + "\n", encoding="utf-8")
    marker_path.chmod(0o400)
    info = stage.stat(follow_symlinks=False)
    return stage, marker, info.st_dev, info.st_ino


def _remove_tree_contents(directory_fd: int) -> None:
    """Remove contents through held directory fds; never reopen an absolute path."""
    for name in os.listdir(directory_fd):
        info = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
        if stat.S_ISDIR(info.st_mode):
            child_fd = os.open(
                name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory_fd
            )
            try:
                opened = os.fstat(child_fd)
                if opened.st_dev != info.st_dev or opened.st_ino != info.st_ino:
                    raise RuntimeError(f"directory inode changed during cleanup: {name}")
                _remove_tree_contents(child_fd)
            finally:
                os.close(child_fd)
            # If the entry was replaced with a nonempty unrelated directory this
            # fails closed. No path-based recursive deletion follows.
            os.rmdir(name, dir_fd=directory_fd)
        else:
            os.unlink(name, dir_fd=directory_fd)


def cleanup_owned_stage(
    stage: Path, marker: str, expected_dev: int, expected_ino: int
) -> bool:
    stage = stage.absolute()
    try:
        info = stage.stat(follow_symlinks=False)
    except (FileNotFoundError, NotADirectoryError, OSError):
        return False
    if info.st_dev != expected_dev or info.st_ino != expected_ino:
        return False
    marker_path = stage / MARKER_NAME
    try:
        actual = marker_path.read_text(encoding="utf-8").strip()
    except (FileNotFoundError, NotADirectoryError, OSError):
        return False
    if actual != marker:
        return False

    parent = stage.parent
    parent_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    quarantine_name = f".{stage.name}.cleanup-{uuid.uuid4().hex}"
    quarantine = parent / quarantine_name
    try:
        os.rename(stage.name, quarantine_name, src_dir_fd=parent_fd, dst_dir_fd=parent_fd)
        quarantine_fd = os.open(
            quarantine_name,
            os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
            dir_fd=parent_fd,
        )
        try:
            moved = os.fstat(quarantine_fd)
            if moved.st_dev != expected_dev or moved.st_ino != expected_ino:
                raise RuntimeError("stage inode changed during cleanup")
            marker_fd = os.open(MARKER_NAME, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=quarantine_fd)
            try:
                with os.fdopen(marker_fd, "r", encoding="utf-8", closefd=False) as handle:
                    quarantined_marker = handle.read().strip()
            finally:
                os.close(marker_fd)
            if quarantined_marker != marker:
                raise RuntimeError("stage ownership changed during cleanup")
            _remove_tree_contents(quarantine_fd)
        finally:
            os.close(quarantine_fd)
        # Only an empty directory can be removed here. A substituted directory
        # containing unrelated data is never recursively traversed by path.
        os.rmdir(quarantine_name, dir_fd=parent_fd)
    finally:
        os.close(parent_fd)
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="action", required=True)
    create_parser = subparsers.add_parser("create")
    create_parser.add_argument("parent", type=Path)
    create_parser.add_argument("prefix")
    cleanup_parser = subparsers.add_parser("cleanup")
    cleanup_parser.add_argument("stage", type=Path)
    cleanup_parser.add_argument("marker")
    cleanup_parser.add_argument("dev", type=int)
    cleanup_parser.add_argument("ino", type=int)
    args = parser.parse_args()
    if args.action == "create":
        stage, marker, dev, ino = create_owned_stage(args.parent, args.prefix)
        print(f"{stage}\t{marker}\t{dev}\t{ino}")
    else:
        if not cleanup_owned_stage(args.stage, args.marker, args.dev, args.ino):
            raise SystemExit(3)


if __name__ == "__main__":
    main()
