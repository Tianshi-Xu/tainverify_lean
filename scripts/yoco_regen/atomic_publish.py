#!/usr/bin/env python3
"""Atomically publish one path without replacing an existing target (Linux)."""
from __future__ import annotations

import argparse
import ctypes
import errno
import os
from pathlib import Path

AT_FDCWD = -100
RENAME_NOREPLACE = 1


def rename_noreplace(source: Path, target: Path) -> None:
    source = source.resolve()
    target = target.absolute()
    libc = ctypes.CDLL(None, use_errno=True)
    renameat2 = getattr(libc, "renameat2", None)
    if renameat2 is None:
        raise RuntimeError("renameat2 is unavailable; refusing non-atomic publication")
    renameat2.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    renameat2.restype = ctypes.c_int
    result = renameat2(
        AT_FDCWD, os.fsencode(source), AT_FDCWD, os.fsencode(target), RENAME_NOREPLACE
    )
    if result != 0:
        error = ctypes.get_errno()
        if error == errno.EEXIST:
            raise FileExistsError(error, os.strerror(error), str(target))
        raise OSError(error, os.strerror(error), f"{source} -> {target}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("target", type=Path)
    args = parser.parse_args()
    rename_noreplace(args.source, args.target)


if __name__ == "__main__":
    main()
