"""Fail-closed startup guard for memfd-sealed nnScaler runtime bytes."""
from __future__ import annotations

import fcntl
import hashlib
import importlib
import importlib.machinery
import importlib.util
import os
import re
import sys
import traceback

_FULL_SEALS = (
    getattr(fcntl, "F_SEAL_SEAL", 0x0001)
    | getattr(fcntl, "F_SEAL_SHRINK", 0x0002)
    | getattr(fcntl, "F_SEAL_GROW", 0x0004)
    | getattr(fcntl, "F_SEAL_WRITE", 0x0008)
)
_PROC_FD = re.compile(r"^/proc/[1-9][0-9]*/fd/[0-9]+$")
_MODULE = "nnscaler.autodist.dp_solver"


def _verify_sealed(path: str, expected_hash: str, *, elf: bool = False) -> None:
    if not _PROC_FD.fullmatch(path) or len(expected_hash) != 64:
        raise RuntimeError("invalid sealed runtime identity")
    descriptor = os.open(path, os.O_RDONLY)
    try:
        if fcntl.fcntl(descriptor, getattr(fcntl, "F_GET_SEALS", 1034)) != _FULL_SEALS:
            raise RuntimeError("runtime memfd is not fully sealed")
        digest = hashlib.sha256()
        prefix = os.read(descriptor, 4)
        digest.update(prefix)
        while chunk := os.read(descriptor, 1 << 20):
            digest.update(chunk)
        if (elf and prefix != b"\x7fELF") or digest.hexdigest() != expected_hash:
            raise RuntimeError("sealed runtime content mismatch")
    finally:
        os.close(descriptor)


class _SolverFinder:
    def __init__(self, extension_path: str) -> None:
        self.extension_path = extension_path

    def find_spec(self, fullname: str, path=None, target=None):
        if fullname != _MODULE:
            return None
        loader = importlib.machinery.ExtensionFileLoader(fullname, self.extension_path)
        return importlib.util.spec_from_loader(fullname, loader)


try:
    extension_path = os.environ.get("TRAINVERIFY_DP_SOLVER_PATH", "")
    extension_hash = os.environ.get("TRAINVERIFY_DP_SOLVER_SHA256", "")
    runtime_path = os.environ.get("TRAINVERIFY_RUNTIME_ZIP_PATH", "")
    runtime_hash = os.environ.get("TRAINVERIFY_RUNTIME_ZIP_SHA256", "")
    _verify_sealed(runtime_path, runtime_hash)
    _verify_sealed(extension_path, extension_hash, elf=True)
    finder = _SolverFinder(extension_path)
    sys.meta_path.insert(0, finder)
    try:
        module = importlib.import_module(_MODULE)
    finally:
        sys.meta_path.remove(finder)
    if getattr(module, "__file__", None) != extension_path:
        raise RuntimeError(f"dp solver resolved outside sealed memfd: {module.__file__}")
except BaseException:
    traceback.print_exc()
    os._exit(126)
