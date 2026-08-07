"""Fail-closed startup guard for the sealed nnScaler dp_solver extension."""
from __future__ import annotations

import hashlib
import importlib
import os
import traceback
from pathlib import Path

try:
    expected_path = os.environ.get("TRAINVERIFY_DP_SOLVER_PATH", "")
    expected_hash = os.environ.get("TRAINVERIFY_DP_SOLVER_SHA256", "")
    if not expected_path or len(expected_hash) != 64:
        raise RuntimeError("missing sealed dp solver startup identity")
    module = importlib.import_module("nnscaler.autodist.dp_solver")
    actual_file = getattr(module, "__file__", None)
    if (
        not isinstance(actual_file, str)
        or Path(actual_file).resolve() != Path(expected_path).resolve()
    ):
        raise RuntimeError(f"dp solver resolved outside sealed import path: {actual_file}")
    digest = hashlib.sha256(Path(actual_file).read_bytes()).hexdigest()
    if digest != expected_hash:
        raise RuntimeError("sealed dp solver startup hash mismatch")
except BaseException:
    traceback.print_exc()
    os._exit(126)
