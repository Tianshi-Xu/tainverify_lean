#!/usr/bin/env python3
"""Fail closed unless a generated authority stage contains only public artifacts."""
from __future__ import annotations

import argparse
import os
import stat
from pathlib import Path

EXPECTED = {
    ".trainverify-stage-owner",
    "comm_profile_intra_2.json",
    "comp_profile.json",
    "gen_args.json",
    "nnscaler_dp_solver.so",
    "pm_mgener.json",
    "pm_mgener.pkl",
    "pm_mgener.pkl.receipt.json",
    "pm_provenance.json",
    "sm_mgener.json",
    "sm_mgener.pkl",
    "sm_mgener.pkl.receipt.json",
    "sm_provenance.json",
}


def validate_fd(stage_fd: int) -> None:
    names = set(os.listdir(stage_fd))
    if names != EXPECTED:
        raise RuntimeError(
            f"authority publication allowlist mismatch: "
            f"missing={sorted(EXPECTED - names)} extra={sorted(names - EXPECTED)}"
        )
    for name in sorted(names):
        info = os.stat(name, dir_fd=stage_fd, follow_symlinks=False)
        if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid():
            raise PermissionError(f"untrusted publication artifact: {name}")
        if stat.S_IMODE(info.st_mode) & 0o022:
            raise PermissionError(f"group/world writable publication artifact: {name}")


def validate(stage: Path) -> None:
    stage_fd = os.open(stage.absolute(), os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        validate_fd(stage_fd)
    finally:
        os.close(stage_fd)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", type=Path)
    args = parser.parse_args()
    validate(args.stage)


if __name__ == "__main__":
    main()
