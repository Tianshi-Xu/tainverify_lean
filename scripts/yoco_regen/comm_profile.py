#!/usr/bin/env python3
"""Validate and securely capture nnScaler two-GPU communication profiles."""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import stat
from pathlib import Path

PRIMITIVES = {"all gather", "all reduce", "reduce scatter", "all to all"}
EXPECTED_SIZES_MB = [0.25 * (2**index) for index in range(12)]


def _pairs(pairs):
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def _reject_constant(value: str):
    raise ValueError(f"non-finite JSON number: {value}")


def validate_profile(profile) -> None:
    if not isinstance(profile, dict) or set(profile) != PRIMITIVES:
        raise RuntimeError("communication profile primitive schema mismatch")
    for primitive, series in profile.items():
        if not isinstance(series, list) or len(series) != 2:
            raise RuntimeError(f"{primitive} communication profile must contain sizes and times")
        sizes, times = series
        if (
            not isinstance(sizes, list)
            or len(sizes) != len(EXPECTED_SIZES_MB)
            or any(
                not isinstance(value, float) or value != expected
                for value, expected in zip(sizes, EXPECTED_SIZES_MB)
            )
        ):
            raise RuntimeError(f"{primitive} communication profile sizes mismatch")
        if not isinstance(times, list) or len(times) != len(EXPECTED_SIZES_MB):
            raise RuntimeError(f"{primitive} communication profile times mismatch")
        if any(
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(value)
            or value <= 0
            for value in times
        ):
            raise RuntimeError(f"{primitive} communication profile has invalid timing")


def parse_profile(content: bytes):
    profile = json.loads(
        content.decode("utf-8"),
        object_pairs_hook=_pairs,
        parse_constant=_reject_constant,
    )
    validate_profile(profile)
    return profile


def profile_sha256(path: Path) -> str:
    content = path.read_bytes()
    parse_profile(content)
    return hashlib.sha256(content).hexdigest()


def capture_profile(source: Path, destination: Path) -> str:
    source = source.absolute()
    destination = destination.absolute()
    source_fd = os.open(source, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        info = os.fstat(source_fd)
        if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid():
            raise PermissionError("untrusted communication profile inode")
        if stat.S_IMODE(info.st_mode) & 0o022:
            raise PermissionError("communication profile is group/world writable")
        with os.fdopen(os.dup(source_fd), "rb") as handle:
            content = handle.read()
        parse_profile(content)
        destination_fd = os.open(
            destination,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
            0o444,
        )
        try:
            with os.fdopen(os.dup(destination_fd), "wb") as handle:
                handle.write(content)
                handle.flush()
                os.fsync(handle.fileno())
        finally:
            os.close(destination_fd)
    finally:
        os.close(source_fd)
    return hashlib.sha256(content).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    print(capture_profile(args.source, args.destination))


if __name__ == "__main__":
    main()
