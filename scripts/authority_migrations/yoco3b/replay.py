#!/usr/bin/env python3
"""Replay and verify the pinned YOCO-3B authority migration chain."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import stat
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MANIFEST = Path(__file__).with_name("manifest.json")
TRUSTED_GIT = "/usr/bin/git"
CANONICAL_ARTIFACT = "trainverify/denote/GeneratedYOCO3B.lean"
CANONICAL_SOURCE = "trainverify/denote/GeneratedYOCO3B.lean"
CANONICAL_SCRIPTS = (
    "scripts/authority_migrations/yoco3b/01_reshape.py",
    "scripts/authority_migrations/yoco3b/02_reduce_scatter.py",
    "scripts/authority_migrations/yoco3b/03_init_alias.py",
    "scripts/authority_migrations/yoco3b/04_attention_replica_groups.py",
    "scripts/authority_migrations/yoco3b/05_heartbeat_budget.py",
)
EXPECTED_TOP_KEYS = {"schema_version", "artifact", "source", "migrations"}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_manifest() -> tuple[dict, bytes]:
    data = MANIFEST.read_bytes()
    if not data.endswith(b"\n"):
        raise RuntimeError("manifest lacks one final newline")
    manifest = json.loads(data, object_pairs_hook=_reject_duplicate_keys)
    canonical = (json.dumps(manifest, sort_keys=True, separators=(",", ":")) + "\n").encode()
    if data != canonical:
        raise RuntimeError("manifest is not canonical sorted compact JSON")
    if set(manifest) != EXPECTED_TOP_KEYS or manifest["schema_version"] != 1:
        raise RuntimeError("manifest schema/top-level keys disagree")
    if set(manifest["source"]) != {"git_commit", "git_blob", "path", "sha256"}:
        raise RuntimeError("manifest source keys disagree")
    if set(manifest["artifact"]) != {"path", "sha256"}:
        raise RuntimeError("manifest artifact keys disagree")
    if manifest["artifact"]["path"] != CANONICAL_ARTIFACT:
        raise RuntimeError("manifest artifact path is not canonical")
    if manifest["source"]["path"] != CANONICAL_SOURCE:
        raise RuntimeError("manifest source path is not canonical")
    expected_migration_keys = {
        "ordinal", "id", "script_path", "script_sha256", "input_sha256", "output_sha256"
    }
    migrations = manifest["migrations"]
    if not migrations or any(set(item) != expected_migration_keys for item in migrations):
        raise RuntimeError("manifest migration keys disagree")
    if [item["ordinal"] for item in migrations] != list(range(1, len(migrations) + 1)):
        raise RuntimeError("manifest migration ordinals are not contiguous")
    if len({item["id"] for item in migrations}) != len(migrations):
        raise RuntimeError("manifest migration IDs are not unique")
    if tuple(item["script_path"] for item in migrations) != CANONICAL_SCRIPTS:
        raise RuntimeError("manifest migration script paths are not the canonical closed set")
    return manifest, data


def _reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise RuntimeError(f"duplicate manifest key: {key}")
        result[key] = value
    return result


def repository_paths() -> tuple[Path, Path]:
    marker = ROOT / ".git"
    if marker.is_symlink():
        raise RuntimeError("repository .git marker is a symlink")
    if marker.is_dir():
        git_dir = marker.resolve()
    elif marker.is_file():
        text = marker.read_text().strip()
        if not text.startswith("gitdir: "):
            raise RuntimeError("repository .git file is malformed")
        candidate = Path(text[8:])
        git_dir = (candidate if candidate.is_absolute() else ROOT / candidate).resolve()
    else:
        raise RuntimeError("repository Git directory is missing")
    common = git_dir
    common_file = git_dir / "commondir"
    if common_file.is_file():
        candidate = Path(common_file.read_text().strip())
        common = (candidate if candidate.is_absolute() else git_dir / candidate).resolve()
    object_dir = common / "objects"
    if not git_dir.is_dir() or not object_dir.is_dir():
        raise RuntimeError("repository Git metadata/object directory is invalid")
    return git_dir, object_dir


def git_bytes(*args: str) -> bytes:
    git_dir, object_dir = repository_paths()
    env = {
        "HOME": "/nonexistent",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_OBJECT_DIRECTORY": str(object_dir),
        "GIT_ALTERNATE_OBJECT_DIRECTORIES": "",
    }
    result = subprocess.run(
        [TRUSTED_GIT, f"--git-dir={git_dir}", *args],
        cwd=ROOT, env=env, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    return result.stdout


def replay(manifest: dict) -> bytes:
    source = manifest["source"]
    commit_type = git_bytes("cat-file", "-t", source["git_commit"]).strip()
    if commit_type != b"commit":
        raise RuntimeError("manifest source revision is not a commit")
    resolved_blob = git_bytes("rev-parse", f"{source['git_commit']}:{source['path']}").strip().decode()
    if resolved_blob != source["git_blob"]:
        raise RuntimeError("manifest commit/path does not resolve to pinned blob")
    data = git_bytes("cat-file", "blob", source["git_blob"])
    if sha256(data) != source["sha256"]:
        raise RuntimeError("historical source SHA-256 mismatch")
    previous = source["sha256"]
    with tempfile.TemporaryDirectory(prefix="yoco3b-authority-replay-") as directory:
        directory = Path(directory)
        input_path = directory / "stage0.lean"
        input_path.write_bytes(data)
        for item in manifest["migrations"]:
            if item["input_sha256"] != previous or sha256(input_path.read_bytes()) != previous:
                raise RuntimeError(f"migration input chain mismatch: {item['id']}")
            script = ROOT / item["script_path"]
            if script.is_symlink() or script.resolve() != script.absolute():
                raise RuntimeError(f"migration script path contains a symlink: {item['id']}")
            mode = script.stat(follow_symlinks=False).st_mode
            if not stat.S_ISREG(mode):
                raise RuntimeError(f"migration script is not a regular file: {item['id']}")
            script_bytes = script.read_bytes()
            if sha256(script_bytes) != item["script_sha256"]:
                raise RuntimeError(f"migration script SHA-256 mismatch: {item['id']}")
            validated_script = directory / f"migration{item['ordinal']}.py"
            validated_script.write_bytes(script_bytes)
            output_path = directory / f"stage{item['ordinal']}.lean"
            subprocess.run(
                [sys.executable, "-I", "-S", str(validated_script), str(input_path), str(output_path)],
                cwd=ROOT, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                env={},
            )
            output = output_path.read_bytes()
            if sha256(output) != item["output_sha256"]:
                raise RuntimeError(f"migration output SHA-256 mismatch: {item['id']}")
            # Stage-level idempotence on its canonical output.
            idem_path = directory / f"stage{item['ordinal']}.idempotent.lean"
            subprocess.run(
                [sys.executable, "-I", "-S", str(validated_script), str(output_path), str(idem_path)],
                cwd=ROOT, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                env={},
            )
            if idem_path.read_bytes() != output:
                raise RuntimeError(f"migration is not byte-idempotent: {item['id']}")
            input_path = output_path
            previous = item["output_sha256"]
        return input_path.read_bytes()


def read_regular_nofollow(path: Path) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    fd = os.open(path, flags)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode):
            raise RuntimeError(f"not a regular file: {path}")
        chunks = []
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        data = b"".join(chunks)
        after = os.fstat(fd)
        if ((info.st_dev, info.st_ino, info.st_mode, info.st_size)
                != (after.st_dev, after.st_ino, after.st_mode, after.st_size)
                or len(data) != info.st_size):
            raise RuntimeError(f"file identity changed while reading: {path}")
        return data
    finally:
        os.close(fd)


def write_output_atomic(path: Path, data: bytes) -> None:
    if path.is_symlink():
        raise RuntimeError("replay output path is a symlink")
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data); stream.flush(); os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try: os.unlink(temporary)
        except FileNotFoundError: pass
        raise


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    manifest, manifest_bytes = load_manifest()
    final = replay(manifest)
    artifact = manifest["artifact"]
    if sha256(final) != artifact["sha256"]:
        raise RuntimeError("final replay digest disagrees with artifact manifest")
    artifact_path = ROOT / artifact["path"]
    if artifact_path.resolve() != artifact_path.absolute():
        raise RuntimeError("checked-in authority path is not canonical")
    checked_in = read_regular_nofollow(artifact_path)
    if checked_in != final:
        raise RuntimeError("checked-in authority differs from replayed bytes")
    if args.output is not None:
        write_output_atomic(args.output, final)
    print(
        f"verified manifest={sha256(manifest_bytes)} artifact={sha256(final)} "
        f"migrations={len(manifest['migrations'])}"
    )


if __name__ == "__main__":
    main()
