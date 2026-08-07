#!/usr/bin/env python3
"""Build nnScaler's dp_solver from a fixed commit in a private read-only tmpfs."""
from __future__ import annotations

import argparse
import hashlib
import shutil
import subprocess
import sys
import sysconfig
import tempfile
from pathlib import Path

SOURCE_PATHS = (
    "setup.py",
    "nnscaler/autodist/dp_solver.cpp",
    "nnscaler/autodist/dp_solver.h",
)
EXPECTED_EXTENSION_SHA256 = "10635af2e67a56c2029296fbc7563952563a0d611e0cde41ac006f748ef08681"
CLEAN_TOOL_ENV = {"LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "PATH": "/usr/bin:/bin"}
PYTHON_LAUNCH_ENV = {
    **CLEAN_TOOL_ENV,
    "PYTHONNOUSERSITE": "1",
    "PYTHONSAFEPATH": "1",
    "PYTHONDONTWRITEBYTECODE": "1",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob_hash(repo: Path, revision: str, relative: str) -> str:
    content = subprocess.check_output(
        ["git", "-C", str(repo), "show", f"{revision}:{relative}"]
    )
    return hashlib.sha256(content).hexdigest()


def _namespace_build(
    repo: Path, revision: str, output: Path, archive_hash: str,
    expected: dict[str, str],
) -> None:
    mountpoint = Path(tempfile.mkdtemp(prefix="trainverify-dp-input-"))
    build_temp = Path(tempfile.mkdtemp(prefix="trainverify-dp-temp-"))
    try:
        subprocess.run(
            ["mount", "-t", "tmpfs", "-o", "mode=0700,size=1G", "tmpfs", str(mountpoint)],
            check=True,
        )
        subprocess.run(
            ["mount", "-t", "tmpfs", "-o", "mode=0700,size=1G", "tmpfs", str(build_temp)],
            check=True,
        )
        archive = subprocess.check_output(
            ["git", "-C", str(repo), "archive", "--format=tar", revision]
        )
        if hashlib.sha256(archive).hexdigest() != archive_hash:
            raise RuntimeError("fixed nnScaler commit archive hash mismatch")
        extract = subprocess.run(
            ["/usr/bin/tar", "-x", "-C", str(mountpoint)],
            input=archive,
            env=CLEAN_TOOL_ENV,
        )
        if extract.returncode:
            raise RuntimeError("failed to materialize fixed nnScaler build input")
        actual = {relative: sha256(mountpoint / relative) for relative in SOURCE_PATHS}
        if actual != expected:
            raise RuntimeError(f"dp solver build input mismatch: {actual}")
        subprocess.run(
            ["mount", "-o", "remount,ro", "tmpfs", str(mountpoint)], check=True
        )
        venv_site = (
            Path(sys.executable).absolute().parent.parent / "lib"
            / f"python{sys.version_info.major}.{sys.version_info.minor}" / "site-packages"
        )
        if not venv_site.is_dir():
            raise RuntimeError("trusted venv site-packages is missing")
        build_env = {
            "HOME": str(build_temp),
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PATH": "/usr/bin:/bin",
            "PYTHONNOUSERSITE": "1",
            "PYTHONPATH": str(venv_site),
            "PYTHONSAFEPATH": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
            "SOURCE_DATE_EPOCH": "0",
        }
        subprocess.run(
            [
                sys.executable,
                "-S",
                str(mountpoint / "setup.py"),
                "build_ext",
                "--build-lib", str(output),
                "--build-temp", str(build_temp),
            ],
            cwd=mountpoint,
            env=build_env,
            stdout=sys.stderr,
            stderr=sys.stderr,
            check=True,
        )
    finally:
        subprocess.run(["umount", str(build_temp)], check=False)
        shutil.rmtree(build_temp, ignore_errors=True)
        try:
            subprocess.run(["umount", str(mountpoint)], check=False)
        finally:
            shutil.rmtree(mountpoint, ignore_errors=True)


def build(repo: Path, revision: str, output: Path) -> Path:
    repo = repo.resolve()
    output = output.absolute()
    output.mkdir(mode=0o700, parents=True, exist_ok=False)
    expected = {relative: git_blob_hash(repo, revision, relative) for relative in SOURCE_PATHS}
    archive_hash = hashlib.sha256(subprocess.check_output(
        ["git", "-C", str(repo), "archive", "--format=tar", revision]
    )).hexdigest()
    command = [
        "unshare", "--user", "--map-root-user", "--mount",
        sys.executable, "-S", str(Path(__file__).resolve()), "_namespace_build",
        str(repo), revision, str(output), archive_hash,
    ]
    for relative in SOURCE_PATHS:
        command.extend([relative, expected[relative]])
    subprocess.run(command, env=PYTHON_LAUNCH_ENV, check=True)
    suffix = sysconfig.get_config_var("EXT_SUFFIX")
    if not isinstance(suffix, str) or not suffix:
        raise RuntimeError("Python EXT_SUFFIX is unavailable")
    extension = output / "nnscaler" / "autodist" / f"dp_solver{suffix}"
    produced = list(output.rglob("*"))
    files = [path for path in produced if path.is_file()]
    directories = [path for path in produced if path.is_dir()]
    expected_dirs = [output / "nnscaler", output / "nnscaler" / "autodist"]
    if files != [extension] or directories != expected_dirs or not extension.is_file():
        raise RuntimeError(f"unexpected dp solver build output: {produced}")
    digest = sha256(extension)
    if digest != EXPECTED_EXTENSION_SHA256:
        raise RuntimeError(f"dp solver differs from canonical build: {digest}")
    extension.chmod(0o555)
    return extension


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    public = sub.add_parser("build")
    public.add_argument("repo", type=Path)
    public.add_argument("revision")
    public.add_argument("output", type=Path)
    private = sub.add_parser("_namespace_build")
    private.add_argument("repo", type=Path)
    private.add_argument("revision")
    private.add_argument("output", type=Path)
    private.add_argument("archive_hash")
    private.add_argument("hash_pairs", nargs="+")
    args = parser.parse_args()
    if args.action == "build":
        extension = build(args.repo, args.revision, args.output)
        print(f"{extension}\t{sha256(extension)}")
        return
    if len(args.hash_pairs) % 2:
        raise RuntimeError("malformed source hash pairs")
    expected = dict(zip(args.hash_pairs[::2], args.hash_pairs[1::2]))
    if set(expected) != set(SOURCE_PATHS):
        raise RuntimeError("incomplete dp solver source hash ledger")
    _namespace_build(
        args.repo.resolve(), args.revision, args.output.absolute(),
        args.archive_hash, expected,
    )


if __name__ == "__main__":
    main()
