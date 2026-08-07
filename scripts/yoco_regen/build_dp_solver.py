#!/usr/bin/env python3
"""Build nnScaler's canonical dp_solver without privileged namespaces."""
from __future__ import annotations

import argparse
import hashlib
import os
import posixpath
import shutil
import stat
import subprocess
import sys
import sysconfig
import tarfile
import tempfile
from pathlib import Path

NNSCALER_REVISION = "d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf"
NNSCALER_ARCHIVE_SHA256 = "fd919ddb50ee7bd380fd4588485ad843fd8a97fce115929b2466c837cdde7110"
SOURCE_SHA256 = {
    "setup.py": "40eb878e1f7fe0bb39afe1e319ee89763f5dfc4444223cb52f22bc4986b0c803",
    "nnscaler/autodist/dp_solver.cpp": "4da50c4da2c0ea5cda6e9ddfb3cbf7f4a8bb856c6f1cef8f9c70a9c2f3c31b12",
    "nnscaler/autodist/dp_solver.h": "9e7d49a014ee048af5ae5d04343db1e3184cdfbb2525c6bc3da61aafb970f80e",
}
EXPECTED_EXTENSION_SHA256 = "10635af2e67a56c2029296fbc7563952563a0d611e0cde41ac006f748ef08681"
CLEAN_TOOL_ENV = {"LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "PATH": "/usr/bin:/bin"}


def sha256(path: Path) -> str:
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode):
            raise RuntimeError(f"not a regular build artifact: {path}")
        digest = hashlib.sha256()
        while chunk := os.read(descriptor, 1 << 20):
            digest.update(chunk)
        return digest.hexdigest()
    finally:
        os.close(descriptor)


def _validate_archive_members(archive: bytes) -> None:
    import io

    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as handle:
        for member in handle.getmembers():
            path = Path(member.name)
            if path.is_absolute() or ".." in path.parts:
                raise RuntimeError(f"unsafe fixed archive member: {member.name}")
            if member.issym():
                target = posixpath.normpath(
                    posixpath.join(posixpath.dirname(member.name), member.linkname)
                )
                if member.linkname.startswith("/") or target == ".." or target.startswith("../"):
                    raise RuntimeError(f"escaping fixed archive symlink: {member.name}")
                continue
            if not (member.isfile() or member.isdir()):
                raise RuntimeError(f"unsupported fixed archive member: {member.name}")


def _make_source_tree_read_only(root: Path) -> None:
    entries = sorted(root.rglob("*"), key=lambda path: len(path.parts), reverse=True)
    for path in entries:
        if path.is_symlink():
            continue
        path.chmod(0o500 if path.is_dir() else 0o400)
    root.chmod(0o500)


def _remove_private_tree(root: Path) -> None:
    if not root.exists():
        return
    for path in sorted(root.rglob("*"), key=lambda item: len(item.parts)):
        if path.is_dir() and not path.is_symlink():
            path.chmod(0o700)
        elif not path.is_symlink():
            path.chmod(0o600)
    root.chmod(0o700)
    shutil.rmtree(root)
    if root.exists():
        raise RuntimeError(f"private build tree survived cleanup: {root}")


def build(repo: Path, revision: str, output: Path) -> Path:
    if revision != NNSCALER_REVISION:
        raise RuntimeError("unexpected nnScaler revision")
    repo = repo.resolve()
    output = output.absolute()
    output.mkdir(mode=0o700, parents=True, exist_ok=False)
    source_root = Path(tempfile.mkdtemp(prefix="trainverify-dp-input-"))
    build_temp = Path(tempfile.mkdtemp(prefix="trainverify-dp-temp-"))
    try:
        archive = subprocess.check_output(
            ["git", "-C", str(repo), "archive", "--format=tar", revision],
            env=CLEAN_TOOL_ENV,
        )
        if hashlib.sha256(archive).hexdigest() != NNSCALER_ARCHIVE_SHA256:
            raise RuntimeError("fixed nnScaler commit archive hash mismatch")
        _validate_archive_members(archive)
        extracted = subprocess.run(
            ["/usr/bin/tar", "-x", "-C", str(source_root)],
            input=archive,
            env=CLEAN_TOOL_ENV,
        )
        if extracted.returncode:
            raise RuntimeError("failed to materialize fixed nnScaler build input")
        actual = {relative: sha256(source_root / relative) for relative in SOURCE_SHA256}
        if actual != SOURCE_SHA256:
            raise RuntimeError(f"dp solver build input mismatch: {actual}")
        _make_source_tree_read_only(source_root)

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
                sys.executable, "-S", str(source_root / "setup.py"), "build_ext",
                "--build-lib", str(output), "--build-temp", str(build_temp),
            ],
            cwd=source_root,
            env=build_env,
            stdout=sys.stderr,
            stderr=sys.stderr,
            check=True,
        )
    finally:
        _remove_private_tree(build_temp)
        _remove_private_tree(source_root)

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
    parser.add_argument("action", choices=("build",))
    parser.add_argument("repo", type=Path)
    parser.add_argument("revision")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    extension = build(args.repo, args.revision, args.output)
    print(f"{extension}\t{sha256(extension)}")


if __name__ == "__main__":
    main()
