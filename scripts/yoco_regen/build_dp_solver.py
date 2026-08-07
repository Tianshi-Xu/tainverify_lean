#!/usr/bin/env python3
"""Build nnScaler's canonical dp_solver from sealed, fixed Git bytes."""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import io
import os
import posixpath
import re
import shutil
import stat
import subprocess
import sys
import sysconfig
import tarfile
import tempfile
from pathlib import Path, PurePosixPath

NNSCALER_REVISION = "d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf"
NNSCALER_ARCHIVE_SHA256 = "fd919ddb50ee7bd380fd4588485ad843fd8a97fce115929b2466c837cdde7110"
SOURCE_SHA256 = {
    "setup.py": "40eb878e1f7fe0bb39afe1e319ee89763f5dfc4444223cb52f22bc4986b0c803",
    "nnscaler/autodist/dp_solver.cpp": "4da50c4da2c0ea5cda6e9ddfb3cbf7f4a8bb856c6f1cef8f9c70a9c2f3c31b12",
    "nnscaler/autodist/dp_solver.h": "9e7d49a014ee048af5ae5d04343db1e3184cdfbb2525c6bc3da61aafb970f80e",
}
EXPECTED_EXTENSION_SHA256 = "e9b3072d6704f81db49726ba1c30da493a6793b388b8afe32dd26d1f6343debe"
CLEAN_TOOL_ENV = {"LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "PATH": "/usr/bin:/bin"}
_FULL_SEALS = (
    getattr(fcntl, "F_SEAL_SEAL", 0x0001)
    | getattr(fcntl, "F_SEAL_SHRINK", 0x0002)
    | getattr(fcntl, "F_SEAL_GROW", 0x0004)
    | getattr(fcntl, "F_SEAL_WRITE", 0x0008)
)
_HEADER_INCLUDE = b'#include "dp_solver.h"'


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


def _canonical_member_name(raw: str) -> str:
    if not raw or "\\" in raw or raw.startswith("/") or raw.endswith("/"):
        raise RuntimeError(f"non-canonical fixed archive member: {raw!r}")
    path = PurePosixPath(raw)
    if any(part in ("", ".", "..") for part in path.parts) or path.as_posix() != raw:
        raise RuntimeError(f"non-canonical fixed archive member: {raw!r}")
    return raw


def _validated_build_inputs(archive: bytes) -> dict[str, bytes]:
    found: dict[str, bytes] = {}
    seen: set[str] = set()
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as handle:
        for member in handle.getmembers():
            raw = member.name.rstrip("/") if member.isdir() else member.name
            name = _canonical_member_name(raw)
            if name in seen:
                raise RuntimeError(f"duplicate fixed archive member: {name}")
            seen.add(name)
            if member.issym():
                target = posixpath.normpath(
                    posixpath.join(posixpath.dirname(name), member.linkname)
                )
                if (
                    not member.linkname
                    or "\\" in member.linkname
                    or member.linkname.startswith("/")
                    or target == ".."
                    or target.startswith("../")
                ):
                    raise RuntimeError(f"escaping fixed archive symlink: {name}")
                continue
            if member.isdir():
                continue
            if not member.isfile():
                raise RuntimeError(f"unsupported fixed archive member: {name}")
            if name in SOURCE_SHA256:
                stream = handle.extractfile(member)
                if stream is None:
                    raise RuntimeError(f"unreadable fixed archive member: {name}")
                found[name] = stream.read()
    if set(found) != set(SOURCE_SHA256):
        raise RuntimeError("fixed archive is missing direct dp solver build inputs")
    actual = {name: hashlib.sha256(content).hexdigest() for name, content in found.items()}
    if actual != SOURCE_SHA256:
        raise RuntimeError(f"dp solver build input mismatch: {actual}")
    return found


def _sealed_memfd(name: str, content: bytes) -> int:
    flags = getattr(os, "MFD_CLOEXEC", 0x0001) | getattr(os, "MFD_ALLOW_SEALING", 0x0002)
    descriptor = os.memfd_create(name, flags)
    try:
        view = memoryview(content)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise RuntimeError("short write to build-input memfd")
            view = view[written:]
        os.fchmod(descriptor, 0o444)
        os.lseek(descriptor, 0, os.SEEK_SET)
        fcntl.fcntl(descriptor, getattr(fcntl, "F_ADD_SEALS", 1033), _FULL_SEALS)
        if fcntl.fcntl(descriptor, getattr(fcntl, "F_GET_SEALS", 1034)) != _FULL_SEALS:
            raise RuntimeError("failed to fully seal build-input memfd")
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def _remove_private_tree(root: Path) -> None:
    if not root.exists():
        return
    shutil.rmtree(root)
    if root.exists():
        raise RuntimeError(f"private build tree survived cleanup: {root}")


def _validate_build_output(output: Path, extension: Path) -> None:
    produced = set(output.rglob("*"))
    expected_dirs = {output / "nnscaler", output / "nnscaler" / "autodist"}
    expected_nodes = {*expected_dirs, extension}
    if produced != expected_nodes:
        raise RuntimeError(f"unexpected dp solver build output: {sorted(map(str, produced))}")
    for directory in expected_dirs:
        info = directory.lstat()
        if not stat.S_ISDIR(info.st_mode):
            raise RuntimeError(f"dp solver build output is not a directory: {directory}")
    info = extension.lstat()
    if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
        raise RuntimeError("dp solver build output is not a unique regular file")


def build(repo: Path, revision: str, output: Path) -> Path:
    if revision != NNSCALER_REVISION:
        raise RuntimeError("unexpected nnScaler revision")
    repo = repo.resolve()
    output = output.absolute()
    output.mkdir(mode=0o700, parents=True, exist_ok=False)
    build_temp = Path(tempfile.mkdtemp(prefix="trainverify-dp-temp-"))
    descriptors: list[int] = []
    try:
        archive = subprocess.check_output(
            ["/usr/bin/git", "-C", str(repo), "archive", "--format=tar", revision],
            env=CLEAN_TOOL_ENV,
        )
        if hashlib.sha256(archive).hexdigest() != NNSCALER_ARCHIVE_SHA256:
            raise RuntimeError("fixed nnScaler commit archive hash mismatch")
        inputs = _validated_build_inputs(archive)

        owner = os.getpid()
        header_fd = _sealed_memfd("dp_solver.h", inputs["nnscaler/autodist/dp_solver.h"])
        descriptors.append(header_fd)
        header_path = f"/proc/{owner}/fd/{header_fd}"
        cpp = inputs["nnscaler/autodist/dp_solver.cpp"]
        if cpp.count(_HEADER_INCLUDE) != 1:
            raise RuntimeError("dp solver source header include is not unique")
        transported_cpp = cpp.replace(
            _HEADER_INCLUDE, f'#include "{header_path}"'.encode("ascii")
        )
        cpp_fd = _sealed_memfd("dp_solver.cpp", transported_cpp)
        descriptors.append(cpp_fd)
        cpp_path = f"/proc/{owner}/fd/{cpp_fd}"

        venv_site = (
            Path(sys.executable).absolute().parent.parent / "lib"
            / f"python{sys.version_info.major}.{sys.version_info.minor}" / "site-packages"
        )
        pybind_include = venv_site / "pybind11" / "include"
        python_include_value = sysconfig.get_path("include")
        python_include = Path(python_include_value) if python_include_value else Path("/")
        compiler = Path("/usr/bin/x86_64-linux-gnu-g++")
        if not compiler.is_file() or not pybind_include.is_dir() or not python_include.is_dir():
            raise RuntimeError("reviewed compiler or include directories are missing")

        suffix = sysconfig.get_config_var("EXT_SUFFIX")
        if not isinstance(suffix, str) or not suffix:
            raise RuntimeError("Python EXT_SUFFIX is unavailable")
        extension = output / "nnscaler" / "autodist" / f"dp_solver{suffix}"
        extension.parent.mkdir(mode=0o700, parents=True)
        object_file = build_temp / "dp_solver.o"
        compile_to_assembly = [
            str(compiler), "-fno-strict-overflow", "-Wsign-compare", "-DNDEBUG",
            "-g", "-O2", "-Wall", "-fPIC", f"-I{pybind_include}",
            f"-I{python_include}", "-x", "c++", "-S", cpp_path, "-o", "-",
            "-fvisibility=hidden", "-g0", "-std=c++11",
            "-O3", "-fPIC", "-D_GLIBCXX_USE_CXX11_ABI=0",
        ]
        assembly = subprocess.check_output(
            compile_to_assembly,
            env=CLEAN_TOOL_ENV,
            pass_fds=tuple(descriptors),
            stderr=sys.stderr,
        )
        file_directive = re.compile(br'(?m)^\s*\.file\s+"[0-9]+"\s*$')
        matches = file_directive.findall(assembly)
        if len(matches) != 1:
            raise RuntimeError("compiler assembly has an unexpected source FILE directive")
        assembly = file_directive.sub(b'\t.file\t"dp_solver.cpp"', assembly, count=1)
        assembly_fd = _sealed_memfd("dp_solver.s", assembly)
        descriptors.append(assembly_fd)
        subprocess.run(
            [
                str(compiler), "-x", "assembler", "-c",
                f"/proc/{owner}/fd/{assembly_fd}", "-o", str(object_file),
            ],
            env=CLEAN_TOOL_ENV,
            pass_fds=tuple(descriptors),
            stdout=sys.stderr,
            stderr=sys.stderr,
            check=True,
        )
        subprocess.run(
            [
                str(compiler), "-fno-strict-overflow", "-Wsign-compare", "-DNDEBUG",
                "-g", "-O2", "-Wall", "-shared", "-Wl,-O1",
                "-Wl,-Bsymbolic-functions", str(object_file),
                "-L/usr/lib/x86_64-linux-gnu", "-o", str(extension), "-lpthread",
            ],
            env=CLEAN_TOOL_ENV,
            stdout=sys.stderr,
            stderr=sys.stderr,
            check=True,
        )
        subprocess.run(
            [
                "/usr/bin/objcopy", "--strip-all",
                "--remove-section=.note.gnu.build-id", str(extension),
            ],
            env=CLEAN_TOOL_ENV,
            stdout=sys.stderr,
            stderr=sys.stderr,
            check=True,
        )
    finally:
        for descriptor in descriptors:
            os.close(descriptor)
        _remove_private_tree(build_temp)

    _validate_build_output(output, extension)
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
