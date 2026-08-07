#!/usr/bin/env python3
"""Execute torchrun from memfd-sealed nnScaler runtime and native bytes."""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import io
import os
import posixpath
import shlex
import stat
import subprocess
import sys
import sysconfig
import tarfile
import zipfile
from pathlib import Path
from pathlib import PurePosixPath

NNSCALER_REVISION = "d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf"
NNSCALER_ARCHIVE_SHA256 = "fd919ddb50ee7bd380fd4588485ad843fd8a97fce115929b2466c837cdde7110"
PATCHED_PARALLEL_SHA256 = "5ce434c544546fbe27fc890e96c39db3191e91d47de6f338460e668e2e38f46c"
SITE_GUARD_SHA256 = "7227a7e0696970a438ac9cb7820d9e4c88a866e86d1a65e99380114ad94bcfed"
CLEAN_TOOL_ENV = {"LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "PATH": "/usr/bin:/bin"}
RUNTIME_INHERITED_KEYS = (
    "HOME",
    "MGENER_DUMP_PATH",
    "TRAINVERIFY_EXPECTED_POLICY",
    "TRAINVERIFY_PATCHED_LLM_GEMM_SHA256",
    "TRAINVERIFY_COMM_PROFILE_SHA256",
    "TRAINVERIFY_COMP_PROFILE_SHA256",
    "TRAINVERIFY_LLM_SOURCE_ROOT",
)
BOOTSTRAP = """import importlib, os, runpy, sys
importlib.import_module("sitecustomize")
sys.executable = os.environ["TRAINVERIFY_WORKER_SHIM"]
mode, target = sys.argv[1:3]
del sys.argv[1:3]
if mode == "module":
    runpy.run_module(target, run_name="__main__", alter_sys=True)
elif mode == "script":
    runpy.run_path(target, run_name="__main__")
else:
    raise RuntimeError("invalid sealed Python bootstrap mode")
"""
SPAWN_BOOTSTRAP = """import importlib, os, sys
importlib.import_module("sitecustomize")
sys.executable = os.environ["TRAINVERIFY_WORKER_SHIM"]
code = sys.argv[1]
del sys.argv[1]
namespace = {"__name__": "__main__", "__builtins__": __builtins__}
exec(compile(code, "<multiprocessing-spawn>", "exec"), namespace, namespace)
"""
_FULL_SEALS = (
    getattr(fcntl, "F_SEAL_SEAL", 0x0001)
    | getattr(fcntl, "F_SEAL_SHRINK", 0x0002)
    | getattr(fcntl, "F_SEAL_GROW", 0x0004)
    | getattr(fcntl, "F_SEAL_WRITE", 0x0008)
)


def _hash(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def allowlisted_runtime_environment(inherited: dict[str, str]) -> dict[str, str]:
    missing = [key for key in RUNTIME_INHERITED_KEYS if not inherited.get(key)]
    if missing:
        raise RuntimeError(f"missing sealed runtime environment: {missing}")
    return {key: inherited[key] for key in RUNTIME_INHERITED_KEYS}


def _read_regular(path: Path, expected_hash: str, *, elf: bool = False) -> bytes:
    descriptor = os.open(path.absolute(), os.O_RDONLY | os.O_NOFOLLOW)
    try:
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid():
            raise PermissionError(f"untrusted runtime input inode: {path}")
        digest = hashlib.sha256()
        content = bytearray()
        while chunk := os.read(descriptor, 1 << 20):
            digest.update(chunk)
            content.extend(chunk)
    finally:
        os.close(descriptor)
    result = bytes(content)
    if (elf and not result.startswith(b"\x7fELF")) or digest.hexdigest() != expected_hash:
        raise RuntimeError(f"runtime input content mismatch: {path}")
    return result


def _sealed_memfd(name: str, content: bytes, *, executable: bool = False) -> int:
    flags = getattr(os, "MFD_CLOEXEC", 0x0001) | getattr(os, "MFD_ALLOW_SEALING", 0x0002)
    descriptor = os.memfd_create(name, flags)
    try:
        view = memoryview(content)
        while view:
            written = os.write(descriptor, view)
            view = view[written:]
        os.fchmod(descriptor, 0o555 if executable else 0o444)
        os.lseek(descriptor, 0, os.SEEK_SET)
        fcntl.fcntl(descriptor, getattr(fcntl, "F_ADD_SEALS", 1033), _FULL_SEALS)
        if fcntl.fcntl(descriptor, getattr(fcntl, "F_GET_SEALS", 1034)) != _FULL_SEALS:
            raise RuntimeError("failed to fully seal runtime memfd")
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def _zip_info(name: str, mode: int) -> zipfile.ZipInfo:
    info = zipfile.ZipInfo(name, date_time=(1980, 1, 1, 0, 0, 0))
    info.compress_type = zipfile.ZIP_STORED
    info.create_system = 3
    info.external_attr = (mode & 0o777) << 16
    return info


def _canonical_archive_name(raw: str, *, directory: bool) -> str:
    candidate = raw[:-1] if directory and raw.endswith("/") else raw
    if (
        not candidate
        or "\\" in candidate
        or candidate.startswith("/")
        or candidate.endswith("/")
    ):
        raise RuntimeError(f"non-canonical fixed archive member: {raw!r}")
    path = PurePosixPath(candidate)
    if (
        any(part in ("", ".", "..") for part in path.parts)
        or path.as_posix() != candidate
    ):
        raise RuntimeError(f"non-canonical fixed archive member: {raw!r}")
    return candidate


def _runtime_zip(archive: bytes, parallel: bytes, guard: bytes) -> bytes:
    source = io.BytesIO(archive)
    target = io.BytesIO()
    parallel_count = 0
    seen: set[str] = set()
    expected_zip_names: set[str] = {"sitecustomize.py"}
    with tarfile.open(fileobj=source, mode="r:") as tar, zipfile.ZipFile(
        target, mode="w", compression=zipfile.ZIP_STORED, strict_timestamps=True
    ) as runtime:
        for member in tar.getmembers():
            name = _canonical_archive_name(member.name, directory=member.isdir())
            if name in seen:
                raise RuntimeError(f"duplicate fixed archive member: {name}")
            seen.add(name)
            if name == "sitecustomize.py":
                raise RuntimeError("fixed archive conflicts with sealed startup guard")
            if member.issym():
                target_name = posixpath.normpath(
                    posixpath.join(posixpath.dirname(name), member.linkname)
                )
                if (
                    not member.linkname
                    or "\\" in member.linkname
                    or member.linkname.startswith("/")
                    or target_name == ".."
                    or target_name.startswith("../")
                ):
                    raise RuntimeError(f"escaping fixed archive symlink: {name}")
                continue
            if member.isdir():
                runtime.writestr(_zip_info(name + "/", 0o555), b"")
                expected_zip_names.add(name + "/")
                continue
            if not member.isfile():
                raise RuntimeError(f"unsupported fixed archive member: {member.name}")
            extracted = tar.extractfile(member)
            if extracted is None:
                raise RuntimeError(f"unreadable fixed archive member: {member.name}")
            content = extracted.read()
            if name == "nnscaler/parallel.py":
                content = parallel
                parallel_count += 1
            if name.startswith("nnscaler/autodist/dp_solver.") and name.endswith(".so"):
                raise RuntimeError("fixed archive unexpectedly contains dp solver extension")
            runtime.writestr(_zip_info(name, 0o444), content)
            expected_zip_names.add(name)
        if parallel_count != 1:
            raise RuntimeError("fixed archive must contain nnscaler/parallel.py exactly once")
        runtime.writestr(_zip_info("sitecustomize.py", 0o444), guard)
    result = target.getvalue()
    with zipfile.ZipFile(io.BytesIO(result), mode="r") as runtime:
        names = [entry.filename for entry in runtime.infolist()]
        if len(names) != len(set(names)) or set(names) != expected_zip_names:
            raise RuntimeError("sealed runtime ZIP member set is ambiguous")
        for name in names:
            _canonical_archive_name(name, directory=name.endswith("/"))
    return result


def _runtime_paths(python_tail: Path) -> list[str]:
    paths = [str(python_tail.resolve())]
    python_executable = Path(sys.executable).absolute()
    venv_site = (
        python_executable.parent.parent / "lib"
        / f"python{sys.version_info.major}.{sys.version_info.minor}" / "site-packages"
    )
    if venv_site.is_dir():
        paths.append(str(venv_site))
    for key in ("purelib", "platlib"):
        value = sysconfig.get_paths().get(key)
        if value and Path(value).is_dir() and value not in paths:
            paths.append(value)
    return paths


def _worker_shim_content(python_executable: Path) -> bytes:
    return (
        "#!/bin/sh\n"
        "while [ \"$#\" -gt 0 ]; do\n"
        "  case \"$1\" in\n"
        "    -B|-S|-E|-s|-I|-O|-OO|-u) shift ;;\n"
        "    *) break ;;\n"
        "  esac\n"
        "done\n"
        "if [ \"${1-}\" = -c ]; then\n"
        "  shift\n"
        "  [ \"$#\" -ge 1 ] || exit 125\n"
        f"  exec {shlex.quote(str(python_executable))} -S -c "
        f"{shlex.quote(SPAWN_BOOTSTRAP)} \"$@\"\n"
        "fi\n"
        "case \"${1-}\" in -*) exit 125 ;; esac\n"
        f"exec {shlex.quote(str(python_executable))} -S -c "
        f"{shlex.quote(BOOTSTRAP)} script \"$@\"\n"
    ).encode("utf-8")


def run_sealed(
    extension: Path,
    expected_hash: str,
    package_root: Path,
    site_guard: Path,
    python_tail: Path,
    command: list[str],
    *,
    comp_profile: Path | None = None,
    comp_profile_hash: str | None = None,
    allow_live_comp_profile: bool = False,
) -> None:
    package_root = package_root.resolve()
    if not package_root.is_dir() or not python_tail.is_dir():
        raise RuntimeError("sealed execution support path is missing")
    if not command or command[0] != "torchrun":
        raise RuntimeError("sealed execution only accepts the torchrun entry point")
    extension_content = _read_regular(extension, expected_hash, elf=True)
    parallel_content = _read_regular(
        package_root / "nnscaler" / "parallel.py", PATCHED_PARALLEL_SHA256
    )
    guard_content = _read_regular(site_guard, SITE_GUARD_SHA256)
    archive_content = subprocess.check_output(
        ["git", "-C", str(package_root), "archive", "--format=tar", NNSCALER_REVISION],
        env=CLEAN_TOOL_ENV,
    )
    if _hash(archive_content) != NNSCALER_ARCHIVE_SHA256:
        raise RuntimeError("fixed nnScaler archive hash mismatch before sealing")
    runtime_content = _runtime_zip(archive_content, parallel_content, guard_content)
    runtime_hash = _hash(runtime_content)
    if allow_live_comp_profile == bool(comp_profile):
        raise RuntimeError("exactly one computation profile mode is required")
    comp_profile_content = None
    if comp_profile is not None:
        if not comp_profile_hash:
            raise RuntimeError("frozen computation profile hash is required")
        comp_profile_content = _read_regular(comp_profile, comp_profile_hash)

    python_executable = Path(sys.executable).absolute()
    shim_content = _worker_shim_content(python_executable)
    runtime_fd = _sealed_memfd("nnscaler-runtime.zip", runtime_content)
    extension_fd = _sealed_memfd(extension.name, extension_content, executable=True)
    shim_fd = _sealed_memfd("python-worker", shim_content, executable=True)
    comp_profile_fd = (
        _sealed_memfd("nnscaler-comp-profile.json", comp_profile_content)
        if comp_profile_content is not None else None
    )
    descriptors = tuple(
        descriptor for descriptor in (runtime_fd, extension_fd, shim_fd, comp_profile_fd)
        if descriptor is not None
    )
    try:
        owner = os.getpid()
        runtime_path = f"/proc/{owner}/fd/{runtime_fd}"
        extension_path = f"/proc/{owner}/fd/{extension_fd}"
        shim_path = f"/proc/{owner}/fd/{shim_fd}"
        environment = allowlisted_runtime_environment(dict(os.environ))
        environment.update({
            "CUDA_VISIBLE_DEVICES": "0,1",
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PATH": "/usr/local/cuda/bin:/usr/local/bin:/usr/bin:/bin",
            "PYTHONNOUSERSITE": "1",
            "PYTHONPATH": ":".join([runtime_path, *_runtime_paths(python_tail)]),
            "PYTHONHASHSEED": "0",
            "PYTHONSAFEPATH": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
            "TRAINVERIFY_DP_SOLVER_PATH": extension_path,
            "TRAINVERIFY_DP_SOLVER_SHA256": expected_hash,
            "TRAINVERIFY_RUNTIME_ZIP_PATH": runtime_path,
            "TRAINVERIFY_RUNTIME_ZIP_SHA256": runtime_hash,
            "TRAINVERIFY_WORKER_SHIM": shim_path,
        })
        if comp_profile_fd is not None:
            environment["TRAINVERIFY_COMP_PROFILE_PATH"] = (
                f"/proc/{owner}/fd/{comp_profile_fd}"
            )
            environment["TRAINVERIFY_COMP_PROFILE_SHA256"] = str(comp_profile_hash)
        else:
            environment["TRAINVERIFY_ALLOW_LIVE_COMP_PROFILE"] = "1"
        subprocess.run(
            [
                str(python_executable), "-S", "-c", BOOTSTRAP,
                "module", "torch.distributed.run", *command[1:],
            ],
            env=environment,
            pass_fds=descriptors,
            check=True,
        )
    finally:
        for descriptor in descriptors:
            os.close(descriptor)


def _parse_args(argv: list[str] | None = None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("run",))
    parser.add_argument("extension", type=Path)
    parser.add_argument("expected_hash")
    parser.add_argument("package_root", type=Path)
    parser.add_argument("site_guard", type=Path)
    parser.add_argument("python_tail", type=Path)
    parser.add_argument("--comp-profile", type=Path)
    parser.add_argument("--comp-profile-sha256")
    parser.add_argument("--allow-live-comp-profile", action="store_true")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    return parser.parse_args(argv)


def main() -> None:
    args = _parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    run_sealed(
        args.extension, args.expected_hash, args.package_root,
        args.site_guard, args.python_tail, command,
        comp_profile=args.comp_profile,
        comp_profile_hash=args.comp_profile_sha256,
        allow_live_comp_profile=args.allow_live_comp_profile,
    )


if __name__ == "__main__":
    main()
