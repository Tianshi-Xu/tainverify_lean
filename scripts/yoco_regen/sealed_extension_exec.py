#!/usr/bin/env python3
"""Execute a command from a private package rebuilt solely from sealed inputs."""
from __future__ import annotations

import argparse
import ctypes
import fcntl
import hashlib
import os
import shlex
import stat
import subprocess
import sys
import sysconfig
import tempfile
from pathlib import Path

NNSCALER_REVISION = "d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf"
NNSCALER_ARCHIVE_SHA256 = "fd919ddb50ee7bd380fd4588485ad843fd8a97fce115929b2466c837cdde7110"
PATCHED_PARALLEL_SHA256 = "76ab814aec94a2a6bfe873bbdaedbfbdf2350c05db5183c20e94515ff8def0d0"
SITE_GUARD_SHA256 = "aecdf2b615b400c4a615f2a3a50a5a91737d6c54e0a4e130c4e41a3fb3822555"
CLEAN_TOOL_ENV = {"LANG": "C.UTF-8", "LC_ALL": "C.UTF-8", "PATH": "/usr/bin:/bin"}
RUNTIME_INHERITED_KEYS = (
    "HOME",
    "MGENER_DUMP_PATH",
    "TRAINVERIFY_EXPECTED_POLICY",
    "TRAINVERIFY_PATCHED_LLM_GEMM_SHA256",
    "TRAINVERIFY_COMM_PROFILE_SHA256",
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


def _hash(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def allowlisted_runtime_environment(inherited: dict[str, str]) -> dict[str, str]:
    missing = [key for key in RUNTIME_INHERITED_KEYS if not inherited.get(key)]
    if missing:
        raise RuntimeError(f"missing sealed runtime environment: {missing}")
    return {key: inherited[key] for key in RUNTIME_INHERITED_KEYS}


def _read_regular(path: Path, expected_hash: str, *, elf: bool = False) -> bytes:
    fd = os.open(path.absolute(), os.O_RDONLY | os.O_NOFOLLOW)
    try:
        info = os.fstat(fd)
        if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid():
            raise PermissionError(f"untrusted runtime input inode: {path}")
        chunks = []
        while chunk := os.read(fd, 1 << 20):
            chunks.append(chunk)
        content = b"".join(chunks)
    finally:
        os.close(fd)
    if (elf and not content.startswith(b"\x7fELF")) or _hash(content) != expected_hash:
        raise RuntimeError(f"runtime input content mismatch: {path}")
    return content


def _sealed_memfd(name: str, content: bytes) -> int:
    flags = getattr(os, "MFD_CLOEXEC", 0x0001) | getattr(os, "MFD_ALLOW_SEALING", 0x0002)
    fd = os.memfd_create(name, flags)
    os.write(fd, content)
    os.lseek(fd, 0, os.SEEK_SET)
    seals = (
        getattr(fcntl, "F_SEAL_SEAL", 0x0001)
        | getattr(fcntl, "F_SEAL_SHRINK", 0x0002)
        | getattr(fcntl, "F_SEAL_GROW", 0x0004)
        | getattr(fcntl, "F_SEAL_WRITE", 0x0008)
    )
    fcntl.fcntl(fd, getattr(fcntl, "F_ADD_SEALS", 1033), seals)
    return fd


def _read_fd(fd: int) -> bytes:
    os.lseek(fd, 0, os.SEEK_SET)
    chunks = []
    while chunk := os.read(fd, 1 << 20):
        chunks.append(chunk)
    return b"".join(chunks)


def run_sealed(
    extension: Path,
    expected_hash: str,
    package_root: Path,
    site_guard: Path,
    python_tail: Path,
    command: list[str],
) -> None:
    package_root = package_root.resolve()
    if not package_root.is_dir() or not python_tail.is_dir():
        raise RuntimeError("sealed execution support path is missing")
    extension_content = _read_regular(extension, expected_hash, elf=True)
    parallel_content = _read_regular(
        package_root / "nnscaler" / "parallel.py", PATCHED_PARALLEL_SHA256
    )
    guard_content = _read_regular(site_guard, SITE_GUARD_SHA256)
    archive_content = subprocess.check_output([
        "git", "-C", str(package_root), "archive", "--format=tar", NNSCALER_REVISION,
    ])
    if _hash(archive_content) != NNSCALER_ARCHIVE_SHA256:
        raise RuntimeError("fixed nnScaler archive hash mismatch before sealing")

    contents = [archive_content, parallel_content, guard_content, extension_content]
    fds = [
        _sealed_memfd(name, content)
        for name, content in zip(
            ("nnscaler-archive", "patched-parallel", "site-guard", "dp-solver"),
            contents,
        )
    ]
    try:
        launcher_environment = allowlisted_runtime_environment(dict(os.environ))
        launcher_environment.update(CLEAN_TOOL_ENV)
        launcher_environment.update({
            "PYTHONNOUSERSITE": "1",
            "PYTHONSAFEPATH": "1",
            "PYTHONDONTWRITEBYTECODE": "1",
        })
        subprocess.run(
            [
                "unshare", "--user", "--map-root-user", "--mount",
                sys.executable, "-S", str(Path(__file__).resolve()), "_exec",
                *(str(fd) for fd in fds), expected_hash,
                extension.name, str(python_tail.resolve()), "--", *command,
            ],
            pass_fds=tuple(fds),
            env=launcher_environment,
            check=True,
        )
    finally:
        for fd in fds:
            os.close(fd)


def _mount(mount, target: Path, flags: int = 0, data: bytes | None = None) -> None:
    if mount(b"tmpfs", os.fsencode(target), b"tmpfs", flags, data) != 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error), str(target))


def _exec(
    archive_fd: int,
    parallel_fd: int,
    guard_fd: int,
    extension_fd: int,
    expected_hash: str,
    extension_name: str,
    python_tail: Path,
    command: list[str],
) -> None:
    if not command or not python_tail.is_dir():
        raise RuntimeError("sealed execution command or tail is missing")
    archive = _read_fd(archive_fd)
    parallel = _read_fd(parallel_fd)
    guard = _read_fd(guard_fd)
    extension = _read_fd(extension_fd)
    for fd in (archive_fd, parallel_fd, guard_fd, extension_fd):
        os.close(fd)
    if _hash(archive) != NNSCALER_ARCHIVE_SHA256:
        raise RuntimeError("sealed nnScaler archive hash mismatch")
    if _hash(parallel) != PATCHED_PARALLEL_SHA256:
        raise RuntimeError("sealed parallel.py hash mismatch")
    if _hash(guard) != SITE_GUARD_SHA256:
        raise RuntimeError("sealed site guard hash mismatch")
    if not extension.startswith(b"\x7fELF") or _hash(extension) != expected_hash:
        raise RuntimeError("sealed dp solver hash mismatch")

    libc = ctypes.CDLL(None, use_errno=True)
    mount = libc.mount
    mount.argtypes = [
        ctypes.c_char_p, ctypes.c_char_p, ctypes.c_char_p,
        ctypes.c_ulong, ctypes.c_void_p,
    ]
    mount.restype = ctypes.c_int
    ms_remount, ms_rdonly = 32, 1
    private_root = Path(tempfile.mkdtemp(prefix="trainverify-sealed-runtime-"))
    _mount(mount, private_root, data=b"mode=0700,size=1G")
    private_package = private_root / "nnscaler-source"
    private_guard = private_root / "guard"
    private_package.mkdir()
    private_guard.mkdir()
    extracted = subprocess.run(
        ["/usr/bin/tar", "-x", "-C", str(private_package)],
        input=archive,
        env=CLEAN_TOOL_ENV,
    )
    if extracted.returncode:
        raise RuntimeError("failed to extract sealed nnScaler archive")
    parallel_path = private_package / "nnscaler" / "parallel.py"
    parallel_path.write_bytes(parallel)
    parallel_path.chmod(0o444)
    guard_path = private_guard / "sitecustomize.py"
    guard_path.write_bytes(guard)
    guard_path.chmod(0o444)
    extension_path = private_package / "nnscaler" / "autodist" / extension_name
    if extension_path.exists():
        raise RuntimeError("fixed archive unexpectedly contains dp solver extension")
    extension_path.write_bytes(extension)
    extension_path.chmod(0o555)
    bootstrap_path = private_root / "bootstrap.py"
    bootstrap_path.write_text(BOOTSTRAP, encoding="utf-8")
    bootstrap_path.chmod(0o444)
    python_executable = Path(sys.executable).absolute()
    worker_shim = private_root / "python-worker"
    worker_shim.write_text(
        "#!/bin/sh\n"
        "if [ \"${1-}\" = -u ]; then shift; fi\n"
        f"exec {shlex.quote(str(python_executable))} -S "
        f"{shlex.quote(str(bootstrap_path))} script \"$@\"\n",
        encoding="utf-8",
    )
    worker_shim.chmod(0o555)
    _mount(mount, private_root, flags=ms_remount | ms_rdonly)
    if _hash(extension_path.read_bytes()) != expected_hash:
        raise RuntimeError("private dp solver materialization hash mismatch")

    environment = allowlisted_runtime_environment(dict(os.environ))
    environment["PYTHONPATH"] = f"{private_guard}:{private_package}:{python_tail.resolve()}"
    runtime_paths = []
    venv_site = (
        python_executable.parent.parent / "lib"
        / f"python{sys.version_info.major}.{sys.version_info.minor}" / "site-packages"
    )
    if venv_site.is_dir():
        runtime_paths.append(str(venv_site))
    for key in ("purelib", "platlib"):
        value = sysconfig.get_paths().get(key)
        if value and Path(value).is_dir() and value not in runtime_paths:
            runtime_paths.append(value)
    environment["PYTHONPATH"] += ":" + ":".join(runtime_paths)
    environment["PYTHONSAFEPATH"] = "1"
    environment["PYTHONNOUSERSITE"] = "1"
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["CUDA_VISIBLE_DEVICES"] = "0,1"
    environment["LANG"] = "C.UTF-8"
    environment["LC_ALL"] = "C.UTF-8"
    environment["PATH"] = "/usr/local/cuda/bin:/usr/local/bin:/usr/bin:/bin"
    environment["TRAINVERIFY_DP_SOLVER_PATH"] = str(extension_path)
    environment["TRAINVERIFY_DP_SOLVER_SHA256"] = expected_hash
    environment["TRAINVERIFY_WORKER_SHIM"] = str(worker_shim)
    if command[0] != "torchrun":
        raise RuntimeError("sealed execution only accepts the torchrun entry point")
    os.execve(
        python_executable,
        [
            str(python_executable), "-S", str(bootstrap_path),
            "module", "torch.distributed.run", *command[1:],
        ],
        environment,
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    public = sub.add_parser("run")
    public.add_argument("extension", type=Path)
    public.add_argument("expected_hash")
    public.add_argument("package_root", type=Path)
    public.add_argument("site_guard", type=Path)
    public.add_argument("python_tail", type=Path)
    public.add_argument("command", nargs=argparse.REMAINDER)
    private = sub.add_parser("_exec")
    private.add_argument("archive_fd", type=int)
    private.add_argument("parallel_fd", type=int)
    private.add_argument("guard_fd", type=int)
    private.add_argument("extension_fd", type=int)
    private.add_argument("expected_hash")
    private.add_argument("extension_name")
    private.add_argument("python_tail", type=Path)
    private.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if args.action == "run":
        run_sealed(
            args.extension, args.expected_hash, args.package_root,
            args.site_guard, args.python_tail, command,
        )
    else:
        _exec(
            args.archive_fd, args.parallel_fd, args.guard_fd, args.extension_fd,
            args.expected_hash, args.extension_name, args.python_tail, command,
        )


if __name__ == "__main__":
    main()
