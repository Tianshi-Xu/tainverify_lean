#!/usr/bin/env python3
"""Bridge emitter — UNIVERSAL end-to-end pipeline (emit2).

    python3 emit2.py <N> [--dry-run] [--no-compile] [--out PATH]

Like emit.py but drives renderer_uni.render_universal (any topology, no family-A gate).
"""
import os, sys, re, subprocess, argparse, hashlib, fcntl, ctypes, secrets, shutil, json, tempfile
from pathlib import Path
from typing import Callable, Optional

HERE = os.path.dirname(os.path.abspath(__file__))
TV   = os.path.dirname(HERE)
REPO = os.path.dirname(TV)
if REPO not in sys.path:
    sys.path.insert(0, REPO)
from trainverify.bridge_emitter.parser import load_goal_ir, analyze
from trainverify.bridge_emitter.probe import DENOTE_DIR
from trainverify.bridge_emitter.emit import trace_input_sources, compute_imports
from trainverify.bridge_emitter.target_config import (
    DENOTE_DIR as _RELDIR, MOD_PREFIX, GEN_FILE,
)
DENOTE = _RELDIR

SUPPORTED_WHOLE_MODEL_ARTIFACTS = {
    "gpt2": {
        "targets": (2, 3, 48),
        "namespace": "GPT2Whole",
        "module_prefix": "denote.gpt_ly4_regen.GPT2Whole",
        "aggregate_theorem": "gpt2_all_goals",
        "public_statement": "TrainVerify.Denote.GeneratedGoals.all_goals_stmt_full",
    },
    "yoco-a04b": {
        "targets": (1, 2, 3, 4, 5),
        "namespace": "YOCOA04BWhole",
        "module_prefix": "denote.yoco_goals.YOCOA04BWhole",
        "aggregate_theorem": "yoco_a04b_all_goals",
        "public_statement": "TrainVerify.Denote.GeneratedGoals.all_goals_stmt_full",
    },
    "yoco-3b": {
        "targets": (1, 2, 3, 4, 5),
        "namespace": "YOCO3BWhole",
        "module_prefix": "denote.yoco3b_heldout.YOCO3BWhole",
        "aggregate_theorem": "yoco3b_all_goals",
        "public_statement": "TrainVerify.Denote.GeneratedYOCO3BHeldout.all_goals_stmt_full",
    },
}


def whole_model_artifact_root(project_dir: str | Path = TV) -> Path:
    return Path(project_dir) / ".artifacts" / "whole-models"


def whole_model_artifact_path(model_id: str, project_dir: str | Path = TV) -> Path:
    try:
        module_prefix = SUPPORTED_WHOLE_MODEL_ARTIFACTS[model_id]["module_prefix"]
    except KeyError as exc:
        raise ValueError(f"unsupported whole-model artifact: {model_id}") from exc
    return whole_model_artifact_root(project_dir).joinpath(*module_prefix.split("."))


def _build_whole_model_catalog_bundle(artifact_root: str | Path) -> dict[str, bytes]:
    root = Path(artifact_root)
    models = []
    lean_entries = {}
    catalog_names = {
        "gpt2": "GPT2",
        "yoco-a04b": "YOCOA04B",
        "yoco-3b": "YOCO3B",
    }
    for model_id, spec in SUPPORTED_WHOLE_MODEL_ARTIFACTS.items():
        publication = root.joinpath(*spec["module_prefix"].split("."))
        if publication.is_symlink() or not publication.is_dir():
            raise ValueError(f"missing whole-model publication: {model_id}")
        main = publication / "Main.lean"
        if main.is_symlink() or not main.is_file() or main.stat().st_size == 0:
            raise ValueError(f"{model_id} publication is missing Main.lean")
        files = sorted(path for path in publication.rglob("*") if path.is_file())
        if any(path.is_symlink() for path in files):
            raise ValueError(f"{model_id} publication contains a symlink")
        theorem_ref = (
            f"TrainVerify.Denote.{spec['namespace']}.{spec['aggregate_theorem']}"
        )
        catalog_name = catalog_names[model_id]
        catalog_module = f"denote.WholeModels.{catalog_name}"
        catalog_theorem = (
            f"TrainVerify.Denote.WholeModels.{catalog_name}.verified"
        )
        lean_entries[f"{catalog_name}.lean"] = "\n".join([
            f"import {spec['module_prefix']}.Main",
            "",
            f"namespace TrainVerify.Denote.WholeModels.{catalog_name}",
            "",
            f"theorem verified : {spec['public_statement']} := {theorem_ref}",
            "",
            f"end TrainVerify.Denote.WholeModels.{catalog_name}",
            "",
        ]).encode("utf-8")
        models.append({
            "model_id": model_id,
            "targets": list(spec["targets"]),
            "path": publication.relative_to(root).as_posix(),
            "module_prefix": spec["module_prefix"],
            "aggregate_theorem": theorem_ref,
            "catalog_module": catalog_module,
            "catalog_theorem": catalog_theorem,
            "modules": len(files),
            "source_bytes": sum(path.stat().st_size for path in files),
        })
    manifest = {
        "schema_version": 1,
        "composition": "isolated-model-entrypoints",
        "models": models,
    }
    return {
        **lean_entries,
        "Manifest.json": (json.dumps(manifest, indent=2) + "\n").encode("utf-8"),
    }

F_ADD_SEALS = getattr(fcntl, "F_ADD_SEALS", 1033)
F_SEAL_SEAL = getattr(fcntl, "F_SEAL_SEAL", 0x0001)
F_SEAL_SHRINK = getattr(fcntl, "F_SEAL_SHRINK", 0x0002)
F_SEAL_GROW = getattr(fcntl, "F_SEAL_GROW", 0x0004)
F_SEAL_WRITE = getattr(fcntl, "F_SEAL_WRITE", 0x0008)
_LIBC = ctypes.CDLL(None, use_errno=True)
_RENAMEAT2 = _LIBC.renameat2
_RENAMEAT2.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
_RENAMEAT2.restype = ctypes.c_int
_LINKAT = _LIBC.linkat
_LINKAT.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_int]
_LINKAT.restype = ctypes.c_int
AT_EMPTY_PATH = 0x1000
AT_FDCWD = -100
AT_SYMLINK_FOLLOW = 0x400


def _renameat2(
    source_dir_fd: int,
    source_name: str,
    target_dir_fd: int,
    target_name: str,
    expected_identity: tuple[int, int],
) -> None:
    source_bytes = os.fsencode(source_name)
    target_bytes = os.fsencode(target_name)
    source_stat = os.stat(source_name, dir_fd=source_dir_fd, follow_symlinks=False)
    if (source_stat.st_dev, source_stat.st_ino) != expected_identity:
        raise RuntimeError("publication anchor identity changed before renameat2")
    result = _RENAMEAT2(
        source_dir_fd,
        source_bytes,
        target_dir_fd,
        target_bytes,
        0,
    )
    if result != 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error), target_name)


def _link_fd(source_fd: int, target_dir_fd: int, target_name: str) -> None:
    result = _LINKAT(source_fd, b"", target_dir_fd, os.fsencode(target_name), AT_EMPTY_PATH)
    if result == 0:
        return
    error = ctypes.get_errno()
    if error == 2:
        result = _LINKAT(
            AT_FDCWD,
            os.fsencode(f"/proc/self/fd/{source_fd}"),
            target_dir_fd,
            os.fsencode(target_name),
            AT_SYMLINK_FOLLOW,
        )
        if result == 0:
            return
        error = ctypes.get_errno()
    raise OSError(error, os.strerror(error), target_name)


def _publish_composed_source(
    text: str,
    out_path: str | Path,
    checker: Optional[Callable[[Path, int], None]],
) -> None:
    """Check a private candidate before atomically replacing the public path."""
    destination = Path(os.path.abspath(os.fspath(out_path)))
    destination.parent.mkdir(parents=True, exist_ok=True)
    expected_digest = hashlib.sha256(text.encode("utf-8")).digest()
    candidate_fd: Optional[int] = None
    publication_fd: Optional[int] = None
    parent_fd: Optional[int] = None
    anchor_name: Optional[str] = None
    anchor_identity: Optional[tuple[int, int]] = None

    def fd_digest(fd: int) -> bytes:
        os.lseek(fd, 0, os.SEEK_SET)
        digest = hashlib.sha256()
        while True:
            chunk = os.read(fd, 1024 * 1024)
            if not chunk:
                return digest.digest()
            digest.update(chunk)

    try:
        parent_fd = os.open(destination.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        fcntl.flock(parent_fd, fcntl.LOCK_EX)
        candidate_fd = os.memfd_create(
            "proof-compiler-candidate",
            os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING,
        )
        payload = text.encode("utf-8")
        offset = 0
        while offset < len(payload):
            offset += os.write(candidate_fd, payload[offset:])
        os.fsync(candidate_fd)
        fcntl.fcntl(
            candidate_fd,
            F_ADD_SEALS,
            F_SEAL_SEAL | F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_WRITE,
        )
        checked_path = Path(f"/proc/self/fd/{candidate_fd}")
        if checker is not None:
            checker(checked_path, candidate_fd)
        if fd_digest(candidate_fd) != expected_digest:
            raise RuntimeError("sealed candidate bytes differ from composed source")
        publication_fd = os.open(
            destination.parent,
            os.O_RDWR | os.O_TMPFILE,
            0o600,
        )
        os.lseek(candidate_fd, 0, os.SEEK_SET)
        while True:
            chunk = os.read(candidate_fd, 1024 * 1024)
            if not chunk:
                break
            offset = 0
            while offset < len(chunk):
                offset += os.write(publication_fd, chunk[offset:])
        os.fchmod(publication_fd, 0o400)
        os.fsync(publication_fd)
        anchor_stat = os.fstat(publication_fd)
        anchor_identity = (anchor_stat.st_dev, anchor_stat.st_ino)
        if fd_digest(publication_fd) != expected_digest:
            raise RuntimeError("anonymous publication inode differs from sealed source")

        anchor_name = f".proof-compiler-{secrets.token_hex(16)}.lean"
        _link_fd(publication_fd, parent_fd, anchor_name)
        anchor_path_stat = os.stat(anchor_name, dir_fd=parent_fd, follow_symlinks=False)
        if (anchor_path_stat.st_dev, anchor_path_stat.st_ino) != (
            anchor_stat.st_dev,
            anchor_stat.st_ino,
        ):
            raise RuntimeError("publication anchor identity changed")
        _renameat2(
            parent_fd,
            anchor_name,
            parent_fd,
            destination.name,
            anchor_identity,
        )
        published_fd = os.open(destination.name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=parent_fd)
        try:
            published_stat = os.fstat(published_fd)
            if (published_stat.st_dev, published_stat.st_ino) != (
                anchor_stat.st_dev,
                anchor_stat.st_ino,
            ):
                raise RuntimeError("published candidate identity differs from checked inode")
            if fd_digest(published_fd) != expected_digest:
                raise RuntimeError("published candidate bytes differ from checked source")
            os.fsync(published_fd)
        finally:
            os.close(published_fd)
        os.fsync(parent_fd)
    finally:
        if candidate_fd is not None:
            os.close(candidate_fd)
        if parent_fd is not None and anchor_name is not None and anchor_identity is not None:
            try:
                residue = os.stat(anchor_name, dir_fd=parent_fd, follow_symlinks=False)
                if (residue.st_dev, residue.st_ino) == anchor_identity:
                    os.unlink(anchor_name, dir_fd=parent_fd)
            except FileNotFoundError:
                pass
        if publication_fd is not None:
            os.close(publication_fd)
        if parent_fd is not None:
            os.close(parent_fd)


def _compile_closed_bundle_sources(
    bundle: dict[str, bytes],
    out_dir: str | Path,
    module_prefix: str,
    *,
    project_dir: str | Path = TV,
    compile_project_dependencies: bool = True,
) -> tuple[str, int, str] | None:
    """Kernel-check a bundle while materializing each importable `.olean`.

    A plain `lean Source.lean` invocation checks a file but does not write the
    object required by the next generated module.  Closed bundles are ordered
    by dependency, so compile each source explicitly into the matching module
    path under Lake's object tree and reject a missing/empty output as failure.
    """
    project = Path(project_dir)
    source_root = Path(out_dir)
    object_root = project / ".lake" / "build" / "lib" / "lean"
    module_root = object_root.joinpath(*module_prefix.split("."))

    def imports(source: str) -> tuple[str, ...]:
        names = []
        for match in re.finditer(
            r"(?m)^\s*import\s+(.+?)(?:\s+--.*)?$", source
        ):
            names.extend(match.group(1).split())
        return tuple(names)

    def compile_one(label: str, source_path: Path, output_path: Path):
        output_path.parent.mkdir(parents=True, mode=0o700, exist_ok=True)
        if output_path.is_symlink():
            return label, 1, f"refusing symlink object path: {output_path}"
        if output_path.exists():
            output_path.chmod(0o600)
            output_path.unlink()
        compiled = subprocess.run(
            [
                "lake", "env", "lean", "--tstack=65536", "-o",
                str(output_path), str(source_path),
            ],
            cwd=project,
            capture_output=True,
            text=True,
            timeout=900,
            env={**os.environ, "LEAN_NUM_THREADS": "1"},
            check=False,
        )
        output = compiled.stdout + compiled.stderr
        if compiled.returncode != 0 or "sorry" in output.lower():
            return label, compiled.returncode, output
        if not output_path.is_file() or output_path.stat().st_size == 0:
            return label, 1, output + f"\nLean produced no object file: {output_path}"
        output_path.chmod(0o400)
        return None

    bundle_modules = {
        f"{module_prefix}.{Path(relative).stem}" for relative in bundle
    }
    visited: set[str] = set()
    visiting: set[str] = set()

    def compile_project_import(module: str):
        if module in visited or module in bundle_modules:
            return None
        source_path = project.joinpath(*module.split(".")).with_suffix(".lean")
        if not source_path.is_file():
            visited.add(module)
            return None
        if module in visiting:
            return f"dependency:{module}", 1, "cyclic project-local Lean imports"
        visiting.add(module)
        for dependency in imports(source_path.read_text(encoding="utf-8")):
            failure = compile_project_import(dependency)
            if failure is not None:
                return failure
        visiting.remove(module)
        output_path = object_root.joinpath(*module.split(".")).with_suffix(".olean")
        failure = compile_one(f"dependency:{module}", source_path, output_path)
        if failure is None:
            visited.add(module)
        return failure

    if compile_project_dependencies:
        for payload in bundle.values():
            for module in imports(payload.decode("utf-8")):
                failure = compile_project_import(module)
                if failure is not None:
                    return failure

    for relative in bundle:
        source_path = source_root / relative
        output_path = module_root / Path(relative).with_suffix(".olean")
        failure = compile_one(relative, source_path, output_path)
        if failure is not None:
            return failure
    return None


def _validate_print_axioms_output(output: str, targets: tuple[str, ...]) -> None:
    allowed = {
        "propext", "Classical.choice", "Quot.sound",
        "Lean.ofReduceBool", "Lean.trustCompiler",
    }
    for target in targets:
        escaped = re.escape(target)
        if re.search(rf"'{escaped}' does not depend on any axioms", output):
            continue
        matched = re.search(
            rf"'{escaped}' depends on axioms: \[(.*?)\]", output, re.DOTALL
        )
        if matched is None:
            raise ValueError(f"missing #print axioms result: {target}")
        names = tuple(
            name.strip() for name in matched.group(1).split(",") if name.strip()
        )
        rejected = tuple(
            name for name in names
            if name not in allowed and not re.fullmatch(
                r".+\._native\.native_decide\.ax_[0-9_]+✝*",
                name,
            )
        )
        if rejected or any("sorryAx" in name for name in names):
            raise ValueError(f"untrusted axioms for {target}: {rejected or names}")


def _validate_chunked_axioms_output(output: str, target: str) -> None:
    escaped = re.escape(target)
    begin = re.search(rf"^AXIOM_RECEIPT_BEGIN {escaped} ([0-9]+)$", output, re.MULTILINE)
    end = re.search(rf"^AXIOM_RECEIPT_END {escaped} ([0-9]+)$", output, re.MULTILINE)
    if begin is None or end is None or begin.group(1) != end.group(1):
        raise ValueError(f"missing complete chunked axiom receipt: {target}")
    names = tuple(re.findall(r"^AXIOM (.+)$", output, re.MULTILINE))
    expected = int(begin.group(1))
    if len(names) != expected or len(set(names)) != expected:
        raise ValueError(
            f"incomplete chunked axiom receipt for {target}: "
            f"expected {expected}, got {len(names)} ({len(set(names))} unique)"
        )
    synthetic = f"'{target}' depends on axioms: [{', '.join(names)}]"
    _validate_print_axioms_output(synthetic, (target,))


def _chunked_axiom_audit_source(module: str, target: str) -> str:
    return f"""import {module}
import Lean.Util.CollectAxioms

open Lean Elab Command

syntax (name := trainVerifyPrintAxiomsChunked) "#trainverify_print_axioms_chunked " ident : command

@[command_elab trainVerifyPrintAxiomsChunked]
def elabTrainVerifyPrintAxiomsChunked : CommandElab
  | `(#trainverify_print_axioms_chunked $id:ident) => do
      let constName := id.getId
      let axioms ← collectAxioms constName
      logInfo m!"AXIOM_RECEIPT_BEGIN {{constName}} {{axioms.size}}"
      for axiomName in axioms.qsort Name.lt do
        logInfo m!"AXIOM {{axiomName}}"
      logInfo m!"AXIOM_RECEIPT_END {{constName}} {{axioms.size}}"
  | _ => throwUnsupportedSyntax

#trainverify_print_axioms_chunked {target}
"""


def _audit_closed_bundle_axioms(
    staged: Path,
    module_prefix: str,
    targets: tuple[str, ...],
    *,
    project_dir: str | Path = TV,
    imported_module: str | None = None,
) -> tuple[str, int, str] | None:
    if not targets:
        return None
    audit_path = staged / ".AxiomAudit.lean"
    imported = "Main" if (staged / "Main.lean").is_file() else "Public"
    imported_module = imported_module or f"{module_prefix}.{imported}"
    source = "\n".join([
        f"import {imported_module}",
        *(f"#print axioms {target}" for target in targets),
        "",
    ])
    audit_path.write_text(source, encoding="utf-8")
    try:
        audited = subprocess.run(
            ["lake", "env", "lean", "--tstack=65536", str(audit_path)],
            cwd=project_dir,
            capture_output=True,
            text=True,
            timeout=900,
            env={**os.environ, "LEAN_NUM_THREADS": "1"},
            check=False,
        )
        output = audited.stdout + audited.stderr
        if audited.returncode != 0:
            if audited.returncode != 134 or "Stack overflow detected" not in output:
                return "axiom-audit", audited.returncode, output
            # Lean's stock #print axioms first materializes the complete Array as
            # one recursive MessageData List.  Very broad, valid aggregate
            # receipts can overflow there after collectAxioms has succeeded.
            # Retry the same aggregate collector and emit one axiom per message;
            # this is not a per-target union or a weakened transitive audit.
            for index, target in enumerate(targets):
                audit_path.write_text(
                    _chunked_axiom_audit_source(
                        imported_module, target
                    ),
                    encoding="utf-8",
                )
                chunked = subprocess.run(
                    ["lake", "env", "lean", "--tstack=65536", str(audit_path)],
                    cwd=project_dir,
                    capture_output=True,
                    text=True,
                    timeout=900,
                    env={**os.environ, "LEAN_NUM_THREADS": "1"},
                    check=False,
                )
                chunked_output = chunked.stdout + chunked.stderr
                if chunked.returncode != 0:
                    return f"axiom-audit-chunked[{index}]", chunked.returncode, chunked_output
                try:
                    _validate_chunked_axioms_output(chunked_output, target)
                except ValueError as exc:
                    return f"axiom-audit-chunked[{index}]", 1, f"{exc}\n{chunked_output}"
            return None
        try:
            _validate_print_axioms_output(output, targets)
        except ValueError as exc:
            return "axiom-audit", 1, f"{exc}\n{output}"
        return None
    finally:
        audit_path.unlink(missing_ok=True)


def _stage_closed_bundle(bundle: dict[str, bytes], out_dir: str | Path) -> Path:
    """Materialize a private same-filesystem candidate without publishing it."""
    destination = Path(os.path.abspath(os.fspath(out_dir)))
    parent = destination.parent
    parent.mkdir(parents=True, exist_ok=True)
    if destination.is_symlink():
        raise ValueError(f"closed bundle destination may not be a symlink: {destination}")
    for relative, payload in bundle.items():
        path = Path(relative)
        if path.is_absolute() or len(path.parts) != 1 or path.name in {"", ".", ".."}:
            raise ValueError(f"invalid closed bundle path: {relative!r}")
        if not isinstance(payload, bytes):
            raise TypeError(f"closed bundle payload must be bytes: {relative}")
    staged = parent / f".{destination.name}.staged-{secrets.token_hex(16)}"
    try:
        staged.mkdir(mode=0o700)
        for relative, payload in bundle.items():
            target = staged / relative
            fd = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o400)
            try:
                offset = 0
                while offset < len(payload):
                    offset += os.write(fd, payload[offset:])
                os.fsync(fd)
            finally:
                os.close(fd)
        staged_fd = os.open(staged, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            os.fsync(staged_fd)
        finally:
            os.close(staged_fd)
        return staged
    except BaseException:
        if staged.exists():
            shutil.rmtree(staged)
        raise


def _publish_staged_closed_bundle(
    staged: Path,
    out_dir: str | Path,
    *,
    parent_fd: Optional[int] = None,
) -> None:
    """Atomically publish one already-checked private candidate directory."""
    destination = Path(os.path.abspath(os.fspath(out_dir)))
    parent = destination.parent
    staged = Path(os.path.abspath(os.fspath(staged)))
    if staged.parent != parent or staged.is_symlink() or not staged.is_dir():
        raise ValueError("closed bundle stage must be a real sibling directory")
    if destination.is_symlink():
        raise ValueError(f"closed bundle destination may not be a symlink: {destination}")
    if destination.exists() and not destination.is_dir():
        raise ValueError(
            f"closed bundle destination must be a real directory: {destination}"
        )
    staged_identity = (staged.stat().st_dev, staged.stat().st_ino)
    exchanged = False
    retired_identity: Optional[tuple[int, int]] = None
    owns_parent_fd = parent_fd is None
    if parent_fd is None:
        parent_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    else:
        held = os.fstat(parent_fd)
        observed_parent = os.stat(parent, follow_symlinks=False)
        if (held.st_dev, held.st_ino) != (
            observed_parent.st_dev, observed_parent.st_ino
        ):
            raise ValueError("held publication lock does not belong to destination parent")
    try:
        if owns_parent_fd:
            fcntl.flock(parent_fd, fcntl.LOCK_EX)
        current = os.stat(staged.name, dir_fd=parent_fd, follow_symlinks=False)
        if (current.st_dev, current.st_ino) != staged_identity:
            raise RuntimeError("closed bundle stage identity changed before publication")
        if destination.exists():
            retired = os.stat(
                destination.name, dir_fd=parent_fd, follow_symlinks=False
            )
            retired_identity = (retired.st_dev, retired.st_ino)
            result = _RENAMEAT2(
                parent_fd, os.fsencode(staged.name),
                parent_fd, os.fsencode(destination.name), 2,
            )
            if result != 0:
                error = ctypes.get_errno()
                raise OSError(error, os.strerror(error), destination.name)
            exchanged = True
        else:
            os.rename(
                staged.name, destination.name,
                src_dir_fd=parent_fd, dst_dir_fd=parent_fd,
            )
        os.fsync(parent_fd)
        if exchanged and retired_identity is not None:
            retired_now = os.stat(
                staged.name, dir_fd=parent_fd, follow_symlinks=False
            )
            if (retired_now.st_dev, retired_now.st_ino) == retired_identity:
                try:
                    shutil.rmtree(staged)
                except OSError:
                    # Publication already committed atomically.  Preserve an
                    # unretired predecessor rather than misreporting failure
                    # and deleting the new snapshot's matching objects.
                    pass
    finally:
        if owns_parent_fd:
            os.close(parent_fd)


def _publish_closed_bundle(bundle: dict[str, bytes], out_dir: str | Path) -> None:
    """Publish a bundle without a kernel gate (used only by explicit no-compile flows)."""
    staged = _stage_closed_bundle(bundle, out_dir)
    try:
        _publish_staged_closed_bundle(staged, out_dir)
    finally:
        if staged.exists():
            shutil.rmtree(staged)


def _remove_closed_bundle_objects(
    bundle: dict[str, bytes], module_prefix: str, project_dir: str | Path
) -> None:
    module_root = (
        Path(project_dir) / ".lake" / "build" / "lib" / "lean"
    ).joinpath(*module_prefix.split("."))
    for relative in bundle:
        object_path = module_root / Path(relative).with_suffix(".olean")
        if object_path.is_symlink() or not object_path.is_file():
            continue
        object_path.chmod(0o600)
        object_path.unlink()


def _compile_and_publish_closed_bundle(
    bundle: dict[str, bytes],
    out_dir: str | Path,
    module_prefix: str,
    *,
    project_dir: str | Path = TV,
    axiom_targets: tuple[str, ...] = (),
) -> tuple[str, int, str] | None:
    """Kernel-check exact private bytes, then atomically publish that directory."""
    staged = _stage_closed_bundle(bundle, out_dir)
    published = False
    try:
        failure = _compile_closed_bundle_sources(
            bundle, staged, module_prefix, project_dir=project_dir
        )
        if failure is not None:
            return failure
        failure = _audit_closed_bundle_axioms(
            staged, module_prefix, axiom_targets, project_dir=project_dir
        )
        if failure is not None:
            return failure
        _publish_staged_closed_bundle(staged, out_dir)
        published = True
        return None
    finally:
        if not published:
            _remove_closed_bundle_objects(bundle, module_prefix, project_dir)
        if staged.exists():
            shutil.rmtree(staged)

def _compile_and_publish_whole_model_catalog(
    artifact_root: str | Path, *, project_dir: str | Path = TV,
) -> tuple[str, int, str] | None:
    root = Path(artifact_root)
    bundle = _build_whole_model_catalog_bundle(root)
    destination = root / "Catalog"
    staged = _stage_closed_bundle(bundle, destination)
    lean_bundle = {
        name: payload for name, payload in bundle.items()
        if name.endswith(".lean")
    }
    published = False
    try:
        failure = _compile_closed_bundle_sources(
            lean_bundle,
            staged,
            "denote.WholeModels",
            project_dir=project_dir,
            compile_project_dependencies=False,
        )
        if failure is not None:
            return failure
        for model in json.loads(bundle["Manifest.json"])["models"]:
            failure = _audit_closed_bundle_axioms(
                staged,
                "denote.WholeModels",
                (model["catalog_theorem"],),
                project_dir=project_dir,
                imported_module=model["catalog_module"],
            )
            if failure is not None:
                return failure
        _publish_staged_closed_bundle(staged, destination)
        published = True
        published_bundle = {
            path.name: path.read_bytes()
            for path in destination.iterdir()
            if path.is_file()
        }
        if published_bundle != bundle:
            return "catalog-readback", 1, "whole-model catalog publication mismatch"
        return None
    finally:
        if not published:
            _remove_closed_bundle_objects(lean_bundle, "denote.WholeModels", project_dir)
        if staged.exists():
            shutil.rmtree(staged)


def _compile_whole_model_snapshot_models(
    artifact_root: str | Path, *, project_dir: str | Path = TV
) -> tuple[str, int, str] | None:
    """Rebuild and audit every model from the exact private snapshot sources."""
    root = Path(artifact_root)
    for model_id, spec in SUPPORTED_WHOLE_MODEL_ARTIFACTS.items():
        publication = root.joinpath(*spec["module_prefix"].split("."))
        if publication.is_symlink() or not publication.is_dir():
            return model_id, 1, f"missing whole-model publication: {model_id}"
        files = sorted(publication.rglob("*.lean"))
        if not files or any(path.is_symlink() for path in files):
            return model_id, 1, f"invalid whole-model source inventory: {model_id}"
        by_module = {
            f"{spec['module_prefix']}.{path.relative_to(publication).with_suffix('').as_posix().replace('/', '.')}": path
            for path in files
        }
        internal_prefix = f"{spec['module_prefix']}."
        for source_path in by_module.values():
            source = source_path.read_text(encoding="utf-8")
            for match in re.finditer(
                r"(?m)^\s*import\s+(.+?)(?:\s+--.*)?$", source
            ):
                for dependency in match.group(1).split():
                    if dependency.startswith(internal_prefix) and dependency not in by_module:
                        return (
                            model_id,
                            1,
                            f"missing internal whole-model source: {dependency}",
                        )
        ordered: list[Path] = []
        visiting: set[str] = set()
        visited: set[str] = set()

        def visit(module: str) -> None:
            if module in visited:
                return
            if module in visiting:
                raise ValueError(f"cyclic whole-model source imports: {module}")
            visiting.add(module)
            source = by_module[module].read_text(encoding="utf-8")
            for match in re.finditer(
                r"(?m)^\s*import\s+(.+?)(?:\s+--.*)?$", source
            ):
                for dependency in match.group(1).split():
                    if dependency in by_module:
                        visit(dependency)
            visiting.remove(module)
            visited.add(module)
            ordered.append(by_module[module])

        for module in sorted(by_module):
            visit(module)
        bundle = {
            path.relative_to(publication).as_posix(): path.read_bytes()
            for path in ordered
        }
        failure = _compile_closed_bundle_sources(
            bundle, publication, spec["module_prefix"], project_dir=project_dir
        )
        if failure is not None:
            return failure
        theorem = f"TrainVerify.Denote.{spec['namespace']}.{spec['aggregate_theorem']}"
        failure = _audit_closed_bundle_axioms(
            publication,
            spec["module_prefix"],
            (theorem,),
            project_dir=project_dir,
        )
        if failure is not None:
            return failure
    return None


def _remove_whole_model_snapshot_objects(
    artifact_root: str | Path, *, project_dir: str | Path = TV
) -> None:
    root = Path(artifact_root)
    for spec in SUPPORTED_WHOLE_MODEL_ARTIFACTS.values():
        publication = root.joinpath(*spec["module_prefix"].split("."))
        if not publication.is_dir() or publication.is_symlink():
            continue
        bundle = {
            path.relative_to(publication).as_posix(): b""
            for path in publication.rglob("*.lean")
            if path.is_file() and not path.is_symlink()
        }
        _remove_closed_bundle_objects(bundle, spec["module_prefix"], project_dir)


def _compile_and_publish_canonical_whole_model(
    bundle: dict[str, bytes],
    model_id: str,
    module_prefix: str,
    *,
    project_dir: str | Path = TV,
    axiom_targets: tuple[str, ...] = (),
) -> tuple[str, int, str] | None:
    """Validate model and catalog privately, then publish one enclosing snapshot."""
    project = Path(project_dir)
    root = whole_model_artifact_root(project)
    root.parent.mkdir(parents=True, exist_ok=True)
    transaction_parent_fd = os.open(
        root.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    )
    staged: Optional[Path] = None
    published = False
    catalog_bundle: dict[str, bytes] = {}
    try:
        fcntl.flock(transaction_parent_fd, fcntl.LOCK_EX)
        if root.is_symlink() or (root.exists() and not root.is_dir()):
            raise ValueError("whole-model artifact root must be a real directory")
        staged = Path(
            tempfile.mkdtemp(prefix=".whole-models.staged-", dir=root.parent)
        )
        if root.exists():
            if any(path.is_symlink() for path in root.rglob("*")):
                raise ValueError("whole-model artifact snapshot contains a symlink")
            shutil.copytree(root, staged, dirs_exist_ok=True)
        model_relative = whole_model_artifact_path(model_id, project).relative_to(root)
        model_destination = staged / model_relative
        if model_destination.exists():
            shutil.rmtree(model_destination)
        model_stage = _stage_closed_bundle(bundle, model_destination)
        try:
            _publish_staged_closed_bundle(model_stage, model_destination)
        finally:
            if model_stage.exists():
                shutil.rmtree(model_stage)
        failure = _compile_whole_model_snapshot_models(
            staged, project_dir=project
        )
        if failure is not None:
            return failure
        failure = _compile_and_publish_whole_model_catalog(staged, project_dir=project)
        if failure is not None:
            return failure
        catalog_bundle = {
            path.name: path.read_bytes()
            for path in (staged / "Catalog").glob("*.lean")
            if path.is_file()
        }
        _publish_staged_closed_bundle(
            staged, root, parent_fd=transaction_parent_fd
        )
        published = True
        return None
    finally:
        try:
            if not published and staged is not None:
                _remove_whole_model_snapshot_objects(staged, project_dir=project)
                if catalog_bundle:
                    lean_catalog = {
                        name: payload for name, payload in catalog_bundle.items()
                        if name.endswith(".lean")
                    }
                    _remove_closed_bundle_objects(
                        lean_catalog, "denote.WholeModels", project
                    )
            if not published and staged is not None and staged.exists():
                shutil.rmtree(staged)
        finally:
            os.close(transaction_parent_fd)


# Auto-detect pm.numRanks from generated-data file and expose via BRIDGE_PM_NUMRANKS
# env var BEFORE importing renderer_uni (which reads it at module load).
from trainverify.bridge_emitter.parser import GEN_DIR as _GD_INIT
_gd_path_init = os.path.join(REPO, _GD_INIT, GEN_FILE)
try:
    _gd_text_init = open(_gd_path_init).read()
    _pm_m_init = re.search(r'def\s+pm\s*:\s*GraphDecl.*?numRanks\s*:=\s*(\d+)', _gd_text_init, re.S)
    if _pm_m_init and "BRIDGE_PM_NUMRANKS" not in os.environ:
        os.environ["BRIDGE_PM_NUMRANKS"] = _pm_m_init.group(1)
except Exception:
    pass
from trainverify.bridge_emitter import renderer_uni as RU
from trainverify.bridge_emitter.proof_compiler import (
    ProofPlanningError,
    build_default_registry,
    require_supported_plan,
)
from trainverify.bridge_emitter.composer import (
    compose_closed_dependent_bundle,
    compose_full_topology,
    compose_shared_closed_bundle,
)
from trainverify.bridge_emitter.model_authority import load_model_authority
from trainverify.bridge_emitter.model_compiler import (
    compile_shared_proof_dag,
    compile_shared_relation_dag,
)
from trainverify.bridge_emitter.relation_compiler import compile_relation_plan

# parse #eval probe output, capturing ALL writer indices per tid (take max = last writer)
LINE_RE = re.compile(r'(SM|PM):(\d+)\s+\[(.*?)\]\s*$', re.M)
TUP_RE = re.compile(r'\(\s*(\d+),\s*\(\s*(?:OpName\.)?([A-Za-z0-9_]+),\s*'
                    r'\(\s*\[([0-9,\s]*)\]\s*,\s*\[([0-9,\s]*)\]')


def parse_probe_last(raw: str):
    res = {"sm": {}, "pm": {}}
    # group lines by side:tid since a tid may have multiple writer tuples
    for m in re.finditer(r'(SM|PM):(\d+)\s+\[', raw):
        side = m.group(1); tid = int(m.group(2))
        # capture the bracketed list following this marker
        start = m.end() - 1
        depth = 0; i = start
        while i < len(raw):
            if raw[i] == '[':
                depth += 1
            elif raw[i] == ']':
                depth -= 1
                if depth == 0:
                    break
            i += 1
        body = raw[start:i+1]
        best = None
        writers = []
        for t in TUP_RE.finditer(body):
            idx = int(t.group(1)); op = t.group(2)
            params = [int(x) for x in re.findall(r'\d+', t.group(4))] or None
            writers.append({"node_idx": idx, "op": op, "params": params})
            if best is None or idx > best[0]:
                best = (idx, op, params)
        if best is not None:
            key = "sm" if side == "SM" else "pm"
            # `best` = max-index writer (the in-place collective when a tid is written
            # twice). `writers` keeps ALL writer tuples so the in-place producer (the
            # earlier, non-collective writer of the same tid) can be recovered.
            res[key][tid] = {"node_idx": best[0], "op": best[1], "params": best[2],
                             "writers": writers}
    return res


def run_probe_all(imports, sm_tids, pm_tids, timeout=900, multi_out=False):
    from trainverify.bridge_emitter.probe import _eval_line
    # The probe only evaluates `denoteGraph sm/pm` over the GLOBAL graphs (provided by
    # GeneratedData via BridgeKit) — it never references prereq-bridge theorems. So we
    # drop any prereq-bridge import whose .olean has not been built; otherwise a single
    # un-built (or un-buildable, e.g. ordering-blocked) sibling bridge would make the
    # probe file fail to elaborate. Base infra imports are kept verbatim.
    def _has_olean(mod):
        if not mod.endswith("Bridge"):
            return True
        rel = mod.replace(".", "/") + ".olean"
        return os.path.exists(os.path.join(TV, ".lake/build/lib/lean", rel))
    imports = [m for m in imports if _has_olean(m)]
    header = ("\n".join(f"import {m}" for m in imports) + "\n"
              "set_option maxRecDepth 100000\n"
              "set_option maxHeartbeats 500000\n"
              "namespace TrainVerify.Denote.GeneratedGoals\n"
              "open TrainVerify.Denote TrainVerify.Denote.Generated\n")
    # For multi-output nodes (e.g. FW_multiref outs=[t1,t2], FW_inner_chunk_ce
    # outs=[fst, snd], FW_topk_routing outs=[scores, map, probs]) an exact
    # `o = [t]` match fails; use membership `t ∈ o` unconditionally so a node is
    # found by ANY of its outputs. The old exact-match path had no known
    # correctness advantage — kept only via `BRIDGE_PROBE_EXACT_MATCH=1` opt-out.
    _exact = os.environ.get("BRIDGE_PROBE_EXACT_MATCH", "0") == "1"
    if _exact and not multi_out:
        pat = lambda t: f"o = [{t}]"
    else:
        pat = lambda t: f"{t} ∈ o"
    lines = [header]
    for t in sm_tids:
        lines.append(_eval_line("sm", pat(t), f'"SM:{t}"'))
    for t in pm_tids:
        lines.append(_eval_line("pm", pat(t), f'"PM:{t}"'))
    lines.append("end TrainVerify.Denote.GeneratedGoals")
    src = "\n".join(lines)
    p = os.path.join(TV, DENOTE_DIR, "ProbeAuto.lean")
    with open(p, "w") as f:
        f.write(src)
    try:
        out = subprocess.run(["lake", "env", "lean", f"{DENOTE_DIR}/ProbeAuto.lean"],
                             cwd=TV, capture_output=True, text=True, timeout=timeout)
        raw = out.stdout + "\n" + out.stderr
        parsed = parse_probe_last(raw)
        parsed["_returncode"] = out.returncode
        parsed["_raw"] = raw
        return parsed
    finally:
        if os.path.exists(p):
            os.remove(p)


def _build_whole_model_bundle(
    target_ids: tuple[int, ...],
    *,
    model_id: str,
    namespace: str,
    module_prefix: str,
    aggregate_theorem_name: str,
    root: str = REPO,
) -> dict[str, bytes]:
    """Compile the one strict whole-model authority into one closed bundle."""
    model = load_model_authority(
        target_ids, root, model_id=model_id, allow_partial=False
    )
    proof = compile_shared_proof_dag(model, build_default_registry())
    relation = compile_shared_relation_dag(model, proof)
    bundle = compose_shared_closed_bundle(
        model,
        relation,
        namespace,
        module_prefix,
        aggregate_theorem_name=aggregate_theorem_name,
    )
    if "Main.lean" not in bundle:
        raise ValueError("whole-model production bundle must contain Main.lean")
    return bundle


def _parse_target_inventory(raw: str) -> tuple[int, ...]:
    ids: list[int] = []
    for token in raw.split(","):
        token = token.strip()
        if not token:
            raise ValueError("target inventory contains an empty item")
        if "-" in token:
            bounds = token.split("-")
            if len(bounds) != 2 or not all(item.isdigit() for item in bounds):
                raise ValueError(f"invalid target range: {token!r}")
            start, stop = (int(item) for item in bounds)
            if start <= 0 or stop < start:
                raise ValueError(f"invalid target range: {token!r}")
            ids.extend(range(start, stop + 1))
        elif token.isdigit() and int(token) > 0:
            ids.append(int(token))
        else:
            raise ValueError(f"invalid target ID: {token!r}")
    if not ids or len(ids) != len(set(ids)):
        raise ValueError("target inventory must be nonempty and contain unique IDs")
    return tuple(ids)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int, nargs="?")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--no-compile", action="store_true")
    ap.add_argument("--out", default=None)
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--closed-bundle", action="store_true")
    ap.add_argument("--whole-model", action="store_true")
    ap.add_argument("--targets")
    ap.add_argument("--model-id")
    ap.add_argument("--namespace")
    ap.add_argument("--aggregate-theorem")
    ap.add_argument("--module-prefix", default=None)
    args = ap.parse_args()
    log = (lambda *a: None) if args.quiet else print

    if args.whole_model:
        required = {
            "--targets": args.targets,
            "--model-id": args.model_id,
            "--namespace": args.namespace,
            "--module-prefix": args.module_prefix,
            "--aggregate-theorem": args.aggregate_theorem,
        }
        missing = [name for name, value in required.items() if not value]
        if args.n is not None or args.closed_bundle or missing:
            detail = f"; missing {', '.join(missing)}" if missing else ""
            ap.error(
                "--whole-model excludes positional n/--closed-bundle and requires "
                "explicit authority fields" + detail
            )
        try:
            targets = _parse_target_inventory(args.targets)
            canonical_output = False
            if args.out is None:
                try:
                    spec = SUPPORTED_WHOLE_MODEL_ARTIFACTS[args.model_id]
                except KeyError as exc:
                    raise ValueError(
                        "--out is required for an unsupported whole-model artifact"
                    ) from exc
                supplied = (
                    targets, args.namespace, args.module_prefix, args.aggregate_theorem,
                )
                expected = (
                    spec["targets"], spec["namespace"], spec["module_prefix"],
                    spec["aggregate_theorem"],
                )
                if supplied != expected:
                    raise ValueError(
                        f"canonical {args.model_id} authority fields do not match registry"
                    )
                args.out = str(whole_model_artifact_path(args.model_id, TV))
                canonical_output = True
            else:
                requested_output = Path(args.out).resolve()
                canonical_root = whole_model_artifact_root(TV).resolve()
                if requested_output.is_relative_to(canonical_root):
                    try:
                        spec = SUPPORTED_WHOLE_MODEL_ARTIFACTS[args.model_id]
                    except KeyError as exc:
                        raise ValueError(
                            "unsupported model may not publish inside canonical artifact root"
                        ) from exc
                    supplied = (
                        targets, args.namespace, args.module_prefix,
                        args.aggregate_theorem,
                    )
                    expected = (
                        spec["targets"], spec["namespace"], spec["module_prefix"],
                        spec["aggregate_theorem"],
                    )
                    expected_output = whole_model_artifact_path(
                        args.model_id, TV
                    ).resolve()
                    if requested_output != expected_output or supplied != expected:
                        raise ValueError(
                            "canonical whole-model output does not match registry authority"
                        )
                    canonical_output = True
            bundle = _build_whole_model_bundle(
                targets,
                model_id=args.model_id,
                namespace=args.namespace,
                module_prefix=args.module_prefix,
                aggregate_theorem_name=args.aggregate_theorem,
                root=REPO,
            )
        except (OSError, TypeError, ValueError) as exc:
            log("[whole-model] render_complete=false kernel_checked=false proof_complete=false")
            log(f"  FAIL {exc}")
            sys.exit(1)
        if args.dry_run:
            log(json.dumps({
                "model_id": args.model_id,
                "targets": targets,
                "module_prefix": args.module_prefix,
                "paths": list(bundle),
                "bytes": {path: len(payload) for path, payload in bundle.items()},
                "render_complete": True,
                "kernel_checked": False,
                "proof_complete": False,
            }, sort_keys=True))
            return
        if args.no_compile and canonical_output:
            log(
                "[whole-model] render_complete=true published=false "
                "kernel_checked=false proof_complete=false"
            )
            log("  FAIL canonical whole-model publication requires kernel and axiom checks")
            sys.exit(1)
        if args.no_compile:
            _publish_closed_bundle(bundle, args.out)
            log(
                f"[whole-model] render_complete=true published=true "
                f"kernel_checked=false proof_complete=false targets={len(targets)} "
                f"modules={len(bundle)} wrote={args.out}"
            )
            return
        axiom_targets = (
            f"TrainVerify.Denote.{args.namespace}.{args.aggregate_theorem}",
        )
        if canonical_output:
            failure = _compile_and_publish_canonical_whole_model(
                bundle,
                args.model_id,
                args.module_prefix,
                project_dir=TV,
                axiom_targets=axiom_targets,
            )
        else:
            failure = _compile_and_publish_closed_bundle(
                bundle,
                args.out,
                args.module_prefix,
                project_dir=TV,
                axiom_targets=axiom_targets,
            )
        if failure is not None:
            relative, returncode, output = failure
            log(
                f"[whole-model] render_complete=true published=false "
                f"kernel_checked=false proof_complete=false "
                f"first_blocker={relative} exit={returncode}"
            )
            log(output[-2500:])
            sys.exit(1)
        log(
            f"[whole-model] render_complete=true published=true kernel_checked=true "
            f"proof_complete=true catalog_published={str(canonical_output).lower()} "
            f"targets={len(targets)} modules={len(bundle)} "
            f"wrote={args.out}"
        )
        return

    if args.n is None:
        ap.error("positional n is required unless --whole-model is used")
    n = args.n

    ir = load_goal_ir(n, REPO)
    try:
        proof_plan = require_supported_plan(ir, build_default_registry())
    except ProofPlanningError as exc:
        raise RU.UnsupportedTopology(str(exc)) from None
    if args.closed_bundle:
        relation = compile_relation_plan(ir, proof_plan)
        namespace = os.environ.get("BRIDGE_NAMESPACE", f"ClosedGoal{n}")
        module_prefix = args.module_prefix or f"{MOD_PREFIX}.Goal{n}Closed"
        try:
            bundle = compose_closed_dependent_bundle(
                ir, relation, namespace, module_prefix
            )
        except ValueError as exc:
            log(f"[g{n}] render_complete=false kernel_checked=false proof_complete=false")
            log(f"  FAIL {exc}")
            sys.exit(1)
        out_dir = args.out or os.path.join(TV, DENOTE, f"Goal{n}Closed")
        if args.dry_run:
            log(json.dumps({
                "goal_id": n,
                "module_prefix": module_prefix,
                "paths": list(bundle),
                "bytes": {path: len(payload) for path, payload in bundle.items()},
                "render_complete": True,
                "kernel_checked": False,
                "proof_complete": False,
            }, sort_keys=True))
            return
        if args.no_compile:
            try:
                _publish_closed_bundle(bundle, out_dir)
            except (OSError, TypeError, ValueError) as exc:
                log(f"[g{n}] render_complete=true published=false kernel_checked=false proof_complete=false")
                log(f"  FAIL {exc}")
                sys.exit(1)
            log(
                f"[g{n}] render_complete=true published=true kernel_checked=false "
                f"proof_complete=false modules={len(bundle)} wrote={out_dir}"
            )
            return
        try:
            failure = _compile_and_publish_closed_bundle(
                bundle,
                out_dir,
                module_prefix,
                project_dir=TV,
                axiom_targets=(
                    f"TrainVerify.Denote.{namespace}.prove_goal_{n}_closed",
                ),
            )
        except (OSError, TypeError, ValueError) as exc:
            log(f"[g{n}] render_complete=true published=false kernel_checked=false proof_complete=false")
            log(f"  FAIL {exc}")
            sys.exit(1)
        if failure is not None:
            relative, returncode, output = failure
            log(
                f"[g{n}] render_complete=true published=false kernel_checked=false "
                f"proof_complete=false first_blocker={relative} exit={returncode}"
            )
            log(output[-2500:])
            sys.exit(1)
        log(
            f"[g{n}] render_complete=true published=true kernel_checked=true "
            f"proof_complete=true modules={len(bundle)} wrote={out_dir}"
        )
        return

    composition = compose_full_topology(ir, MOD_PREFIX)
    if composition.supported:
        text = composition.lean_source
        out_path = args.out or os.path.join(TV, DENOTE, f"Goal{n}Compiled.lean")
        if args.dry_run:
            log(text)
            return
        def check_candidate(stage: Path, candidate_fd: int) -> None:
            compiled = subprocess.run(
                ["lake", "env", "lean", "--tstack=65536", str(stage)],
                cwd=TV,
                capture_output=True,
                text=True,
                timeout=900,
                env={**os.environ, "LEAN_NUM_THREADS": "1"},
                pass_fds=(candidate_fd,),
            )
            output = compiled.stdout + compiled.stderr
            if compiled.returncode != 0 or "sorry" in output.lower():
                raise RuntimeError(
                    f"Lean rejected candidate (exit={compiled.returncode})\n{output[-2500:]}"
                )

        try:
            _publish_composed_source(
                text,
                out_path,
                None if args.no_compile else check_candidate,
            )
        except (OSError, subprocess.SubprocessError, RuntimeError) as exc:
            log(f"  FAIL {exc}")
            sys.exit(1)
        log(
            f"[g{n}] composed rule={composition.rule_id} "
            f"plan_steps={len(proof_plan.steps)} wrote={out_path}"
        )
        if not args.no_compile:
            log("  OK exit=0")
        return
    topo = analyze(ir)
    log(f"[g{n}] single_tp={topo.single_tp} mid={len(topo.mid_tids)} finals={len(topo.final_tps)} "
        f"smop={ir.sm_nodes[0].op} plan_steps={len(proof_plan.steps)}")

    input_sources, missing = trace_input_sources(ir)
    if missing:
        log(f"  WARNING unresolved inputs: {missing}")

    imports = compute_imports(ir.prereqs)
    imports.append(f"{MOD_PREFIX}.Goal_{n}")
    # NOTE (prereq-trim 2026-06-21): we used to ALSO union-in the ORIGINAL bridge's
    # imports for regression robustness. That is now HARMFUL: the renderer body only
    # references `goal_M_intermediate` for M in ir.prereqs (the *trimmed* prereq set),
    # so compute_imports(ir.prereqs) already lists exactly the GoalNBridge imports the
    # body needs. Unioning the stale original imports perpetuates the old fat (~264)
    # import list and defeats the whole DAG-trim. We therefore only union NON-bridge
    # imports from the original (rare base-infra a handwritten original may have had);
    # any `GoalNBridge` import the body doesn't reference is intentionally dropped.
    orig = os.path.join(TV, DENOTE, f"Goal{n}Bridge.lean")
    if os.path.exists(orig):
        orig_imports = [l.split(None, 1)[1].strip()
                        for l in open(orig) if l.startswith("import ")]
        seen = set(imports)
        for m in orig_imports:
            # skip GoalNBridge imports: those must come from compute_imports(ir.prereqs)
            if re.match(rf"{re.escape(MOD_PREFIX)}\.Goal\d+Bridge$", m):
                continue
            if m not in seen:
                imports.append(m); seen.add(m)

    # The universal renderer always emits sm_val/pm_val/initGoals_preserved/...
    # which live in BridgeKit; storeShapes_weaken lives in SpikeBridge. Guarantee
    # both are imported no matter which import-building path ran above (handwritten
    # originals predate BridgeKit and don't import it).
    kits = [f"{MOD_PREFIX}.BridgeKit"]
    if os.path.exists(os.path.join(TV, DENOTE, "SpikeBridge.lean")):
        kits.append(f"{MOD_PREFIX}.SpikeBridge")
    # BRIDGE_EXTRA_IMPORTS: comma-separated module names always prepended to
    # imports. Use this to pull in a target-specific `Pattern_N.lean` (e.g. yoco
    # keeps `prove_goal_N` in `denote.yoco_goals.Pattern_N` instead of the
    # gpt_ly4 convention where `prove_goal_N_cut` lives in the Goal file).
    _extra_imports = os.environ.get("BRIDGE_EXTRA_IMPORTS", "").strip()
    if _extra_imports:
        for m in [x.strip() for x in _extra_imports.split(",") if x.strip()]:
            if m not in kits:
                kits.append(m)
    for kit in kits:
        if kit not in imports:
            imports.insert(0, kit)

    # Keep every prereq-bridge import whose bridge SOURCE (.lean) exists. We build in
    # strict topological order, so a prereq bridge's .olean is guaranteed present by the
    # time this downstream goal is compiled. (The earlier worker dropped imports lacking
    # an .olean to survive UNORDERED validation, but that produces a broken bridge: the
    # proof body still references `goal_K_intermediate`, so dropping the import => an
    # unknown-identifier error. With ordered builds we must KEEP the import.)
    def _bridge_src_exists(mod):
        if not mod.endswith("Bridge"):
            return True
        rel = mod.replace(".", "/") + ".lean"
        return os.path.exists(os.path.join(TV, rel))
    imports = [m for m in imports if _bridge_src_exists(m)]

    # probe ALL pm node outs + sm out (one tid per node; dedupe)
    # Family-aware tid selection: the multiref-2-second family's goal finals are the
    # SECOND outputs of each multiref node (SM final = lineage.ts; PM finals =
    # topo.final_tps), NOT outs[0]. Probing outs[0] (the throwaway first output)
    # fails to resolve. Pick the tids the renderer will actually frame.
    # Multi-output backward goals (BW_linear/matmul/add/layernorm): the SM/PM nodes
    # are multi-output, and the goal frames the projection at bw_idx = position of
    # lineage.ts among the SM node's outs. Probe each node's FRAMED output (outs[idx]
    # for BW nodes, outs[0] otherwise) using membership matching.
    _bw_sm = ir.sm_nodes[0] if ir.sm_nodes else None
    _is_bw_multi_goal = (_bw_sm is not None and RU.is_bw_multi(_bw_sm.op)
                         and ir.lineage.ts in _bw_sm.outs
                         and not (RU.is_multiref2_second(ir, topo)
                                  or RU.is_multirefN_nth(ir, topo)
                                  or RU.is_multiref_first_collective(ir, topo)))
    if RU.is_multiref2_second(ir, topo) or RU.is_multirefN_nth(ir, topo):
        sm_tids = [ir.lineage.ts]
        pm_tids = sorted(set(topo.final_tps))
    elif RU.is_multiref_first_collective(ir, topo):
        # Family B: SM final = i-th output (lineage.ts); PM tids = multiref-i-th-out
        # MIDs (outs[idx]) + collective finals (outs[0]). Multiref nodes are multi-
        # output so membership matching is required (multi_out=True).
        num_out, midx = RU._mref_mid_index(ir, topo)
        sm_tids = [ir.lineage.ts]
        mid_set = set(topo.mid_tids)
        final_set = set(topo.final_tps)
        pm_tids = sorted(
            {nd.outs[midx] for nd in ir.pm_nodes
             if nd.op == "FW_multiref" and nd.outs[midx] in mid_set}
            | {nd.outs[0] for nd in ir.pm_nodes if nd.outs[0] in final_set})
    elif _is_bw_multi_goal:
        bw_idx = _bw_sm.outs.index(ir.lineage.ts)
        sm_tids = [ir.lineage.ts]
        def _lout(nd):
            return nd.outs[bw_idx] if RU.is_bw_multi(nd.op) else nd.outs[0]
        # Probe every node's framed output AND its first output. The first output is
        # needed for in-place collectives (CROSS_DP_WRED): the collective's output tid
        # equals a per-rank BW node's framed output, so the framed tid resolves (via
        # `parse_probe_last`, highest-index-wins) to the COLLECTIVE node, hiding the
        # per-rank producer. Probing the producer's distinct outs[0] recovers its index.
        pm_tids = sorted({_lout(nd) for nd in ir.pm_nodes}
                         | {nd.outs[0] for nd in ir.pm_nodes})
    else:
        sm_tids = [nd.outs[0] for nd in ir.sm_nodes]
        pm_tids = sorted({nd.outs[0] for nd in ir.pm_nodes})
    log(f"  probing with {len(imports)} imports ...")
    _multi_out = (RU.is_multiref2_second(ir, topo) or RU.is_multirefN_nth(ir, topo)
                  or RU.is_multiref_first_collective(ir, topo) or _is_bw_multi_goal)
    probe = run_probe_all(imports, sm_tids, pm_tids, multi_out=_multi_out)
    if probe["_returncode"] != 0 or not probe["sm"]:
        log(f"  PROBE FAILED rc={probe['_returncode']}")
        log(probe.get("_raw", "")[-1500:])
        sys.exit(3)
    missing_idx = [t for t in pm_tids if t not in probe["pm"]] + [t for t in sm_tids if t not in probe["sm"]]
    if missing_idx:
        log(f"  PROBE missing indices for {missing_idx}")
        sys.exit(3)

    text = RU.render_universal(n, ir, topo, probe, input_sources, ir.prereqs, imports)
    # Apply BRIDGE_NAMESPACE / EXTRA_OPENS / PROVE_GOAL / PM_NUMRANKS substitutions.
    _ns = os.environ.get("BRIDGE_NAMESPACE", "GeneratedGoals")
    _extra = os.environ.get("BRIDGE_EXTRA_OPENS", "")
    _extra_str = (" " + _extra) if _extra else ""
    _prove_fmt = os.environ.get("BRIDGE_PROVE_GOAL_FMT", "prove_goal_{n}_cut")
    _prove_ref = _prove_fmt.format(n=n)
    # Auto-detect pm.numRanks from the generated-data file (parses `def pm : GraphDecl := by refine { numRanks := N, ... }`).
    from trainverify.bridge_emitter.parser import GEN_DIR
    from trainverify.bridge_emitter.target_config import GEN_FILE
    _gd_text = open(os.path.join(REPO, GEN_DIR, GEN_FILE)).read()
    _pm_nr_m = re.search(r'def\s+pm\s*:\s*GraphDecl.*?numRanks\s*:=\s*(\d+)', _gd_text, re.S)
    _pm_nr = _pm_nr_m.group(1) if _pm_nr_m else os.environ.get("BRIDGE_PM_NUMRANKS", "4")
    text = (text
            .replace("@@BRIDGE_NAMESPACE@@", _ns)
            .replace("@@EXTRA_OPENS@@", _extra_str)
            .replace(f"@@PROVE_GOAL_{n}@@", _prove_ref)
            .replace("@@PM_NUMRANKS@@", _pm_nr))
    out_path = args.out or os.path.join(TV, DENOTE, f"Goal{n}Bridge.lean")
    if args.dry_run:
        log(text)
        return
    with open(out_path, "w") as f:
        f.write(text)
    log(f"  wrote {out_path} ({len(text)} chars)")

    if args.no_compile:
        return
    r = subprocess.run(["lake", "env", "lean", f"{DENOTE}/Goal{n}Bridge.lean"],
                       cwd=TV, capture_output=True, text=True, timeout=900)
    ok = r.returncode == 0 and "sorry" not in (r.stdout + r.stderr).lower()
    log(("  OK" if ok else "  FAIL") + f" exit={r.returncode}")
    if not ok:
        log((r.stdout + r.stderr)[-2500:])
        sys.exit(1)


if __name__ == "__main__":
    main()
