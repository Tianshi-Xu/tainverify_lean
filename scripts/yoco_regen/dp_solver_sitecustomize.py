"""Fail-closed startup guard for memfd-sealed nnScaler runtime bytes."""
from __future__ import annotations

import base64
import binascii
import copy
import fcntl
import hashlib
import importlib
import importlib.machinery
import importlib.util
import json
import math
import os
import queue
import re
import sys
import time
import traceback

_FULL_SEALS = (
    getattr(fcntl, "F_SEAL_SEAL", 0x0001)
    | getattr(fcntl, "F_SEAL_SHRINK", 0x0002)
    | getattr(fcntl, "F_SEAL_GROW", 0x0004)
    | getattr(fcntl, "F_SEAL_WRITE", 0x0008)
)
_PROC_FD = re.compile(r"^/proc/[1-9][0-9]*/fd/[0-9]+$")
_MODULE = "nnscaler.autodist.dp_solver"
_METRIC_KEYS = {
    "in_mem_info", "param_mem_info", "buffer_mem_info", "fw_span", "bw_span",
    "infer_memory", "train_mem_info", "train_mem2in_idx",
}
_ORIGINAL_PROFILE_GRAPH = None
_ORIGINAL_PROFILE_COMP = None


def _guarded_profile_graph(*args):
    result = args[-1]
    try:
        return _ORIGINAL_PROFILE_GRAPH(*args)
    except BaseException:
        result.put({"trainverify_error": traceback.format_exc()})
        raise


def _robust_profile_comp(
    self, partition_degree, parallel_profile, re_profile, exact_nodes=None,
):
    if not parallel_profile:
        return _ORIGINAL_PROFILE_COMP(
            self, partition_degree, parallel_profile, re_profile, exact_nodes,
        )
    import multiprocessing
    import torch
    from nnscaler.autodist import cost_database

    device_count = torch.cuda.device_count()
    if device_count < 1:
        raise RuntimeError("no CUDA devices available for computation profile workers")
    context = multiprocessing.get_context("spawn")
    results = context.Queue()
    processes = [
        context.Process(
            target=cost_database._profile_graph,
            args=(
                self.graph.dumps(), device, partition_degree, re_profile,
                self.comp_profile_path, results,
            ),
        )
        for device in range(device_count)
    ]
    succeeded = False
    started_processes = []
    try:
        for process in processes:
            process.start()
            started_processes.append(process)
        responses = []
        deadline = time.monotonic() + 1800
        while len(responses) < len(processes):
            try:
                response = results.get(timeout=1)
            except queue.Empty:
                failed = [
                    process for process in processes
                    if process.exitcode is not None and process.exitcode != 0
                ]
                if failed:
                    raise RuntimeError(
                        "computation profile worker exited without a result: "
                        + ",".join(str(process.exitcode) for process in failed)
                    )
                if time.monotonic() >= deadline:
                    raise TimeoutError("computation profile workers exceeded 1800 seconds")
                continue
            if isinstance(response, dict) and set(response) == {"trainverify_error"}:
                raise RuntimeError(
                    "computation profile worker failed:\n" + response["trainverify_error"]
                )
            if not isinstance(response, list):
                raise RuntimeError("computation profile worker returned an invalid envelope")
            responses.append(response)
        for process in processes:
            process.join(timeout=30)
            if process.exitcode != 0:
                raise RuntimeError(
                    f"computation profile worker exit code is {process.exitcode}"
                )
        for response in responses:
            for signature, serialized, metrics in response:
                self.db.insert(signature, serialized, metrics)
        if exact_nodes:
            response = cost_database._profile_exact_nodes(exact_nodes, self.db, re_profile)
            for signature, serialized, metrics in response:
                self.db.insert(signature, serialized, metrics)
        self.db.dump_ops(self.comp_profile_path, override=True)
        succeeded = True
    finally:
        try:
            if not succeeded:
                for process in started_processes:
                    if process.is_alive():
                        process.terminate()
            for process in started_processes:
                process.join(timeout=30)
                if process.is_alive():
                    process.kill()
                    process.join()
        finally:
            results.close()
            results.join_thread()


def _install_profile_worker_guard() -> None:
    global _ORIGINAL_PROFILE_GRAPH, _ORIGINAL_PROFILE_COMP
    from nnscaler.autodist import cost_database

    _ORIGINAL_PROFILE_GRAPH = cost_database._profile_graph
    _ORIGINAL_PROFILE_COMP = cost_database.CostDatabase.profile_comp
    cost_database._profile_graph = _guarded_profile_graph
    cost_database.CostDatabase.profile_comp = _robust_profile_comp


def _verify_sealed(path: str, expected_hash: str, *, elf: bool = False) -> bytes:
    if not _PROC_FD.fullmatch(path) or len(expected_hash) != 64:
        raise RuntimeError("invalid sealed runtime identity")
    descriptor = os.open(path, os.O_RDONLY)
    try:
        if fcntl.fcntl(descriptor, getattr(fcntl, "F_GET_SEALS", 1034)) != _FULL_SEALS:
            raise RuntimeError("runtime memfd is not fully sealed")
        digest = hashlib.sha256()
        content = bytearray()
        while chunk := os.read(descriptor, 1 << 20):
            digest.update(chunk)
            content.extend(chunk)
        result = bytes(content)
        if (elf and not result.startswith(b"\x7fELF")) or digest.hexdigest() != expected_hash:
            raise RuntimeError("sealed runtime content mismatch")
        return result
    finally:
        os.close(descriptor)


def _reject_constant(value: str):
    raise ValueError(f"non-finite constant: {value}")


def _reject_duplicate_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _strict_json(content: bytes):
    return json.loads(
        content.decode("utf-8"),
        object_pairs_hook=_reject_duplicate_pairs,
        parse_constant=_reject_constant,
    )


def _frozen_profile(artifact: bytes):
    envelope = _strict_json(artifact)
    if (
        not isinstance(envelope, dict)
        or set(envelope) != {"schema_version", "files"}
        or envelope["schema_version"] != 1
        or not isinstance(envelope["files"], list)
        or not envelope["files"]
    ):
        raise RuntimeError("sealed computation profile schema mismatch")
    from nnscaler.profiler.database import ProfiledMetrics

    database = {}
    canonical_files = []
    previous = None
    for record in envelope["files"]:
        if not isinstance(record, dict) or set(record) != {"name", "sha256", "content_base64"}:
            raise RuntimeError("sealed computation profile file schema mismatch")
        name = record["name"]
        expected = record["sha256"]
        encoded = record["content_base64"]
        if (
            not isinstance(name, str)
            or not name.endswith(".json")
            or "/" in name or "\\" in name
            or not isinstance(expected, str) or len(expected) != 64
            or any(char not in "0123456789abcdef" for char in expected)
            or not isinstance(encoded, str)
        ):
            raise RuntimeError("invalid sealed computation profile file record")
        order = name.encode("utf-8")
        if previous is not None and order <= previous:
            raise RuntimeError("sealed computation profile filenames are not sorted and unique")
        previous = order
        try:
            content = base64.b64decode(encoded, validate=True)
        except (ValueError, binascii.Error) as exc:
            raise RuntimeError("invalid sealed computation profile base64") from exc
        if hashlib.sha256(content).hexdigest() != expected:
            raise RuntimeError("sealed computation profile content hash mismatch")
        entries = _strict_json(content)
        if not isinstance(entries, dict) or not entries:
            raise RuntimeError("sealed computation profile operator file is empty")
        parsed = {}
        for serialized, metrics in entries.items():
            if not isinstance(serialized, str) or not serialized:
                raise RuntimeError("invalid sealed computation profile operation key")
            if not isinstance(metrics, dict) or set(metrics) != _METRIC_KEYS:
                raise RuntimeError("sealed computation profile metric schema mismatch")
            for field in ("in_mem_info", "param_mem_info", "buffer_mem_info", "train_mem_info"):
                if not isinstance(metrics[field], list) or any(
                    type(item) is not int or item < 0 for item in metrics[field]
                ):
                    raise RuntimeError("invalid sealed computation profile memory list")
            if not isinstance(metrics["train_mem2in_idx"], list) or any(
                type(item) is not int or item < -1
                for item in metrics["train_mem2in_idx"]
            ):
                raise RuntimeError("invalid sealed computation profile index list")
            if len(metrics["train_mem_info"]) != len(metrics["train_mem2in_idx"]):
                raise RuntimeError("sealed computation profile saved-tensor mismatch")
            if any(
                type(metrics[field]) not in (int, float)
                or not math.isfinite(metrics[field])
                or metrics[field] < 0
                for field in ("fw_span", "bw_span")
            ) or type(metrics["infer_memory"]) is not int or metrics["infer_memory"] < 0:
                raise RuntimeError("invalid sealed computation profile scalar")
            parsed[serialized] = ProfiledMetrics(**metrics)
        signature = name[:-5]
        if signature in database:
            raise RuntimeError("duplicate sealed computation profile signature")
        database[signature] = parsed
        canonical_files.append({
            "name": name,
            "sha256": expected,
            "content_base64": base64.b64encode(content).decode("ascii"),
        })
    canonical = (
        json.dumps(
            {"schema_version": 1, "files": canonical_files},
            sort_keys=True, separators=(",", ":"),
        ) + "\n"
    ).encode("utf-8")
    if canonical != artifact:
        raise RuntimeError("sealed computation profile artifact is not canonical")
    return database


def _install_frozen_profile(artifact: bytes) -> None:
    from nnscaler.profiler.database import ProfileDataBase

    frozen = _frozen_profile(artifact)

    def load_ops(self, _folder):
        self._data = copy.deepcopy(frozen)

    def profile(self, node, override=False):
        if not self.exist(node):
            raise RuntimeError(f"operation missing from sealed computation profile: {node.signature}")
        metrics = self.query(node)
        input_count = len(node.inputs())
        if any(index >= input_count for index in metrics.train_mem2in_idx):
            raise RuntimeError(
                f"sealed computation profile input index out of range: {node.signature}"
            )
        return metrics

    def dump_ops(self, _folder, override=False):
        if self._data != frozen:
            raise RuntimeError("sealed computation profile database mutated")

    ProfileDataBase.load_ops = load_ops
    ProfileDataBase.profile = profile
    ProfileDataBase.dump_ops = dump_ops


class _SolverFinder:
    def __init__(self, extension_path: str) -> None:
        self.extension_path = extension_path

    def find_spec(self, fullname: str, path=None, target=None):
        if fullname != _MODULE:
            return None
        loader = importlib.machinery.ExtensionFileLoader(fullname, self.extension_path)
        return importlib.util.spec_from_loader(fullname, loader)


try:
    extension_path = os.environ.get("TRAINVERIFY_DP_SOLVER_PATH", "")
    extension_hash = os.environ.get("TRAINVERIFY_DP_SOLVER_SHA256", "")
    runtime_path = os.environ.get("TRAINVERIFY_RUNTIME_ZIP_PATH", "")
    runtime_hash = os.environ.get("TRAINVERIFY_RUNTIME_ZIP_SHA256", "")
    _verify_sealed(runtime_path, runtime_hash)
    _verify_sealed(extension_path, extension_hash, elf=True)
    _install_profile_worker_guard()
    profile_path = os.environ.get("TRAINVERIFY_COMP_PROFILE_PATH", "")
    profile_hash = os.environ.get("TRAINVERIFY_COMP_PROFILE_SHA256", "")
    live_profile = os.environ.get("TRAINVERIFY_ALLOW_LIVE_COMP_PROFILE") == "1"
    if bool(profile_path) == live_profile:
        raise RuntimeError("sealed computation profile mode is ambiguous")
    if profile_path:
        _install_frozen_profile(_verify_sealed(profile_path, profile_hash))
    finder = _SolverFinder(extension_path)
    sys.meta_path.insert(0, finder)
    try:
        module = importlib.import_module(_MODULE)
    finally:
        sys.meta_path.remove(finder)
    if getattr(module, "__file__", None) != extension_path:
        raise RuntimeError(f"dp solver resolved outside sealed memfd: {module.__file__}")
except BaseException:
    traceback.print_exc()
    os._exit(126)
