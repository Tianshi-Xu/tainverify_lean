#!/usr/bin/env python3
"""Inspect a ModuleCodeGen artifact without invoking Verdict."""
from __future__ import annotations

import argparse
import collections
import json
import sys
from pathlib import Path


STUBS = Path(__file__).resolve().parent / "stubs"


def configure_imports(llm_train: Path, nnscaler_repo: Path):
    import os

    os.environ["YOCO_LLM_TRAIN_REPO"] = str(llm_train.resolve())
    sys.path[:0] = [
        str(STUBS), str(nnscaler_repo.resolve()), str(llm_train.resolve() / "llm")]
    import triton_shim  # noqa: F401
    import nnscaler

    imported = Path(nnscaler.__file__).resolve()
    if not imported.is_relative_to(nnscaler_repo.resolve()):
        raise RuntimeError(f"imported nnScaler is outside pinned checkout: {imported}")


def _nodes(graph):
    nodes = graph.nodes() if callable(getattr(graph, "nodes", None)) else graph.nodes
    return list(nodes)


def _tid(value):
    return getattr(value, "tid", None)


def _shape(value):
    shape = getattr(value, "shape", None)
    return list(shape) if shape is not None else None


def inspect(path: Path):
    import dill

    sys.setrecursionlimit(100000)
    with path.open("rb") as handle:
        mgener = dill.load(handle)
    nodes = _nodes(mgener.execplan.graph)
    counts = collections.Counter(
        getattr(node, "signature", None) or type(node).__name__ for node in nodes
    )
    interesting = []
    needles = ("maybe_shuffle", "maybe_unshuffle", "stack")
    for index, node in enumerate(nodes):
        signature = getattr(node, "signature", None) or type(node).__name__
        if not any(needle in signature for needle in needles):
            continue
        inputs = node.inputs() if callable(getattr(node, "inputs", None)) else []
        outputs = node.outputs() if callable(getattr(node, "outputs", None)) else []
        interesting.append(
            {
                "index": index,
                "cid": getattr(node, "cid", None),
                "device": sorted(getattr(node, "device", [])),
                "signature": signature,
                "inputs": [
                    {"tid": _tid(value), "shape": _shape(value)} for value in inputs
                ],
                "outputs": [
                    {"tid": _tid(value), "shape": _shape(value)} for value in outputs
                ],
                "kwargs": {
                    str(key): repr(value)
                    for key, value in getattr(node, "kwargs", {}).items()
                },
            }
        )
    return {
        "path": str(path.resolve()),
        "devices": list(mgener.devices),
        "runtime_ndevs": mgener.runtime_ndevs,
        "node_count": len(nodes),
        "signature_counts": dict(sorted(counts.items())),
        "interesting_nodes": interesting,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pkl", type=Path)
    parser.add_argument("--llm-train", type=Path, required=True)
    parser.add_argument("--nnscaler", type=Path, required=True)
    parser.add_argument("--trust-local-pickle", action="store_true")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    if not args.trust_local_pickle:
        parser.error("--trust-local-pickle is required because dill input is executable")
    configure_imports(args.llm_train, args.nnscaler)
    report = inspect(args.pkl)
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.write_text(text, encoding="utf-8")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
