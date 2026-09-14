#  Copyright (c) Microsoft Corporation.
#  Licensed under the MIT License.

"""Inspect trusted local SM/PM graphs; this entry does not verify equivalence."""

import argparse
from pathlib import Path
import sys


def _parser():
    parser = argparse.ArgumentParser(
        description="Graph inspection of trusted local SM/PM pickle captures; not verification.",
        allow_abbrev=False,
    )
    parser.add_argument("--sm", required=True, help="trusted single-model capture file")
    parser.add_argument("--pm", required=True, help="trusted parallel-model capture file")
    parser.add_argument("--cache_dir", required=True, help="private external cache directory")
    parser.add_argument("--log_dir", required=True, help="private external log directory")
    parser.add_argument("--max_ser_proc", type=int, help="positive graph-serialization worker count")
    parser.add_argument("--loglevel", choices=("DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"))
    parser.add_argument("--seed", type=int, help="backend preparation random seed")
    parser.add_argument("--time", action="store_true", default=None, help="enable backend timing")
    cache = parser.add_mutually_exclusive_group()
    cache.add_argument("--use_cache_nodes", action="store_true", default=None,
                       help="write serialized graph caches in the fresh private cache directory")
    cache.add_argument("--no_cache_nodes", dest="use_cache_nodes", action="store_false")
    return parser


def _validate(args):
    # Parse all options before filesystem checks or optional backend imports.
    for name in ("sm", "pm", "cache_dir", "log_dir"):
        if not getattr(args, name).strip():
            raise ValueError(f"--{name} must not be empty")
    if args.max_ser_proc is not None and args.max_ser_proc < 1:
        raise ValueError("--max_ser_proc must be positive")
    source = Path(__file__).resolve().parent.parent
    for name in ("sm", "pm"):
        path = Path(getattr(args, name)).resolve()
        if not path.is_file():
            raise ValueError(f"--{name} must name an existing capture file: {path}")
        # Both backend cache layers use the resolved capture stem as a directory.
        if path.stem in {"", ".", ".."}:
            raise ValueError(f"--{name} capture stem must be a normal cache component: {path.name}")
        setattr(args, name, path)
    protected = (source, args.sm.parent, args.pm.parent)
    for name in ("cache_dir", "log_dir"):
        path = Path(getattr(args, name))
        if not path.is_absolute():
            raise ValueError(f"--{name} must be an absolute private path")
        path = path.resolve()
        if any(path.is_relative_to(p) or p.is_relative_to(path) for p in protected):
            raise ValueError(f"--{name} must be outside source and capture directories")
        if path.exists() and (not path.is_dir() or any(path.iterdir())):
            raise ValueError(f"--{name} must be a fresh or empty private directory")
        setattr(args, name, path)
    if args.cache_dir.is_relative_to(args.log_dir) or args.log_dir.is_relative_to(args.cache_dir):
        raise ValueError("--cache_dir and --log_dir must not overlap")


def _inspect(args):
    # Legacy backend imports need these roots, never the caller's working directory.
    root = Path(__file__).resolve().parent
    for path in (root, root.parent, root.parent / "genmodel"):
        if str(path) not in sys.path:
            sys.path.insert(0, str(path))

    from verdict.config import Config

    for name in ("cache_dir", "log_dir", "max_ser_proc", "loglevel", "seed", "time", "use_cache_nodes"):
        value = getattr(args, name)
        if value is not None:
            setattr(Config, name, value)

    import logging
    import z3
    from verdict.log import setup_logger, loginfo
    from verdict.timer import timer
    from verdict.verifier import StageParallelVerifier
    from nnscaler_backend import nnScalerGraphBackend
    from z3_backend import z3Backend

    Config.cache_dir.mkdir(parents=True, exist_ok=True)
    Config.log_dir.mkdir(parents=True, exist_ok=True)
    setup_logger(Config.loglevel)
    handler = logging.FileHandler(Config.log_dir / "inspection.log", mode="x", encoding="utf-8")
    handler.setFormatter(logging.Formatter("%(levelname)s: %(message)s"))
    logging.getLogger().addHandler(handler)
    z3.set_param("smt.random_seed", Config.seed)
    z3.set_param("memory_max_size", 0)
    sys.setrecursionlimit(10000)
    try:
        timer.start("graph inspection")
        loginfo("Start graph inspection (not verification).")
        verifier = StageParallelVerifier(
            Gs_path=args.sm, Ws_path=None, Gp_path=args.pm, Wp_path=None,
            graph_backend=nnScalerGraphBackend, symbolic_backend=z3Backend,
        )
        single, parallel = verifier.get_graph()
        print("Graph inspection — Single-model graph:")
        for node in single.nodes():
            print(single.node_opname(node), single.node_kwargs(node))
            print("Input shapes:")
            for tensor in single.node_inputs(node):
                print(single.tensor_shape(tensor))
            print("Output shapes:")
            for tensor in single.node_outputs(node):
                print(single.tensor_shape(tensor))
        timer.end("graph inspection")
        timer.display(print_fn=loginfo)
    finally:
        logging.getLogger().removeHandler(handler)
        handler.close()


def cli(argv=None):
    parser = _parser()
    args = parser.parse_args(argv)
    try:
        _validate(args)
    except (ValueError, OSError) as exc:
        parser.error(str(exc))
    try:
        _inspect(args)
    except Exception as exc:
        print(f"Graph inspection failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(cli())
