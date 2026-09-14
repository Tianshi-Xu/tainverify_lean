"""Graph-inspection CLI only; import blockers are boundary spies, not loaders."""
import ast
import importlib.util
import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
ENTRY = ROOT / "Verdict/main.py"


def run_python(args, cwd, tmp_path):
    env = {**os.environ, "PYTHONDONTWRITEBYTECODE": "1"}
    env.pop("PYTHONPATH", None)
    result = subprocess.run([sys.executable, *args], cwd=cwd, env=env,
                            text=True, capture_output=True, timeout=90)
    (tmp_path / "stdout.txt").write_text(result.stdout)
    (tmp_path / "stderr.txt").write_text(result.stderr)
    (tmp_path / "exit.txt").write_text(str(result.returncode))
    return result


@pytest.mark.parametrize("mode", ["module", "script"])
def test_help_without_pythonpath(mode, tmp_path):
    args = ["-m", "Verdict.main"] if mode == "module" else [str(ENTRY)]
    result = run_python([*args, "--help"], ROOT if mode == "module" else tmp_path, tmp_path)
    assert result.returncode == 0, result.stderr
    assert "graph inspection" in result.stdout.lower()
    for flag in ("--sm", "--pm", "--cache_dir", "--log_dir"):
        assert flag in result.stdout


@pytest.mark.parametrize("args", [None, [], ["--sm", "missing"], ["--pm", "missing"], ["--help"],
    ["--sm", "missing", "--pm", "missing", "--cache_dir", "cache"],
    ["--sm", "missing", "--pm", "missing", "--log_dir", "logs"],
    ["--sm", "missing", "--pm", "missing", "--cache_dir", "cache", "--log_dir", "logs", "--unknown"],
    ["--sm", "", "--pm", "missing", "--cache_dir", "cache", "--log_dir", "logs"]],
    ids=["import", "default", "missing-pm", "missing-sm", "help", "missing-log", "missing-cache", "unknown", "empty-sm"])
def test_preflight_has_no_backend_or_io(args, tmp_path):
    # Boundary spies: block optional imports and application filesystem access
    # after the entry is discoverable; this does not simulate any graph data.
    code = f'''
import argparse, importlib.util, pathlib, sys, warnings, builtins, os
before_path = sys.path[:]
before_warnings = warnings.filters[:]
def reject_application_writes(event, args):
    if event in ('os.mkdir', 'os.remove', 'os.rename'):
        raise AssertionError('import-time application write: ' + event)
    if event == 'open' and args[2] & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND):
        raise AssertionError('import-time application file write')
sys.addaudithook(reject_application_writes)
class BlockOptional:
    def find_spec(self, fullname, *args):
        if fullname.split('.')[0] in {{'z3', 'nnscaler', 'verdict', 'nnscaler_backend', 'z3_backend'}}:
            raise AssertionError('optional import: ' + fullname)
sys.meta_path.insert(0, BlockOptional())
spec = importlib.util.spec_from_file_location('inspection_entry', {str(ENTRY)!r})
entry = importlib.util.module_from_spec(spec)
spec.loader.exec_module(entry)
assert sys.path == before_path
assert warnings.filters == before_warnings
def forbidden(*a, **kw):
    raise AssertionError('application filesystem access')
builtins.open = forbidden
for name in ('open', 'stat', 'resolve', 'mkdir', 'exists', 'is_file'):
    setattr(pathlib.Path, name, forbidden)
args = {args!r}
if args is not None:
    try:
        status = entry.cli(args)
    except SystemExit as exc:
        status = exc.code
    assert status == (0 if args == ['--help'] else 2), status
assert sys.path == before_path
assert warnings.filters == before_warnings
'''
    result = run_python(["-c", code], tmp_path, tmp_path)
    assert result.returncode == 0, result.stderr


def entry_module():
    spec = importlib.util.spec_from_file_location("inspection_entry", ENTRY)
    entry = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(entry)
    return entry


def arguments(tmp_path):
    captures = tmp_path / "captures"
    captures.mkdir()
    for name in ("sm.pkl", "pm.pkl"):
        (captures / name).write_bytes(b"not a capture: validation only")
    return ["--sm", str(captures / "sm.pkl"), "--pm", str(captures / "pm.pkl"),
            "--cache_dir", str(tmp_path / "cache"), "--log_dir", str(tmp_path / "logs")]


@pytest.mark.parametrize("case", ["empty-sm", "absent-pm", "directory-sm", "source-cache",
    "input-log", "shared-output", "nonempty-cache", "relative-cache", "symlink-source",
    "missing-cache", "missing-log", "unknown", "inactive-stats", "zero-workers", "bad-loglevel"])
def test_invalid_arguments_reject_before_loading(case, tmp_path, monkeypatch, capsys):
    entry = entry_module()
    args = arguments(tmp_path)
    if case == "empty-sm": args[1] = ""
    elif case == "absent-pm": args[3] += ".absent"
    elif case == "directory-sm": args[1] = str(tmp_path / "captures")
    elif case == "source-cache": args[5] = str(ROOT / "must-not-create")
    elif case == "input-log": args[7] = str(tmp_path / "captures" / "logs")
    elif case == "shared-output": args[7] = args[5]
    elif case == "nonempty-cache":
        Path(args[5]).mkdir()
        (Path(args[5]) / "accepted-sentinel").write_text("unchanged")
    elif case == "relative-cache": args[5] = "relative-cache"
    elif case == "symlink-source":
        (tmp_path / "source-link").symlink_to(ROOT, target_is_directory=True)
        args[5] = str(tmp_path / "source-link" / "must-not-create")
    elif case == "missing-cache": del args[4:6]
    elif case == "missing-log": del args[6:8]
    elif case == "unknown": args += ["--unknown-option"]
    elif case == "inactive-stats": args += ["--stats_dir", str(tmp_path / "stats")]
    elif case == "zero-workers": args += ["--max_ser_proc", "0"]
    elif case == "bad-loglevel": args += ["--loglevel", "nonsense"]
    # Narrow load-boundary spy, never a synthetic graph result.
    def forbidden(*a, **kw):
        pytest.fail("loading reached before validation")
    monkeypatch.setattr(entry, "_inspect", forbidden)
    before = sorted(str(p.relative_to(tmp_path)) for p in tmp_path.rglob("*"))
    with pytest.raises(SystemExit) as exc:
        entry.cli(args)
    assert exc.value.code == 2
    assert "error:" in capsys.readouterr().err
    assert sorted(str(p.relative_to(tmp_path)) for p in tmp_path.rglob("*")) == before


@pytest.mark.parametrize("side", ("sm", "pm"))
@pytest.mark.parametrize("filename", ("..pkl", "...pkl"))
def test_capture_cache_stem_rejects_before_loading(side, filename, tmp_path, monkeypatch, capsys):
    entry = entry_module()
    args = arguments(tmp_path)
    capture = tmp_path / "captures" / filename
    capture.write_bytes(b"preflight only: never deserialize")
    args[args.index(f"--{side}") + 1] = str(capture)
    sibling = tmp_path / "cells" / "r0.pkl"
    sibling.parent.mkdir()
    sibling.write_bytes(b"existing sibling cache must survive")
    calls = []
    monkeypatch.setattr(entry, "_inspect", lambda parsed: calls.append(parsed))
    before = sorted(str(p.relative_to(tmp_path)) for p in tmp_path.rglob("*"))
    with pytest.raises(SystemExit) as exc:
        entry.cli(args)
    assert exc.value.code == 2
    assert "cache component" in capsys.readouterr().err
    assert not calls
    assert sibling.read_bytes() == b"existing sibling cache must survive"
    assert sorted(str(p.relative_to(tmp_path)) for p in tmp_path.rglob("*")) == before


def test_config_routing_boundary_spy(tmp_path, monkeypatch):
    entry = entry_module()
    args = arguments(tmp_path)
    observed = []
    # Only argument routing is isolated; no backend or loaded graph is invented.
    monkeypatch.setattr(entry, "_inspect", lambda parsed: observed.append(vars(parsed)))
    assert entry.cli(args + ["--max_ser_proc", "1", "--loglevel", "WARNING",
                            "--seed", "7", "--time", "--use_cache_nodes"]) == 0
    assert observed == [dict(sm=Path(args[1]), pm=Path(args[3]), cache_dir=Path(args[5]),
        log_dir=Path(args[7]), max_ser_proc=1, loglevel="WARNING", seed=7,
        time=True, use_cache_nodes=True)]


def test_exception_exit_status_boundary_spy(tmp_path, monkeypatch, capsys):
    entry = entry_module()
    def fail(args):
        raise RuntimeError("isolated loading failure")
    monkeypatch.setattr(entry, "_inspect", fail)
    assert entry.cli(arguments(tmp_path)) == 1
    assert "Graph inspection failed: isolated loading failure" in capsys.readouterr().err


def test_no_verification_or_dead_stats_scaffold():
    tree = ast.parse(ENTRY.read_text())
    assert not any(isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                   and n.func.attr == "launch" for n in ast.walk(tree))
    assert not {n.name for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)} & {
        "main_w_stats", "dump_stats"}


# A real, locally constructed nnScaler IR fixture, not a traced model capture.
# No fake ModuleCodeGen, DFG, load_graph, Pool, or get_graph implementation.
FIXTURE_CODE = '''
import json, pickle, torch
from pathlib import Path
from nnscaler.ir.tensor import IRFullTensor
from nnscaler.graph.function import Sigmoid
from nnscaler.graph import IRGraph
from nnscaler.execplan import ExecutionPlan
from nnscaler.codegen.module.module import ModuleCodeGen
x = IRFullTensor((2, 3), name="input", dtype=torch.float32).tosub()
op = Sigmoid(x)
op.set_output(0, IRFullTensor((2, 3), name="output", dtype=torch.float32).tosub())
op.device = (0,)
graph = IRGraph([op], [x], [op.output(0)], "inspection_fixture")
mg = ModuleCodeGen(ExecutionPlan(graph, [op]), runtime_ndevs=1)
p = Path("captures")
p.mkdir()
for name in ("sm", "pm"):
    (p / (name + ".pkl")).write_bytes(pickle.dumps(mg))
    (p / (name + ".json")).write_text(json.dumps(dict(
        model_name="inspection_fixture", num_dp=1, num_tp=1, num_pp=1,
        num_mb=1, gbs=2, num_layers=1, num_heads=1, hidden_size=3, seqlen=1)))
'''


@pytest.mark.parametrize("cache_flag", ["--use_cache_nodes", "--no_cache_nodes"])
def test_real_minimal_graph_printing(cache_flag, tmp_path):
    build = tmp_path / "build-receipt"
    build.mkdir()
    result = run_python(["-c", FIXTURE_CODE], tmp_path, build)
    assert result.returncode == 0, result.stderr
    cache, logs = tmp_path / "cache", tmp_path / "logs"
    inputs_before = {p.name: p.read_bytes() for p in (tmp_path / "captures").iterdir()}
    result = run_python([str(ENTRY), "--sm", str(tmp_path / "captures/sm.pkl"),
        "--pm", str(tmp_path / "captures/pm.pkl"), "--cache_dir", str(cache),
        "--log_dir", str(logs), "--max_ser_proc", "1", "--loglevel", "INFO",
        "--seed", "7", "--time", cache_flag], tmp_path, tmp_path)
    assert result.returncode == 0, result.stderr
    assert "Graph inspection" in result.stdout
    assert "OpName.FW_sigmoid" in result.stdout
    assert "Input shapes:\n(2, 3)\nOutput shapes:\n(2, 3)" in result.stdout
    assert "Start verifying" not in result.stdout
    assert "SUCCESS" not in result.stdout
    assert (cache / "sm/cells/r0.pkl").is_file()
    assert (cache / "pm/cells/r0.pkl").is_file()
    assert (cache / "sm/snodes.pkl").exists() == (cache_flag == "--use_cache_nodes")
    assert (cache / "pm/pnodes.pkl").exists() == (cache_flag == "--use_cache_nodes")
    assert "graph inspection" in (logs / "inspection.log").read_text().lower()
    assert {p.name: p.read_bytes() for p in (tmp_path / "captures").iterdir()} == inputs_before


def test_real_invalid_pickle_has_nonzero_exit(tmp_path):
    args = arguments(tmp_path)
    result = run_python([str(ENTRY), *args], tmp_path, tmp_path)
    assert result.returncode == 1
    assert "Graph inspection failed:" in result.stderr
    assert "SUCCESS" not in result.stdout
