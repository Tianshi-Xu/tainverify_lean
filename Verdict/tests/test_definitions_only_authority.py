"""CPU-only producer authority regressions; no capture or Lean execution."""
import re
import subprocess
import sys
import types
from pathlib import Path

import pytest

import Verdict.graph_to_lean as exporter
from Verdict.tests.test_graph_to_lean_lineage import Graph, Node, Tensor


class EmissionGraph(Graph):
    def tensors(self):
        return list({t.tid: t for n in self.nodes() for t in (*n.ins, *n.outs)}.values())

    def is_initialized(self, tensor):
        return all(tensor not in n.outs for n in self.nodes())


def fixture_kwargs(out, sm_count=1):
    sm = EmissionGraph([
        Node("OpName.FW_sum", (Tensor(i + 1, (1,)),), (Tensor(i + 2, (1,)),))
        for i in range(sm_count)
    ])
    pm = EmissionGraph([
        Node("OpName.FW_sum", (Tensor(10, (1,)),), (Tensor(20, (1,)),)),
        Node("OpName.FW_sum", (Tensor(11, (1,)),), (Tensor(21, (1,)),), rank=1),
        Node("OpName.FW_sum", (Tensor(20, (1,)),), (Tensor(22, (1,)),)),
    ])
    return dict(out_path=out, spec_out_path=None, emit_spec_template=False,
                overwrite_spec=False, module_name="FreshGPT.GeneratedData",
                sm_nodes=sm.nodes(), pm_nodes=pm.nodes(), sm_graph=sm, pm_graph=pm,
                sm_logical_ids={}, pm_logical_ids={}, sm_input_value_classes=[],
                pm_input_value_classes=[],
                init_goals=[exporter.SelectedLineage(ts=1, tps=[(0, 10), (1, 11)])],
                goals=[exporter.SelectedLineage(ts=sm_count + 1, tps=[(0, 20), (1, 21)])],
                intermediate_lineages={1: exporter.SelectedLineage(ts=1, tps=[(0, 10)])})


def emit(module, out, **options):
    kwargs = fixture_kwargs(out, options.pop("sm_count", 1))
    kwargs.update(options)
    module.emit_lean_spec(**kwargs)
    return {p.name: p.read_bytes() for p in out.parent.glob("*.lean")}


def definitions(payload):
    # Capture each complete declaration body, including tactic-style definitions.
    return re.findall(rb"^def [^\n]+(?:\n[ \t]+[^\n]*)*", payload, re.MULTILINE)


def test_definitions_only_keeps_ordered_definition_bytes(tmp_path, monkeypatch):
    root = Path(exporter.__file__).resolve().parents[1]
    source = subprocess.check_output(
        ["git", "-C", str(root), "show", "38366919:Verdict/graph_to_lean.py"], text=True)
    baseline = types.ModuleType("definitions_only_baseline")
    baseline.__file__ = exporter.__file__
    monkeypatch.setitem(sys.modules, baseline.__name__, baseline)
    exec(compile(source, exporter.__file__, "exec"), baseline.__dict__)
    expected = emit(baseline, tmp_path / "baseline" / "GeneratedData.lean")
    assert emit(exporter, tmp_path / "default" / "GeneratedData.lean") == expected
    actual = emit(exporter, tmp_path / "authority" / "GeneratedData.lean", definitions_only=True)
    data = actual["GeneratedData.lean"]
    assert definitions(data) == definitions(expected["GeneratedData.lean"])
    assert actual["GeneratedGraphNodes.lean"] == expected["GeneratedGraphNodes.lean"]
    assert b"import FreshGPT.GeneratedGraphNodes" in data
    for name in (b"smShapeCheck", b"pmShapeCheck", b"pm_prefix_goal_2", b"pm_suffix_goal_2",
                 b"goal_1_stmt", b"all_goals_stmt", b"intermediateGoal_1_stmt"):
        assert b"def " + name + b" :" in data
    assert not re.search(rb"^\s*(?:(?:private|protected)\s+)*(?:theorem|lemma|example)\b", data, re.MULTILINE)
    exporter._validate_generated_authority_tree(tmp_path / "authority")
    assert emit(exporter, tmp_path / "disabled" / "GeneratedData.lean", definitions_only=False) == expected


@pytest.mark.parametrize("kind", ["old", "legacy", "partial", "empty"])
def test_existing_tree_refused_before_generation_publish_or_cleanup(tmp_path, monkeypatch, kind):
    out = tmp_path / "authority" / "GeneratedData.lean"
    if kind == "empty":
        out.parent.mkdir()
    else:
        emit(exporter, out, definitions_only=kind != "legacy")
        if kind == "partial":
            out.unlink()
    before = {p.name: p.read_bytes() for p in out.parent.iterdir()}

    def forbidden(*args, **kwargs):
        pytest.fail("generation, publisher or cleanup reached for existing destination")

    monkeypatch.setattr(exporter, "_atomic_publish_generated_directory", forbidden)
    monkeypatch.setattr(exporter.shutil, "rmtree", forbidden)
    monkeypatch.setattr(exporter.tempfile, "TemporaryDirectory", forbidden)
    monkeypatch.setattr(exporter, "_validate_generated_authority_tree", forbidden)
    with pytest.raises(ValueError, match="fresh.*directory"):
        emit(exporter, out, definitions_only=True, sm_count=2)
    assert {p.name: p.read_bytes() for p in out.parent.iterdir()} == before
    assert set(tmp_path.iterdir()) == {out.parent}


def test_fresh_rename_failure_cleans_private_stage(tmp_path, monkeypatch):
    out = tmp_path / "authority" / "GeneratedData.lean"
    seen = []

    def fail_rename(*args):
        seen.append(args)
        raise OSError("injected publish failure")

    monkeypatch.setattr(exporter.os, "replace", fail_rename)
    with pytest.raises(OSError, match="injected publish failure"):
        emit(exporter, out, definitions_only=True, sm_count=2)
    assert len(seen) == 1
    assert not out.parent.exists()
    assert set(tmp_path.iterdir()) == set()


def test_fresh_publication_publishes_coherent_private_pair(tmp_path, monkeypatch):
    out = tmp_path / "authority" / "GeneratedData.lean"
    expected = emit(exporter, tmp_path / "expected" / out.name,
                    definitions_only=True, sm_count=2)
    publish = exporter._atomic_publish_generated_directory
    seen = []

    def check(staged, target):
        assert staged.parent == target.parent == tmp_path
        assert staged.stat().st_dev == target.parent.stat().st_dev
        assert staged.stat().st_mode & 0o777 == 0o700
        assert {p.name: p.read_bytes() for p in staged.iterdir()} == expected
        assert not target.exists()
        seen.append(staged)
        publish(staged, target)

    monkeypatch.setattr(exporter, "_atomic_publish_generated_directory", check)
    assert emit(exporter, out, definitions_only=True, sm_count=2) == expected
    assert len(seen) == 1 and not seen[0].exists()
    assert set(tmp_path.iterdir()) == {out.parent, tmp_path / "expected"}


@pytest.mark.parametrize("entrypoint", ["main", "_generate"])
@pytest.mark.parametrize("kind", ["directory", "symlink", "dangling"])
def test_entrypoints_refuse_existing_target_before_generation(tmp_path, monkeypatch, entrypoint, kind):
    target = tmp_path / "authority"
    if kind == "directory":
        target.mkdir()
    else:
        target.symlink_to(tmp_path if kind == "symlink" else tmp_path / "missing",
                          target_is_directory=True)
    monkeypatch.setattr(sys, "argv", ["graph_to_lean.py", "--out", str(target / "GeneratedData.lean"),
        "--module", "FreshGPT.GeneratedData", "--definitions-only"])
    monkeypatch.setattr(exporter, "load_verifier", lambda *a: pytest.fail("verifier loaded"))
    if entrypoint == "main":
        monkeypatch.setattr(exporter, "_generate", lambda *a: pytest.fail("generation started"))
        run = exporter.main
    else:
        run = lambda: exporter._generate(exporter.parse_args())
    with pytest.raises(ValueError, match="fresh.*directory"):
        run()
    assert set(tmp_path.iterdir()) == {target}


@pytest.mark.parametrize("entry", ["unrelated.lean", "notes.txt", "nested", "node-symlink",
                                  "data-symlink", "target-symlink", "target-file"])
def test_rejects_shared_or_symlink_destination_without_mutation(tmp_path, entry):
    out = tmp_path / "authority" / "GeneratedData.lean"
    outside = tmp_path / "outside"
    outside.mkdir()
    sentinel = outside / "sentinel"
    sentinel.write_bytes(b"unrelated bytes")
    if entry == "target-symlink":
        out.parent.symlink_to(outside, target_is_directory=True)
    elif entry == "target-file":
        out.parent.write_bytes(b"not a directory")
    else:
        emit(exporter, out, definitions_only=True)
        if entry in {"node-symlink", "data-symlink"}:
            member = out if entry == "data-symlink" else out.with_name("GeneratedGraphNodes.lean")
            member.unlink()
            member.symlink_to(sentinel)
        elif entry == "nested":
            (out.parent / entry).mkdir()
            (out.parent / entry / "sentinel").write_bytes(b"keep nested")
        else:
            (out.parent / entry).write_bytes(b"keep sibling")

    def snapshot():
        return {str(p.relative_to(tmp_path)): ("link", str(p.readlink())) if p.is_symlink()
                else ("dir",) if p.is_dir() else ("file", p.read_bytes())
                for p in tmp_path.rglob("*")}

    before = snapshot()
    with pytest.raises(ValueError, match="dedicated|symlink|directory"):
        emit(exporter, out, definitions_only=True, sm_count=2)
    assert snapshot() == before


def test_shared_node_helper_without_small_sm_unfold(tmp_path):
    actual = emit(exporter, tmp_path / "fresh" / "GeneratedData.lean", definitions_only=True, sm_count=25)
    assert b"def pm_prefix_goal_26 : GraphDecl := by" in actual["GeneratedData.lean"]
    assert b"theorem " not in actual["GeneratedData.lean"]


@pytest.mark.parametrize("options", [
    {"emit_spec_template": True}, {"goal_slices": []},
    {"goals_out_dir": Path("unused")}, {"emit_segment_patterns": True},
])
def test_api_conflicts_before_destination_writes(tmp_path, options):
    out = tmp_path / "destination" / "GeneratedData.lean"
    with pytest.raises(ValueError, match="definitions.only"):
        emit(exporter, out, definitions_only=True, **options)
    assert list(tmp_path.iterdir()) == []


@pytest.mark.parametrize("flag", ["--emit-spec-template", "--split-goals", "--emit-segment-patterns"])
def test_cli_conflicts_before_generation(monkeypatch, tmp_path, flag):
    monkeypatch.setattr(sys, "argv", ["graph_to_lean.py", "--out", str(tmp_path / "out.lean"),
        "--module", "FreshGPT.GeneratedData", "--definitions-only", flag])
    monkeypatch.setattr(exporter, "_generate", lambda args: pytest.fail("generation started"))
    with pytest.raises(ValueError, match="definitions-only"):
        exporter.main()
    assert list(tmp_path.iterdir()) == []


def test_cli_flag_and_generate_propagation(monkeypatch):
    import ast
    import inspect
    argv = ["graph_to_lean.py", "--out", "unused.lean", "--module", "FreshGPT.GeneratedData"]
    monkeypatch.setattr(sys, "argv", argv)
    assert exporter.parse_args().definitions_only is False
    monkeypatch.setattr(sys, "argv", argv + ["--definitions-only"])
    args = exporter.parse_args()
    assert args.definitions_only is True
    tree = ast.parse(inspect.getsource(exporter._generate))
    calls = [n for n in ast.walk(tree) if isinstance(n, ast.Call)
             and isinstance(n.func, ast.Name) and n.func.id == "emit_lean_spec"]
    kw = next(k for k in calls[0].keywords if k.arg == "definitions_only")
    assert eval(compile(ast.Expression(kw.value), "<flag>", "eval"), {"args": args}) is True


@pytest.mark.parametrize("existing", [False, True])
def test_scanner_rejection_preserves_destination(tmp_path, existing):
    out = tmp_path / "destination" / "GeneratedData.lean"
    nodes = out.with_name("GeneratedGraphNodes.lean")
    if existing:
        out.parent.mkdir()
        out.write_bytes(b"existing data")
        nodes.write_bytes(b"existing nodes")
    # A forbidden token in retained data must be rejected, not stripped.
    with pytest.raises(ValueError, match="fresh.*directory" if existing else "forbidden sorry"):
        emit(exporter, out, definitions_only=True, manifest_name="sorry")
    if existing:
        assert out.read_bytes() == b"existing data"
        assert nodes.read_bytes() == b"existing nodes"
    else:
        assert not out.parent.exists()


def test_scanner_runs_on_complete_private_tree(monkeypatch, tmp_path):
    out = tmp_path / "destination" / "GeneratedData.lean"
    scanner = exporter._validate_generated_authority_tree
    calls = []

    def check(root):
        assert not out.parent.exists()
        assert {p.name for p in root.iterdir()} == {"GeneratedData.lean", "GeneratedGraphNodes.lean"}
        scanner(root)
        calls.append(root)

    monkeypatch.setattr(exporter, "_validate_generated_authority_tree", check)
    emit(exporter, out, definitions_only=True)
    assert len(calls) == 1
    assert not calls[0].exists()
