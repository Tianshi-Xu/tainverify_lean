from __future__ import annotations

import runpy
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "trainverify/scripts/generate_multiref_certificates.py"


def module() -> dict[str, Any]:
    return runpy.run_path(str(SCRIPT), run_name="multiref_generator_test")


def minimal_graph(node: str) -> list[str]:
    return [
        "def sm : GraphDecl := by",
        "  exact [",
        node,
        "  ]",
        "def pm : GraphDecl := by",
        "  exact [",
        "  ]",
    ]


def test_current_authority_parses_computed_multiref_outputs() -> None:
    api = module()
    text = Path(api["AUTHORITY"]).read_text()
    graphs = api["parse_graphs"](text.splitlines())
    matches = [
        node
        for nodes in graphs.values()
        for node in nodes
        if node is not None and node.outs == tuple(range(11853, 11865))
    ]
    assert len(matches) == 2
    assert all(node.op == "OpName.FW_multiref" for node in matches)


def test_unknown_rank_node_syntax_fails_closed() -> None:
    api = module()
    malformed = (
        '  { rank := 0, op := "OpName.FW_multiref", ins := dynamicInputs, '
        'outs := [2], params := [1] },'
    )
    with pytest.raises(ValueError, match="unparsed sm graph entry"):
        api["parse_graphs"](minimal_graph(malformed))


def test_duplicate_requested_goal_is_rejected() -> None:
    api = module()
    with pytest.raises(ValueError, match="duplicate --goals"):
        api["render"]((7747, 7747))


def test_duplicate_authority_goal_is_rejected() -> None:
    api = module()
    duplicated = """def intermediateGoal_7 : LineageGoal :=
  { ts := 11, tps := [{ rank := 0, tid := 21 }] }
def intermediateGoal_7 : LineageGoal :=
  { ts := 12, tps := [{ rank := 0, tid := 22 }] }
"""
    with pytest.raises(ValueError, match="duplicate intermediate goal 7"):
        api["parse_goals"](duplicated)


def test_atomic_write_guards_authority_and_symlinks(tmp_path: Path) -> None:
    api = module()
    with pytest.raises(ValueError, match="overwrite authority"):
        api["write_atomic"](Path(api["AUTHORITY"]), "bad")

    target = tmp_path / "generated.lean"
    target.write_text("old")
    link = tmp_path / "link.lean"
    link.symlink_to(target)
    with pytest.raises(ValueError, match="symlink output"):
        api["write_atomic"](link, "bad")
    assert target.read_text() == "old"

    api["write_atomic"](target, "new")
    assert target.read_text() == "new"


def test_cli_defaults_to_check_and_requires_write(tmp_path: Path) -> None:
    output = tmp_path / "certificates.lean"
    checked = subprocess.run(
        [sys.executable, str(SCRIPT), "--output", str(output)],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    assert checked.returncode != 0
    assert not output.exists()

    written = subprocess.run(
        [sys.executable, str(SCRIPT), "--write", "--output", str(output)],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    assert written.returncode == 0, written.stderr
    assert output.exists()
