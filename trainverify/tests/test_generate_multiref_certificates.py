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


def minimal_graph(*nodes: str) -> list[str]:
    return [
        "def sm : GraphDecl := by",
        "  exact [",
        *nodes,
        "  ]",
        "def pm : GraphDecl := by",
        "  exact [",
        "  ]",
    ]


def test_current_authority_preserves_computed_node_writes() -> None:
    api = module()
    text = Path(api["AUTHORITY"]).read_text()
    graphs = api["parse_graphs"](text.splitlines())
    multirefs = [
        node
        for nodes in graphs.values()
        for node in nodes
        if node.outs == tuple(range(11853, 11865))
    ]
    assert len(multirefs) == 2
    assert all(node.op == "OpName.FW_multiref" for node in multirefs)
    assert any(
        node.op == "OpName.FW_attn_zigzag" and node.outs == (5347,)
        for node in graphs["sm"]
    )


def test_unknown_and_malformed_node_syntax_fail_closed() -> None:
    api = module()
    unknown = (
        '  { rank := 0, op := "OpName.FW_multiref", ins := dynamicInputs, '
        'outs := [2], params := [1] },'
    )
    with pytest.raises(ValueError, match="unparsed sm graph entry"):
        api["parse_graphs"](minimal_graph(unknown))

    malformed = (
        '  { rank := 0, op := "OpName.FW_multiref", ins := [1,, 9], '
        'outs := [2], params := [1] },'
    )
    with pytest.raises(ValueError, match="malformed numeric list"):
        api["parse_graphs"](minimal_graph(malformed))


def test_computed_zigzag_write_counts_for_producer_uniqueness() -> None:
    api = module()
    multiref = (
        '  { rank := 0, op := "OpName.FW_multiref", ins := [1], '
        'outs := [2], params := [1] },'
    )
    zigzag = (
        '  { rank := 0, op := "OpName.FW_attn_zigzag", '
        'ins := ((List.range 5).map (fun r => 10 + r)), '
        'outs := [2], params := [16, 4, 64, 64, 1, 0] },'
    )
    graph = api["parse_graphs"](minimal_graph(multiref, zigzag))["sm"]
    with pytest.raises(ValueError, match="expected one producer, found 2"):
        api["producer"](graph, 2)


def test_duplicate_requested_goal_is_rejected() -> None:
    api = module()
    with pytest.raises(ValueError, match="duplicate --goals"):
        api["render"]((7747, 7747))


def test_duplicate_authority_goal_with_whitespace_is_rejected() -> None:
    api = module()
    duplicated = """def intermediateGoal_7 : LineageGoal :=
  { ts := 11, tps := [{ rank := 0, tid := 21 }] }
  def intermediateGoal_7 : LineageGoal :=
  { ts := 12, tps := [{ rank := 0, tid := 22 }] }
"""
    with pytest.raises(ValueError, match="duplicate intermediate goal 7"):
        api["parse_goals"](duplicated)


def test_atomic_write_restricts_path_and_symlinks(tmp_path: Path) -> None:
    api = module()
    write_atomic = api["write_atomic"]
    globals_ = write_atomic.__globals__
    target = tmp_path / "generated.lean"
    globals_["ROOT"] = tmp_path.resolve()
    globals_["DEFAULT_OUTPUT"] = target
    globals_["AUTHORITY"] = tmp_path / "authority.lean"
    Path(globals_["AUTHORITY"]).write_text("authority")

    other = tmp_path / "other.lean"
    with pytest.raises(ValueError, match="non-canonical output"):
        api["write_atomic"](other, "bad")

    target.write_text("old")
    link = tmp_path / "link.lean"
    link.symlink_to(target)
    globals_["DEFAULT_OUTPUT"] = link
    with pytest.raises(ValueError, match="symlink output"):
        write_atomic(link, "bad")
    assert target.read_text() == "old"

    victim = tmp_path / "victim"
    victim.mkdir()
    alias = tmp_path / "alias"
    alias.symlink_to(victim, target_is_directory=True)
    aliased_output = alias / "generated.lean"
    globals_["DEFAULT_OUTPUT"] = aliased_output
    with pytest.raises(ValueError, match="symlinked output parent"):
        write_atomic(aliased_output, "bad")
    assert not (victim / "generated.lean").exists()

    globals_["DEFAULT_OUTPUT"] = target
    write_atomic(target, "new")
    assert target.read_text() == "new"


def test_cli_defaults_to_check_and_has_no_arbitrary_output_flag(tmp_path: Path) -> None:
    authority_before = (ROOT / "trainverify/denote/GeneratedYOCOMoE.lean").read_bytes()
    generated = ROOT / "trainverify/denote/yoco_goals/GeneratedMultirefCertificates.lean"
    generated_before = generated.read_bytes()

    checked = subprocess.run(
        [sys.executable, str(SCRIPT)], cwd=ROOT, text=True, capture_output=True
    )
    assert checked.returncode == 0, checked.stderr
    assert generated.read_bytes() == generated_before
    assert (ROOT / "trainverify/denote/GeneratedYOCOMoE.lean").read_bytes() == authority_before

    rejected = subprocess.run(
        [sys.executable, str(SCRIPT), "--output", str(tmp_path / "bad.lean")],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    assert rejected.returncode != 0
    assert "unrecognized arguments: --output" in rejected.stderr
