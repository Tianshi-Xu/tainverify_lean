import json
from pathlib import Path

import pytest

from scripts import incremental_test_selector as selector


BW_SUM_PATHS = (
    "trainverify/bridge_emitter/relation_compiler.py",
    "trainverify/bridge_emitter/bw_sum_renderer.py",
    "trainverify/bridge_emitter/compound_rule_dispatch.py",
    "trainverify/bridge_emitter/sum_bw_sum_atomic_renderer.py",
    "trainverify/denote/KRankBWSum.lean",
    "scripts/tests/test_k_rank_bw_sum.py",
)


def test_full_python_inventory_covers_every_repository_test_module():
    root = Path(__file__).resolve().parents[2]
    expected = {
        path.relative_to(root).as_posix()
        for directory in (root / "scripts/tests", root / "Verdict/tests")
        for path in directory.glob("test_*.py")
    }
    assert set(selector.FULL_PYTHON_TESTS) == expected


def test_cache_helper_change_selects_only_cache_focused_gate():
    plan = selector.select_gates(("scripts/tests/real_goal_cache.py",))

    assert plan.full_python is False
    assert plan.formal_publication is False
    assert plan.exact_models == ()
    assert "scripts/tests/test_real_goal_cache.py" in plan.pytest_nodes
    assert any("test_ce_terminal_relation_plan" in node for node in plan.pytest_nodes)


def test_bw_sum_family_selects_gpt_exact_and_formal_semantic_gates():
    plan = selector.select_gates(BW_SUM_PATHS, family="k-rank-bw-sum")

    assert plan.full_python is False
    assert plan.exact_models == ("gpt2",)
    assert plan.lean_modules == ("denote.KRankBWSum",)
    assert plan.staged_lean is True
    assert plan.axiom_audit is True
    assert plan.formal_publication is True
    assert "scripts/tests/test_k_rank_bw_sum.py" in plan.pytest_nodes
    assert any("Goal107" in reason or "Goal 107" in reason for reason in plan.explanations)


def test_shared_relation_compiler_without_family_fails_closed():
    plan = selector.select_gates(
        ("trainverify/bridge_emitter/relation_compiler.py",)
    )

    assert plan.full_python is True
    assert plan.exact_models == ("gpt2", "yoco-a04b", "yoco-3b")
    assert plan.staged_lean is True
    assert plan.axiom_audit is True
    assert plan.formal_publication is True


def test_family_hint_rejects_paths_outside_declared_scope():
    plan = selector.select_gates(
        (*BW_SUM_PATHS, "trainverify/bridge_emitter/model_authority.py"),
        family="k-rank-bw-sum",
    )

    assert plan.full_python is True
    assert any("outside" in reason for reason in plan.explanations)


def test_unknown_path_fails_closed_instead_of_returning_empty_plan():
    plan = selector.select_gates(("trainverify/new_unknown_authority.py",))

    assert plan.full_python is True
    assert plan.formal_publication is True
    assert plan.pytest_nodes


@pytest.mark.parametrize("path", (
    "docs/../trainverify/denote/KRankBWSum.lean",
    "/repo/docs/TESTING.md",
    "docs//TESTING.md",
    "docs/./TESTING.md",
))
def test_noncanonical_or_absolute_paths_fail_closed(path):
    plan = selector.select_gates((path,))

    assert plan.full_python is True
    assert plan.staged_lean is True
    assert plan.axiom_audit is True
    assert plan.formal_publication is True
    assert any("noncanonical" in reason for reason in plan.explanations)


def test_release_mode_escalates_known_focused_change():
    plan = selector.select_gates(
        ("scripts/tests/real_goal_cache.py",), release=True
    )

    assert plan.full_python is True
    assert plan.formal_publication is True
    assert plan.exact_models == ("gpt2", "yoco-a04b", "yoco-3b")


def test_docs_only_and_direct_test_changes_have_minimal_gates():
    docs = selector.select_gates(("docs/TESTING.md",))
    direct_test = selector.select_gates(("scripts/tests/test_k_rank_bw_sum.py",))

    assert docs.pytest_nodes == () and docs.full_python is False
    assert direct_test.pytest_nodes == ("scripts/tests/test_k_rank_bw_sum.py",)
    assert direct_test.full_python is False


def test_cli_explain_and_json_outputs_are_machine_readable(capsys):
    assert selector.main(["scripts/tests/real_goal_cache.py"]) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["full_python"] is False
    assert payload["pytest_nodes"]

    assert selector.main([
        "--explain", "--family", "k-rank-bw-sum", *BW_SUM_PATHS
    ]) == 0
    explanation = capsys.readouterr().out
    assert "pytest:" in explanation
    assert "exact-model: gpt2" in explanation
    assert "lean-module: denote.KRankBWSum" in explanation
