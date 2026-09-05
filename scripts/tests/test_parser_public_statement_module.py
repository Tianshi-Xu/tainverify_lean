from trainverify.bridge_emitter import parser
from pathlib import Path


def test_public_full_scope_uses_configured_module_prefix(tmp_path, monkeypatch):
    goal_path = tmp_path / "Goal_1.lean"
    goal_text = "def unrelated : Nat := 0\n"
    goal_path.write_text(goal_text)
    (tmp_path / "Goal_1_Full.lean").write_text(
        "def goal_1_stmt_full :\n"
        "  CoarseLineageHoldsWithInit Graphs.sm Graphs.pm goals "
        "Graphs.smEnv Graphs.pmEnv := by trivial\n"
    )

    monkeypatch.setattr(parser, "MOD_PREFIX", "denote.gpt_ly4_regen")
    result = parser._public_full_scope(1, str(goal_path), goal_text, "")

    assert result[1] == "denote.gpt_ly4_regen.Goal_1_Full"


def test_gpt_legacy_statement_is_an_explicit_full_scope_fallback(monkeypatch):
    root = Path(__file__).resolve().parents[2]
    monkeypatch.setattr(parser, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser, "MOD_PREFIX", "denote.gpt_ly4_regen")

    ir = parser.load_goal_ir(2, str(root))

    assert ir.public_statement_ref == "TrainVerify.Denote.Generated.goal_2_stmt"
    assert ir.public_statement_module == "denote.gpt_ly4_regen.GeneratedData"
    assert ir.sm_graph_ref == "TrainVerify.Denote.Generated.sm"
    assert ir.pm_graph_ref == "TrainVerify.Denote.Generated.pm"
    assert ir.init_goals_ref == "TrainVerify.Denote.Generated.initGoals"
    assert ir.sm_input_value_classes == ()
    assert ir.pm_input_value_classes == ()
