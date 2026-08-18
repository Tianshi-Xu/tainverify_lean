from trainverify.bridge_emitter import parser


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
