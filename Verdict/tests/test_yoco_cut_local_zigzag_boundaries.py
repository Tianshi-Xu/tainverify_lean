"""Regression tests for the final authority's post-unshuffle router stacks."""

from pathlib import Path



ROOT = Path(__file__).resolve().parents[2]
TV = ROOT / "trainverify"

GOAL3_LATE_UNSHUFFLED = [5655, 5709, 5763, 5817, 5871, 5925, 5979, 6033, 6087, 6141, 6195, 6249]
GOAL4_LATE_UNSHUFFLED = [5657, 5711, 5765, 5819, 5873, 5927, 5981, 6035, 6089, 6143, 6197, 6251]


def test_final_router_stacks_only_gather_post_unshuffle_outputs():
    generated = (TV / "denote/GeneratedYOCOMoE.lean").read_text()
    lines = generated.splitlines()
    for tid in GOAL3_LATE_UNSHUFFLED + GOAL4_LATE_UNSHUFFLED:
        assert any(
            'op := "OpName.FW_maybe_unshuffle"' in line
            and f"outs := [{tid}]" in line
            for line in lines
        )
    assert 'ins := [11608, 11609], outs := [4928], params := [1]' in generated
    assert 'ins := [11660, 11661], outs := [4929], params := [1]' in generated


def test_patterns_do_not_take_an_unconstrained_zigzag_hypothesis():
    p1 = (TV / "denote/yoco_goals/Pattern_1.lean").read_text()
    p4 = (TV / "denote/yoco_goals/Pattern_4.lean").read_text()
    main = (TV / "denote/yoco_goals/YocoMoE_MainSummary.lean").read_text()
    for text in (p1, p4, main):
        assert "ZigzagCutGatherHyp" not in text
        assert "Pattern1ZigzagCutGatherHyp" not in text
