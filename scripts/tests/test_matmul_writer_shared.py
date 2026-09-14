"""Byte compatibility and public wiring for the shared matmul writer."""

import hashlib
from pathlib import Path

import pytest

from scripts.tests import test_k_rank_matmul_contraction as contraction
from scripts.tests import test_k_rank_matmul_head_axis as head
from scripts.tests import test_k_rank_matmul_output_axis as output
from scripts.tests import test_k_rank_matmul_query_axis_compiler as query
from trainverify.bridge_emitter import composer


FAMILIES = {"head": head, "output": output, "query": query, "contraction": contraction}

# Full public renderer outputs frozen before extracting the writer.
@pytest.mark.parametrize(("family", "k", "digest"), [
    ("head", 3, "15c57ff9f7423448b1b5631c51333cc25bf15f49e756212bb2fc83b9cac421d1"),
    ("head", 4, "65cd7d0fc66e86fbef07647fb8a9484cbd69788613294c9e14285ee33810c56e"),
    ("output", 3, "1d98eb28fc1fe1d0db15ca8a5a508fa9fbba6405ca85697b81873a7796f74d05"),
    ("output", 4, "95a97438245b34f3b834ae11edf5d1eb0229f84de8292b69affa3cfbdebedc91"),
    ("query", 3, "a21f5c996d679ad7877cc24a1dd9b1660a7a4f5818f01e47ce7f3b81c50cd88f"),
    ("query", 4, "e4cca47eacb71cfb30fe65e92c8be344b75d6b40d72e1f63627c392ee1a678a5"),
    ("contraction", 3, "4bfa55531454cbdee4e7ed9d2470b9288874c5064a36c7a73767406a924641b2"),
    ("contraction", 4, "2aa58237c75e66c39e066d699b83b8657127670132ea6c6e8ee6cb5fea78a8a6"),
], ids=[f"{family}-k{k}" for family in ("head", "output", "query", "contraction") for k in (3, 4)])
def test_public_renderer_bytes(family, k, digest):
    ir, relation, segment, *_ = FAMILIES[family]._closed_fixture(k)
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert hashlib.sha256(rendered.encode("utf-8")).hexdigest() == digest


@pytest.mark.parametrize(("side", "pos", "name", "suffix"), [
    ("sm", 0, "hSmWriter", "sm_node"),
    ("pm", 1, "hPmWriter1", "pm_node_1"),
], ids=("sm", "pm"))
def test_shared_writer_matches_existing_witness(side, pos, name, suffix):
    ir, _, segment, *_ = head._closed_fixture(3)
    node = ir.sm_nodes[0] if side == "sm" else ir.pm_nodes[1]
    witness = (
        Path(__file__).parents[2]
        / "trainverify/denote/GeneratedKRankMatmulHeadAxisWitness.lean"
    ).read_text(encoding="utf-8")
    start = witness.index(f"    have {name} :")
    end = witness.index("    have ", start + 1)

    lines = composer._matmul_writer_lines(
        ir, name, side, pos, node, f"{segment.segment_id}_{suffix}"
    )

    assert lines == witness[start:end].splitlines()


@pytest.mark.parametrize("family", FAMILIES)
def test_public_renderer_uses_shared_writer(monkeypatch, family):
    ir, relation, segment, *_ = FAMILIES[family]._closed_fixture(3)
    writer = composer._matmul_writer_lines
    calls = []

    def record(*args):
        calls.append(args)
        return writer(*args)

    monkeypatch.setattr(composer, "_matmul_writer_lines", record)
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)

    assert calls == [
        (ir, "hSmWriter", "sm", 0, ir.sm_nodes[0], f"{segment.segment_id}_sm_node"),
        *(
            (ir, f"hPmWriter{rank}", "pm", rank, node, f"{segment.segment_id}_pm_node_{rank}")
            for rank, node in enumerate(ir.pm_nodes)
        ),
    ]
    for args in calls:
        assert "\n".join(writer(*args)) + "\n" in rendered
