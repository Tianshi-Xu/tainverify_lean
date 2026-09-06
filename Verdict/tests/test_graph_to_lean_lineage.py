from dataclasses import dataclass
import re

import pytest
from pathlib import Path
from argparse import Namespace

import Verdict.graph_to_lean as graph_to_lean

from Verdict.graph_to_lean import (
    SelectedLineage,
    _computed_boundary_tids,
    _goal_requires_distributed_faithful,
    _goal_slice_is_full_topology,
    GENERATED_LEAN_SOURCE_LIMIT,
    _atomic_publish_generated_directory,
    _extract_untrusted_pattern_templates,
    _is_pattern_template_path,
    _owned_snapshot_key,
    _validate_untrusted_pattern_template_tree,
    _goals_module_prefix,
    _remap_output_path,
    _uncovered_computed_boundary_tids,
    _validate_generated_authority_tree,
    canonicalize_init_lineage_multiref,
    close_nodes_to_external_inputs,
    deduplicate_intermediate_lineages,
    derive_input_value_classes,
    compress_if_replicated,
    final_writer_ranks_by_tid,
)


def test_goals_module_prefix_for_top_level_and_nested_modules(tmp_path):
    goals_dir = tmp_path / "proof_bins"
    assert _goals_module_prefix("GeneratedSpec", goals_dir) == "proof_bins"
    assert (
        _goals_module_prefix("Acme.Custom.GeneratedSpec", goals_dir)
        == "Acme.Custom.proof_bins"
    )


@dataclass(frozen=True)
class Tensor:
    tid: int
    shape: tuple[int, ...]


@dataclass(frozen=True)
class Node:
    op: str
    ins: tuple[Tensor, ...]
    outs: tuple[Tensor, ...]
    rank: int = 0
    kwargs: dict | None = None


@dataclass(frozen=True)
class Root:
    _id: int


class Graph:
    def __init__(self, nodes):
        self._nodes = list(nodes)

    def nodes(self): return self._nodes
    def node_opname(self, n): return n.op
    def node_inputs(self, n): return list(n.ins)
    def node_outputs(self, n): return list(n.outs)
    def tensor_shape(self, t): return list(t.shape)
    def node_kwargs(self, n): return n.kwargs or {}


def test_checked_in_gpt_replicated_goals_name_the_surviving_pm_writer():
    root = Path(__file__).resolve().parents[2]
    source = (root / "trainverify/denote/gpt_ly4_regen/GeneratedData.lean").read_text()
    pm_start = source.index("def pm : GraphDecl")
    pm_end = source.index("def initGoal_", pm_start)
    pm_source = source[pm_start:pm_end]
    final_writers = {}
    for rank, outputs in re.findall(
        r'\{ rank := (\d+),.*?outs := \[([^]]+)\]', pm_source
    ):
        for tid in re.findall(r"\d+", outputs):
            final_writers[int(tid)] = int(rank)
    mismatches = []
    for goal_id, body in re.findall(
        r"def goal_(\d+) : LineageGoal :=\s*\n\s*\{([^\n]+)\}", source
    ):
        pieces = [
            (int(rank), int(tid))
            for rank, tid in re.findall(r"rank := (\d+), tid := (\d+)", body)
        ]
        if len(pieces) == 1 and pieces[0][1] in final_writers:
            expected = final_writers[pieces[0][1]]
            if pieces[0][0] != expected:
                mismatches.append((int(goal_id), pieces[0], expected))
    assert mismatches == []


def test_replicated_lineage_uses_the_writer_that_survives_ordered_pm_fold():
    shared = Tensor(577, (1, 8, 4, 8))
    graph = Graph([
        Node("OpName.FW_view", (), (shared,), rank=rank)
        for rank in range(4)
    ])
    lineage = SelectedLineage(
        ts=577, tps=[(rank, 577) for rank in range(4)]
    )
    writers = final_writer_ranks_by_tid(graph)
    assert writers[577] == 3
    assert compress_if_replicated(lineage, writers) == SelectedLineage(
        ts=577, tps=[(3, 577)]
    )


def test_collective_normalization_preserves_observed_nonzero_output_ranks():
    graph = Graph([
        Node('OpName.AllReducePrim', (Tensor(10, (2,)), Tensor(11, (2,))),
             (Tensor(20, (2,)),), rank=rank)
        for rank in (2, 3)
    ])
    normalize = graph_to_lean.make_collective_lineage_normalizer(graph)
    result = normalize(SelectedLineage(ts=1, tps=[(2, 10), (3, 11)]))
    assert result.tps == [(2, 20), (3, 20)]
    # Emission may retain only one shared-output collective. The writer must
    # come from this emitted node schedule, not the pre-dedup expanded graph.
    emitted = graph.nodes()[:1]
    writers = final_writer_ranks_by_tid(graph, emitted)
    assert compress_if_replicated(result, writers).tps == [(2, 20)]


def test_collective_normalization_does_not_accept_unrelated_final_writer():
    graph = Graph([
        Node('OpName.AllReducePrim', (Tensor(10, (2,)), Tensor(11, (2,))),
             (Tensor(20, (2,)),), rank=2),
        Node('OpName.FW_view', (Tensor(99, (2,)),), (Tensor(20, (2,)),), rank=3),
    ])
    normalize = graph_to_lean.make_collective_lineage_normalizer(graph)
    result = normalize(SelectedLineage(ts=1, tps=[(2, 10), (3, 11)]))
    with pytest.raises(ValueError, match='absent from lineage ranks'):
        compress_if_replicated(result, final_writer_ranks_by_tid(graph))


def test_goal_faithful_evaluator_selection_is_collective_driven():
    plain = [Node("OpName.FW_inner_chunk_ce", (), ())]
    for op in (
        "OpName.FW_all2all_moe_gmm",
        "OpName.FW_maybe_shuffle",
        "OpName.FW_maybe_unshuffle",
        "OpName.FW_attn_zigzag",
    ):
        assert _goal_requires_distributed_faithful([Node(op, (), ())])
    assert not _goal_requires_distributed_faithful(plain)
    # Similar collectives already modeled faithfully by the ordinary evaluator
    # do not switch the whole statement to the zigzag-distributed evaluator.
    assert not _goal_requires_distributed_faithful([
        Node("OpName.AllToAllPrim", (), ()),
        Node("OpName.AllGatherPrim", (), ()),
    ])


def test_full_ancestry_is_independent_of_faithful_evaluator_selection():
    # Goal 5: an external-input-closed embedding+AllToAll slice is full even
    # though ordinary semantics already models its collectives faithfully.
    assert _goal_slice_is_full_topology([], False)
    # An actual computed cut remains a cut under ordinary semantics.
    assert not _goal_slice_is_full_topology([object()], False)
    # Faithful collectives force closure past any proposed computed boundary.
    assert _goal_slice_is_full_topology([object()], True)


def test_computed_cut_boundary_is_not_an_external_input():
    external = Tensor(10, (8,))
    computed = Tensor(11, (8,))
    result = Tensor(12, (8,))
    producer = Node("OpName.FW_linear", (external,), (computed,))
    consumer = Node("OpName.FW_all2all_moe_gmm", (computed,), (result,))
    graph = Graph([producer, consumer])

    assert _computed_boundary_tids(graph, [consumer]) == [11]
    assert _computed_boundary_tids(graph, [producer, consumer]) == []
    assert _uncovered_computed_boundary_tids(graph, [consumer], []) == [11]
    assert _uncovered_computed_boundary_tids(graph, [consumer], [11]) == []


def test_faithful_topology_closes_to_external_inputs_without_goal_whitelist():
    external = Tensor(10, (8,))
    computed = Tensor(11, (8,))
    moe_out = Tensor(12, (8,))
    loss = Tensor(13, (8,))
    nodes = [
        Node("OpName.FW_linear", (external,), (computed,)),
        Node("OpName.FW_all2all_moe_gmm", (computed,), (moe_out,)),
        Node("OpName.FW_inner_chunk_ce", (moe_out,), (loss,)),
    ]
    graph = Graph(nodes)

    closed = close_nodes_to_external_inputs(graph, [loss.tid])
    cut_after_collective = [nodes[-1]]

    assert not _goal_requires_distributed_faithful(cut_after_collective, graph)
    assert closed == nodes
    assert _computed_boundary_tids(graph, closed) == []
    assert _goal_requires_distributed_faithful(closed, graph)


def test_init_lineage_follows_fw_multiref_to_source_leaf():
    source = Tensor(4691, (4096, 64))
    copy = Tensor(11853, (4096, 64))
    graph = Graph([Node("OpName.FW_multiref", (source,), (copy,))])
    got = canonicalize_init_lineage_multiref(
        graph, SelectedLineage(ts=4691, tps=[(0, 11853)])
    )
    assert got == SelectedLineage(ts=4691, tps=[(0, 4691)])


def test_init_lineage_indexes_producers_by_rank_and_tid():
    source0 = Tensor(100, (8,))
    source1 = Tensor(200, (8,))
    shared_tid_copy0 = Tensor(300, (8,))
    shared_tid_copy1 = Tensor(300, (8,))
    graph = Graph([
        Node("OpName.FW_multiref", (source0,), (shared_tid_copy0,), rank=0),
        Node("OpName.FW_multiref", (source1,), (shared_tid_copy1,), rank=1),
    ])
    got = canonicalize_init_lineage_multiref(
        graph, SelectedLineage(ts=10, tps=[(0, 300), (1, 300)])
    )
    assert got == SelectedLineage(ts=10, tps=[(0, 100), (1, 200)])


@pytest.mark.parametrize("op", ["OpName.FW_reshape", "OpName.FW_linear", "OpName.AllGatherPrim"])
def test_init_lineage_does_not_cross_non_alias_ops(op):
    source = Tensor(10, (8, 8))
    output = Tensor(11, (8, 8))
    graph = Graph([Node(op, (source,), (output,))])
    got = canonicalize_init_lineage_multiref(
        graph, SelectedLineage(ts=10, tps=[(0, 11)])
    )
    assert got == SelectedLineage(ts=10, tps=[(0, 11)])


def test_init_lineage_rejects_shape_changing_multiref():
    graph = Graph([Node("OpName.FW_multiref", (Tensor(10, (8,)),), (Tensor(11, (4,)),))])
    with pytest.raises(ValueError, match="shape"):
        canonicalize_init_lineage_multiref(graph, SelectedLineage(ts=10, tps=[(0, 11)]))


def test_final_goals_win_over_intermediate_goals():
    final = [SelectedLineage(ts=4680, tps=[(0, 4680)])]
    intermediate = {
        4680: SelectedLineage(ts=4680, tps=[(0, 4680)]),
        4681: SelectedLineage(ts=4681, tps=[(0, 4681)]),
    }
    kept, removed = deduplicate_intermediate_lineages(final, intermediate)
    assert set(kept) == {4681}
    assert removed == [4680]


def test_getitem_provenance_forms_deterministic_input_value_classes():
    root = Root(4188)
    other_root = Root(9000)
    graph = Graph([
        Node("OpName.FW_pyfunc", (), (Tensor(5345, (2,)),), rank=1,
             kwargs={"__consts": [root, "cu_seqlens_q"]}),
        Node("OpName.FW_pyfunc", (), (Tensor(5337, (2,)),), rank=0,
             kwargs={"__consts": [root, "cu_seqlens_q"]}),
        # Rank replicas use the same tid and must not duplicate it.
        Node("OpName.FW_pyfunc", (), (Tensor(5337, (2,)),), rank=1,
             kwargs={"__consts": [root, "cu_seqlens_q"]}),
        Node("OpName.FW_pyfunc", (), (Tensor(5346, (2,)),),
             kwargs={"__consts": [root, "cu_seqlens_k"]}),
        Node("OpName.FW_pyfunc", (), (Tensor(6000, (2,)),),
             kwargs={"__consts": [other_root, "cu_seqlens_q"]}),
    ])

    assert derive_input_value_classes(graph) == [
        ("getitem:root=4188:key=cu_seqlens_q", (5337, 5345)),
    ]


def test_getitem_provenance_ignores_malformed_non_tensor_and_singleton_classes():
    root = Root(7)
    graph = Graph([
        Node("OpName.BW_pyfunc", (), (Tensor(1, (2,)),),
             kwargs={"__consts": [root, "x"]}),
        Node("OpName.FW_pyfunc", (), (Tensor(2, (2,)),),
             kwargs={"__consts": [root, 123]}),
        Node("OpName.FW_pyfunc", (), (Tensor(3, (2,)),),
             kwargs={"__consts": [object(), "x"]}),
        Node("OpName.FW_pyfunc", (), (), kwargs={"__consts": [root, "x"]}),
    ])
    assert derive_input_value_classes(graph) == []


def test_generated_authority_tree_accepts_import_only_full_compatibility_module(tmp_path):
    (tmp_path / "Goal_1.lean").write_text(
        "set_option maxHeartbeats 500000\ndef goal_1_stmt_full : Prop := True\n",
        encoding="utf-8",
    )
    (tmp_path / "Goal_1_Full.lean").write_text("import Goal_1\n", encoding="utf-8")
    _validate_generated_authority_tree(tmp_path)


def test_generated_authority_tree_rejects_duplicate_full_statement(tmp_path):
    for name in ("Goal_1.lean", "Goal_1_Full.lean"):
        (tmp_path / name).write_text("def goal_1_stmt_full : Prop := True\n", encoding="utf-8")
    with pytest.raises(ValueError, match="duplicate generated full public statements"):
        _validate_generated_authority_tree(tmp_path)


def test_generated_authority_tree_rejects_oversize_and_high_heartbeat(tmp_path):
    oversized = tmp_path / "Oversized.lean"
    oversized.write_bytes(b"x" * GENERATED_LEAN_SOURCE_LIMIT)
    with pytest.raises(ValueError, match="exceeds 2500000 byte limit"):
        _validate_generated_authority_tree(tmp_path)
    oversized.unlink()
    (tmp_path / "High.lean").write_text(
        "set_option maxHeartbeats 500001\ndef x : Prop := True\n", encoding="utf-8"
    )
    with pytest.raises(ValueError, match="heartbeat limit"):
        _validate_generated_authority_tree(tmp_path)
    (tmp_path / "High.lean").write_text(
        "set_option maxHeartbeats 0\ndef x : Prop := True\n", encoding="utf-8"
    )
    with pytest.raises(ValueError, match="heartbeat limit"):
        _validate_generated_authority_tree(tmp_path)


def test_generated_authority_tree_rejects_forbidden_proof_placeholders(tmp_path):
    for forbidden in (
        "sorry",
        "sorryAx False true",
        "admit",
        "axiom forged : False",
        "private axiom forged : False",
        "unsafe def forged := 0",
        "False.elim h",
    ):
        path = tmp_path / "Forbidden.lean"
        path.write_text(f"def goal_1_stmt_full : Prop := True\n{forbidden}\n", encoding="utf-8")
        with pytest.raises(ValueError, match="contains forbidden"):
            _validate_generated_authority_tree(tmp_path)


def test_atomic_generated_directory_exchange_removes_stale_owned_files(tmp_path):
    target = tmp_path / "authority"
    staged = tmp_path / ".authority.stage"
    target.mkdir()
    staged.mkdir()
    (target / "stale.lean").write_text("stale", encoding="utf-8")
    (staged / "GeneratedData.lean").write_text("fresh", encoding="utf-8")
    _atomic_publish_generated_directory(staged, target)
    assert sorted(path.name for path in target.iterdir()) == ["GeneratedData.lean"]
    assert (target / "GeneratedData.lean").read_text(encoding="utf-8") == "fresh"
    assert not staged.exists()


def test_owned_snapshot_key_is_stage_name_independent_and_confined(tmp_path: Path) -> None:
    root = tmp_path / ".random-stage"
    nested = root / "goals" / "Goal_1.lean"
    nested.parent.mkdir(parents=True)
    nested.write_text("def x := 1\n")
    assert _owned_snapshot_key(nested, root) == "goals/Goal_1.lean"
    outside = tmp_path / "outside.lean"
    outside.write_text("def y := 2\n")
    with pytest.raises(ValueError, match="escapes owned output tree"):
        _owned_snapshot_key(outside, root)


def test_pattern_template_classification_excludes_only_untrusted_scaffolds() -> None:
    for name in (
        "Pattern_1.lean", "SegmentPattern_99.lean", "Patterns.lean",
        "Instances.lean", "ProofObligations.lean", "MainTheorem.lean",
        "SegmentPatterns.lean", "SegmentInstances.lean",
    ):
        assert _is_pattern_template_path(Path(name))
    for name in ("GeneratedData.lean", "Goal_1.lean", "Goal_1_Full.lean"):
        assert not _is_pattern_template_path(Path(name))


def test_pattern_skeletons_are_extracted_and_labelled_untrusted(tmp_path: Path) -> None:
    authority = tmp_path / "authority"
    templates = tmp_path / "templates"
    authority.mkdir()
    (authority / "Goal_1.lean").write_text("def goal_1_stmt_full : Prop := True\n")
    (authority / "Pattern_1.lean").write_text("theorem pattern_1 : True := by sorry\n")
    (authority / "Patterns.lean").write_text("import X.Pattern_1\n")
    (authority / "MainTheorem.lean").write_text("theorem main : True := by sorry\n")

    moved = _extract_untrusted_pattern_templates(authority, templates)
    assert moved == ["MainTheorem.lean", "Pattern_1.lean", "Patterns.lean"]
    assert sorted(path.name for path in authority.iterdir()) == ["Goal_1.lean"]
    assert "UNTRUSTED PROOF TEMPLATE" in (templates / "Pattern_1.lean").read_text()
    assert "sorry" in (templates / "Pattern_1.lean").read_text()
    _validate_untrusted_pattern_template_tree(templates)


def test_untrusted_pattern_validator_keeps_heartbeat_bound(tmp_path: Path) -> None:
    templates = tmp_path / "templates"
    templates.mkdir()
    (templates / "Pattern_1.lean").write_text(
        "/- UNTRUSTED PROOF TEMPLATE. This file may contain sorry and is not part of "
        "the validated authority tree. -/\n"
        "set_option maxHeartbeats 500001\n"
        "theorem pattern_1 : True := by sorry\n"
    )
    with pytest.raises(RuntimeError, match="heartbeat limit"):
        _validate_untrusted_pattern_template_tree(templates)
    (templates / "Pattern_1.lean").write_text(
        "/- UNTRUSTED PROOF TEMPLATE. This file may contain sorry and is not part of "
        "the validated authority tree. -/\n"
        "set_option maxHeartbeats 0\n"
        "theorem pattern_1 : True := by sorry\n"
    )
    with pytest.raises(RuntimeError, match="heartbeat limit"):
        _validate_untrusted_pattern_template_tree(templates)


def test_main_publishes_pattern_opt_in_outside_trusted_authority(tmp_path, monkeypatch) -> None:
    authority = tmp_path / "authority"
    templates = tmp_path / "templates"
    for root in (authority, templates):
        root.mkdir()
        (root / "STALE").write_text("stale")

    args = Namespace(
        split_goals=True,
        atomic_output_root=str(authority),
        emit_segment_patterns=True,
        pattern_template_output_root=str(templates),
        out=str(authority / "GeneratedData.lean"),
        goals_out_dir=str(authority),
        module="TrainVerify.Denote.Fake.GeneratedData",
        emit_spec_template=False,
        manifest_out=None,
    )

    def fake_generate(staged_args) -> None:
        root = Path(staged_args.goals_out_dir)
        root.mkdir(parents=True, exist_ok=True)
        Path(staged_args.out).write_text("def generatedData : Nat := 0\n")
        (root / "Goal_1.lean").write_text("def goal_1_stmt_full : Prop := True\n")
        (root / "Pattern_1.lean").write_text("theorem pattern_1 : True := by sorry\n")
        (root / "Patterns.lean").write_text("import Fake.Pattern_1\n")
        (root / "Instances.lean").write_text("import Fake.Patterns\n")
        (root / "ProofObligations.lean").write_text("theorem obligation : True := by sorry\n")
        (root / "MainTheorem.lean").write_text("theorem main : True := by sorry\n")
        (root / "SegmentPattern_1.lean").write_text("theorem segment_pattern_1 : True := by sorry\n")
        (root / "SegmentPatterns.lean").write_text("import Fake.SegmentPattern_1\n")
        (root / "SegmentInstances.lean").write_text("import Fake.SegmentPatterns\n")

    monkeypatch.setattr(graph_to_lean, "parse_args", lambda: args)
    monkeypatch.setattr(graph_to_lean, "_generate", fake_generate)
    graph_to_lean.main()

    assert not (authority / "STALE").exists()
    assert not (templates / "STALE").exists()
    assert sorted(path.name for path in authority.glob("*.lean")) == [
        "GeneratedData.lean", "Goal_1.lean"
    ]
    assert all("sorry" not in path.read_text() for path in authority.glob("*.lean"))
    assert (templates / "Pattern_1.lean").read_text().startswith(
        "/- UNTRUSTED PROOF TEMPLATE."
    )
    assert "sorry" in (templates / "Pattern_1.lean").read_text()
    assert (templates / "SegmentPattern_1.lean").exists()
    assert (templates / "SegmentPatterns.lean").exists()
    assert (templates / "SegmentInstances.lean").exists()
    assert not (authority / "SegmentPatterns.lean").exists()
    assert not (authority / "SegmentInstances.lean").exists()


def test_atomic_generated_directory_exchange_rejects_symlink_target(tmp_path):
    staged = tmp_path / ".authority.stage"
    staged.mkdir()
    real = tmp_path / "real"
    real.mkdir()
    target = tmp_path / "authority"
    target.symlink_to(real, target_is_directory=True)
    with pytest.raises(ValueError, match="must not be a symlink"):
        _atomic_publish_generated_directory(staged, target)
    assert staged.is_dir()
    assert target.is_symlink()


def test_atomic_output_remap_rejects_escape(tmp_path):
    root = tmp_path / "authority"
    stage = tmp_path / ".authority.stage"
    assert _remap_output_path(str(root / "goals"), root, stage) == str(stage / "goals")
    with pytest.raises(ValueError, match="escapes --atomic-output-root"):
        _remap_output_path(str(tmp_path / "other"), root, stage)
