"""Certificate rank roles never replace the graph's execution footprint."""
from dataclasses import replace

import pytest

from scripts.tests.test_sharded_contiguous_propagation import _closed_fixture
from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter.parser import Node


def bind_certificate(relation, cert, **transition_changes):
    """Keep typed digest, transition and materialized sources coherent for graph gates."""
    old = relation.certificates[0]
    relation.certificates = (cert,)
    relation.transition_specs = (replace(
        relation.transition_specs[0], certificate_digest=composer._typed_certificate_digest(cert),
        pre_facts=(cert.input_fact,), post_facts=(cert.output_fact,), **transition_changes),)
    relation.dependent_chain_plan.relation_facts = tuple(
        replace(f, source=cert.input_fact if f.source == old.input_fact else cert.output_fact)
        for f in relation.dependent_chain_plan.relation_facts)


@pytest.mark.parametrize("mutation,message", [
    ("duplicate_id", "footprint"), ("missing_id", "footprint"),
    ("shifted_id", "footprint"), ("out_of_bounds", "footprint"),
    ("wrong_side", "canonical"), ("projection", "canonical"),
    ("leading_zero", "canonical"), ("negative_index", "canonical"),
    ("sm_shifted", "SM step"), ("sm_side", "SM step"), ("sm_projection", "SM step"),
    ("duplicate_footprint", "footprint"), ("shifted_footprint", "footprint"),
    ("duplicate_rank", "ordered ranks"), ("shifted_rank", "ordered ranks"),
    ("swapped_roles", "ordered relation TIDs"),
    ("sm_header", "rank headers"), ("pm_header", "rank headers"),
    ("frame_bounds", "frame bounds"),
])
def test_coordinated_certificate_mutations_reach_graph_checks(mutation, message):
    ir, relation, segment, pre, post = _closed_fixture()
    cert = relation.certificates[0]
    ids = list(cert.pm_step_ids)
    changes = {}
    if mutation == "duplicate_id": ids[1] = ids[0]
    elif mutation == "missing_id": ids.pop()
    elif mutation in ("shifted_id", "out_of_bounds"): ids[-1] = "pm:3:0"
    elif mutation == "wrong_side": ids[0] = "sm:0:0"
    elif mutation == "projection": ids[0] = "pm:0:1"
    elif mutation == "leading_zero": ids[0] = "pm:00:0"
    elif mutation == "negative_index": ids[0] = "pm:-1:0"
    elif mutation == "sm_shifted": cert = replace(cert, sm_step_id="sm:1:0")
    elif mutation == "sm_side": cert = replace(cert, sm_step_id="pm:0:0")
    elif mutation == "sm_projection": cert = replace(cert, sm_step_id="sm:0:1")
    elif mutation == "duplicate_footprint": changes["pm_node_indices"] = (0, 0, 2)
    elif mutation == "shifted_footprint": changes["pm_node_indices"] = (0, 1, 3)
    elif mutation == "duplicate_rank": ir.pm_nodes[1].rank = 0
    elif mutation == "shifted_rank": ir.pm_nodes[2].rank = 3
    elif mutation == "sm_header": ir.sm_num_ranks = 2
    elif mutation == "pm_header": ir.pm_num_ranks = 4
    elif mutation == "frame_bounds": segment.pm_range = (-1, 3)
    if mutation in ("shifted_id", "shifted_footprint"):
        ir.pm_nodes.append(Node(2, "FW_contiguous", [202], [302], []))
        segment.pm_range = (0, 4)
    cert = replace(cert, pm_step_ids=tuple(ids), output_fact=replace(
        cert.output_fact, step_triple=(cert.sm_step_id, *ids)))
    if mutation == "swapped_roles":
        cert = replace(cert, input_fact=cert.output_fact, output_fact=cert.input_fact)
    bind_certificate(relation, cert, **changes)
    if mutation == "swapped_roles":
        relation.dependent_chain_plan.relation_facts = (
            replace(pre, source=cert.input_fact, sm_tid=post.sm_tid, pm_tids=post.pm_tids),
            replace(post, source=cert.output_fact, sm_tid=pre.sm_tid, pm_tids=pre.pm_tids))
    # This assertion excludes an accidental stale-digest/typed-selection rejection.
    assert composer._select_exact_typed_certificate(
        relation, relation.transition_specs[0], cert.rule_id, cert.lean_theorem,
        type(cert), lambda c: ((c.input_fact,), (c.output_fact,))) is cert
    with pytest.raises(ValueError, match=message):
        composer.render_closed_k_rank_contiguous_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize("k", [3, 5])
def test_permuted_sparse_contiguous_frame_keeps_actual_positions(k):
    ir, relation, segment, _, _ = _closed_fixture(k)
    semantic_nodes = ir.pm_nodes
    order = [k - 1, *range(k - 1)]
    frame = lambda tid: Node(0, "FW_contiguous", [900], [tid], [])
    ir.pm_nodes = [frame(901)]
    positions = {}
    for rank in order:
        ir.pm_nodes.append(frame(910 + rank))
        positions[rank] = len(ir.pm_nodes)
        ir.pm_nodes.append(semantic_nodes[rank])
    ir.pm_nodes.append(frame(920))
    ir.sm_nodes = [frame(901), frame(902), ir.sm_nodes[0], frame(903)]
    segment.sm_range = (1, len(ir.sm_nodes))
    segment.pm_range = (1, len(ir.pm_nodes))
    cert = relation.certificates[0]
    ids = tuple(f"pm:{positions[r]}:0" for r in range(k))
    cert = replace(cert, sm_step_id="sm:2:0", pm_step_ids=ids,
                   output_fact=replace(cert.output_fact, step_triple=("sm:2:0", *ids)))
    bind_certificate(relation, cert, sm_node_indices=(2,), pm_node_indices=tuple(sorted(positions.values())))
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    frame_text = ", ".join(composer._node_text(n) for n in ir.pm_nodes[1:])
    assert f"private def {segment.segment_id}_pm_nodes : List NodeDecl := [{frame_text}]" in source
    for rank, index in positions.items():
        assert f"pmNodes.take {index - 1} ++ [{segment.segment_id}_pm_node_{rank}] ++ pmNodes.drop {index}" in source
    assert "smNodes.take 1 ++" in source
    assert source.count("foldl_faithful_middle_writer") == k + 1
    assert source.count("foldl_applyNodeDistributedFaithful_at_not_written") == k + 1
    assert "RelationState.Holds.fold_frame" in source
