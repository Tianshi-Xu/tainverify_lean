from collections import namedtuple

import pytest

from Verdict.graph_to_lean import derive_replica_groups


Node = namedtuple("Node", "rank cid mb irname op outs")
Tensor = namedtuple("Tensor", "tid")


class Graph:
    def node_opname(self, node):
        return node.op

    def node_outputs(self, node):
        return node.outs


def replica(rank, cid, tid, *, mb=0, irname="Attention"):
    return Node(
        rank=rank,
        cid=cid,
        mb=mb,
        irname=irname,
        op="OpName.FW_attn_zigzag",
        outs=(Tensor(tid),),
    )


def logical_ids(nodes):
    return {id(node): (node.cid, node.mb, node.irname) for node in nodes}


def test_same_metadata_distinct_logical_calls_do_not_merge():
    # The calls intentionally have identical op metadata; alignment is authoritative.
    nodes = [replica(0, 10, 100), replica(1, 10, 101),
             replica(0, 11, 200), replica(1, 11, 201)]
    groups = derive_replica_groups(Graph(), nodes, logical_ids(nodes))
    assert [group.logical for group in groups] == [
        (10, 0, "Attention"), (11, 0, "Attention")
    ]
    assert [group.members for group in groups] == [
        ((0, 100), (1, 101)), ((0, 200), (1, 201))
    ]


def test_subgroups_stay_separate_and_members_are_rank_ordered():
    nodes = [
        replica(3, 20, 303, mb=4), replica(1, 20, 301, mb=4),
        replica(2, 21, 402, mb=4), replica(0, 21, 400, mb=4),
    ]
    groups = derive_replica_groups(Graph(), nodes, logical_ids(nodes))
    assert groups[0].members == ((1, 301), (3, 303))
    assert groups[1].members == ((0, 400), (2, 402))


def test_expanded_rank_local_cids_use_alignment_identity():
    nodes = [replica(0, 7999, 7437), replica(1, 8000, 7438)]
    aligned = {id(node): (14, 0, "wrap_sliding_window_attn_func") for node in nodes}
    groups = derive_replica_groups(Graph(), nodes, aligned)
    assert len(groups) == 1
    assert groups[0].logical == (14, 0, "wrap_sliding_window_attn_func")
    assert groups[0].members == ((0, 7437), (1, 7438))


def test_duplicate_member_rank_is_rejected():
    nodes = [replica(0, 30, 500), replica(0, 30, 501)]
    with pytest.raises(ValueError, match="duplicate replica member rank"):
        derive_replica_groups(Graph(), nodes, logical_ids(nodes))
