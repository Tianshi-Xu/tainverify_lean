from dataclasses import dataclass

import pytest

from Verdict.graph_to_lean import (
    SelectedLineage,
    canonicalize_init_lineage_multiref,
    deduplicate_intermediate_lineages,
    derive_input_value_classes,
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
