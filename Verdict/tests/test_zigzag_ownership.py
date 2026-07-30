"""Tests for the CP zigzag ownership predicate used by the goal emitter.

A `FW_maybe_shuffle` changes which global sequence positions a rank owns without
changing the shard shape, so shape-based layout inference cannot see it. These
tests pin the structural detector that the goal emitter uses instead.
"""

from dataclasses import dataclass

from Verdict.graph_to_lean import build_zigzag_owner_predicate


@dataclass(frozen=True)
class Tensor:
    tid: int
    shape: tuple[int, ...] = (2048, 64)


@dataclass(frozen=True)
class Node:
    op: str
    ins: tuple[Tensor, ...]
    outs: tuple[Tensor, ...]
    rank: int = 0
    kwargs: dict | None = None


class Graph:
    def __init__(self, nodes):
        self._nodes = list(nodes)

    def nodes(self):
        return self._nodes

    def node_opname(self, n):
        return n.op

    def node_inputs(self, n):
        return list(n.ins)

    def node_outputs(self, n):
        return list(n.outs)

    def tensor_shape(self, t):
        return list(t.shape)

    def node_kwargs(self, n):
        return n.kwargs or {}


def test_no_shuffle_means_nothing_is_zigzag():
    a, b = Tensor(1), Tensor(2)
    g = Graph([Node("OpName.FW_linear", (a,), (b,))])
    is_zigzag, _cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert not is_zigzag(1)
    assert not is_zigzag(2)


def test_direct_shuffle_output_is_zigzag():
    src, cu, sh = Tensor(1), Tensor(2), Tensor(3)
    g = Graph([Node("OpName.FW_maybe_shuffle", (src, cu), (sh,))])
    is_zigzag, _cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert is_zigzag(3)
    # The shuffle's own input is upstream of it, hence still contiguous.
    assert not is_zigzag(1)


def test_zigzag_propagates_through_downstream_ops():
    src, cu, sh = Tensor(1), Tensor(2), Tensor(3)
    mid, out = Tensor(4), Tensor(5)
    g = Graph(
        [
            Node("OpName.FW_maybe_shuffle", (src, cu), (sh,)),
            Node("OpName.FW_linear", (sh,), (mid,)),
            Node("OpName.FW_topk_routing", (mid,), (out,)),
        ]
    )
    is_zigzag, _cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert is_zigzag(5)
    assert is_zigzag(4)


def test_unshuffle_restores_contiguous_ownership():
    src, cu, sh = Tensor(1), Tensor(2), Tensor(3)
    mid, unsh, after = Tensor(4), Tensor(5), Tensor(6)
    g = Graph(
        [
            Node("OpName.FW_maybe_shuffle", (src, cu), (sh,)),
            Node("OpName.FW_linear", (sh,), (mid,)),
            Node("OpName.FW_maybe_unshuffle", (mid, cu), (unsh,)),
            Node("OpName.FW_rms_norm", (unsh,), (after,)),
        ]
    )
    is_zigzag, _cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert is_zigzag(4), "still zigzag before the unshuffle"
    assert not is_zigzag(5), "the unshuffle output is restored"
    assert not is_zigzag(6), "and so is everything after it"


def test_a_branch_that_bypasses_the_unshuffle_stays_zigzag():
    """The YOCO-MoE shape: routing tensors fork off before the unshuffle.

    The unshuffle sits on the residual stream, so tensors on the routing branch
    never pass through it and remain zigzag-owned even though a later,
    unrelated unshuffle exists in the graph.
    """
    src, cu, sh = Tensor(1), Tensor(2), Tensor(3)
    resid, routing = Tensor(4), Tensor(5)
    unsh, head = Tensor(6), Tensor(7)
    g = Graph(
        [
            Node("OpName.FW_maybe_shuffle", (src, cu), (sh,)),
            Node("OpName.FW_multiref", (sh,), (resid, routing)),
            Node("OpName.FW_maybe_unshuffle", (resid, cu), (unsh,)),
            Node("OpName.FW_rms_norm", (unsh,), (head,)),
        ]
    )
    is_zigzag, _cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert not is_zigzag(7), "the loss head is downstream of the unshuffle"
    assert is_zigzag(5), "the routing branch bypassed it and is still zigzag"


def test_mixed_stack_has_both_kinds_of_member():
    """The exact goal_3 situation: one stack over pre- and post-shuffle members."""
    pre, src, cu, sh, post = Tensor(1), Tensor(2), Tensor(3), Tensor(4), Tensor(5)
    g = Graph(
        [
            Node("OpName.FW_topk_routing", (src,), (pre,)),
            Node("OpName.FW_maybe_shuffle", (src, cu), (sh,)),
            Node("OpName.FW_topk_routing", (sh,), (post,)),
        ]
    )
    is_zigzag, _cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    members = [1, 5]
    verdicts = [is_zigzag(t) for t in members]
    assert verdicts == [False, True], (
        "a stack over these members cannot be stated as one uniform gather"
    )


def test_predicate_is_memoised_and_stable():
    src, cu, sh = Tensor(1), Tensor(2), Tensor(3)
    g = Graph([Node("OpName.FW_maybe_shuffle", (src, cu), (sh,))])
    is_zigzag, _cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert [is_zigzag(3) for _ in range(5)] == [True] * 5
    assert [is_zigzag(1) for _ in range(5)] == [False] * 5


def test_backward_ops_are_also_recognised():
    src, cu, sh, out = Tensor(1), Tensor(2), Tensor(3), Tensor(4)
    g = Graph(
        [
            Node("OpName.BW_maybe_shuffle", (src, cu), (sh,)),
            Node("OpName.BW_linear", (sh,), (out,)),
        ]
    )
    is_zigzag, _cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert is_zigzag(4)


def test_cu_tid_is_recovered_for_a_zigzag_tensor():
    """The emitter needs the cu tid to state a ZigzagLineageGoal.

    Ownership is not recoverable from shapes, so the cu_seqlens tensor that
    pins the layout must be carried explicitly in the goal. It is read off the
    shuffle node's second input, per the generated `[data, cu_seqlens]` calling
    convention.
    """
    src, cu, sh, out = Tensor(1), Tensor(2), Tensor(3), Tensor(4)
    g = Graph(
        [
            Node("OpName.FW_maybe_shuffle", (src, cu), (sh,)),
            Node("OpName.FW_linear", (sh,), (out,)),
        ]
    )
    is_zigzag, cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert is_zigzag(4)
    assert cu_of(4) == 2, "cu tid propagates to downstream zigzag tensors"
    assert cu_of(3) == 2, "and is available at the shuffle output itself"
    assert cu_of(1) is None, "contiguous tensors have no cu tid"


def test_cu_of_is_none_after_unshuffle():
    src, cu, sh, unsh = Tensor(1), Tensor(2), Tensor(3), Tensor(4)
    g = Graph(
        [
            Node("OpName.FW_maybe_shuffle", (src, cu), (sh,)),
            Node("OpName.FW_maybe_unshuffle", (sh, cu), (unsh,)),
        ]
    )
    _is_zigzag, cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert cu_of(3) == 2
    assert cu_of(4) is None


def test_unaudited_multi_rank_graph_is_conservative():
    """Graph rank count alone is not cpSize.

    nnScaler `emit_ring` gives maybe_shuffle `process_group=None` when its input
    is dim-1 partitioned or unpartitioned, even in a multi-rank graph. The
    generic emitter cannot recover the parent-tensor partition dimension from
    its compact DFG, so ownership suppression is opt-in. Without the audited
    dim-0 flag, mark nothing rather than deleting valid goals.
    """
    src, cu, sh, out = Tensor(1), Tensor(2), Tensor(3), Tensor(4)
    g = Graph(
        [
            Node("OpName.FW_maybe_shuffle", (src, cu), (sh,)),
            Node("OpName.FW_linear", (sh,), (out,)),
        ]
    )
    is_zigzag, cu_of = build_zigzag_owner_predicate(
        g, 2, cp_dim0_audited=False
    )
    assert not is_zigzag(3)
    assert not is_zigzag(4)
    assert cu_of(3) is None


def test_single_device_graph_has_no_zigzag_ownership():
    """cpSize = 1 makes `maybe_shuffle` the identity, so nothing is permuted.

    This is the case the first version of the gate got wrong. It tested only
    whether a shuffle appeared in the backward closure, which is true in the SM
    (single-device) graph too — `FW_maybe_shuffle` is emitted unconditionally,
    and the two graphs differ only in `params := [cpSize, cpRank]`:

        SM node 472 : params := [1, 0]
        PM node 1003: params := [2, 0]

    `fw_maybe_shuffle_collective` short-circuits with
    `if cpSize = 1 then localTensor`, so at cpSize = 1 an ordinary gather is
    perfectly correct and suppressing those goals would be a false alarm.
    """
    src, cu, sh, out = Tensor(1), Tensor(2), Tensor(3), Tensor(4)
    g = Graph(
        [
            Node("OpName.FW_maybe_shuffle", (src, cu), (sh,)),
            Node("OpName.FW_linear", (sh,), (out,)),
        ]
    )
    is_zigzag, cu_of = build_zigzag_owner_predicate(g, 1, cp_dim0_audited=True)
    assert not is_zigzag(3), "cpSize=1 shuffle is the identity"
    assert not is_zigzag(4)
    assert cu_of(3) is None
    # The very same graph at cpSize = 2 does permute.
    is_zigzag2, cu_of2 = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert is_zigzag2(3)
    assert cu_of2(3) == 2


def test_a_tensor_after_the_unshuffle_is_clean_even_with_zigzag_ancestry():
    """Regression: the loss head (goal_1/goal_2) must NOT be flagged.

    Its entire dataflow ancestry is full of zigzag tensors, but it sits after
    the `FW_maybe_unshuffle`, so its own value is contiguous and its goal is
    true. An earlier version of the gate suppressed these transitively — via
    their zigzag *prereqs* — and would have discarded two goals that are
    already machine-checked in `L23FaithfulLossGoals.lean`.

    Dropping a hypothesis makes a statement stronger, not false, so prereq
    contamination must never trigger suppression. Only the goal's OWN tensors
    matter.
    """
    src, cu, sh = Tensor(1), Tensor(2), Tensor(3)
    deep = Tensor(4)
    unsh, norm, loss = Tensor(5), Tensor(6), Tensor(7)
    g = Graph(
        [
            Node("OpName.FW_maybe_shuffle", (src, cu), (sh,)),
            Node("OpName.FW_linear", (sh,), (deep,)),
            Node("OpName.FW_maybe_unshuffle", (deep, cu), (unsh,)),
            Node("OpName.FW_rms_norm", (unsh,), (norm,)),
            Node("OpName.FW_inner_chunk_ce", (norm,), (loss,)),
        ]
    )
    is_zigzag, _cu_of = build_zigzag_owner_predicate(g, 2, cp_dim0_audited=True)
    assert is_zigzag(4), "the deep tensor really is zigzag"
    assert not is_zigzag(7), (
        "the loss head is contiguous despite zigzag ancestry — suppressing it "
        "would discard an already-proven goal"
    )
