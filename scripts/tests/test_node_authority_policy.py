import inspect
from dataclasses import dataclass


@dataclass
class NodeStub:
    rank: int
    op: str
    ins: list[int]
    outs: list[int]
    params: list[int] | None = None


def test_node_authority_fingerprint_canonicalizes_all_identity_fields():
    from trainverify.bridge_emitter.node_authority_policy import (
        node_authority_fingerprint,
    )

    expected = (1, "FW_view", (2, 3), (4,), ())
    assert node_authority_fingerprint(NodeStub(1, "FW_view", [2, 3], [4])) == expected
    assert node_authority_fingerprint(NodeStub(1, "FW_view", [2, 3], [4], [])) == expected
    assert node_authority_fingerprint(
        NodeStub(1, "FW_view", [2, 3], [4], [5, 6])
    ) == (1, "FW_view", (2, 3), (4,), (5, 6))


def test_schedule_digest_and_coverage_delegate_the_same_fingerprint_contract():
    from trainverify.bridge_emitter import relation_compiler

    schedule_source = inspect.getsource(relation_compiler.build_atomic_schedule)
    coverage_source = inspect.getsource(relation_compiler.build_exact_node_coverage_plan)
    assert "node_authority_fingerprint" in schedule_source
    assert "node_authority_fingerprint" in coverage_source
    assert "def node_payload" not in schedule_source
    assert "tuple(int(value) for value in node.ins)" not in coverage_source
