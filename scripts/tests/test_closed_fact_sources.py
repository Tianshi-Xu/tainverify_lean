"""Fact authority boundaries using the existing typed renderer fixtures."""
from dataclasses import fields, is_dataclass, replace
from importlib import import_module

import pytest

from scripts.tests import (
    alltoall_reduce_scatter_witness,
    bw_gelu_wred_witness,
    bw_layernorm_wred_witness,
    bw_softmax_reduce_scatter_witness,
)
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node


BUILDERS = {
    "alltoall_reduce_scatter": alltoall_reduce_scatter_witness.renderer_fixture,
    "bw_gelu_wred": bw_gelu_wred_witness.fixture,
    "bw_layernorm_wred": bw_layernorm_wred_witness.fixture,
    "bw_softmax_reduce_scatter": bw_softmax_reduce_scatter_witness.fixture,
    "cross_dp_wred": bw_gelu_wred_witness.fixture,
}
SOURCE_CONSUMERS = tuple(name for name in BUILDERS if name != "cross_dp_wred")
SEGMENT_ID = "segment_000000"


def renderer_case(consumer, k=3):
    ir, relation = BUILDERS[consumer](k)
    if consumer == "cross_dp_wred":
        # Isolate the existing independent WRED writer, preserving its typed
        # certificate, source refs, original position and retained inputs.
        chain = relation.dependent_chain_plan
        chain.segments = (replace(
            chain.segments[0], transition_ids=("wred",),
            sm_range=(0, 0), pm_range=(k - 1, k),
        ),)
        chain.states = (chain.states[0], replace(
            chain.states[1],
            fact_ids=tuple(fid for fid in chain.states[1].fact_ids if fid != "fo"),
        ))
    module = import_module(f"trainverify.bridge_emitter.{consumer}_renderer")
    return ir, relation, getattr(module, f"render_closed_{consumer}_segment")


def retain_fact(relation, fact):
    chain = relation.dependent_chain_plan
    chain.authority_facts = (*chain.authority_facts, fact)
    chain.states = tuple(
        replace(state, fact_ids=(*state.fact_ids, fact.fact_id))
        for state in chain.states
    )


def rebind_source(relation, fact, source):
    """Update the real records, certificate payloads, digests and transitions."""
    old = fact.source
    certificates = []
    for cert in relation.certificates:
        changes = {
            field.name: source
            for field in fields(cert) if getattr(cert, field.name) == old
        }
        certificates.append(replace(cert, **changes))
    relation.certificates = tuple(certificates)
    relation.transition_specs = tuple(
        replace(
            transition,
            pre_facts=tuple(sorted(source if f == old else f for f in transition.pre_facts)),
            post_facts=tuple(source if f == old else f for f in transition.post_facts),
            certificate_digest=_typed_certificate_digest(cert),
        )
        for transition, cert in zip(relation.transition_specs, certificates)
    )
    chain = relation.dependent_chain_plan
    chain.relation_facts = tuple(
        replace(record, source=source) if record.source == old else record
        for record in chain.relation_facts
    )


class DerivedShapeFact(rc.ClosedTensorShapeFactRecord):
    pass


def retained_cases():
    _, relation = bw_gelu_wred_witness.fixture()
    template = replace(
        relation.dependent_chain_plan.relation_facts[0],
        fact_id="guard", sm_tid=9000, pm_tids=(9001, 9002),
    )
    cases = []
    for kind in ("sharded", "chunked", "reduction", "replicated", "ordinary"):
        cases.append((replace(template, kind=kind), ({9000}, {9001, 9002})))
    cases.extend([
        (replace(template, kind="joined", joined_pm_tid=9003), ({9000}, {9003})),
        (replace(template, kind="zigzag", metadata_tid=9003), ({9000}, {9001, 9002, 9003})),
        (replace(template, kind="joined_ordinary", joined_pm_tid=9003),
         ({9000}, {9001, 9002, 9003})),
        (replace(template, kind="joined_indexed_stack_dim1", joined_pm_tid=9003,
                 source_tid_triples=((9004, 9005, 9006), (9007, 9006, 9008))),
         ({9000, 9004, 9007}, {9001, 9002, 9003, 9005, 9006, 9008})),
        (replace(template, kind="label_chunks"), (set(), {9000, 9001, 9002})),
        (rc.ClosedGatherFactRecord("guard", 9000, 9001, 9002, 0, (2,), (1,)),
         ({9000}, {9001, 9002})),
    ])
    for side in ("sm", "pm"):
        expected = ({9000}, set()) if side == "sm" else (set(), {9000})
        cases.extend([
            (rc.ClosedTensorShapeFactRecord("guard", side, 9000, (1,), 0), expected),
            (rc.ClosedPackedCuFactRecord("guard", side, 9000, 8, 2), expected),
            (rc.ClosedLabelBoundFactRecord("guard", side, 9000, 8, 2), expected),
        ])
        for right in ("sm", "pm"):
            sm, pm = set(), set()
            (sm if side == "sm" else pm).add(9000)
            (sm if right == "sm" else pm).add(9001)
            cases.append((
                rc.ClosedTensorEqFactRecord("guard", side, 9000, right, 9001), (sm, pm),
            ))
    return cases


def invalid_retained_cases():
    template = retained_cases()[0][0]
    return {
        "shape-side": (rc.ClosedTensorShapeFactRecord("guard", "other", 9000, (1,), 0),
                       "retained tensor-shape fact has invalid side"),
        "eq-left-side": (rc.ClosedTensorEqFactRecord("guard", "other", 9000, "pm", 9001),
                         "retained tensor-equality fact has invalid side"),
        "eq-right-side": (rc.ClosedTensorEqFactRecord("guard", "sm", 9000, "other", 9001),
                          "retained tensor-equality fact has invalid side"),
        "packed-side": (rc.ClosedPackedCuFactRecord("guard", "other", 9000, 8, 2),
                        "retained side-specific authority fact has invalid side"),
        "label-side": (rc.ClosedLabelBoundFactRecord("guard", "other", 9000, 8, 2),
                       "retained side-specific authority fact has invalid side"),
        "subclass": (DerivedShapeFact("guard", "sm", 9000, (1,), 0),
                     "unsupported retained fact record: DerivedShapeFact"),
        "kind": (replace(template, kind="unknown"),
                 "unsupported retained relation fact kind: 'unknown'"),
        "joined": (replace(template, kind="joined", joined_pm_tid=None),
                   "joined retained fact lacks PM TID"),
        "zigzag": (replace(template, kind="zigzag", metadata_tid=None),
                   "zigzag retained fact lacks metadata TID"),
        "joined-ordinary": (replace(template, kind="joined_ordinary", joined_pm_tid=None),
                            "joined ordinary retained fact lacks PM TID"),
        "indexed-joined": (
            replace(template, kind="joined_indexed_stack_dim1",
                    joined_pm_tid=None, source_tid_triples=((9003, 9004, 9005),)),
            "joined indexed-stack retained fact is incomplete",
        ),
        "indexed-sources": (
            replace(template, kind="joined_indexed_stack_dim1",
                    joined_pm_tid=9003, source_tid_triples=()),
            "joined indexed-stack retained fact is incomplete",
        ),
    }


@pytest.mark.parametrize("consumer", BUILDERS)
def test_retained_fact_kinds_render(consumer):
    for fact, _ in retained_cases():
        ir, relation, render = renderer_case(consumer)
        retain_fact(relation, fact)
        assert render(ir, relation, SEGMENT_ID)


@pytest.mark.parametrize("consumer", BUILDERS)
@pytest.mark.parametrize("mutation", invalid_retained_cases())
def test_retained_fact_rejections(consumer, mutation):
    ir, relation, render = renderer_case(consumer)
    assert render(ir, relation, SEGMENT_ID)
    fact, diagnostic = invalid_retained_cases()[mutation]
    retain_fact(relation, fact)
    with pytest.raises(ValueError) as error:
        render(ir, relation, SEGMENT_ID)
    assert str(error.value) == diagnostic


SOURCE_MUTATIONS = ("layout", "axis", "source-triples", "order", "history", "joined")


def mutate_source(ir, relation, mutation):
    chain = relation.dependent_chain_plan
    fact = next(
        f for f in chain.relation_facts
        if f.source == relation.certificates[-1].input_fact
    )
    source = fact.source
    if mutation == "layout":
        source = replace(source, layout="ordinary")
    elif mutation == "axis":
        source = replace(source, gather_dim=1)
    elif mutation == "source-triples":
        source = replace(source, source_step_triples=(("init:1", "init:2", "init:3"),))
    elif mutation == "order":
        source = replace(source, step_triple=(
            source.step_triple[0], *reversed(source.step_triple[1:]),
        ))
    elif mutation == "history":
        # Add a prior writer outside the frame, keeping all frame refs coherent.
        ir.sm_nodes.insert(0, Node(0, "FW_contiguous", [8000], [fact.sm_tid], []))
        chain.segments = tuple(replace(
            segment, sm_range=tuple(index + 1 for index in segment.sm_range),
        ) for segment in chain.segments)
        for record in tuple(chain.relation_facts):
            refs = tuple(shift_sm_ref(ref) for ref in record.source.step_triple)
            if refs != record.source.step_triple:
                rebind_source(relation, record, replace(record.source, step_triple=refs))
        relation.certificates = tuple(
            replace(cert, sm_step_id=shift_sm_ref(cert.sm_step_id))
            if hasattr(cert, "sm_step_id") else cert for cert in relation.certificates
        )
        relation.transition_specs = tuple(
            replace(transition,
                    sm_node_indices=tuple(i + 1 for i in transition.sm_node_indices),
                    certificate_digest=_typed_certificate_digest(cert))
            for transition, cert in zip(relation.transition_specs, relation.certificates)
        )
    elif mutation == "joined":
        source = replace(source, joined_pm_step="pm:0:0")
    else:
        raise AssertionError(mutation)
    rebind_source(relation, fact, source)


def shift_sm_ref(ref):
    if not ref.startswith("sm:"):
        return ref
    side, index, slot = ref.split(":")
    return f"{side}:{int(index) + 1}:{slot}"


@pytest.mark.parametrize("consumer", SOURCE_CONSUMERS)
@pytest.mark.parametrize("mutation", SOURCE_MUTATIONS)
def test_source_rejections(consumer, mutation):
    ir, relation, render = renderer_case(consumer)
    assert render(ir, relation, SEGMENT_ID)
    mutate_source(ir, relation, mutation)
    context = ("BW_softmax/ReduceScatter" if consumer == "bw_softmax_reduce_scatter"
               else "BW_gelu/WRED")
    suffix = (
        "source layout/axis mismatch" if mutation in {"layout", "axis", "source-triples"}
        else "joined source is not the latest writer" if mutation == "joined"
        else "source is not the latest ordered TID authority"
    )
    with pytest.raises(ValueError) as error:
        render(ir, relation, SEGMENT_ID)
    assert str(error.value) == f"{context} {suffix}"


@pytest.mark.parametrize("k", (2, 3, 4))
def test_cross_dp_original_writer(k):
    ir, relation, render = renderer_case("cross_dp_wred", k)
    text = render(ir, relation, SEGMENT_ID)
    assert "cross_dp_wred_eq_allReducePrim" in text
    assert "ClosedDepSegmentCertificate" in text


def convert_records(value, module):
    """Rebuild package records as the corresponding real bare-module types."""
    if is_dataclass(value):
        cls = getattr(module, type(value).__name__)
        return cls(**{
            field.name: convert_records(getattr(value, field.name), module)
            for field in fields(value) if field.init
        })
    if isinstance(value, tuple):
        return tuple(convert_records(item, module) for item in value)
    return value


@pytest.mark.parametrize("consumer", BUILDERS)
def test_bare_module_renderer_matches_package(consumer):
    ir, relation, render = renderer_case(consumer)
    expected = render(ir, relation, SEGMENT_ID)
    bare_rc = import_module("relation_compiler")
    relation.certificates = convert_records(relation.certificates, bare_rc)
    relation.transition_specs = convert_records(relation.transition_specs, bare_rc)
    chain = relation.dependent_chain_plan
    for name in ("relation_facts", "authority_facts", "anchor_fact", "states", "segments"):
        setattr(chain, name, convert_records(getattr(chain, name), bare_rc))
    module = import_module(f"{consumer}_renderer")
    assert getattr(module, f"render_closed_{consumer}_segment")(ir, relation, SEGMENT_ID) == expected


def test_shared_fact_tids_exact_records():
    from trainverify.bridge_emitter.closed_fact_sources import fact_tids

    for fact, expected in retained_cases():
        assert fact_tids(fact) == expected
        derived_type = type(f"Derived{type(fact).__name__}", (type(fact),), {})
        derived = derived_type(**{field.name: getattr(fact, field.name) for field in fields(fact)})
        with pytest.raises(ValueError, match=f"unsupported retained fact record: {derived_type.__name__}"):
            fact_tids(derived)
    for fact, diagnostic in invalid_retained_cases().values():
        with pytest.raises(ValueError) as error:
            fact_tids(fact)
        assert str(error.value) == diagnostic


def test_shared_latest_ref_prefix_order_and_output_slots():
    from trainverify.bridge_emitter.closed_fact_sources import latest_ref

    ir, _ = bw_gelu_wred_witness.fixture()
    ir.sm_nodes = [
        Node(0, "BW_layernorm", [1, 2, 3, 4], [10, 20, 10], []),
        Node(0, "FW_contiguous", [10], [30], []),
        Node(0, "FW_contiguous", [30], [10], []),
    ]
    ir.pm_nodes = [Node(0, "FW_contiguous", [10], [20, 10], [])]
    assert [latest_ref(ir, "sm", 10, end) for end in range(4)] == [
        "init:10", "sm:0:2", "sm:0:2", "sm:2:0",
    ]
    assert latest_ref(ir, "pm", 10, 0) == "init:10"
    assert latest_ref(ir, "pm", 10, 1) == "pm:0:1"
    assert latest_ref(ir, "sm", 99, 3) == "init:99"


@pytest.mark.parametrize("consumer", SOURCE_CONSUMERS)
def test_shared_source_exact_original_boundaries(consumer):
    from trainverify.bridge_emitter.closed_fact_sources import source_exact

    ir, relation, _ = renderer_case(consumer)
    chain = relation.dependent_chain_plan
    segment = chain.segments[0]
    records = {fact.source: fact for fact in chain.relation_facts}
    for transition in relation.transition_specs:
        for boundary, sources in enumerate((transition.pre_facts, transition.post_facts)):
            for source in sources:
                source_exact(ir, records[source], segment.sm_range[boundary],
                             segment.pm_range[boundary], context="test")


def test_shared_source_exact_joined_writer_and_diagnostics():
    from trainverify.bridge_emitter.closed_fact_sources import source_exact

    ir, relation = bw_gelu_wred_witness.fixture()
    chain = relation.dependent_chain_plan
    joined = next(fact for fact in chain.relation_facts if fact.kind == "joined")
    source_exact(ir, joined, 1, 3, context="test")
    mutations = (
        (replace(joined.source, layout="ordinary"), "source layout/axis mismatch"),
        (replace(joined.source, gather_dim=1), "source layout/axis mismatch"),
        (replace(joined.source, source_step_triples=(("init:1", "init:2", "init:3"),)),
         "source layout/axis mismatch"),
        (replace(joined.source, step_triple=("init:999",)),
         "source is not the latest ordered TID authority"),
        (replace(joined.source, joined_pm_step="init:600"),
         "joined source is not the latest writer"),
        (replace(joined.source, joined_pm_step=None),
         "joined source is not the latest writer"),
    )
    for source, diagnostic in mutations:
        with pytest.raises(ValueError) as error:
            source_exact(ir, replace(joined, source=source), 1, 3, context="test")
        assert str(error.value) == f"test {diagnostic}"
    ir.pm_nodes.append(Node(0, "FW_contiguous", [999], [600], []))
    source_exact(ir, joined, 1, 3, context="test")
    with pytest.raises(ValueError, match="test joined source is not the latest writer"):
        source_exact(ir, joined, 1, 4, context="test")


def test_shared_bare_module_exact_types():
    helper = import_module("closed_fact_sources")
    bare_rc = import_module("relation_compiler")
    for fact, expected in retained_cases():
        assert helper.fact_tids(convert_records(fact, bare_rc)) == expected
        with pytest.raises(ValueError, match="unsupported retained fact record"):
            helper.fact_tids(fact)
