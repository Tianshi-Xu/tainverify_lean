from dataclasses import replace
from pathlib import Path
import os
import subprocess
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter import composer


def _view_step(step_id, *, side, node_index, rank, source, input_shape=(1, 8, 3, 4),
               output_shape=(1, 8, 12), parameters=(1, 8, 12)):
    return SimpleNamespace(
        step_id=step_id,
        side=side,
        node_index=node_index,
        rank=rank,
        op="FW_view",
        input_bindings=(source,),
        input_shapes=(input_shape,),
        output_shape=output_shape,
        parameters=parameters,
    )


def _single_pair():
    sm = _view_step("sm:50:0", side="sm", node_index=50, rank=0, source="sm:49:0")
    pm = _view_step("pm:321:0", side="pm", node_index=321, rank=3, source="pm:317:0")
    plan = SimpleNamespace(steps=(sm, pm))
    return plan, sm, pm


def test_joined_view_matcher_rewrites_to_joined_inputs_without_rank_zero_specialization():
    plan, sm, pm = _single_pair()

    certs, frontiers, layouts = rc.advance_joined_view_relation_frontiers(
        plan, ((sm.step_id, pm.step_id),), ("joined",)
    )

    assert len(certs) == 1
    cert = certs[0]
    assert cert.rule_id == "joined-view-unary"
    assert cert.pm_rank == 3
    assert cert.parameters == (1, 8, 12)
    assert cert.input_fact == rc.RelationFactSpec(
        "joined", ("sm:49:0",), joined_pm_step="pm:317:0"
    )
    assert cert.output_fact == rc.RelationFactSpec(
        "joined", (sm.step_id,), joined_pm_step=pm.step_id
    )
    assert frontiers == (("sm:49:0", "pm:317:0"),)
    assert layouts == ("joined",)


def test_joined_view_normalization_reaches_fixed_point_and_emits_exact_transitions():
    sm0 = _view_step("sm:10:0", side="sm", node_index=10, rank=0, source="sm:9:0")
    pm0 = _view_step("pm:20:0", side="pm", node_index=20, rank=2, source="pm:19:0")
    sm1 = _view_step("sm:11:0", side="sm", node_index=11, rank=0, source=sm0.step_id)
    pm1 = _view_step("pm:21:0", side="pm", node_index=21, rank=2, source=pm0.step_id)
    sink = []

    frontiers, layouts = rc.normalize_relation_frontiers(
        SimpleNamespace(steps=(sm0, pm0, sm1, pm1)),
        ((sm1.step_id, pm1.step_id),),
        ("joined",),
        rules=("joined_view",),
        certificate_sink=sink,
    )

    assert frontiers == (("sm:9:0", "pm:19:0"),)
    assert layouts == ("joined",)
    assert len(sink) == 2
    transitions = rc.build_certificate_transition_specs(SimpleNamespace(), tuple(sink))
    assert {(item.sm_node_indices, item.pm_node_indices) for item in transitions} == {
        ((10,), (20,)),
        ((11,), (21,)),
    }
    assert all(len(item.pre_facts) == len(item.post_facts) == 1 for item in transitions)


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        ({"parameters": (1, 8, 13)}, "literal parameters"),
        ({"input_shapes": ((1, 8, 4, 3),)}, "declared input shapes"),
        ({"output_shape": (1, 8, 13)}, "declared output shapes"),
        ({"input_bindings": ("pm:317:0", "pm:316:0")}, "unary arity"),
    ],
)
def test_joined_view_matcher_fails_closed_on_incompatible_authority(mutation, message):
    plan, sm, pm = _single_pair()
    bad_pm = SimpleNamespace(**{**pm.__dict__, **mutation})

    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_joined_view_relation_frontiers(
            SimpleNamespace(steps=(sm, bad_pm)),
            ((sm.step_id, bad_pm.step_id),),
            ("joined",),
        )


def test_joined_view_matcher_does_not_claim_non_view_or_non_joined_frontiers():
    plan, sm, pm = _single_pair()
    not_view = SimpleNamespace(**{**pm.__dict__, "op": "FW_reshape"})

    certs, frontiers, layouts = rc.advance_joined_view_relation_frontiers(
        SimpleNamespace(steps=(sm, not_view)),
        ((sm.step_id, not_view.step_id),),
        ("joined",),
    )
    assert certs == ()
    assert frontiers == ((sm.step_id, not_view.step_id),)
    assert layouts == ("joined",)

    certs, frontiers, layouts = rc.advance_joined_view_relation_frontiers(
        plan, ((sm.step_id, pm.step_id),), ("sharded",)
    )
    assert certs == ()
    assert frontiers == ((sm.step_id, pm.step_id),)
    assert layouts == ("sharded",)


def test_certificate_dedup_uses_authority_facts_not_coarse_object_equality():
    class CoarseCertificate:
        def __init__(self, sm_step, pm_step):
            self.rule_id = "coarse"
            self.lean_theorem = "T"
            self.input_fact = rc.RelationFactSpec(
                "joined", (f"sm:{sm_step - 1}:0",),
                joined_pm_step=f"pm:{pm_step - 1}:0",
            )
            self.output_fact = rc.RelationFactSpec(
                "joined", (f"sm:{sm_step}:0",),
                joined_pm_step=f"pm:{pm_step}:0",
            )
            self.sm_step_id = f"sm:{sm_step}:0"
            self.pm_step_id = f"pm:{pm_step}:0"

        def __hash__(self):
            return hash((self.rule_id, self.lean_theorem))

        def __eq__(self, other):
            return isinstance(other, CoarseCertificate)

    first = CoarseCertificate(10, 20)
    second = CoarseCertificate(11, 21)
    exact_duplicate = CoarseCertificate(10, 20)
    sink = []

    rc._extend_unique_certificates(sink, (first, second, exact_duplicate))

    assert sink == [first, second]


def _closed_joined_view_fixture(rank_count=3):
    plan, sm_step, pm_step = _single_pair()
    pm_step.rank = rank_count - 1
    pm_step.node_index = 321 + rank_count - 1
    pm_step.step_id = f"pm:{pm_step.node_index}:0"
    certificates, _, _ = rc.advance_joined_view_relation_frontiers(
        plan, ((sm_step.step_id, pm_step.step_id),), ("joined",)
    )
    certificate = certificates[0]
    transition = rc.build_certificate_transition_specs(plan, certificates)[0]
    pre = SimpleNamespace(
        fact_id="fact_joined_input", source=certificate.input_fact, kind="joined",
        sm_tid=49, joined_pm_tid=317, full_shape=certificate.input_shape,
        shard_shape=certificate.input_shape, pm_tids=(), gather_dim=None,
    )
    post = SimpleNamespace(
        fact_id="fact_joined_output", source=certificate.output_fact, kind="joined",
        sm_tid=50, joined_pm_tid=321, full_shape=certificate.output_shape,
        shard_shape=certificate.output_shape, pm_tids=(), gather_dim=None,
    )
    before = SimpleNamespace(state_id="state_pre", fact_ids=("anchor", pre.fact_id))
    after = SimpleNamespace(state_id="state_post", fact_ids=("anchor", post.fact_id))
    segment = SimpleNamespace(
        segment_id="segment_000000", transition_ids=(transition.transition_id,),
        sm_range=(50, 51), pm_range=(321, 321 + rank_count),
        pre_state_id=before.state_id, post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(pre, post), authority_facts=(),
        anchor_fact=SimpleNamespace(fact_id="anchor", side="sm", tid=77, shape=(1,)),
        states=(before, after), segments=(segment,),
    )
    filler = lambda rank=0: SimpleNamespace(
        rank=rank, op="FW_identity", ins=[], outs=[], params=[]
    )
    sm_node = SimpleNamespace(
        rank=0, op="FW_view", ins=[49], outs=[50], params=[1, 8, 12]
    )
    pm_nodes = [SimpleNamespace(
        rank=rank, op="FW_view", ins=[317], outs=[321], params=[1, 8, 12]
    ) for rank in range(rank_count)]
    ir = SimpleNamespace(
        sm_graph_ref="sm_graph", pm_graph_ref="pm_graph",
        sm_nodes=[filler() for _ in range(50)] + [sm_node],
        pm_nodes=[filler() for _ in range(321)] + pm_nodes,
    )
    relation = SimpleNamespace(
        certificates=certificates, transition_specs=(transition,),
        dependent_chain_plan=chain,
    )
    return ir, relation, segment, pre, post


@pytest.mark.parametrize("rank_count", (2, 3, 5))
def test_closed_joined_view_renderer_reduces_one_sm_and_ordered_dynamic_k_pm_writers(rank_count):
    ir, relation, segment, pre, post = _closed_joined_view_fixture(rank_count)

    source = composer.render_closed_joined_view_segment(
        ir, relation, segment.segment_id
    )

    assert source == composer.render_closed_segment(ir, relation, segment.segment_id)
    assert 'op := "OpName.FW_view", ins := [49], outs := [50], params := [1, 8, 12]' in source
    for rank in range(rank_count):
        assert f'rank := {rank}, op := "OpName.FW_view", ins := [317], outs := [321]' in source
    assert source.count('op := "OpName.FW_view"') >= rank_count + 1
    assert "applyNode_fw_view_out smGraph" in source
    assert "applyNode_fw_view_out pmGraph" in source
    assert "JoinedRel.fw_view" in source
    assert pre.fact_id in source and post.fact_id in source
    assert "Goal_" not in source and "Tid" not in source


def test_closed_joined_view_renderer_rejects_parameter_mismatch():
    ir, relation, segment, *_ = _closed_joined_view_fixture()
    ir.pm_nodes[322].params = [1, 8, 13]

    with pytest.raises(ValueError, match="literal parameters"):
        composer.render_closed_joined_view_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        (lambda ir, relation, segment: setattr(ir.pm_nodes[322], "rank", 0), "ordered ranks"),
        (lambda ir, relation, segment: setattr(ir.pm_nodes[322], "op", "FW_reshape"), "literal FW_view"),
        (lambda ir, relation, segment: setattr(ir.pm_nodes[322], "ins", [316]), "joined pre-fact"),
        (lambda ir, relation, segment: setattr(ir.pm_nodes[322], "outs", [320]), "joined post-fact"),
    ],
)
def test_closed_joined_view_renderer_rejects_malformed_writer_authority(mutation, message):
    ir, relation, segment, *_ = _closed_joined_view_fixture()
    mutation(ir, relation, segment)
    with pytest.raises(ValueError, match=message):
        composer.render_closed_joined_view_segment(ir, relation, segment.segment_id)


def test_closed_joined_view_renderer_requires_one_exact_typed_certificate():
    ir, relation, segment, *_ = _closed_joined_view_fixture()
    exact = relation.certificates[0]

    class Spoof:
        pass

    spoof = Spoof()
    spoof.__dict__.update(exact.__dict__)
    for certificates in ((exact, exact), (spoof,)):
        bad = SimpleNamespace(**{**relation.__dict__, "certificates": certificates})
        with pytest.raises(ValueError, match="one exact typed certificate"):
            composer.render_closed_joined_view_segment(ir, bad, segment.segment_id)


@pytest.mark.parametrize("field", ("rule_id", "lean_theorem", "input_fact", "output_fact"))
def test_closed_joined_view_renderer_rejects_tampered_certificate_authority(field):
    ir, relation, segment, *_ = _closed_joined_view_fixture()
    cert = relation.certificates[0]
    bad_cert = replace(cert, **{field: "tampered"})
    bad = SimpleNamespace(**{**relation.__dict__, "certificates": (bad_cert,)})
    with pytest.raises(ValueError, match="one exact typed certificate"):
        composer.render_closed_joined_view_segment(ir, bad, segment.segment_id)


def test_generated_joined_view_witness_is_exact_renderer_output():
    ir, relation, segment, *_ = _closed_joined_view_fixture()
    namespace = "GeneratedJoinedViewWitness"
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)
    source = "\n".join((
        composer.render_closed_relation_declarations(
            relation.dependent_chain_plan, namespace
        ),
        f"namespace TrainVerify.Denote.{namespace}",
        "noncomputable section",
        ('private def sm_graph : GraphDecl := { numRanks := 1, nodes := '
         '[{ rank := 0, op := "OpName.FW_view", ins := [49], outs := [50], '
         'params := [1, 8, 12] }] }'),
        ('private def pm_graph : GraphDecl := { numRanks := 3, nodes := '
         '[{ rank := 0, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }, '
         '{ rank := 1, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }, '
         '{ rank := 2, op := "OpName.FW_view", ins := [317], outs := [321], params := [1, 8, 12] }] }'),
        rendered,
        f"#print axioms {segment.segment_id}",
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ))
    witness = (Path(__file__).resolve().parents[2]
               / "trainverify/denote/GeneratedJoinedViewWitness.lean")

    assert witness.read_text(encoding="utf-8") == source
    assert "sorry" not in source
