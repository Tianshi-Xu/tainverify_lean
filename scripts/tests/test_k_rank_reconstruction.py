from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

import trainverify.bridge_emitter.relation_compiler as relation_compiler
from trainverify.bridge_emitter.composer import (
    render_closed_k_rank_allgather_segment,
    render_closed_k_rank_allreduce_segment,
    render_closed_relation_declarations,
    render_closed_segment,
)


def _synthetic_joined_allgather(*, rank_count=5, gather_dim=1):
    sm = SimpleNamespace(
        step_id="sm:0:0",
        side="sm",
        op="FW_identity",
        rank=0,
        input_bindings=(),
        input_shapes=(),
        parameters=(),
        output_shape=(2, 3 * rank_count, 7),
    )
    shards = tuple(
        SimpleNamespace(
            step_id=f"pm:{rank}:0",
            side="pm",
            op="FW_identity",
            rank=rank,
            input_bindings=(),
            input_shapes=(),
            parameters=(),
            output_shape=(2, 3, 7),
        )
        for rank in range(rank_count)
    )
    gather = SimpleNamespace(
        step_id=f"pm:{rank_count}:0",
        side="pm",
        op="AllGatherPrim",
        rank=0,
        input_bindings=tuple(step.step_id for step in shards),
        input_shapes=tuple(step.output_shape for step in shards),
        parameters=(gather_dim,),
        output_shape=sm.output_shape,
    )
    return SimpleNamespace(steps=(sm, *shards, gather)), sm, shards, gather


def test_ordered_k_rank_allgather_reconstruction_matches_arbitrary_k():
    plan, sm, shards, gather = _synthetic_joined_allgather(rank_count=5, gather_dim=1)
    root = (sm.step_id, gather.step_id)

    certificates, frontiers, layouts = (
        relation_compiler.advance_k_rank_allgather_reconstruction_frontiers(
            plan, (root,), ("joined",)
        )
    )

    assert len(certificates) == 1
    certificate = certificates[0]
    ordered_inputs = tuple(step.step_id for step in shards)
    assert certificate.rank_count == 5
    assert certificate.gather_dim == 1
    assert certificate.input_fact == relation_compiler.RelationFactSpec(
        "sharded", (sm.step_id, *ordered_inputs), gather_dim=1
    )
    assert certificate.output_fact == relation_compiler.RelationFactSpec(
        "joined", (sm.step_id,), joined_pm_step=gather.step_id
    )
    assert certificate.pm_allgather_step == gather.step_id
    assert frontiers == ((sm.step_id, *ordered_inputs),)
    assert layouts == ("sharded",)



def test_ordered_k_rank_allgather_reconstruction_is_registered_at_fixed_point():
    plan, sm, shards, gather = _synthetic_joined_allgather(rank_count=3, gather_dim=2)
    root = (sm.step_id, gather.step_id)
    # Use a dimension-2-compatible synthetic shape for this registration pass.
    sm.output_shape = (2, 3, 21)
    for shard in shards:
        shard.output_shape = (2, 3, 7)
    gather.input_shapes = tuple(shard.output_shape for shard in shards)
    gather.output_shape = sm.output_shape
    sink = []

    frontiers, layouts = relation_compiler.normalize_relation_frontiers(
        plan,
        (root,),
        ("joined",),
        rules=("allgather_reconstruction_k",),
        certificate_sink=sink,
    )

    assert frontiers == ((sm.step_id, *(step.step_id for step in shards)),)
    assert layouts == ("sharded",)
    assert len(sink) == 1
    assert sink[0].rule_id == "allgather-reconstruction-k-rank"



def test_ordered_k_rank_allgather_transition_preserves_exact_writer_footprint():
    plan, sm, shards, gather = _synthetic_joined_allgather(rank_count=4, gather_dim=1)
    certificates, _, _ = (
        relation_compiler.advance_k_rank_allgather_reconstruction_frontiers(
            plan, ((sm.step_id, gather.step_id),), ("joined",)
        )
    )

    transition = relation_compiler.build_certificate_transition_specs(
        plan, certificates
    )[0]

    certificate = certificates[0]
    assert transition.pre_facts == (certificate.input_fact,)
    assert transition.post_facts == (certificate.output_fact,)
    assert transition.sm_node_indices == ()
    assert transition.pm_node_indices == (4,)
    assert transition.lean_theorem == certificate.lean_theorem



def _closed_k_rank_segment_fixture(*, rank_count=5, gather_dim=1):
    plan, sm, shards, gather_step = _synthetic_joined_allgather(
        rank_count=rank_count, gather_dim=gather_dim
    )
    certificates, _, _ = (
        relation_compiler.advance_k_rank_allgather_reconstruction_frontiers(
            plan, ((sm.step_id, gather_step.step_id),), ("joined",)
        )
    )
    certificate = certificates[0]
    transition = relation_compiler.build_certificate_transition_specs(
        plan, certificates
    )[0]
    input_tids = tuple(100 + rank for rank in range(rank_count))
    full_tid, joined_tid = 10, 900
    before = SimpleNamespace(
        fact_id="fact_sharded",
        source=certificate.input_fact,
        kind="sharded",
        sm_tid=full_tid,
        pm_tids=input_tids,
        gather_dim=gather_dim,
        full_shape=certificate.full_shape,
        shard_shape=certificate.shard_shape,
        joined_pm_tid=None,
    )
    after = SimpleNamespace(
        fact_id="fact_joined",
        source=certificate.output_fact,
        kind="joined",
        sm_tid=full_tid,
        pm_tids=(),
        gather_dim=None,
        full_shape=certificate.full_shape,
        shard_shape=certificate.full_shape,
        joined_pm_tid=joined_tid,
    )
    pre_state = SimpleNamespace(
        state_id="state_pre", fact_ids=("anchor", before.fact_id)
    )
    post_state = SimpleNamespace(
        state_id="state_post", fact_ids=("anchor", after.fact_id)
    )
    segment = SimpleNamespace(
        segment_id="segment_000000",
        transition_ids=(transition.transition_id,),
        sm_range=(0, 0),
        pm_range=(rank_count, rank_count + 1),
        pre_state_id=pre_state.state_id,
        post_state_id=post_state.state_id,
    )
    chain = SimpleNamespace(
        complete=True,
        relation_facts=(before, after),
        authority_facts=(),
        anchor_fact=SimpleNamespace(
            fact_id="anchor", side="sm", tid=77, shape=(1,)
        ),
        states=(pre_state, post_state),
        segments=(segment,),
    )
    gather_node = SimpleNamespace(
        rank=0,
        op="AllGatherPrim",
        ins=list(input_tids),
        outs=[joined_tid],
        params=[gather_dim],
    )
    ir = SimpleNamespace(
        sm_num_ranks=1,
        pm_num_ranks=rank_count,
        sm_graph_ref="sm_graph",
        pm_graph_ref="pm_graph",
        sm_nodes=[],
        pm_nodes=[
            SimpleNamespace(rank=rank, op="FW_identity", ins=[], outs=[100 + rank], params=[])
            for rank in range(rank_count)
        ] + [gather_node],
    )
    relation = SimpleNamespace(
        certificates=certificates,
        transition_specs=(transition,),
        dependent_chain_plan=chain,
    )
    return ir, relation, segment, before, after, gather_node


def test_closed_k_rank_allgather_renderer_uses_exact_dynamic_authority():
    ir, relation, segment, before, after, gather = (
        _closed_k_rank_segment_fixture(rank_count=5, gather_dim=1)
    )

    source = render_closed_k_rank_allgather_segment(
        ir, relation, segment.segment_id
    )

    assert source == render_closed_segment(ir, relation, segment.segment_id)
    assert 'List NodeDecl := [{ rank := 0, op := "OpName.AllGatherPrim"' in source
    assert "ins := [100, 101, 102, 103, 104]" in source
    assert "params := [1]" in source
    assert "allGatherPrimDimN 1 5 0" in source
    assert "ShardedRel" in source
    assert "ShardedRel.to_joined_allGather" in source
    assert f"{before.fact_id}.Holds" in source
    assert f"{after.fact_id}.Holds" in source
    assert "smNodes : List NodeDecl := []" in source


def test_closed_k_rank_allgather_renderer_rejects_nonexact_writer_footprint():
    ir, relation, segment, *_ = _closed_k_rank_segment_fixture()
    transition = relation.transition_specs[0]
    broken_transition = SimpleNamespace(
        **{**transition.__dict__, "pm_node_indices": (0, 1)}
    )
    broken = SimpleNamespace(
        **{**relation.__dict__, "transition_specs": (broken_transition,)}
    )

    with pytest.raises(ValueError, match="exact PM AllGather writer"):
        render_closed_k_rank_allgather_segment(ir, broken, segment.segment_id)



def test_fresh_exact_synthetic_lean_module_is_renderer_output(tmp_path):
    ir, relation, segment, *_ = _closed_k_rank_segment_fixture(
        rank_count=5, gather_dim=1
    )
    namespace = "GeneratedKRankReconstructionWitness"
    declarations = render_closed_relation_declarations(
        relation.dependent_chain_plan, namespace
    )
    rendered_segment = render_closed_segment(ir, relation, segment.segment_id)
    source = "\n".join((
        declarations,
        f"namespace TrainVerify.Denote.{namespace}",
        "noncomputable section",
        "private def sm_graph : GraphDecl := { numRanks := 1, nodes := [] }",
        "private def pm_graph : GraphDecl := { numRanks := 5, nodes := [] }",
        rendered_segment,
        f"#print axioms {segment.segment_id}",
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ))
    witness = tmp_path / "GeneratedKRankReconstructionWitness.lean"
    witness.write_text(source)

    assert witness.read_text() == source
    assert rendered_segment == render_closed_k_rank_allgather_segment(
        ir, relation, segment.segment_id
    )
    assert "sorry" not in source



def _synthetic_joined_allreduce(*, rank_count=3, shape=(2, 5, 7)):
    sm = SimpleNamespace(
        step_id="sm:0:0", side="sm", op="FW_linear", rank=0,
        input_bindings=(), input_shapes=(), parameters=(), output_shape=shape,
    )
    contributions = tuple(
        SimpleNamespace(
            step_id=f"pm:{rank}:0", side="pm", op="FW_linear", rank=rank,
            input_bindings=(), input_shapes=(), parameters=(), output_shape=shape,
        )
        for rank in range(rank_count)
    )
    reduce = SimpleNamespace(
        step_id=f"pm:{rank_count}:0", side="pm", op="AllReducePrim", rank=0,
        input_bindings=tuple(step.step_id for step in contributions),
        input_shapes=tuple(step.output_shape for step in contributions),
        parameters=(), output_shape=shape,
    )
    return SimpleNamespace(steps=(sm, *contributions, reduce)), sm, contributions, reduce


def test_ordered_k_rank_allreduce_reconstruction_is_producer_agnostic_and_dynamic():
    plan, sm, contributions, reduce = _synthetic_joined_allreduce(rank_count=3)
    root = (sm.step_id, reduce.step_id)

    certificates, frontiers, layouts = (
        relation_compiler.advance_k_rank_allreduce_reconstruction_frontiers(
            plan, (root,), ("joined",)
        )
    )

    ordered = tuple(step.step_id for step in contributions)
    assert len(certificates) == 1
    certificate = certificates[0]
    assert certificate.rank_count == 3
    assert certificate.full_shape == (2, 5, 7)
    assert certificate.input_fact == relation_compiler.RelationFactSpec(
        "reduction", (sm.step_id, *ordered)
    )
    assert certificate.output_fact == relation_compiler.RelationFactSpec(
        "joined", (sm.step_id,), joined_pm_step=reduce.step_id
    )
    assert frontiers == ((sm.step_id, *ordered),)
    assert layouts == ("reduction",)


def test_ordered_k_rank_allreduce_reconstruction_validates_writer_contracts():
    plan, sm, contributions, reduce = _synthetic_joined_allreduce(rank_count=3)
    reduce.parameters = (1,)
    with pytest.raises(relation_compiler.RelationCompositionError, match="parameters"):
        relation_compiler.advance_k_rank_allreduce_reconstruction_frontiers(
            plan, ((sm.step_id, reduce.step_id),), ("joined",)
        )

    reduce.parameters = ()
    contributions[1].output_shape = (2, 4, 7)
    with pytest.raises(relation_compiler.RelationCompositionError, match="full shapes"):
        relation_compiler.advance_k_rank_allreduce_reconstruction_frontiers(
            plan, ((sm.step_id, reduce.step_id),), ("joined",)
        )


def test_ordered_k_rank_allreduce_reconstruction_is_registered_at_fixed_point():
    plan, sm, contributions, reduce = _synthetic_joined_allreduce(rank_count=4)
    sink = []
    frontiers, layouts = relation_compiler.normalize_relation_frontiers(
        plan,
        ((sm.step_id, reduce.step_id),),
        ("joined",),
        rules=("allreduce_reconstruction_k",),
        certificate_sink=sink,
    )
    assert frontiers == ((sm.step_id, *(step.step_id for step in contributions)),)
    assert layouts == ("reduction",)
    assert [item.rule_id for item in sink] == ["allreduce-reconstruction-k-rank"]


def test_ordered_k_rank_allreduce_transition_owns_only_actual_writer():
    plan, sm, contributions, reduce = _synthetic_joined_allreduce(rank_count=3)
    certificates, _, _ = relation_compiler.advance_k_rank_allreduce_reconstruction_frontiers(
        plan, ((sm.step_id, reduce.step_id),), ("joined",)
    )
    transition = relation_compiler.build_certificate_transition_specs(plan, certificates)[0]
    assert transition.pre_facts == (certificates[0].input_fact,)
    assert transition.post_facts == (certificates[0].output_fact,)
    assert transition.sm_node_indices == ()
    assert transition.pm_node_indices == (3,)
    assert transition.lean_theorem.endswith("ReductionRel.to_joined_allReduce")



def _closed_k_rank_allreduce_fixture(*, rank_count=3, shape=(2, 5, 7)):
    plan, sm, contributions, reduce_step = _synthetic_joined_allreduce(
        rank_count=rank_count, shape=shape
    )
    certificates, _, _ = relation_compiler.advance_k_rank_allreduce_reconstruction_frontiers(
        plan, ((sm.step_id, reduce_step.step_id),), ("joined",)
    )
    certificate = certificates[0]
    transition = relation_compiler.build_certificate_transition_specs(plan, certificates)[0]
    input_tids = tuple(200 + rank for rank in range(rank_count))
    full_tid, joined_tid = 20, 901
    before = SimpleNamespace(
        fact_id="fact_reduction", source=certificate.input_fact, kind="reduction",
        sm_tid=full_tid, pm_tids=input_tids, gather_dim=None,
        full_shape=shape, shard_shape=shape, joined_pm_tid=None,
    )
    after = SimpleNamespace(
        fact_id="fact_joined_reduce", source=certificate.output_fact, kind="joined",
        sm_tid=full_tid, pm_tids=(), gather_dim=None,
        full_shape=shape, shard_shape=shape, joined_pm_tid=joined_tid,
    )
    pre_state = SimpleNamespace(state_id="reduce_pre", fact_ids=("anchor", before.fact_id))
    post_state = SimpleNamespace(state_id="reduce_post", fact_ids=("anchor", after.fact_id))
    segment = SimpleNamespace(
        segment_id="segment_reduce", transition_ids=(transition.transition_id,),
        sm_range=(0, 0), pm_range=(rank_count, rank_count + 1),
        pre_state_id=pre_state.state_id, post_state_id=post_state.state_id,
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(before, after), authority_facts=(),
        anchor_fact=SimpleNamespace(fact_id="anchor", side="sm", tid=77, shape=(1,)),
        states=(pre_state, post_state), segments=(segment,),
    )
    writer = SimpleNamespace(
        rank=0, op="AllReducePrim", ins=list(input_tids), outs=[joined_tid], params=[]
    )
    ir = SimpleNamespace(
        sm_num_ranks=1, pm_num_ranks=rank_count,
        sm_graph_ref="sm_graph", pm_graph_ref="pm_graph", sm_nodes=[],
        pm_nodes=[
            SimpleNamespace(rank=rank, op="FW_linear", ins=[], outs=[200 + rank], params=[])
            for rank in range(rank_count)
        ] + [writer],
    )
    relation = SimpleNamespace(
        certificates=certificates, transition_specs=(transition,), dependent_chain_plan=chain
    )
    return ir, relation, segment, before, after, writer


def test_closed_k_rank_allreduce_renderer_is_exact_and_writer_only():
    ir, relation, segment, before, after, writer = _closed_k_rank_allreduce_fixture(rank_count=3)
    source = render_closed_k_rank_allreduce_segment(ir, relation, segment.segment_id)
    assert source == render_closed_segment(ir, relation, segment.segment_id)
    assert 'List NodeDecl := [{ rank := 0, op := "OpName.AllReducePrim"' in source
    assert "ins := [200, 201, 202]" in source
    assert "params :=" not in source  # canonical NodeDecl omits default empty params
    assert "allReducePrim 3 0" in source
    assert "ReductionRel" in source
    assert "ReductionRel.to_joined_allReduce" in source
    assert f"{before.fact_id}.Holds" in source
    assert f"{after.fact_id}.Holds" in source
    assert "smNodes : List NodeDecl := []" in source


def test_closed_k_rank_allreduce_renderer_rejects_extra_ownership():
    ir, relation, segment, *_ = _closed_k_rank_allreduce_fixture()
    transition = relation.transition_specs[0]
    broken_transition = SimpleNamespace(**{**transition.__dict__, "sm_node_indices": (0,)})
    broken = SimpleNamespace(**{**relation.__dict__, "transition_specs": (broken_transition,)})
    with pytest.raises(ValueError, match="exact PM AllReduce writer"):
        render_closed_k_rank_allreduce_segment(ir, broken, segment.segment_id)




def test_closed_k_rank_allreduce_selects_exact_typed_transition_certificate():
    ir, relation, segment, *_ = _closed_k_rank_allreduce_fixture()
    expected = render_closed_segment(ir, relation, segment.segment_id)
    exact = relation.certificates[0]
    unrelated = replace(
        exact,
        input_fact=relation_compiler.RelationFactSpec(
            "reduction", ("sm:99:0", "pm:99:0", "pm:100:0")
        ),
    )
    foreign = SimpleNamespace(
        rule_id=exact.rule_id,
        lean_theorem=exact.lean_theorem,
        input_fact=exact.input_fact,
        output_fact=exact.output_fact,
    )
    with_unrelated = SimpleNamespace(
        **{
            **relation.__dict__,
            "certificates": (unrelated, foreign, exact),
        }
    )

    assert render_closed_segment(ir, with_unrelated, segment.segment_id) == expected


def test_closed_k_rank_allreduce_rejects_malformed_or_duplicate_exact_certificate():
    ir, relation, segment, *_ = _closed_k_rank_allreduce_fixture()
    exact = relation.certificates[0]
    malformed = replace(
        exact,
        output_fact=relation_compiler.RelationFactSpec(
            "joined", ("sm:99:0",), joined_pm_step="pm:99:0"
        ),
    )

    with pytest.raises(ValueError, match="one exact typed certificate"):
        render_closed_segment(
            ir,
            SimpleNamespace(**{**relation.__dict__, "certificates": (malformed,)}),
            segment.segment_id,
        )

    with pytest.raises(ValueError, match="one exact typed certificate"):
        render_closed_segment(
            ir,
            SimpleNamespace(**{**relation.__dict__, "certificates": (exact, exact)}),
            segment.segment_id,
        )

def test_generated_allreduce_segment_witness_is_exact_renderer_output():
    ir, relation, segment, *_ = _closed_k_rank_allreduce_fixture(rank_count=3)
    namespace = "GeneratedKRankAllReduceSegmentWitness"
    declarations = render_closed_relation_declarations(
        relation.dependent_chain_plan, namespace
    )
    rendered = render_closed_segment(ir, relation, segment.segment_id)
    pm_nodes = (
        '[{ rank := 0, op := "OpName.FW_linear", ins := [], outs := [200] }, '
        '{ rank := 1, op := "OpName.FW_linear", ins := [], outs := [201] }, '
        '{ rank := 2, op := "OpName.FW_linear", ins := [], outs := [202] }, '
        '{ rank := 0, op := "OpName.AllReducePrim", '
        'ins := [200, 201, 202], outs := [901] }]'
    )
    source = "\n".join((
        declarations,
        f"namespace TrainVerify.Denote.{namespace}",
        "noncomputable section",
        "private def sm_graph : GraphDecl := { numRanks := 1, nodes := [] }",
        f"private def pm_graph : GraphDecl := {{ numRanks := 3, nodes := {pm_nodes} }}",
        rendered,
        f"#print axioms {segment.segment_id}",
        "end",
        f"end TrainVerify.Denote.{namespace}",
        "",
    ))
    witness = (
        Path(__file__).resolve().parents[2]
        / "trainverify/denote/GeneratedKRankAllReduceSegmentWitness.lean"
    )
    assert witness.read_text() == source
    assert rendered == render_closed_k_rank_allreduce_segment(
        ir, relation, segment.segment_id
    )
    assert "sorry" not in source
