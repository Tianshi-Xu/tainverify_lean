from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import composer
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.parser import Node


def _source(step_id, *, side, rank, shape):
    return SimpleNamespace(
        step_id=step_id,
        side=side,
        node_index=-1,
        rank=rank,
        op="Source",
        input_bindings=(),
        input_shapes=(),
        output_shape=shape,
        parameters=(),
    )


def _swap_axes(shape, dim0, dim1):
    if dim0 >= len(shape) or dim1 >= len(shape):
        return tuple(shape)
    values = list(shape)
    values[dim0], values[dim1] = values[dim1], values[dim0]
    return tuple(values)


def _transpose_fixture(k=3, *, output_full_shape=None, output_shard_shape=None, params=(1, 2)):
    output_shard_shape = output_shard_shape or (2, 3, 4, 5)
    output_full_shape = output_full_shape or (2, 3 * k, 4, 5)
    input_full_shape = _swap_axes(output_full_shape, *params)
    input_shard_shape = _swap_axes(output_shard_shape, *params)
    sm_input = _source("sm:9:0", side="sm", rank=0, shape=input_full_shape)
    pm_inputs = tuple(
        _source(f"pm:{19 + rank}:0", side="pm", rank=rank, shape=input_shard_shape)
        for rank in range(k)
    )
    sm_writer = SimpleNamespace(
        step_id="sm:10:0", side="sm", node_index=10, rank=0,
        op="FW_transpose", input_bindings=(sm_input.step_id,),
        input_shapes=(input_full_shape,), output_shape=output_full_shape, parameters=params,
    )
    pm_writers = tuple(
        SimpleNamespace(
            step_id=f"pm:{30 + rank}:0", side="pm", node_index=30 + rank,
            rank=rank, op="FW_transpose",
            input_bindings=(pm_inputs[rank].step_id,),
            input_shapes=(input_shard_shape,), output_shape=output_shard_shape,
            parameters=params,
        )
        for rank in range(k)
    )
    plan = SimpleNamespace(steps=(sm_input, *pm_inputs, sm_writer, *pm_writers))
    frontier = (sm_writer.step_id, *(step.step_id for step in pm_writers))
    return plan, frontier, sm_writer, pm_writers


@pytest.mark.parametrize(
    ("k", "output_full", "output_shard", "params", "output_dim", "input_dim", "lean_theorem"),
    [
        (3, (2, 9, 4, 5), (2, 3, 4, 5), (1, 2), 1, 2, "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4"),
        (4, (1, 1024, 12, 64), (1, 1024, 12, 16), (1, 2), 3, 3, "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim3_rank4"),
        (4, (1, 1024, 12, 64), (1, 256, 12, 64), (1, 2), 1, 2, "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4"),
        (4, (1, 1024, 12, 64), (1, 1024, 3, 64), (1, 2), 2, 1, "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim1_to_dim2_rank4"),
        (3, (2, 4, 5, 9), (2, 4, 5, 3), (2, 3), 3, 2, "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4"),
        (3, (2, 4, 15, 3), (2, 4, 5, 3), (2, 3), 2, 3, "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4"),
        (3, (2, 12, 5, 7), (2, 4, 5, 7), (2, 3), 1, 1, "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4"),
    ],
)
def test_sharded_transpose_matcher_is_dynamic_and_derives_inverse_relation(
    k, output_full, output_shard, params, output_dim, input_dim, lean_theorem
):
    plan, frontier, sm_writer, pm_writers = _transpose_fixture(
        k, output_full_shape=output_full, output_shard_shape=output_shard, params=params
    )

    certs, frontiers, layouts = rc.advance_k_rank_transpose_relation_frontiers(
        plan, (frontier,), ("sharded",)
    )

    assert len(certs) == 1
    cert = certs[0]
    assert cert.rule_id == "transpose-sharded-k-rank"
    assert cert.rank_count == k
    assert cert.parameters == params
    assert cert.lean_theorem == lean_theorem
    assert cert.output_gather_dim == output_dim
    assert cert.input_gather_dim == input_dim
    assert cert.output_full_shape == output_full
    assert cert.output_shard_shape == output_shard
    assert cert.input_full_shape == _swap_axes(output_full, *params)
    assert cert.input_shard_shape == _swap_axes(output_shard, *params)
    assert cert.sm_step_id == sm_writer.step_id
    assert cert.pm_step_ids == tuple(step.step_id for step in pm_writers)
    assert cert.input_fact == rc.RelationFactSpec(
        "sharded", ("sm:9:0", *(f"pm:{19 + rank}:0" for rank in range(k))),
        gather_dim=input_dim,
    )
    assert cert.output_fact == rc.RelationFactSpec("sharded", frontier, gather_dim=output_dim)
    assert frontiers == (cert.input_fact.step_triple,)
    assert layouts == ("sharded",)


def test_sharded_transpose_normalization_reaches_fixed_point_and_transition_is_exact_1xk():
    plan0, frontier0, sm0, pm0 = _transpose_fixture(3)
    input_full = tuple(sm0.input_shapes[0])
    input_shard = tuple(pm0[0].input_shapes[0])
    sm1 = SimpleNamespace(**{
        **sm0.__dict__, "step_id": "sm:11:0", "node_index": 11,
        "input_bindings": (sm0.step_id,), "input_shapes": (sm0.output_shape,),
        "output_shape": input_full,
    })
    pm1 = tuple(
        SimpleNamespace(**{
            **step.__dict__, "step_id": f"pm:{40 + rank}:0", "node_index": 40 + rank,
            "input_bindings": (pm0[rank].step_id,), "input_shapes": (step.output_shape,),
            "output_shape": input_shard,
        })
        for rank, step in enumerate(pm0)
    )
    plan = SimpleNamespace(steps=(*plan0.steps, sm1, *pm1))
    sink = []

    frontiers, layouts = rc.normalize_relation_frontiers(
        plan, ((sm1.step_id, *(step.step_id for step in pm1)),), ("sharded",),
        rules=("transpose_k",), certificate_sink=sink,
    )

    assert frontiers == (("sm:9:0", "pm:19:0", "pm:20:0", "pm:21:0"),)
    assert layouts == ("sharded",)
    assert len(sink) == 2
    transitions = rc.build_certificate_transition_specs(plan, tuple(sink))
    assert {(item.sm_node_indices, item.pm_node_indices) for item in transitions} == {
        ((10,), (30, 31, 32)), ((11,), (40, 41, 42)),
    }
    assert all(item.pre_facts == (cert.input_fact,) for item, cert in zip(transitions, sink))
    assert all(item.post_facts == (cert.output_fact,) for item, cert in zip(transitions, sink))


@pytest.mark.parametrize(
    ("target", "mutation", "message"),
    [
        ("pm", {"parameters": (2, 3)}, "matching parameters"),
        ("pm", {"parameters": (1,)}, "exactly two parameters"),
        ("pm", {"input_bindings": ("pm:19:0", "pm:18:0")}, "unary"),
        ("pm", {"input_shapes": ((2, 5, 3),)}, "declared input shape"),
        ("pm", {"output_shape": (2, 4, 3)}, "transpose output shape"),
        ("sm", {"output_shape": (2, 8, 4)}, "transpose output shape"),
    ],
)
def test_sharded_transpose_matcher_fails_closed_on_inexact_authority(target, mutation, message):
    plan, frontier, sm_writer, pm_writers = _transpose_fixture(3)
    if target == "sm":
        bad = SimpleNamespace(**{**sm_writer.__dict__, **mutation})
        steps = tuple(bad if step is sm_writer else step for step in plan.steps)
    else:
        bad = SimpleNamespace(**{**pm_writers[0].__dict__, **mutation})
        steps = tuple(bad if step is pm_writers[0] else step for step in plan.steps)
    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_k_rank_transpose_relation_frontiers(
            SimpleNamespace(steps=steps), (frontier,), ("sharded",)
        )


def test_sharded_transpose_matcher_rejects_reordered_pm_writers():
    plan, frontier, *_ = _transpose_fixture(3)
    with pytest.raises(rc.RelationCompositionError, match="ordered ranks"):
        rc.advance_k_rank_transpose_relation_frontiers(
            plan, ((frontier[0], frontier[2], frontier[1], frontier[3]),), ("sharded",)
        )


def test_sharded_transpose_matcher_fails_closed_on_unchecked_axis_pair():
    plan, frontier, *_ = _transpose_fixture(
        3,
        output_full_shape=(6, 4, 5, 7),
        output_shard_shape=(2, 4, 5, 7),
        params=(0, 1),
    )
    with pytest.raises(rc.RelationCompositionError, match="checked axis pair"):
        rc.advance_k_rank_transpose_relation_frontiers(
            plan, (frontier,), ("sharded",)
        )


def test_sharded_transpose_matcher_rejects_reverse_3_2_axis_order():
    plan, frontier, *_ = _transpose_fixture(
        3,
        output_full_shape=(2, 4, 15, 3),
        output_shard_shape=(2, 4, 5, 3),
        params=(3, 2),
    )
    with pytest.raises(rc.RelationCompositionError, match="checked axis pair"):
        rc.advance_k_rank_transpose_relation_frontiers(plan, (frontier,), ("sharded",))


@pytest.mark.parametrize(
    ("full", "shard", "message"),
    [
        ((2, 6, 12), (2, 3, 4), "one output gather dimension"),
        ((2, 9, 4), (2, 3, 5), "one output gather dimension"),
        ((8,), (2,), "legal axes"),
    ],
)
def test_sharded_transpose_matcher_rejects_ambiguous_or_incompatible_shapes(full, shard, message):
    plan, frontier, *_ = _transpose_fixture(3, output_full_shape=full, output_shard_shape=shard)
    with pytest.raises(rc.RelationCompositionError, match=message):
        rc.advance_k_rank_transpose_relation_frontiers(plan, (frontier,), ("sharded",))



def _closed_fixture(
    k=3, *, output_full=(2, 9, 4, 5), output_shard=(2, 3, 4, 5), params=(1, 2)
):
    plan, frontier, _, _ = _transpose_fixture(
        k, output_full_shape=output_full, output_shard_shape=output_shard, params=params
    )
    cert = rc.advance_k_rank_transpose_relation_frontiers(
        plan, (frontier,), ("sharded",)
    )[0][0]
    input_tids = tuple(200 + rank for rank in range(k))
    output_tids = tuple(300 + rank for rank in range(k))
    input_fact = replace(
        cert.input_fact,
        step_triple=("init:100", *(f"init:{tid}" for tid in input_tids)),
    )
    output_fact = replace(
        cert.output_fact,
        step_triple=("sm:0:0", *(f"pm:{rank}:0" for rank in range(k))),
    )
    cert = replace(
        cert, input_fact=input_fact, output_fact=output_fact,
        sm_step_id="sm:0:0", pm_step_ids=tuple(f"pm:{rank}:0" for rank in range(k)),
    )
    transition = rc.build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    pre = rc.ClosedRelationFactRecord(
        "fact_in", input_fact, "sharded", 100, input_tids, None, None,
        cert.input_full_shape, cert.input_shard_shape, cert.input_gather_dim,
    )
    post = rc.ClosedRelationFactRecord(
        "fact_out", output_fact, "sharded", 110, output_tids, None, None,
        cert.output_full_shape, cert.output_shard_shape, cert.output_gather_dim,
    )
    before = SimpleNamespace(state_id="state_pre", fact_ids=(pre.fact_id,))
    after = SimpleNamespace(state_id="state_post", fact_ids=(post.fact_id,))
    segment = SimpleNamespace(
        segment_id="segment_000000", transition_ids=(transition.transition_id,),
        sm_range=(0, 1), pm_range=(0, k),
        pre_state_id=before.state_id, post_state_id=after.state_id,
    )
    chain = SimpleNamespace(
        complete=True, relation_facts=(pre, post), authority_facts=(),
        states=(before, after), segments=(segment,),
    )
    params = list(cert.parameters)
    sm_node = Node(0, "FW_transpose", [100], [110], params)
    pm_nodes = [
        Node(rank, "FW_transpose", [input_tids[rank]], [output_tids[rank]], params)
        for rank in range(k)
    ]
    ir = SimpleNamespace(
        sm_nodes=[sm_node], pm_nodes=pm_nodes,
        sm_num_ranks=1, pm_num_ranks=k,
        sm_graph_ref="SyntheticTranspose.gSM", pm_graph_ref="SyntheticTranspose.gPM",
    )
    relation = SimpleNamespace(
        certificates=(cert,), transition_specs=(transition,), dependent_chain_plan=chain,
    )
    return ir, relation, segment, pre, post


def test_closed_sharded_transpose_renderer_replays_exact_ordered_writers():
    ir, relation, segment, pre, post = _closed_fixture(k=3)
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert source == composer.render_closed_k_rank_transpose_segment(
        ir, relation, segment.segment_id
    )
    assert source.count('op := "OpName.FW_transpose"') == 4
    assert source.count("foldl_faithful_middle_writer") == 4
    assert source.count("applyNode_fw_transposeAxes_out") == 4
    assert "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4 hin" in source
    assert "transposeAxes 1 2" in source
    assert f"[pmStore {pre.pm_tids[0]}, pmStore {pre.pm_tids[1]}, pmStore {pre.pm_tids[2]}]" in source
    assert f"[pmFinal {post.pm_tids[0]}, pmFinal {post.pm_tids[1]}, pmFinal {post.pm_tids[2]}]" in source
    assert "rankCount = 3" not in source


def test_closed_sharded_transpose_selector_ignores_unrelated_same_family_certificate():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    expected = composer.render_closed_segment(ir, relation, segment.segment_id)
    exact = relation.certificates[0]
    unrelated = tuple(
        replace(
            exact,
            input_fact=replace(
                exact.input_fact,
                step_triple=(f"init:{900 + index}", *exact.input_fact.step_triple[1:]),
            ),
        )
        for index in range(60)
    )
    relation.certificates = (*unrelated, exact)

    assert composer.render_closed_segment(ir, relation, segment.segment_id) == expected


@pytest.mark.parametrize("mutation", ["malformed", "duplicate"])
def test_closed_sharded_transpose_selector_rejects_nonunique_exact_certificate(mutation):
    ir, relation, segment, *_ = _closed_fixture(k=3)
    exact = relation.certificates[0]
    if mutation == "malformed":
        malformed = replace(
            exact,
            output_fact=replace(exact.output_fact, step_triple=("sm:999:0", *exact.output_fact.step_triple[1:])),
        )
        relation.certificates = (malformed,)
    else:
        relation.certificates = (exact, exact)

    with pytest.raises(ValueError, match="requires one exact typed certificate"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def test_closed_sharded_transpose_selector_rejects_unknown_transition_theorem():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    unknown = "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_unknown"
    relation.transition_specs = (replace(relation.transition_specs[0], lean_theorem=unknown),)
    relation.certificates = (replace(relation.certificates[0], lean_theorem=unknown),)

    with pytest.raises(ValueError, match="no checked axis-specific theorem"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


@pytest.mark.parametrize(
    ("output_full", "output_shard", "theorem"),
    [
        ((2, 4, 5, 9), (2, 4, 5, 3), "fw_transposeAxes_2_3_dim2_to_dim3_rank4"),
        ((2, 4, 15, 3), (2, 4, 5, 3), "fw_transposeAxes_2_3_dim3_to_dim2_rank4"),
        ((2, 12, 5, 7), (2, 4, 5, 7), "fw_transposeAxes_2_3_dim1_rank4"),
    ],
)
def test_closed_sharded_transpose_renderer_supports_all_2_3_families(
    output_full, output_shard, theorem
):
    ir, relation, segment, *_ = _closed_fixture(
        output_full=output_full, output_shard=output_shard, params=(2, 3)
    )
    source = composer.render_closed_segment(ir, relation, segment.segment_id)
    assert f"TrainVerify.Denote.RelationCompiler.ShardedRel.{theorem} hin" in source
    assert "transposeAxes 2 3" in source
    assert source.count("applyNode_fw_transposeAxes_out") == 4


def test_closed_transpose_bundle_imports_exact_theorem_module():
    family = ("transpose-sharded-k-rank",)
    assert composer._closed_segment_family_imports(
        family,
        ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim3_rank4",),
    ) == ("denote.KRankTranspose",)
    assert composer._closed_segment_family_imports(
        family,
        ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4",),
    ) == ("denote.KRankTranspose23Extra",)


def test_closed_sharded_transpose_renderer_rejects_tampered_live_writer():
    ir, relation, segment, *_ = _closed_fixture(k=3)
    ir.pm_nodes[1].params = [2, 3]
    with pytest.raises(ValueError, match="matching parameters"):
        composer.render_closed_segment(ir, relation, segment.segment_id)


def _witness_namespace(namespace, output_full, output_shard):
    ir, relation, segment, pre, post = _closed_fixture(
        k=3, output_full=output_full, output_shard=output_shard, params=(2, 3)
    )
    ir.sm_graph_ref = f"{namespace}.gSM"
    ir.pm_graph_ref = f"{namespace}.gPM"
    rendered = composer.render_closed_segment(ir, relation, segment.segment_id)
    return f'''namespace {namespace}
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := "OpName.FW_transpose", ins := [100], outs := [110], params := [2, 3] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := "OpName.FW_transpose", ins := [200], outs := [300], params := [2, 3] }}, {{ rank := 1, op := "OpName.FW_transpose", ins := [201], outs := [301], params := [2, 3] }}, {{ rank := 2, op := "OpName.FW_transpose", ins := [202], outs := [302], params := [2, 3] }}] }}

def fact_in : RelationFact := .sharded 100 [200, 201, 202] {pre.gather_dim} {list(pre.full_shape)} {list(pre.shard_shape)}
def fact_out : RelationFact := .sharded 110 [300, 301, 302] {post.gather_dim} {list(post.full_shape)} {list(post.shard_shape)}
def state_pre : RelationState where
  facts := [fact_in]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

{rendered}
#print axioms segment_000000
end
end {namespace}
'''


def _witness_source():
    families = (
        ("SyntheticTranspose23Dim2To3", (2, 4, 5, 9), (2, 4, 5, 3)),
        ("SyntheticTranspose23Dim3To2", (2, 4, 15, 3), (2, 4, 5, 3)),
        ("SyntheticTranspose23Dim1", (2, 12, 5, 7), (2, 4, 5, 7)),
    )
    bodies = "\n".join(_witness_namespace(*family) for family in families)
    return f'''import denote.KRankTranspose23Extra

namespace TrainVerify.Denote
open RelationCompiler

{bodies}
end TrainVerify.Denote
'''


def test_generated_sharded_transpose_witness_is_exact_renderer_output():
    source = _witness_source()
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedShardedTransposeWitness.lean"
    witness.unlink(missing_ok=True)
    witness.write_text(source, encoding="utf-8")
    assert witness.read_text(encoding="utf-8") == source
    assert source.count("import denote.KRankTranspose23Extra") == 1
    assert source.count('op := "OpName.FW_transpose"') == 24
    assert source.count("applyNode_fw_transposeAxes_out") == 12
    assert source.count("#print axioms segment_000000") == 3
    assert "fw_transposeAxes_2_3_dim2_to_dim3_rank4 hin" in source
    assert "fw_transposeAxes_2_3_dim3_to_dim2_rank4 hin" in source
    assert "fw_transposeAxes_2_3_dim1_rank4 hin" in source
    assert "SyntheticTranspose.gSM" not in source
    assert "SyntheticTranspose.gPM" not in source
    assert "sorry" not in source
