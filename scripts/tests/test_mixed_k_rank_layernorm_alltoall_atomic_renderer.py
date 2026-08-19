from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import render_closed_segment
from trainverify.bridge_emitter.parser import Node


LAYERNORM_RULE = "layernorm-sharded-k-rank-dim1"
ALLTOALL_RULE = "alltoall-k-rank-layout-transport"
LAYERNORM_THEOREM = (
    "TrainVerify.Denote."
    "fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d"
)
ALLTOALL_THEOREM = (
    "TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn"
)


def _fixture(k=4, *, segment_id="segment_000092"):
    sm_index = 54
    pm_start = 338
    if k == 4:
        # Real segment 92: rank authority and graph authority interleave.
        layer_pm_indices = (338, 339, 340, 344)
        alltoall_pm_indices = (341, 342, 343, 345)
    else:
        layer_pm_indices = tuple(pm_start + rank for rank in range(k - 1)) + (pm_start + 2 * k - 2,)
        alltoall_pm_indices = tuple(pm_start + k - 1 + rank for rank in range(k - 1)) + (pm_start + 2 * k - 1,)
    input_pm_tids = tuple(200 + rank for rank in range(k))
    alltoall_input_pm_tids = tuple(220 + rank for rank in range(k))
    layer_pm_tids = tuple(300 + rank for rank in range(k))
    output_pm_tids = tuple(400 + rank for rank in range(k))
    full_shape = (4, 3 * k, 2 * k)
    input_shard_shape = (4, 3, 2 * k)
    output_shard_shape = (4, 3 * k, 2)

    input_spec = rc.RelationFactSpec(
        "sharded",
        ("sm:53:0", *(f"pm:{334 + rank}:0" for rank in range(k))),
        gather_dim=1,
    )
    alltoall_input_spec = rc.RelationFactSpec(
        "sharded",
        ("sm:53:1", *(f"pm:{334 + rank}:1" for rank in range(k))),
        gather_dim=1,
    )
    layer_spec = rc.RelationFactSpec(
        "sharded",
        (f"sm:{sm_index}:0", *(f"pm:{index}:0" for index in layer_pm_indices)),
        gather_dim=1,
    )
    output_spec = rc.RelationFactSpec(
        "sharded",
        ("sm:53:1", *(f"pm:{index}:0" for index in alltoall_pm_indices)),
        gather_dim=2,
    )
    layer_cert = rc.KRankLocalRelationCertificate(
        LAYERNORM_RULE,
        "FW_layernorm",
        k,
        1,
        input_spec,
        layer_spec,
        f"sm:{sm_index}:0",
        tuple(f"pm:{index}:0" for index in layer_pm_indices),
        (91, 92),
        ((2 * k,), (2 * k,)),
        LAYERNORM_THEOREM,
    )
    alltoall_cert = rc.KRankAllToAllRelationCertificate(
        ALLTOALL_RULE,
        k,
        1,
        2,
        alltoall_input_spec,
        output_spec,
        tuple(f"pm:{index}:0" for index in alltoall_pm_indices),
        ALLTOALL_THEOREM,
    )
    transitions = rc.build_certificate_transition_specs(
        SimpleNamespace(), (layer_cert, alltoall_cert)
    )

    input_fact = rc.ClosedRelationFactRecord(
        "fact_input",
        input_spec,
        "sharded",
        100,
        input_pm_tids,
        None,
        None,
        full_shape,
        input_shard_shape,
        gather_dim=1,
    )
    alltoall_input_fact = rc.ClosedRelationFactRecord(
        "fact_alltoall_input",
        alltoall_input_spec,
        "sharded",
        120,
        alltoall_input_pm_tids,
        None,
        None,
        full_shape,
        input_shard_shape,
        gather_dim=1,
    )
    layer_fact = rc.ClosedRelationFactRecord(
        "fact_layer",
        layer_spec,
        "sharded",
        110,
        layer_pm_tids,
        None,
        None,
        full_shape,
        input_shard_shape,
        gather_dim=1,
    )
    output_fact = rc.ClosedRelationFactRecord(
        "fact_output",
        output_spec,
        "sharded",
        120,
        output_pm_tids,
        None,
        None,
        full_shape,
        output_shard_shape,
        gather_dim=2,
    )
    gamma_eq = rc.ClosedTensorEqFactRecord(
        "gamma_eq", "pm", 91, "sm", 91
    )
    gamma_shape = rc.ClosedTensorShapeFactRecord(
        "gamma_shape", "pm", 91, (2 * k,), 91
    )
    beta_eq = rc.ClosedTensorEqFactRecord(
        "beta_eq", "sm", 92, "pm", 92
    )
    beta_shape = rc.ClosedTensorShapeFactRecord(
        "beta_shape", "pm", 92, (2 * k,), 92
    )
    before = rc.ClosedRelationStateRecord(
        "state_pre",
        (
            input_fact.fact_id,
            alltoall_input_fact.fact_id,
            gamma_eq.fact_id,
            gamma_shape.fact_id,
            beta_eq.fact_id,
            beta_shape.fact_id,
        ),
    )
    after = rc.ClosedRelationStateRecord(
        "state_post", (layer_fact.fact_id, output_fact.fact_id)
    )
    segment = rc.ClosedDependentSegmentRecord(
        segment_id,
        "component_layernorm_alltoall",
        before.state_id,
        after.state_id,
        tuple(transition.transition_id for transition in transitions),
        (sm_index, sm_index + 1),
        (pm_start, pm_start + 2 * k),
    )
    chain = SimpleNamespace(
        complete=True,
        segments=(segment,),
        states=(before, after),
        relation_facts=(input_fact, alltoall_input_fact, layer_fact, output_fact),
        authority_facts=(gamma_eq, gamma_shape, beta_eq, beta_shape),
    )

    filler = Node(0, "FW_identity", [900], [901], [])
    sm_nodes = [filler for _ in range(sm_index)]
    sm_nodes.append(Node(0, "FW_layernorm", [100, 91, 92], [110], []))
    pm_nodes = [filler for _ in range(pm_start)]
    pm_nodes.extend(filler for _ in range(2 * k))
    for rank, index in enumerate(layer_pm_indices):
        pm_nodes[index] = Node(
            rank, "FW_layernorm", [input_pm_tids[rank], 91, 92],
            [layer_pm_tids[rank]], []
        )
    for rank, index in enumerate(alltoall_pm_indices):
        pm_nodes[index] = Node(
            rank, "AllToAllPrim", list(alltoall_input_pm_tids),
            [output_pm_tids[rank]], [1, 2]
        )
    ir = SimpleNamespace(
        sm_nodes=sm_nodes,
        pm_nodes=pm_nodes,
        sm_num_ranks=1,
        pm_num_ranks=k,
        sm_graph_ref="SyntheticMixedLayernormAllToAll.gSM",
        pm_graph_ref="SyntheticMixedLayernormAllToAll.gPM",
    )
    relation = SimpleNamespace(
        dependent_chain_plan=chain,
        transition_specs=transitions,
        certificates=(layer_cert, alltoall_cert),
    )
    return ir, relation, segment


@pytest.mark.parametrize("k", (2, 4))
def test_mixed_layernorm_alltoall_is_one_dynamic_atomic_fold_per_axis(k):
    ir, relation, segment = _fixture(k, segment_id="dynamic_component")

    source = render_closed_segment(ir, relation, segment.segment_id)

    assert "private def dynamic_component :" in source
    assert "segment_000092" not in source
    assert source.count("let smFinal := smNodes.foldl") == 1
    assert source.count("let pmFinal := pmNodes.foldl") == 1
    assert source.count("foldl_faithful_middle_writer") == 1 + 2 * k
    assert source.count('op := "OpName.FW_layernorm"') >= 1 + k
    assert source.count('op := "OpName.AllToAllPrim"') >= k
    assert LAYERNORM_THEOREM in source
    assert ALLTOALL_THEOREM in source
    assert (
        "K := [" + ", ".join(f"pmStore {200 + rank}" for rank in range(k))
        + "].length"
    ) in source
    assert f"rankCount = {k}" not in source
    assert "have hLayerIn" in source and "have hAllToAllIn" in source
    assert "have hLayerOut" in source and "have hFinalOut" in source
    assert "have hRankXs : rankCount = xs.length" in source
    assert "rw [hRankXs] at hOdimXs hDivXs" in source
    assert "[pmStore 220" in source
    assert 'ins := [300, 301' not in source
    assert "rcases fresh with rfl | rfl" in source


def _witness(source):
    return f"""import denote.RelationCompiler
import denote.KRankLayernormGather
import denote.KRankAllToAll

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticMixedLayernormAllToAll
noncomputable section
set_option maxHeartbeats 1000000

def gSM : GraphDecl := {{ numRanks := 1, nodes := [] }}
def gPM : GraphDecl := {{ numRanks := 4, nodes := [] }}
def fact_input : RelationFact :=
  .sharded 100 [200, 201, 202, 203] 1 [4, 12, 8] [4, 3, 8]
def fact_alltoall_input : RelationFact :=
  .sharded 120 [220, 221, 222, 223] 1 [4, 12, 8] [4, 3, 8]
def fact_layer : RelationFact :=
  .sharded 110 [300, 301, 302, 303] 1 [4, 12, 8] [4, 3, 8]
def fact_output : RelationFact :=
  .sharded 120 [400, 401, 402, 403] 2 [4, 12, 8] [4, 12, 2]
def gamma_eq : RelationFact := .tensorEq .pm 91 .sm 91
def gamma_shape : RelationFact := .tensorShape .pm 91 [8]
def beta_eq : RelationFact := .tensorEq .sm 92 .pm 92
def beta_shape : RelationFact := .tensorShape .pm 92 [8]
def state_pre : RelationState where
  facts := [fact_input, fact_alltoall_input, gamma_eq, gamma_shape, beta_eq, beta_shape]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_layer, fact_output]
  nonempty := by decide

{source}
#print axioms segment_000092
end
end SyntheticMixedLayernormAllToAll
end TrainVerify.Denote
"""


def test_generated_mixed_layernorm_alltoall_witness_is_exact_renderer_output():
    ir, relation, segment = _fixture()
    source = _witness(render_closed_segment(ir, relation, segment.segment_id))
    path = (
        Path(__file__).parents[2]
        / "trainverify/denote/GeneratedMixedKRankLayernormAllToAllAtomicWitness.lean"
    )
    path.write_text(source, encoding="utf-8")
    assert path.read_text(encoding="utf-8") == source
    assert "sorry" not in source


@pytest.mark.parametrize(
    "tamper",
    (
        "duplicate-certificate",
        "duplicate-transition",
        "transition-class",
        "transition-rule",
        "transition-theorem",
        "transition-pre",
        "transition-post",
        "transition-authority",
        "footprint",
        "footprint-order",
        "component",
        "writer-role",
        "writer-rank",
        "writer-params",
        "writer-output",
        "state",
        "state-extra",
        "authority",
    ),
)
def test_mixed_layernorm_alltoall_rejects_tampering(tamper):
    ir, relation, segment = _fixture()
    if tamper == "duplicate-certificate":
        relation.certificates = (*relation.certificates, relation.certificates[0])
    elif tamper == "duplicate-transition":
        relation.transition_specs = (
            *relation.transition_specs,
            relation.transition_specs[0],
        )
    elif tamper == "transition-class":
        relation.transition_specs = (
            replace(
                relation.transition_specs[0],
                transition_id=relation.transition_specs[0].transition_id.replace(
                    "KRankLocalRelationCertificate",
                    "KRankAllToAllRelationCertificate",
                ),
            ),
            relation.transition_specs[1],
        )
        relation.dependent_chain_plan.segments = (
            replace(
                segment,
                transition_ids=(
                    relation.transition_specs[0].transition_id,
                    relation.transition_specs[1].transition_id,
                ),
            ),
        )
    elif tamper == "transition-rule":
        relation.transition_specs = (
            replace(relation.transition_specs[0], rule_id="other-rule"),
            relation.transition_specs[1],
        )
    elif tamper == "transition-theorem":
        relation.transition_specs = (
            replace(relation.transition_specs[0], lean_theorem="Other.theorem"),
            relation.transition_specs[1],
        )
    elif tamper == "transition-pre":
        relation.transition_specs = (
            replace(
                relation.transition_specs[0],
                pre_facts=(relation.transition_specs[0].post_facts[0],),
            ),
            relation.transition_specs[1],
        )
    elif tamper == "transition-post":
        relation.transition_specs = (
            relation.transition_specs[0],
            replace(
                relation.transition_specs[1],
                post_facts=(relation.transition_specs[1].pre_facts[0],),
            ),
        )
    elif tamper == "transition-authority":
        relation.transition_specs = (
            replace(relation.transition_specs[0], authority_requirements=()),
            relation.transition_specs[1],
        )
    elif tamper == "footprint":
        relation.transition_specs = (
            replace(
                relation.transition_specs[0],
                pm_node_indices=(
                    *relation.transition_specs[0].pm_node_indices,
                    relation.transition_specs[0].pm_node_indices[0],
                ),
            ),
            relation.transition_specs[1],
        )
    elif tamper == "footprint-order":
        relation.transition_specs = (
            replace(
                relation.transition_specs[0],
                pm_node_indices=tuple(
                    reversed(relation.transition_specs[0].pm_node_indices)
                ),
            ),
            relation.transition_specs[1],
        )
    elif tamper == "component":
        relation.dependent_chain_plan.segments = (
            replace(segment, pm_range=(segment.pm_range[0], segment.pm_range[1] - 1)),
        )
    elif tamper == "writer-role":
        ir.sm_nodes[segment.sm_range[0]].ins[1:] = [92, 91]
    elif tamper == "writer-rank":
        ir.pm_nodes[segment.pm_range[0]].rank = 3
    elif tamper == "writer-params":
        ir.pm_nodes[segment.pm_range[0] + 4].params = [0, 1]
    elif tamper == "writer-output":
        ir.pm_nodes[segment.pm_range[0] + 4].outs = [999]
    elif tamper == "state":
        relation.dependent_chain_plan.states = (
            relation.dependent_chain_plan.states[0],
            replace(relation.dependent_chain_plan.states[1], fact_ids=("fact_layer",)),
        )
    elif tamper == "state-extra":
        relation.dependent_chain_plan.states = (
            relation.dependent_chain_plan.states[0],
            replace(
                relation.dependent_chain_plan.states[1],
                fact_ids=("fact_output", "unknown_fact"),
            ),
        )
    else:
        relation.dependent_chain_plan.authority_facts = (
            *relation.dependent_chain_plan.authority_facts,
            relation.dependent_chain_plan.authority_facts[0],
        )

    with pytest.raises(ValueError):
        render_closed_segment(ir, relation, segment.segment_id)


def test_mixed_layernorm_alltoall_rejects_zero_rank_authority():
    ir, relation, segment = _fixture()
    records = relation.dependent_chain_plan.relation_facts
    relation.dependent_chain_plan.relation_facts = tuple(
        replace(record, pm_tids=()) for record in records
    )

    with pytest.raises(ValueError):
        render_closed_segment(ir, relation, segment.segment_id)


def test_mixed_layernorm_alltoall_rejects_duplicate_rank_authority():
    ir, relation, segment = _fixture()
    records = relation.dependent_chain_plan.relation_facts
    relation.dependent_chain_plan.relation_facts = (
        replace(records[0], pm_tids=(200, 200, 202, 203)),
        *records[1:],
    )

    with pytest.raises(ValueError):
        render_closed_segment(ir, relation, segment.segment_id)
