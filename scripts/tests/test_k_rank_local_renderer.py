from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter.composer import render_closed_segment
from trainverify.bridge_emitter.parser import Node
from trainverify.bridge_emitter.relation_compiler import (
    ClosedRelationFactRecord,
    ClosedTensorEqFactRecord,
    ClosedTensorShapeFactRecord,
    KRankLocalRelationCertificate,
    RelationFactSpec,
    build_certificate_transition_specs,
)


def _fixture(op="FW_linear", k=3):
    input_tids = tuple(200 + rank for rank in range(k))
    output_tids = tuple(300 + rank for rank in range(k))
    sm_inputs = [100]
    external_tids = (90,)
    external_shapes = ((7, 5),)
    if op == "FW_layernorm":
        external_tids = (91, 92)
        external_shapes = ((5,), (5,))
    sm_inputs.extend(external_tids)
    pm_nodes = [
        Node(rank, op, [input_tids[rank], *external_tids], [output_tids[rank]], [])
        for rank in range(k)
    ]
    sm_node = Node(0, op, sm_inputs, [110], [])
    input_fact = RelationFactSpec(
        "sharded", ("init:100", *(f"init:{tid}" for tid in input_tids)), gather_dim=1
    )
    output_fact = RelationFactSpec(
        "sharded", ("sm:0:0", *(f"pm:{rank}:0" for rank in range(k))), gather_dim=1
    )
    rule, theorem, output_shape = {
        "FW_linear": (
            "linear-sharded-k-rank-dim1",
            "TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm",
            (2, 3 * k, 7),
        ),
        "FW_layernorm": (
            "layernorm-sharded-k-rank-dim1",
            "TrainVerify.Denote.fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d",
            (2, 3 * k, 5),
        ),
    }[op]
    cert = KRankLocalRelationCertificate(
        rule_id=rule,
        op=op,
        rank_count=k,
        gather_dim=1,
        input_fact=input_fact,
        output_fact=output_fact,
        sm_step_id="sm:0:0",
        pm_step_ids=tuple(f"pm:{rank}:0" for rank in range(k)),
        external_tids=external_tids,
        external_shapes=external_shapes,
        lean_theorem=theorem,
    )
    transition = build_certificate_transition_specs(SimpleNamespace(), (cert,))[0]
    pre = ClosedRelationFactRecord(
        "fact_in", input_fact, "sharded", 100, input_tids, None, None,
        (2, 3 * k, 5), (2, 3, 5), 1,
    )
    post = ClosedRelationFactRecord(
        "fact_out", output_fact, "sharded", 110, output_tids, None, None,
        output_shape, (2, 3, output_shape[-1]), 1,
    )
    authorities = []
    authority_ids = []
    for tid, shape in zip(external_tids, external_shapes):
        eq = ClosedTensorEqFactRecord(f"external_eq_{tid}", "sm", tid, "pm", tid)
        sh = ClosedTensorShapeFactRecord(f"external_shape_{tid}", "pm", tid, shape, tid)
        authorities.extend((eq, sh))
        authority_ids.extend((eq.fact_id, sh.fact_id))
    segment = SimpleNamespace(
        segment_id="segment_000000", pre_state_id="state_pre", post_state_id="state_post",
        transition_ids=(transition.transition_id,), sm_range=(0, 1), pm_range=(0, k),
    )
    states = (
        SimpleNamespace(state_id="state_pre", fact_ids=("fact_in", *authority_ids)),
        SimpleNamespace(state_id="state_post", fact_ids=("fact_out",)),
    )
    chain = SimpleNamespace(
        complete=True, segments=(segment,), states=states,
        relation_facts=(pre, post), authority_facts=tuple(authorities),
    )
    namespace = "SyntheticLinear" if op == "FW_linear" else "SyntheticLayernorm"
    ir = SimpleNamespace(
        sm_nodes=[sm_node], pm_nodes=pm_nodes,
        sm_graph_ref=f"{namespace}.gSM", pm_graph_ref=f"{namespace}.gPM",
    )
    relation = SimpleNamespace(
        dependent_chain_plan=chain, transition_specs=(transition,), certificates=(cert,)
    )
    return ir, relation, cert, transition, pre, post


def _renderer_witness(linear_source, layernorm_source):
    return f"""import denote.RelationCompiler
import denote.KRankLinearGather
import denote.KRankLayernormGather

namespace TrainVerify.Denote
open RelationCompiler

namespace SyntheticLinear
noncomputable section

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := \"OpName.FW_linear\", ins := [100, 90], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := \"OpName.FW_linear\", ins := [200, 90], outs := [300] }}, {{ rank := 1, op := \"OpName.FW_linear\", ins := [201, 90], outs := [301] }}, {{ rank := 2, op := \"OpName.FW_linear\", ins := [202, 90], outs := [302] }}] }}

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 9, 5] [2, 3, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 9, 7] [2, 3, 7]
def external_eq_90 : RelationFact := .tensorEq .sm 90 .pm 90
def external_shape_90 : RelationFact := .tensorShape .pm 90 [7, 5]

def state_pre : RelationState where
  facts := [fact_in, external_eq_90, external_shape_90]
  nonempty := by decide

def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

{linear_source}
#check segment_000000
end
end SyntheticLinear

namespace SyntheticLayernorm
noncomputable section

def gSM : GraphDecl := {{ numRanks := 1, nodes := [{{ rank := 0, op := \"OpName.FW_layernorm\", ins := [100, 91, 92], outs := [110] }}] }}
def gPM : GraphDecl := {{ numRanks := 3, nodes := [{{ rank := 0, op := \"OpName.FW_layernorm\", ins := [200, 91, 92], outs := [300] }}, {{ rank := 1, op := \"OpName.FW_layernorm\", ins := [201, 91, 92], outs := [301] }}, {{ rank := 2, op := \"OpName.FW_layernorm\", ins := [202, 91, 92], outs := [302] }}] }}

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 9, 5] [2, 3, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 9, 5] [2, 3, 5]
def external_eq_91 : RelationFact := .tensorEq .sm 91 .pm 91
def external_shape_91 : RelationFact := .tensorShape .pm 91 [5]
def external_eq_92 : RelationFact := .tensorEq .sm 92 .pm 92
def external_shape_92 : RelationFact := .tensorShape .pm 92 [5]

def state_pre : RelationState where
  facts := [fact_in, external_eq_91, external_shape_91, external_eq_92, external_shape_92]
  nonempty := by decide

def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

{layernorm_source}
#check segment_000000
end
end SyntheticLayernorm

end TrainVerify.Denote
"""


def test_closed_k_rank_linear_renderer_uses_ordered_list_length_and_integrated_theorem():
    ir, relation, _cert, _transition, pre, post = _fixture("FW_linear", k=3)

    source = render_closed_segment(ir, relation, "segment_000000")

    ordered_inputs = ", ".join(
        f"(segment_000000_pmFinal pmStore) {tid}" for tid in pre.pm_tids
    )
    ordered_outputs = ", ".join(
        f"(segment_000000_pmFinal pmStore) {tid}" for tid in post.pm_tids
    )
    assert f"[{ordered_inputs}].length" in source
    assert f"[{ordered_outputs}]" in source
    assert "fw_linear_3d_allGatherPrimDimN_dim1_comm" in source
    assert source.count("foldl_faithful_middle_writer") == 4
    assert "external_eq_90.Holds" in source
    assert "external_shape_90.Holds" in source
    assert "shards_nonempty := by simp" in source
    assert "shape_contract := by norm_num" in source


def test_closed_k_rank_linear_renderer_recreates_exact_lean_witness():
    ir, relation, _cert, _transition, _pre, _post = _fixture("FW_linear", k=3)
    witness = Path(__file__).parents[2] / "trainverify/denote/GeneratedKRankLocalRendererWitness.lean"

    layer_ir, layer_relation, *_ = _fixture("FW_layernorm", k=3)
    exact_source = _renderer_witness(
        render_closed_segment(ir, relation, "segment_000000"),
        render_closed_segment(layer_ir, layer_relation, "segment_000000"),
    )

    assert witness.read_text(encoding="utf-8") == exact_source
    assert "open RelationCompiler" in exact_source
    assert "import denote.KRankLinearGather" in exact_source
    assert "import denote.KRankLayernormGather" in exact_source


def test_closed_k_rank_layernorm_renderer_uses_both_external_equalities_and_shapes():
    ir, relation, _cert, _transition, _pre, _post = _fixture("FW_layernorm", k=3)

    source = render_closed_segment(ir, relation, "segment_000000")

    assert "fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d" in source
    for tid in (91, 92):
        assert f"hframe external_eq_{tid}" in source
        assert f"hframe external_shape_{tid}" in source
    assert source.count("foldl_faithful_middle_writer") == 4


@pytest.mark.parametrize("k", (2, 4))
def test_closed_k_rank_layernorm_owns_one_sm_plus_ordered_dynamic_k_pm_writers(k):
    ir, relation, _cert, _transition, pre, post = _fixture("FW_layernorm", k=k)

    source = render_closed_segment(ir, relation, "segment_000000")

    assert source.count("foldl_faithful_middle_writer") == 1 + k
    assert "[" + ", ".join(
        f"(segment_000000_pmFinal pmStore) {tid}" for tid in pre.pm_tids
    ) + "].length" in source
    assert "[" + ", ".join(
        f"(segment_000000_pmFinal pmStore) {tid}" for tid in post.pm_tids
    ) + "]" in source


def test_closed_k_rank_layernorm_selects_exact_transition_certificate():
    ir, relation, cert, _transition, _pre, _post = _fixture("FW_layernorm", k=3)
    expected = render_closed_segment(ir, relation, "segment_000000")
    unrelated = replace(
        cert,
        input_fact=RelationFactSpec(
            "sharded", ("sm:99:0", "pm:99:0", "pm:100:0"), gather_dim=1,
        ),
    )
    relation = SimpleNamespace(
        **{**relation.__dict__, "certificates": (unrelated, cert)}
    )

    assert render_closed_segment(ir, relation, "segment_000000") == expected


def test_closed_k_rank_layernorm_rejects_malformed_or_duplicate_exact_certificate():
    ir, relation, cert, _transition, _pre, _post = _fixture("FW_layernorm", k=3)
    malformed = replace(
        cert,
        input_fact=RelationFactSpec(
            "sharded", ("sm:99:0", "pm:99:0", "pm:100:0"), gather_dim=1,
        ),
    )
    with pytest.raises(ValueError, match="one exact typed certificate"):
        render_closed_segment(
            ir,
            SimpleNamespace(**{**relation.__dict__, "certificates": (malformed,)}),
            "segment_000000",
        )

    with pytest.raises(ValueError, match="one exact typed certificate"):
        render_closed_segment(
            ir,
            SimpleNamespace(**{**relation.__dict__, "certificates": (cert, cert)}),
            "segment_000000",
        )


def test_closed_k_rank_linear_selects_exact_transition_certificate():
    ir, relation, cert, _transition, _pre, _post = _fixture("FW_linear", k=4)
    expected = render_closed_segment(ir, relation, "segment_000000")
    unrelated = replace(
        cert,
        input_fact=RelationFactSpec(
            "sharded", ("sm:99:0", *(f"pm:{99 + rank}:0" for rank in range(4))),
            gather_dim=1,
        ),
    )
    relation = SimpleNamespace(
        **{**relation.__dict__, "certificates": (unrelated, cert)}
    )

    assert render_closed_segment(ir, relation, "segment_000000") == expected


def test_closed_k_rank_linear_rejects_malformed_or_duplicate_exact_certificate():
    ir, relation, cert, _transition, _pre, _post = _fixture("FW_linear", k=4)
    malformed = replace(
        cert,
        output_fact=RelationFactSpec(
            "sharded", ("sm:99:0", *(f"pm:{99 + rank}:0" for rank in range(4))),
            gather_dim=1,
        ),
    )
    for certificates in ((malformed,), (cert, cert)):
        with pytest.raises(ValueError, match="one exact typed certificate"):
            render_closed_segment(
                ir,
                SimpleNamespace(**{**relation.__dict__, "certificates": certificates}),
                "segment_000000",
            )


@pytest.mark.parametrize("k", (2, 4))
def test_closed_k_rank_linear_owns_one_sm_plus_ordered_dynamic_k_pm_writers(k):
    ir, relation, _cert, _transition, pre, post = _fixture("FW_linear", k=k)

    source = render_closed_segment(ir, relation, "segment_000000")

    assert source.count("foldl_faithful_middle_writer") == 1 + k
    assert "[" + ", ".join(
        f"(segment_000000_pmFinal pmStore) {tid}" for tid in pre.pm_tids
    ) + "].length" in source
    assert "[" + ", ".join(
        f"(segment_000000_pmFinal pmStore) {tid}" for tid in post.pm_tids
    ) + "]" in source


def test_closed_k_rank_layernorm_preserves_data_gamma_beta_input_roles():
    ir, relation, cert, _transition, _pre, _post = _fixture("FW_layernorm", k=3)
    swapped = replace(
        cert,
        external_tids=tuple(reversed(cert.external_tids)),
        external_shapes=tuple(reversed(cert.external_shapes)),
    )
    relation = SimpleNamespace(
        **{**relation.__dict__, "certificates": (swapped,)}
    )

    with pytest.raises(ValueError, match="exact typed certificate"):
        render_closed_segment(ir, relation, "segment_000000")


def test_closed_k_rank_local_renderer_rejects_tampered_theorem_identity():
    ir, relation, cert, transition, _pre, _post = _fixture("FW_linear", k=3)
    bad_cert = replace(cert, lean_theorem="TrainVerify.Denote.fw_gelu_allGatherPrimDimN_eq")
    bad_transition = replace(transition, lean_theorem=bad_cert.lean_theorem)
    relation = SimpleNamespace(
        dependent_chain_plan=relation.dependent_chain_plan,
        transition_specs=(bad_transition,), certificates=(bad_cert,),
    )

    with pytest.raises(ValueError, match="theorem identity mismatch"):
        render_closed_segment(ir, relation, "segment_000000")


def test_closed_k_rank_local_renderer_rejects_dim2_with_dim1_theorem():
    ir, relation, cert, transition, _pre, _post = _fixture("FW_linear", k=3)
    bad_cert = replace(cert, gather_dim=2)
    relation = SimpleNamespace(
        dependent_chain_plan=relation.dependent_chain_plan,
        transition_specs=(transition,), certificates=(bad_cert,),
    )

    with pytest.raises(ValueError, match="exact typed certificate"):
        render_closed_segment(ir, relation, "segment_000000")


def test_closed_k_rank_local_renderer_rejects_reordered_pm_tid_authority():
    ir, relation, _cert, _transition, pre, post = _fixture("FW_linear", k=3)
    broken_post = replace(post, pm_tids=tuple(reversed(post.pm_tids)))
    chain = SimpleNamespace(
        complete=True, segments=relation.dependent_chain_plan.segments,
        states=relation.dependent_chain_plan.states,
        relation_facts=(pre, broken_post),
        authority_facts=relation.dependent_chain_plan.authority_facts,
    )
    broken = SimpleNamespace(
        dependent_chain_plan=chain,
        transition_specs=relation.transition_specs,
        certificates=relation.certificates,
    )

    with pytest.raises(ValueError, match="writer signatures mismatch"):
        render_closed_segment(ir, broken, "segment_000000")
