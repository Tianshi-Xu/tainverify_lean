from dataclasses import replace
from types import SimpleNamespace

import pytest

from trainverify.bridge_emitter import relation_compiler as rc


def matcher_fixture(k=3, b=2, h=3, q=5, d=7, *, axis=1, params=(3,)):
    shard = (b, h, q, d)
    full = tuple(x * k if i == axis else x for i, x in enumerate(shard))
    steps = []
    for side, ranks in (("sm", range(1)), ("pm", range(k))):
        for r in ranks:
            shape = full if side == "sm" else shard
            steps.append(SimpleNamespace(
                step_id=f"{side}:{r}:0", side=side, rank=r, op="BW_softmax",
                parameters=params, input_bindings=(f"{side}:g:{r}", f"{side}:x:{r}"),
                input_shapes=(shape, shape), output_shape=shape,
            ))
    return SimpleNamespace(steps=tuple(steps)), tuple(s.step_id for s in steps)


@pytest.mark.parametrize("axis", (1, 2))
@pytest.mark.parametrize("case", ((2, 1, 4, 8, 8), (3, 2, 3, 5, 7), (4, 3, 2, 4, 6)))
def test_general_matcher(axis, case):
    plan, frontier = matcher_fixture(*case, axis=axis)
    certs, inputs, layouts = rc.advance_k_rank_bw_softmax_frontiers(plan, (frontier,), ("sharded",))
    assert len(certs) == 1
    c = certs[0]
    assert (c.rule_id, c.rank_count, c.gather_dim) == (f"bw-softmax-sharded-dim{axis}-k-rank", case[0], axis)
    assert c.lean_theorem == f"TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim{axis}_rank4"
    assert c.parameters == (3,)
    assert inputs == tuple(tuple(s.input_bindings[a] for s in plan.steps) for a in (0, 1))
    assert layouts == ("sharded", "sharded")

@pytest.mark.parametrize("axis",(1,2))
@pytest.mark.parametrize("mutation",("rank","params","pairing","output","full-shape","axis","type","duplicate","digest","frame-input"))
def test_renderer_rejects_tampering(axis,mutation):
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel = renderer_fixture(axis=axis,frames=True)
    if mutation == "rank": ir.pm_nodes[3].rank=0
    elif mutation == "params": ir.pm_nodes[3].params=[]
    elif mutation == "pairing": ir.pm_nodes[3].ins.reverse()
    elif mutation == "output": ir.pm_nodes[3].outs=[9999]
    elif mutation in {"full-shape","axis"}:
        rel.dependent_chain_plan.relation_facts=tuple(replace(f,full_shape=(2,9,5,8)) if mutation=="full-shape" else replace(f,gather_dim=3) for f in rel.dependent_chain_plan.relation_facts)
    elif mutation == "type": rel.certificates=(SimpleNamespace(**rel.certificates[0].__dict__),)
    elif mutation == "duplicate": rel.certificates=rel.certificates*2
    elif mutation == "digest": rel.transition_specs=(replace(rel.transition_specs[0],certificate_digest="bad"),)
    else: ir.pm_nodes[0].outs=[1000]
    with pytest.raises(ValueError): render_closed_segment(ir,rel,"segment_000000")


def test_unrelated_certificate_does_not_change_output():
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel = renderer_fixture()
    source=render_closed_segment(ir,rel,"segment_000000")
    cert=rel.certificates[0]
    rel.certificates+=(replace(cert,output_fact=replace(cert.output_fact,step_triple=("sm:99:0","pm:99:0"))),)
    assert render_closed_segment(ir,rel,"segment_000000")==source


@pytest.fixture(scope="module")
def mixed_goal107():
    from pathlib import Path
    from trainverify.bridge_emitter import parser
    from trainverify.bridge_emitter.proof_compiler import compile_proof_plan,build_default_registry
    with pytest.MonkeyPatch.context() as m:
        for key,value in {"DENOTE_DIR":"trainverify/denote/gpt_ly4_regen","GEN_DIR":"trainverify/denote/gpt_ly4_regen","GEN_FILE":"GeneratedData.lean","MOD_PREFIX":"denote.gpt_ly4_regen"}.items():
            m.setattr(parser,key,value)
        ir=parser.load_goal_ir(107,str(Path(__file__).resolve().parents[2]))
        rel=rc.compile_relation_plan(ir,compile_proof_plan(ir,build_default_registry()))
    return ir,rel


def test_mixed_consumers_preserve_params_and_checked_domains(mixed_goal107):
    from copy import deepcopy
    from trainverify.bridge_emitter.composer import render_closed_segment
    base_ir,base_rel=mixed_goal107
    tm={t.transition_id:t for t in base_rel.transition_specs}
    seen=set()
    for seg in base_rel.dependent_chain_plan.segments:
        ts=[tm[t] for t in seg.transition_ids]
        soft=[t for t in ts if t.rule_id.startswith("bw-softmax-sharded-")]
        if not soft or len(ts) not in (2,5): continue
        seen.add(len(ts))
        source=render_closed_segment(base_ir,base_rel,seg.segment_id)
        assert soft[0].lean_theorem in source and "softmaxBwd" not in source
        assert "List.zipWith" in source
        ir=deepcopy(base_ir)
        ir.pm_nodes[soft[0].pm_node_indices[0]].params=[91]
        with pytest.raises(ValueError): render_closed_segment(ir,base_rel,seg.segment_id)
        rel=deepcopy(base_rel)
        # General softmax must not silently widen the other proof half.
        other=next(t for t in ts if t.rule_id=="transpose-sharded-k-rank")
        rel=replace(rel,dependent_chain_plan=replace(rel.dependent_chain_plan,relation_facts=tuple(
            replace(f,full_shape=(2,4,8,8)) if f.source==other.pre_facts[0] else f
            for f in rel.dependent_chain_plan.relation_facts)))
        with pytest.raises(ValueError): render_closed_segment(base_ir,rel,seg.segment_id)
    assert seen=={2,5}


def test_mixed_import_policy_names_general_softmax_theorems():
    from trainverify.bridge_emitter.closed_segment_import_policy import plan_closed_segment_imports
    for axis in (1,2):
        imports=plan_closed_segment_imports(("transpose-sharded-k-rank",f"bw-softmax-sharded-dim{axis}-k-rank"),
            ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim3_rank4",
             f"TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim{axis}_rank4"))
        assert "denote.KRankBWSoftmaxGeneral" in imports


def test_renderer_top_level_import_mode(monkeypatch):
    import importlib
    import sys
    from pathlib import Path
    from trainverify.bridge_emitter.composer import render_closed_segment
    monkeypatch.syspath_prepend(str(Path(__file__).resolve().parents[2]/"trainverify/bridge_emitter"))
    monkeypatch.setitem(sys.modules,"relation_compiler",rc)
    module=importlib.import_module("bw_softmax_renderer")
    ir,rel=renderer_fixture(params=())
    for node in ir.sm_nodes+ir.pm_nodes: node.params=None
    assert module.render_closed_k_rank_bw_softmax_segment(ir,rel,"segment_000000")==render_closed_segment(ir,rel,"segment_000000")


def test_witness_generator_is_deterministic_and_self_contained():
    source=witness_source()
    assert source==witness_source()
    assert source.count("#print axioms segment_000000")==6
    assert "import denote.KRankBWSoftmaxGeneral" in source
    assert "Goal_" not in source and "softmaxBwd" not in source



@pytest.mark.parametrize("mutation", ("rank", "sm-rank", "params", "shape-arity", "input", "output", "zero", "axis0", "axis3"))
def test_matcher_rejects_drift(mutation):
    plan, frontier = matcher_fixture(axis=int(mutation[-1]) if mutation.startswith("axis") else 1)
    sm, *pm = plan.steps
    if mutation == "rank": pm[1].rank = 0
    elif mutation == "sm-rank": sm.rank = 1
    elif mutation == "params": pm[1].parameters = ()
    elif mutation == "shape-arity": pm[1].input_shapes = (pm[1].output_shape,)
    elif mutation == "input": pm[1].input_shapes = ((2, 3, 5, 8), pm[1].output_shape)
    elif mutation == "output": pm[1].output_shape = (2, 3, 5)
    elif mutation == "zero": pm[1].output_shape = (2, 0, 5, 7)
    with pytest.raises(rc.RelationCompositionError):
        rc.advance_k_rank_bw_softmax_frontiers(plan, (frontier,), ("sharded",))


def renderer_fixture(k=3, b=2, h=3, q=5, d=7, *, axis=1, params=(3,), frames=False):
    from trainverify.bridge_emitter.parser import Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    plan, frontier = matcher_fixture(k,b,h,q,d,axis=axis,params=params)
    cert = rc.advance_k_rank_bw_softmax_frontiers(plan,(frontier,),("sharded",))[0][0]
    if k == 1 and axis == 2:
        cert = replace(cert, rule_id="bw-softmax-sharded-dim2-k-rank", gather_dim=2,
            lean_theorem="TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim2_rank4",
            gradient_fact=replace(cert.gradient_fact,gather_dim=2),
            activation_fact=replace(cert.activation_fact,gather_dim=2), output_fact=replace(cert.output_fact,gather_dim=2))
    full, shard = plan.steps[0].output_shape, plan.steps[1].output_shape
    facts = tuple(rc.ClosedRelationFactRecord(name, src, "sharded", tid,
        tuple(tid*10+r for r in range(k)), None, None, full, shard, gather_dim=axis)
        for name, src, tid in (("fg",cert.gradient_fact,100),("fx",cert.activation_fact,200),("fo",cert.output_fact,300)))
    sm = [Node(0,"BW_softmax",[100,200],[300],list(params))]
    pm = [Node(r,"BW_softmax",[1000+r,2000+r],[3000+r],list(params)) for r in range(k)]
    si, pi = (0,), tuple(range(k))
    if frames:
        sm.insert(0,Node(0,"FW_contiguous",[800],[801],[]))
        pm = [n for r,node in enumerate(pm) for n in (Node(r,"FW_contiguous",[8000+r],[9000+r],[]),node)]
        si, pi = (1,), tuple(2*r+1 for r in range(k))
        cert = replace(cert,sm_step_id="sm:1:0",pm_step_ids=tuple(f"pm:{i}:0" for i in pi))
    tr = replace(rc.CertificateTransitionSpec("tr",cert.rule_id,
        tuple(sorted((cert.gradient_fact,cert.activation_fact))),(cert.output_fact,),si,pi,cert.lean_theorem),
        certificate_digest=_typed_certificate_digest(cert))
    before = rc.ClosedRelationStateRecord("state_000000",("fg","fx"))
    after = rc.ClosedRelationStateRecord("state_000001",("fg","fx","fo"))
    seg = rc.ClosedDependentSegmentRecord("segment_000000","component",before.state_id,after.state_id,("tr",),(0,len(sm)),(0,len(pm)))
    rel = SimpleNamespace(certificates=(cert,),transition_specs=(tr,),dependent_chain_plan=SimpleNamespace(
        complete=True,relation_facts=facts,states=(before,after),segments=(seg,)))
    ir = SimpleNamespace(sm_nodes=sm,pm_nodes=pm,sm_graph_ref="SyntheticBWLayernorm.smGraph",pm_graph_ref="SyntheticBWLayernorm.pmGraph")
    return ir,rel


@pytest.mark.parametrize("axis", (1,2))
@pytest.mark.parametrize("k", (1,2,3,4))
@pytest.mark.parametrize("frames", (False,True))
def test_registered_renderer(axis,k,frames):
    from trainverify.bridge_emitter.composer import render_closed_segment
    ir,rel = renderer_fixture(k,axis=axis,frames=frames)
    source = render_closed_segment(ir,rel,"segment_000000")
    assert source == render_closed_segment(ir,rel,"segment_000000")
    assert f"bw_softmax_allGatherPrimDimN_dim{axis}_rank4" in source
    assert "softmaxBwd" not in source and "hOutValue :=" not in source
    assert source.count("private theorem segment_000000_hPmWriter") == k
    assert source.count("private def segment_000000_sm_final") == 1
    assert source.count("private def segment_000000_pm_final") == 1
    assert "List.zipWith" in source and "[3]" in source


def witness_source(axes=(1,2), cases=((2,1,4,8,8),(3,2,3,5,7),(4,3,2,4,6))):
    """Return exact generated witnesses; no filesystem/build side effects."""
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.composer import render_closed_segment
    sources = []
    for axis in axes:
        for i,case in enumerate(cases):
            ir,rel = renderer_fixture(*case,axis=axis,frames=True)
            src = fixture_source(ir,rel,render_closed_segment,pm_num_ranks=case[0])
            sources.append(src.replace("import denote.KRankBWLayernorm","import denote.KRankBWSoftmaxGeneral").replace("SyntheticBWLayernorm",f"BWSoftmaxA{axis}Case{i}"))
    imports = list(dict.fromkeys(line for src in sources for line in src.splitlines() if line.startswith("import ")))
    return "\n".join(imports)+"\n"+"\n".join("\n".join(line for line in src.splitlines() if not line.startswith("import ")) for src in sources)+"\n"


def test_softmax_checked_in_witness_matches_generator():
    from pathlib import Path
    path=Path(__file__).resolve().parents[2]/"trainverify/denote/GeneratedBWSoftmaxGeneralWitness.lean"
    assert path.read_text()==witness_source()
