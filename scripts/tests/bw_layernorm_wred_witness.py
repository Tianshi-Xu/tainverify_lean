"""Portable shared-writer LayerNorm + independent prior WRED fixtures; Python only."""
from dataclasses import replace
from types import SimpleNamespace
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node

def fixture(k=2,b=2,s=3,d=7,collision=False):
    from scripts.tests.bw_layernorm_param_witness import renderer_fixture
    ir, rel, sid = renderer_fixture(k,b,s,d,projections=("dx","dgamma","dbeta"))
    ir.sm_num_ranks=1
    chain=rel.dependent_chain_plan
    wi=2*k-2
    ir.pm_nodes[wi]=Node(0,"CROSS_DP_WRED",list(range(600,600+k)),[600],[])
    w=rc.RelationFactSpec("reduction",("init:50",*(f"init:{600+r}" for r in range(k))))
    j=rc.RelationFactSpec("joined",("init:50",),joined_pm_step=f"pm:{wi}:0")
    pre=rc.ClosedRelationFactRecord("fact_w",w,"reduction",50,tuple(range(600,600+k)),None,None,(5,7),())
    post=rc.ClosedRelationFactRecord("fact_j",j,"joined",50,(),None,None,(5,7),(),joined_pm_tid=600)
    wc=rc.KRankAllReduceReconstructionCertificate("cross-dp-wred-reconstruction-k-rank",k,(5,7),w,j,f"pm:{wi}:0","TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce")
    wt=replace(rc.CertificateTransitionSpec("wred",wc.rule_id,(w,),(j,),(),(wi,),wc.lean_theorem),certificate_digest=_typed_certificate_digest(wc))
    rel.certificates=(*rel.certificates,wc);rel.transition_specs=(*rel.transition_specs,wt)
    chain.relation_facts=(*chain.relation_facts,pre,post)
    chain.states=(replace(chain.states[0],fact_ids=(*chain.states[0].fact_ids,"fact_w")),replace(chain.states[1],fact_ids=(*chain.states[1].fact_ids,"fact_j")))
    ids=tuple(t.transition_id for t in rel.transition_specs)
    if k==4: ids=(ids[1],ids[0],*ids[2:])
    chain.segments=(replace(chain.segments[0],transition_ids=ids),)
    if collision:
        ir.sm_nodes[1].outs[0]=600
        chain.relation_facts=tuple(replace(f,sm_tid=600) if f.fact_id=="fact_dx" else f for f in chain.relation_facts)
    return ir,rel

def witness_source(k=3, b=2, s=3, d=7, collision=False):
    """Return a self-contained conditional Lean witness with explicit world size."""
    from trainverify.bridge_emitter.composer import _node_text, render_closed_relation_declarations
    from trainverify.bridge_emitter.bw_layernorm_wred_renderer import render_closed_bw_layernorm_wred_segment

    ir, relation = fixture(k,b,s,d,collision)
    segment_id="segment_000000"
    tags = "".join({".1": "Dx", ".2.1": "Dgamma", ".2.2": "Dbeta"}[
        ".1" if c.rule_id == "bw-layernorm-dx-dim1-k-rank" else c.projection] for c in relation.certificates[:3])
    suffix_name = f"K{k}B{b}S{s}D{d}{tags}"
    graph_ns, namespace = f"BWLayernormWredGraph{suffix_name}", f"GeneratedBWLayernormWred{suffix_name}"
    ir.sm_graph_ref, ir.pm_graph_ref = f"{graph_ns}.sm", f"{graph_ns}.pm"
    chunks = ["import denote.GraphGears", "import denote.RelationCompiler", "import denote.KRankBWLayernormParam"]
    if any(c.rule_id == "bw-layernorm-dx-dim1-k-rank" for c in relation.certificates[:3]):
        chunks.append("import denote.KRankBWLayernorm")
    chunks.extend([
        "open TrainVerify.Denote", f"namespace {graph_ns}",
        "def sm : GraphDecl := { numRanks := 1, nodes := [" + ", ".join(_node_text(n) for n in ir.sm_nodes) + "] }",
        f"def pm : GraphDecl := {{ numRanks := {k}, nodes := [" + ", ".join(_node_text(n) for n in ir.pm_nodes) + "] }",
        f"end {graph_ns}",
    ])
    declarations = render_closed_relation_declarations(relation.dependent_chain_plan, namespace)
    suffix = f"end\nend TrainVerify.Denote.{namespace}\n"
    if not declarations.endswith(suffix):
        raise ValueError("closed declaration namespace suffix changed")
    body = "\n".join(line for line in declarations[:-len(suffix)].splitlines() if not line.startswith("import "))
    chunks.extend([body, render_closed_bw_layernorm_wred_segment(ir, relation, segment_id),
                   f"#print axioms {segment_id}_sound", f"#print axioms {segment_id}", suffix])
    return "\n".join(chunks)
