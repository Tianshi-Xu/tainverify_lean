"""Generator-owned conditional sequence dW/dual witnesses (no kernel invocation)."""
from dataclasses import replace
from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node

RULE = "bw-linear-dw-sequence-reduction-k-rank"
THEOREM = "TrainVerify.Denote.bw_linear_dw_sequence_reduction_rank3"
CASES = ((1,3,2,1,4),(2,1,8,64,64),(3,2,5,7,11),(4,1,4,64,64),(5,2,1,3,2))


def renderer_fixture(k=3,b=2,s=5,o=7,i=11,*,dual=False,sparse=False,namespace="SyntheticBWLinearDwSequence"):
    from scripts.tests.test_k_rank_bw_linear_dx_sequence import renderer_fixture as dx_fixture
    ir,rel=dx_fixture(k,b,s,o,i)
    g,x,w,dx=rel.dependent_chain_plan.relation_facts
    g=replace(g,source=replace(g.source,step_triple=("init:100",*(f"init:{u}" for u in g.pm_tids))))
    x=replace(x,source=replace(x.source,step_triple=("init:200",*(f"init:{u}" for u in x.pm_tids))))
    w=replace(w,sm_tid=206,pm_tids=(206,),source=replace(w.source,step_triple=("init:206","init:206")))
    ir.sm_nodes[0].ins[2]=206
    for n in ir.pm_nodes:n.ins[2]=206
    indices=tuple(range(k))
    if sparse:
        ir.pm_nodes.insert(1,Node(0,"FW_neg",[9000],[9001],[]))
        ir.sm_nodes.append(Node(0,"FW_neg",[9010],[9011],[]))
        indices=tuple(0 if r==0 else r+1 for r in range(k))
    dx=replace(dx,source=replace(dx.source,step_triple=("sm:0:0",*(f"pm:{p}:0" for p in indices))))
    dwsource=rc.RelationFactSpec("reduction",("sm:0:1",*(f"pm:{p}:1" for p in indices)))
    dw=replace(dx,fact_id="fact_dw",source=dwsource,kind="reduction",gather_dim=None,sm_tid=401,pm_tids=tuple(5000+r for r in range(k)),full_shape=(o,i),shard_shape=(o,i))
    c=rc.KRankBWLinearDwReductionCertificate(RULE,k,1,g.source,x.source,w.source,dwsource,"sm:0:1",tuple(f"pm:{p}:1" for p in indices),THEOREM)
    base=rel.transition_specs[0]
    t=replace(base,transition_id="transition_dw",rule_id=RULE,pre_facts=tuple(sorted((g.source,x.source,w.source))),post_facts=(dwsource,),pm_node_indices=indices,lean_theorem=THEOREM,certificate_digest=_typed_certificate_digest(c))
    certs=[c];ts=[t]
    if dual:
        dc=replace(rel.certificates[0],input_facts=(g.source,x.source,w.source),output_fact=dx.source,pm_step_ids=tuple(f"pm:{p}:0" for p in indices))
        dt=replace(base,pre_facts=tuple(sorted(dc.input_facts)),post_facts=(dx.source,),pm_node_indices=indices,certificate_digest=_typed_certificate_digest(dc))
        certs.append(dc);ts.append(dt)
    chain=rel.dependent_chain_plan
    chain.relation_facts=(g,x,w,dw,*((dx,) if dual else ()))
    chain.states=(chain.states[0],replace(chain.states[1],fact_ids=("fact_g","fact_x","fact_w","fact_dw",*(("fact_out",) if dual else ()))))
    chain.segments=(replace(chain.segments[0],transition_ids=tuple(t.transition_id for t in ts),sm_range=(0,len(ir.sm_nodes)),pm_range=(0,len(ir.pm_nodes))),)
    rel.certificates=tuple(certs);rel.transition_specs=tuple(ts)
    ir.pm_num_ranks=k;ir.sm_graph_ref=f"{namespace}.smGraph";ir.pm_graph_ref=f"{namespace}.pmGraph"
    return ir,rel


def witness_source(k=3,b=2,s=5,o=7,i=11,*,dual=False,sparse=False,namespace="SyntheticBWLinearDwSequence",render=None):
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    if render is None:
        from trainverify.bridge_emitter.bw_linear_dw_sequence_renderer import render_closed_bw_linear_dw_sequence_segment as render
    ir,rel=renderer_fixture(k,b,s,o,i,dual=dual,sparse=sparse,namespace=namespace)
    return fixture_source(ir,rel,render,pm_num_ranks=k).replace("SyntheticBWLayernorm",namespace).replace("import denote.KRankBWLayernorm","import denote.KRankBWLinearDwSequenceGeneral\nimport denote.KRankBWLinearDxSequence").replace("noncomputable section","set_option maxHeartbeats 500000\nnoncomputable section")


def combined_witness_source():
    parts=[witness_source(*args,dual=dual,sparse=True,namespace=f"SequenceDwCase{j}_{int(dual)}") for j,args in enumerate(CASES) for dual in (False,True)]
    imports=list(dict.fromkeys(line for p in parts for line in p.splitlines() if line.startswith("import ")))
    return "\n".join(imports)+"\n"+"\n".join("\n".join(l for l in p.splitlines() if not l.startswith("import ")) for p in parts)+"\n"
