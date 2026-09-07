"""Uniform, generator-owned row-dW candidates; no Lean acceptance is implied.

The renderer is called directly: registry/matcher integration is owned separately.
"""
from types import SimpleNamespace

from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node

RULE = "bw-linear-dw-output-row-sharded-k-rank"
THEOREM = "TrainVerify.Denote.bw_linear_dw_row_allGather_rank3"


def renderer_fixture(k=3, b=2, s=5, o=7, i=11, *, with_dx=False, tail=None):
    """One shared writer per rank; optional independent AllReduce/BW_view tail."""
    if min(k, b, s, o, i) <= 0 or tail not in (None, "allreduce", "view"):
        raise ValueError("positive dimensions and a supported tail are required")
    g = rc.RelationFactSpec("sharded", ("init:100", *(f"init:{1000+r}" for r in range(k))), gather_dim=2)
    x = rc.RelationFactSpec("joined", ("init:200",), joined_pm_step="init:2000")
    w = rc.RelationFactSpec("sharded", ("init:300", *(f"init:{3000+r}" for r in range(k))), gather_dim=0)
    dx = rc.RelationFactSpec("reduction", ("sm:0:0", *(f"pm:{r}:0" for r in range(k))))
    dw = rc.RelationFactSpec("sharded", ("sm:0:1", *(f"pm:{r}:1" for r in range(k))), gather_dim=0)
    def record(fid, source, sm, pm, full, shard, joined=None):
        return rc.ClosedRelationFactRecord(fid, source, source.layout, sm, tuple(pm), None, None,
            tuple(full), tuple(shard), gather_dim=source.gather_dim, joined_pm_tid=joined)
    records = [record("fact_g",g,100,range(1000,1000+k),(b,s,o*k),(b,s,o)),
        record("fact_x",x,200,(),(b,s,i),(b,s,i),2000),
        record("fact_w",w,300,range(3000,3000+k),(o*k,i),(o,i)),
        record("fact_dw",dw,401,range(5000,5000+k),(o*k,i),(o,i))]
    sm_nodes = [Node(0,"BW_linear",[100,200,300],[400,401],[])]
    pm_nodes = [Node(r,"BW_linear",[1000+r,2000,3000+r],[4000+r,5000+r],[]) for r in range(k)]
    certs: list = [rc.KRankBWLinearDwShardedCertificate(RULE,k,g,x,w,dw,"sm:0:1",
        tuple(f"pm:{r}:1" for r in range(k)),THEOREM)]
    transitions = []
    def transition(c, pres, post, sm, pm):
        return rc.CertificateTransitionSpec(f"transition_{len(transitions):06d}",c.rule_id,
            tuple(sorted(pres)),(post,),tuple(sm),tuple(pm),c.lean_theorem,
            certificate_digest=_typed_certificate_digest(c))
    transitions.append(transition(certs[0],(g,x,w),dw,(0,),range(k)))
    pre = ["fact_g","fact_x","fact_w"]
    fresh = ["fact_dw"]
    if with_dx:
        c = rc.KRankBWLinearDxCertificate("bw-linear-dx-row-reduction-k-rank","row-reduction",k,
            "reduction",None,(g,x,w),dx,"sm:0:0",tuple(f"pm:{r}:0" for r in range(k)),
            "TrainVerify.Denote.bw_linear_dx_row_reduction_rank3")
        certs.append(c);transitions.append(transition(c,(g,x,w),dx,(0,),range(k)))
        records.append(record("fact_dx",dx,400,range(4000,4000+k),(b,s,i),(b,s,i)))
        fresh.append("fact_dx")
    if tail == "allreduce":
        source = rc.RelationFactSpec("reduction",("init:600",*(f"init:{6000+r}" for r in range(k))))
        out = rc.RelationFactSpec("joined",("init:600",),joined_pm_step=f"pm:{k}:0")
        records.extend((record("fact_tail_in",source,600,range(6000,6000+k),(b,s,i),(b,s,i)),
                        record("fact_tail_out",out,600,(),(b,s,i),(b,s,i),7000)))
        c = rc.KRankAllReduceReconstructionCertificate("allreduce-reconstruction-k-rank",k,(b,s,i),source,out,
            f"pm:{k}:0","TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce")
        pm_nodes.append(Node(0,"AllReducePrim",list(range(6000,6000+k)),[7000],[]))
        certs.append(c);transitions.append(transition(c,(source,),out,(),(k,)))
    elif tail == "view":
        source = rc.RelationFactSpec("joined",("init:600",),joined_pm_step="init:6000")
        out = rc.RelationFactSpec("joined",("sm:1:0",),joined_pm_step=f"pm:{k}:0")
        records.extend((record("fact_tail_in",source,600,(),(b,s,i),(b,s,i),6000),
                        record("fact_tail_out",out,700,(),(b*s,i),(b*s,i),7000)))
        c = rc.JoinedBWViewCertificate("bw-view-joined",(b,s,i),(b*s,i),source,out,
            "sm:1:0",f"pm:{k}:0","TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view")
        sm_nodes.append(Node(0,"BW_view",[600,601],[700],[b*s,i]))
        pm_nodes.append(Node(0,"BW_view",[6000,6001],[7000],[b*s,i]))
        certs.append(c);transitions.append(transition(c,(source,),out,(1,),(k,)))
    if tail:
        pre.append("fact_tail_in");fresh.append("fact_tail_out")
    states = (rc.ClosedRelationStateRecord("state_before",tuple(pre)),
              rc.ClosedRelationStateRecord("state_after",tuple(pre+fresh)))
    segment = rc.ClosedDependentSegmentRecord("segment_000000","component_000000",
        "state_before","state_after",tuple(t.transition_id for t in transitions),
        (0,len(sm_nodes)),(0,len(pm_nodes)))
    chain = SimpleNamespace(relation_facts=tuple(records),states=states,segments=(segment,),
        authority_facts=(),anchor_fact=None,complete=True)
    ir = SimpleNamespace(sm_nodes=sm_nodes,pm_nodes=pm_nodes,pm_num_ranks=k,
        sm_graph_ref="SyntheticBWLinearDwRow.smGraph",pm_graph_ref="SyntheticBWLinearDwRow.pmGraph")
    return ir, SimpleNamespace(dependent_chain_plan=chain,certificates=tuple(certs),transition_specs=tuple(transitions))


def witness_source(k=3, b=2, s=5, o=7, i=11, *, with_dx=False, tail=None):
    """Return exact renderer bytes plus graph/fact declarations, without writing Lean."""
    from scripts.tests.test_k_rank_bw_layernorm import fixture_source
    from trainverify.bridge_emitter.bw_linear_dual_renderer import render_closed_k_rank_bw_linear_dual_segment
    ir, rel = renderer_fixture(k,b,s,o,i,with_dx=with_dx,tail=tail)
    return fixture_source(ir,rel,render_closed_k_rank_bw_linear_dual_segment,pm_num_ranks=k).replace(
        "SyntheticBWLayernorm","SyntheticBWLinearDwRow").replace(
        "import denote.KRankBWLayernorm",
        "import denote.KRankBWLinearDwRowGeneral\nimport denote.KRankBWLinearDxRow")
