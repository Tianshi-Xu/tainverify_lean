"""Compact generator-owned C03 witnesses: independent prior weight gradients.

WRED consumes a ReductionRel, never the ShardedRel produced by BW_gelu.
This is the captured DP1 reducer contract, not general distributed-DP authority.
"""
from dataclasses import replace
from types import SimpleNamespace

from trainverify.bridge_emitter import relation_compiler as rc
from trainverify.bridge_emitter.composer import _typed_certificate_digest
from trainverify.bridge_emitter.parser import Node


def fixture(k=2, dim=1, shard=(2, 3), collision=False):
    full = tuple(n * k if i == dim else n for i, n in enumerate(shard))
    output_tid = 600 if collision else 30
    sm = [Node(0, "BW_gelu", [10, 20], [output_tid], [])]
    pm = [Node(r, "BW_gelu", [100+r, 200+r], [300+r], []) for r in range(k)]
    pm.insert(k-1, Node(0, "CROSS_DP_WRED", list(range(600, 600+k)), [600], []))
    indices = tuple(i for i, n in enumerate(pm) if n.op == "BW_gelu")
    def src(kind, st, pts, axis=None, joined=None):
        return rc.RelationFactSpec(kind, (st, *pts), gather_dim=axis, joined_pm_step=joined)
    g = src("sharded", "init:10", tuple(f"init:{100+r}" for r in range(k)), dim)
    x = src("sharded", "init:20", tuple(f"init:{200+r}" for r in range(k)), dim)
    o = src("sharded", "sm:0:0", tuple(f"pm:{i}:0" for i in indices), dim)
    w = src("reduction", "init:50", tuple(f"init:{600+r}" for r in range(k)))
    j = src("joined", "init:50", (), joined=f"pm:{k-1}:0")
    def record(name, source, smtid, pmtids, shape=full, piece=shard, joined=None):
        return rc.ClosedRelationFactRecord(name, source, source.layout, smtid, pmtids,
            None, None, shape, piece, gather_dim=source.gather_dim, joined_pm_tid=joined)
    facts = (record("fg", g, 10, tuple(range(100,100+k))),
             record("fx", x, 20, tuple(range(200,200+k))),
             record("fo", o, output_tid, tuple(range(300,300+k))),
             record("fw", w, 50, tuple(range(600,600+k)), (5,7), ()),
             record("fj", j, 50, (), (5,7), (), 600))
    anchor = rc.ClosedTensorShapeFactRecord("anchor", "sm", 99, (1,), 0)
    gelu = rc.KRankBWGeluCertificate("bw-gelu-pointwise-sharded-k-rank", k, dim,
        g,x,o,"sm:0:0",tuple(f"pm:{i}:0" for i in indices),
        "TrainVerify.Denote.bw_gelu_allGatherPrimDimN_eq")
    wred = rc.KRankAllReduceReconstructionCertificate("cross-dp-wred-reconstruction-k-rank",
        k,(5,7),w,j,f"pm:{k-1}:0",
        "TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce")
    transitions = tuple(replace(rc.CertificateTransitionSpec(name,c.rule_id,pre,(post,),si,pi,c.lean_theorem),
        certificate_digest=_typed_certificate_digest(c)) for name,c,pre,post,si,pi in (
        ("gelu",gelu,tuple(sorted((g,x))),o,(0,),indices),
        ("wred",wred,(w,),j,(),(k-1,))))
    before = rc.ClosedRelationStateRecord("state_000000",("anchor","fg","fx","fw"))
    after = rc.ClosedRelationStateRecord("state_000001",("anchor","fg","fx","fo","fj"))
    segment = rc.ClosedDependentSegmentRecord("segment_000000","component",before.state_id,
        after.state_id,("gelu","wred"),(0,1),(0,k+1))
    chain = SimpleNamespace(complete=True,relation_facts=facts,authority_facts=(),anchor_fact=anchor,
        states=(before,after),segments=(segment,))
    ir = SimpleNamespace(sm_nodes=sm,pm_nodes=pm,sm_num_ranks=1,pm_num_ranks=k,
        sm_graph_ref="SyntheticBWGeluWred.smGraph",pm_graph_ref="SyntheticBWGeluWred.pmGraph")
    return ir, SimpleNamespace(certificates=(gelu,wred),transition_specs=transitions,dependent_chain_plan=chain)


def witness_source(k=2, **kwargs):
    from trainverify.bridge_emitter.bw_gelu_wred_renderer import render_closed_bw_gelu_wred_segment
    from trainverify.bridge_emitter.composer import _node_text, render_closed_relation_declarations
    ir, relation = fixture(k, **kwargs)
    ns = "SyntheticBWGeluWred"
    declarations = render_closed_relation_declarations(relation.dependent_chain_plan, ns)
    declarations = declarations.replace(f"namespace TrainVerify.Denote.{ns}", f"namespace {ns}")
    graphs = f"def smGraph : GraphDecl := {{ numRanks := 1, nodes := [{', '.join(_node_text(n) for n in ir.sm_nodes)}] }}\ndef pmGraph : GraphDecl := {{ numRanks := {k}, nodes := [{', '.join(_node_text(n) for n in ir.pm_nodes)}] }}\n"
    declarations = declarations.replace("noncomputable section", "noncomputable section\n" + graphs)
    closing = f"\nend\nend TrainVerify.Denote.{ns}\n"
    assert declarations.endswith(closing)
    return declarations[:-len(closing)] + "\n" + render_closed_bw_gelu_wred_segment(ir,relation,"segment_000000") + f"\n#print axioms segment_000000\nend\nend {ns}\n"


def captured_fixture(inventory_root, model_root, k):
    """Replay retained typed audit authority against the actual parsed graphs (no planner/build)."""
    import json
    from pathlib import Path
    from dataclasses import fields
    from trainverify.bridge_emitter import parser
    from trainverify.bridge_emitter.model_authority import load_model_authority, materialize_target_ir
    def tuples(value):
        if isinstance(value, list): return tuple(tuples(x) for x in value)
        if isinstance(value, dict): return {key:tuples(x) for key,x in value.items()}
        return value
    def fact(value): return rc.RelationFactSpec(**tuples(value))
    def construct(cls,value):
        value=tuples(value)
        for key in ("source","gradient_fact","activation_fact","input_fact","output_fact"):
            if key in value: value[key]=fact(value[key])
        for key in ("pre_facts","post_facts"):
            if key in value: value[key]=tuple(fact(x) for x in value[key])
        return cls(**{key:x for key,x in value.items() if key in {f.name for f in fields(cls) if f.init}})
    root=Path(inventory_root)/f"p{k}"
    raw=json.loads((root/"global_relation.json").read_text())
    cr=raw["dependent_chain_plan"]
    authority_types={"tensor_shape":rc.ClosedTensorShapeFactRecord,"tensor_eq":rc.ClosedTensorEqFactRecord,
        "gather":rc.ClosedGatherFactRecord,"packed_cu":rc.ClosedPackedCuFactRecord,"label_bound":rc.ClosedLabelBoundFactRecord}
    chain=rc.ClosedDependentChainPlan(**{**tuples(cr),
        "relation_facts":tuple(construct(rc.ClosedRelationFactRecord,x) for x in cr["relation_facts"]),
        "authority_facts":tuple(construct(authority_types[x["kind"]],x) for x in cr["authority_facts"]),
        "anchor_fact":construct(rc.ClosedTensorShapeFactRecord,cr["anchor_fact"]),
        "states":tuple(construct(rc.ClosedRelationStateRecord,x) for x in cr["states"]),
        "segments":tuple(construct(rc.ClosedDependentSegmentRecord,x) for x in cr["segments"])})
    types={"KRankBWGeluCertificate":rc.KRankBWGeluCertificate,
           "KRankAllReduceReconstructionCertificate":rc.KRankAllReduceReconstructionCertificate}
    certs=tuple(construct(types[x["type"]],x["data"]) for x in json.loads((root/"certificates.json").read_text()) if x["type"] in types)
    rel=SimpleNamespace(dependent_chain_plan=chain,certificates=certs,
        transition_specs=tuple(construct(rc.CertificateTransitionSpec,x) for x in raw["transition_specs"]))
    old=parser.DENOTE_DIR,parser.GEN_DIR,parser.GEN_FILE,parser.MOD_PREFIX
    try:
        parser.DENOTE_DIR=parser.GEN_DIR="trainverify/FreshGPT"
        parser.GEN_FILE="GeneratedData.lean";parser.MOD_PREFIX="FreshGPT"
        model=load_model_authority(tuple(range(1,27)),str(Path(model_root)/f"p{k}"),model_id="C03-replay",allow_partial=False)
        ir=materialize_target_ir(model,3)
    finally:
        parser.DENOTE_DIR,parser.GEN_DIR,parser.GEN_FILE,parser.MOD_PREFIX=old
    return ir,rel
