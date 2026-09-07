"""Self-contained, deterministic conditional hidden BW_embedding witnesses.

The fixture uses the production frozen certificate class, loaded at call time so
this generator can be integrated before its parent-owned registry wiring lands.
These are closed-segment witnesses, not whole-model/public-contract proofs.
"""
from types import SimpleNamespace


def renderer_fixture(k=2, b=1, s=16, v=256, d=32):
    """Return (ir, relation, segment_id), retaining inputs across sparse frames."""
    from dataclasses import replace
    from trainverify.bridge_emitter import relation_compiler as rc
    from trainverify.bridge_emitter.parser import LineageGoal, Node
    from trainverify.bridge_emitter.composer import _typed_certificate_digest

    if any(type(x) is not int or x <= 0 for x in (k, b, s, v, d)):
        raise ValueError("hidden embedding fixture dimensions must be positive integers")
    spec = rc.get_closed_rule_spec("bw-embedding-hidden-sharded-k-rank")
    # Disjoint ranges for arbitrary K; no fixture-specific production branching.
    gradients = tuple(range(100, 100 + k))
    weights = tuple(range(100 + k, 100 + 2 * k))
    outputs = tuple(range(100 + 2 * k, 100 + 3 * k))
    scratch = 100 + 3 * k
    sm_index = 1
    pm_indices = tuple(2 * rank + 1 for rank in range(k))
    sm_step = f"sm:{sm_index}:0"
    pm_steps = tuple(f"pm:{index}:0" for index in pm_indices)
    g = rc.RelationFactSpec("sharded", ("init:1", *(f"init:{tid}" for tid in gradients)), gather_dim=2)
    i = rc.RelationFactSpec("sharded", ("init:2", "init:2"), gather_dim=0)
    w = rc.RelationFactSpec("sharded", ("init:3", *(f"init:{tid}" for tid in weights)), gather_dim=1)
    o = rc.RelationFactSpec("sharded", (sm_step, *pm_steps), gather_dim=1)
    cert = rc.KRankBWEmbeddingHiddenCertificate(
        rule_id=spec.rule_id, rank_count=k, batch_size=b, sequence_size=s,
        vocab_size=v, shard_hidden=d, gradient_fact=g, ids_fact=i,
        weight_fact=w, output_fact=o, sm_step_id=sm_step,
        pm_step_ids=pm_steps, lean_theorem=spec.lean_theorems[0],
    )
    records = (
        rc.ClosedRelationFactRecord("fact_g", g, "sharded", 1, gradients, None, None,
                                   (b, s, d * k), (b, s, d), gather_dim=2),
        rc.ClosedRelationFactRecord("fact_i", i, "sharded", 2, (2,), None, None,
                                   (b, s), (b, s), gather_dim=0),
        rc.ClosedRelationFactRecord("fact_w", w, "sharded", 3, weights, None, None,
                                   (v, d * k), (v, d), gather_dim=1),
        rc.ClosedRelationFactRecord("fact_o", o, "sharded", 4, outputs, None, None,
                                   (v, d * k), (v, d), gather_dim=1),
    )
    before = rc.ClosedRelationStateRecord("state_before", ("fact_g", "fact_i", "fact_w"))
    after = rc.ClosedRelationStateRecord("state_after", (*before.fact_ids, "fact_o"))
    transition = replace(rc.CertificateTransitionSpec(
        "transition_000000", spec.rule_id, tuple(sorted((g, i, w))), (o,),
        (sm_index,), pm_indices, cert.lean_theorem),
        certificate_digest=_typed_certificate_digest(cert))
    sm_nodes = [Node(0, "FW_float", [80], [81], []),
                Node(0, "BW_embedding", [1, 2, 3], [4], []),
                Node(0, "FW_float", [81], [82], [])]
    pm_nodes = []
    for rank in range(k):
        pm_nodes.extend([
            Node(rank, "FW_float", [scratch], [scratch + rank + 1], []),
            Node(rank, "BW_embedding", [gradients[rank], 2, weights[rank]], [outputs[rank]], []),
        ])
    pm_nodes.append(Node(0, "FW_float", [scratch], [scratch + k + 1], []))
    segment = rc.ClosedDependentSegmentRecord(
        "segment_000000", "component_000000", before.state_id, after.state_id,
        (transition.transition_id,), (0, len(sm_nodes)), (0, len(pm_nodes)))
    chain = SimpleNamespace(relation_facts=records, authority_facts=(),
                            states=(before, after), segments=(segment,))
    ir = SimpleNamespace(
        pm_num_ranks=k, sm_graph_ref="Fixture.sm", pm_graph_ref="Fixture.pm",
        sm_nodes=sm_nodes, pm_nodes=pm_nodes,
        init_lineages={
            1: LineageGoal(1, [b, s, d * k], list(enumerate(gradients)),
                           [[b, s, d] for _ in range(k)], gatherDim=2),
            2: LineageGoal(2, [b, s], [(0, 2)], [[b, s]], gatherDim=0),
            3: LineageGoal(3, [v, d * k], list(enumerate(weights)),
                           [[v, d] for _ in range(k)], gatherDim=1),
        },
    )
    relation = SimpleNamespace(certificates=(cert,), transition_specs=(transition,),
                               dependent_chain_plan=chain)
    return ir, relation, segment.segment_id


def witness_source(k=2, b=1, s=16, v=256, d=32):
    """Generate exact Lean source in memory; never writes Lean/build/cache files."""
    from trainverify.bridge_emitter.composer import _node_text, render_closed_relation_declarations
    from trainverify.bridge_emitter.bw_embedding_hidden_renderer import render_closed_k_rank_bw_embedding_hidden_segment

    ir, relation, segment = renderer_fixture(k, b, s, v, d)
    graph_ns = f"BWHiddenGraphK{k}B{b}S{s}V{v}D{d}"
    namespace = f"GeneratedBWHiddenK{k}B{b}S{s}V{v}D{d}"
    ir.sm_graph_ref, ir.pm_graph_ref = f"{graph_ns}.sm", f"{graph_ns}.pm"
    chunks = [
        "import denote.GraphGears", "import denote.BWEmbeddingHiddenShardK",
        "import denote.RelationCompiler", "open TrainVerify.Denote", "",
        f"namespace {graph_ns}",
        "def sm : GraphDecl := { numRanks := 1, nodes := [" + ", ".join(_node_text(n) for n in ir.sm_nodes) + "] }",
        f"def pm : GraphDecl := {{ numRanks := {k}, nodes := [" + ", ".join(_node_text(n) for n in ir.pm_nodes) + "] }",
        f"end {graph_ns}",
    ]
    chain = relation.dependent_chain_plan
    chain.complete = True  # Conditional fixture only; no whole-model closure claim.
    chain.anchor_fact = SimpleNamespace(fact_id="unused_anchor", side="sm", tid=1,
                                       shape=chain.relation_facts[0].full_shape)
    declarations = render_closed_relation_declarations(chain, namespace)
    suffix = f"end\nend TrainVerify.Denote.{namespace}\n"
    if not declarations.endswith(suffix):
        raise ValueError("closed relation declaration namespace suffix changed")
    body = "\n".join(line for line in declarations[:-len(suffix)].splitlines()
                     if not line.startswith("import "))
    chunks.extend([body, render_closed_k_rank_bw_embedding_hidden_segment(ir, relation, segment),
                   "#print axioms segment_000000_sound", suffix])
    return "\n".join(chunks)
