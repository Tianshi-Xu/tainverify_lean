"""Deterministic conditional witnesses for sequence-sharded LayerNorm gradients.

Production certificate imports are deferred until fixture invocation. Generation
returns source in memory, without writing Lean, build artifacts, or caches.
"""
from types import SimpleNamespace


def renderer_fixture(k=3, b=2, s=3, d=7, projections=("dgamma", "dbeta")):
    """Return (ir, relation, segment_id), with sparse writers and retained inputs.

    Projections are dx/dgamma/dbeta (also .1/.2.1/.2.2 or slot 0/1/2).
    At least one parameter projection is required. Width one uses the actual
    singleton ReductionRel InitGoal authority, not an invented ShardedRel.
    """
    from dataclasses import replace
    from trainverify.bridge_emitter import relation_compiler as rc
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    from trainverify.bridge_emitter.parser import LineageGoal, Node

    if any(type(n) is not int or n <= 0 for n in (k, b, s, d)):
        raise ValueError("LayerNorm fixture dimensions must be positive integers")
    aliases = {"dx": 0, "dgamma": 1, "dbeta": 2, ".1": 0, ".2.1": 1, ".2.2": 2, 0: 0, 1: 1, 2: 2}
    try:
        slots = tuple(aliases[p] for p in projections)
    except (KeyError, TypeError) as exc:
        raise ValueError("invalid LayerNorm fixture projection") from exc
    if not slots or len(set(slots)) != len(slots) or not set(slots) & {1, 2}:
        raise ValueError("LayerNorm fixture requires distinct projections including a parameter gradient")
    slots = tuple(sorted(slots))
    gradients = tuple(range(100, 100 + k))
    activations = tuple(range(100 + k, 100 + 2*k))
    output_tids = tuple(tuple(range(100 + (2 + slot)*k, 100 + (3 + slot)*k)) for slot in range(3))
    scratch = 100 + 5*k
    full, local, param = (b, s*k, d), (b, s, d), (d,)
    g = rc.RelationFactSpec("sharded", ("init:1", *(f"init:{tid}" for tid in gradients)), gather_dim=1)
    x = rc.RelationFactSpec("sharded", ("init:2", *(f"init:{tid}" for tid in activations)), gather_dim=1)
    param_kind, param_axis = ("reduction", None) if d == 1 else ("sharded", 0)
    gamma = rc.RelationFactSpec(param_kind, ("init:3", "init:3"), gather_dim=param_axis)
    beta = rc.RelationFactSpec(param_kind, ("init:4", "init:4"), gather_dim=param_axis)
    inputs = (g, x, gamma, beta)
    records = [
        rc.ClosedRelationFactRecord("fact_g", g, "sharded", 1, gradients, None, None, full, local, gather_dim=1),
        rc.ClosedRelationFactRecord("fact_x", x, "sharded", 2, activations, None, None, full, local, gather_dim=1),
        rc.ClosedRelationFactRecord("fact_gamma", gamma, param_kind, 3, (3,), None, None, param, param, gather_dim=param_axis),
        rc.ClosedRelationFactRecord("fact_beta", beta, param_kind, 4, (4,), None, None, param, param, gather_dim=param_axis),
    ]
    sm_index, pm_indices = 1, tuple(2*rank + 1 for rank in range(k))
    certs, transitions = [], []
    for slot in slots:
        name = ("dx", "dgamma", "dbeta")[slot]
        kind, axis = ("sharded", 1) if slot == 0 else ("reduction", None)
        sm_step = f"sm:{sm_index}:{slot}"
        pm_steps = tuple(f"pm:{index}:{slot}" for index in pm_indices)
        out = rc.RelationFactSpec(kind, (sm_step, *pm_steps), gather_dim=axis)
        rule = "bw-layernorm-dx-dim1-k-rank" if slot == 0 else f"bw-layernorm-{name}-sequence-reduction-k-rank"
        theorem = ("TrainVerify.Denote.bw_layernorm_dx_allGatherPrimDimN_dim1_3d" if slot == 0
                   else f"TrainVerify.Denote.bw_layernorm_{name}_sequence_reduction_rank3")
        if slot == 0:
            cert = rc.KRankBWLayernormDxCertificate(
                rule_id=rule, rank_count=k, gradient_fact=g, activation_fact=x,
                gamma_fact=gamma, beta_fact=beta, output_fact=out,
                sm_step_id=sm_step, pm_step_ids=pm_steps, lean_theorem=theorem,
                gather_dim=1, full_shape=full, shard_shape=local)
        else:
            cert = rc.KRankBWLayernormParamReductionCertificate(
                rule_id=rule, rank_count=k, gradient_fact=g, activation_fact=x,
                gamma_fact=gamma, beta_fact=beta, output_fact=out,
                sm_step_id=sm_step, pm_step_ids=pm_steps, lean_theorem=theorem,
                projection=(".2.1" if slot == 1 else ".2.2"))
        certs.append(cert)
        transitions.append(replace(rc.CertificateTransitionSpec(
            f"transition_{name}", rule, tuple(sorted(inputs)), (out,), (sm_index,), pm_indices, theorem),
            certificate_digest=_typed_certificate_digest(cert)))
        records.append(rc.ClosedRelationFactRecord(
            f"fact_{name}", out, kind, 10 + slot, output_tids[slot], None, None,
            full if slot == 0 else param, local if slot == 0 else param, gather_dim=axis))
    # The public anchor is intentionally separate from authority_facts and live.
    anchor = rc.ClosedTensorShapeFactRecord("public_anchor", "sm", 3, param, 3)
    before = rc.ClosedRelationStateRecord("state_before", (*tuple(r.fact_id for r in records[:4]), anchor.fact_id))
    after = rc.ClosedRelationStateRecord("state_after", (*tuple(r.fact_id for r in records), anchor.fact_id))
    sm_nodes = [Node(0, "FW_float", [80], [81], []),
                Node(0, "BW_layernorm", [1, 2, 3, 4], [10, 11, 12], None),
                Node(0, "FW_float", [81], [82], [])]
    pm_nodes = []
    for rank in range(k):
        pm_nodes.extend([
            Node(rank, "FW_float", [scratch], [scratch + rank + 1], []),
            Node(rank, "BW_layernorm", [gradients[rank], activations[rank], 3, 4],
                 [output_tids[slot][rank] for slot in range(3)], []),
        ])
    pm_nodes.append(Node(0, "FW_float", [scratch], [scratch + k + 1], []))
    segment = rc.ClosedDependentSegmentRecord(
        "segment_000000", "component_000000", before.state_id, after.state_id,
        tuple(t.transition_id for t in transitions), (0, len(sm_nodes)), (0, len(pm_nodes)))
    chain = SimpleNamespace(relation_facts=tuple(records), authority_facts=(), anchor_fact=anchor,
                            states=(before, after), segments=(segment,), complete=True)
    ir = SimpleNamespace(
        pm_num_ranks=k, sm_graph_ref="Fixture.sm", pm_graph_ref="Fixture.pm",
        sm_nodes=sm_nodes, pm_nodes=pm_nodes,
        init_lineages={
            1: LineageGoal(1, list(full), list(enumerate(gradients)), [list(local) for _ in range(k)], gatherDim=1),
            2: LineageGoal(2, list(full), list(enumerate(activations)), [list(local) for _ in range(k)], gatherDim=1),
            3: LineageGoal(3, [d], [(0, 3)], [[d]], gatherDim=0),
            4: LineageGoal(4, [d], [(0, 4)], [[d]], gatherDim=0),
        },
    )
    relation = SimpleNamespace(certificates=tuple(certs), transition_specs=tuple(transitions), dependent_chain_plan=chain)
    return ir, relation, segment.segment_id


def witness_source(k=3, b=2, s=3, d=7, projections=("dgamma", "dbeta")):
    """Return a self-contained conditional Lean witness with explicit world size."""
    from trainverify.bridge_emitter.composer import _node_text, render_closed_relation_declarations
    from trainverify.bridge_emitter.bw_layernorm_triple_renderer import render_closed_k_rank_bw_layernorm_triple_segment

    ir, relation, segment_id = renderer_fixture(k, b, s, d, projections)
    tags = "".join({".1": "Dx", ".2.1": "Dgamma", ".2.2": "Dbeta"}[
        ".1" if c.rule_id == "bw-layernorm-dx-dim1-k-rank" else c.projection] for c in relation.certificates)
    suffix_name = f"K{k}B{b}S{s}D{d}{tags}"
    graph_ns, namespace = f"BWLayernormParamGraph{suffix_name}", f"GeneratedBWLayernormParam{suffix_name}"
    ir.sm_graph_ref, ir.pm_graph_ref = f"{graph_ns}.sm", f"{graph_ns}.pm"
    chunks = ["import denote.GraphGears", "import denote.RelationCompiler", "import denote.KRankBWLayernormParam"]
    if any(c.rule_id == "bw-layernorm-dx-dim1-k-rank" for c in relation.certificates):
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
    chunks.extend([body, render_closed_k_rank_bw_layernorm_triple_segment(ir, relation, segment_id),
                   f"#print axioms {segment_id}_sound", f"#print axioms {segment_id}", suffix])
    return "\n".join(chunks)
