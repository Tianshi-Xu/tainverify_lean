"""Closed one-fold renderer for the hybrid attention component.

This renderer intentionally owns the whole graph interval of the component.  It
materialises exactly one SM fold and one PM fold, extracts semantic writer
values from those named folds, proves dependency-only intermediate relations,
and publishes only the relations live in the segment post-state.

The implementation is data driven: dimensions, tensor ids, ranks, projections,
and metadata ids come from typed certificates, materialised relation facts, and
literal graph nodes.  No segment-854 constants occur here.
"""
from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Callable, Iterable, Sequence


def _certificate_digest(certificate: object) -> str:
    payload = {"type": type(certificate).__name__, "fields": asdict(certificate)}
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def _unique(items: Iterable[object], message: str):
    values = list(items)
    if len(values) != 1:
        raise ValueError(f"{message}: expected one, found {len(values)}")
    return values[0]


def _duplicates(values: Sequence[object]) -> bool:
    return len(values) != len(set(values))


@dataclass(frozen=True)
class _Row:
    ordinal: int
    transition: object
    certificate: object
    pres: tuple[object, ...]
    posts: tuple[object, ...]


class _Emitter:
    def __init__(self, ir, relation, segment, before, after, rows, node_text, shape_text,
                 mixed_value):
        self.ir = ir
        self.relation = relation
        self.segment = segment
        self.before = before
        self.after = after
        self.rows = rows
        self.node_text = node_text
        self.shape_text = shape_text
        self.mixed_value = mixed_value
        self.sid = segment.segment_id
        self.sm_nodes = tuple(ir.sm_nodes[slice(*segment.sm_range)])
        self.pm_nodes = tuple(ir.pm_nodes[slice(*segment.pm_range)])
        self.sm_name = f"{self.sid}_smNodes"
        self.pm_name = f"{self.sid}_pmNodes"
        self.sm_final = f"{self.sid}_smFinal"
        self.pm_final = f"{self.sid}_pmFinal"
        self.declarations: list[str] = []
        self.lines: list[str] = []
        self.writer_names: dict[tuple[str, int, int], str] = {}
        self.proofs: dict[str, str] = {}
        self.authority = {f.fact_id: f for f in relation.dependent_chain_plan.authority_facts}
        self.live_authority = tuple(
            self.authority[fid] for fid in before.fact_ids if fid in self.authority
        )

    def shape(self, value) -> str:
        return self.shape_text(list(value))

    def final(self, side: str) -> str:
        return f"({self.sm_final} smStore)" if side == "sm" else f"({self.pm_final} pmStore)"

    def graph(self, side: str) -> str:
        return self.ir.sm_graph_ref if side == "sm" else self.ir.pm_graph_ref

    def frame(self, side: str):
        return self.sm_nodes if side == "sm" else self.pm_nodes

    def nodes_name(self, side: str) -> str:
        return self.sm_name if side == "sm" else self.pm_name

    def store(self, side: str) -> str:
        return "smStore" if side == "sm" else "pmStore"

    def position(self, side: str, absolute: int) -> int:
        start = self.segment.sm_range[0] if side == "sm" else self.segment.pm_range[0]
        frame = self.frame(side)
        position = absolute - start
        if not 0 <= position < len(frame):
            raise ValueError(f"{side} writer {absolute} lies outside complete component frame")
        return position

    def authority_fact(self, kind: str, predicate: Callable[[object], bool], label: str):
        return _unique((f for f in self.live_authority
                        if getattr(f, "kind", None) == kind and predicate(f)),
                       f"hybrid component lacks unique live {label} authority")

    def proof_of(self, fact) -> str:
        if fact.fact_id in self.proofs:
            return self.proofs[fact.fact_id]
        if fact.fact_id in self.before.fact_ids:
            name = f"hpre_{len(self.proofs):02d}"
            self.lines.append(
                f"  have {name} : {fact.fact_id}.Holds ({self.sm_final} smStore) "
                f"({self.pm_final} pmStore) := hframe _ (by native_decide)"
            )
            self.proofs[fact.fact_id] = name
            return name
        raise ValueError(f"transition consumes unavailable fact {fact.fact_id}")

    @staticmethod
    def _ordinary_apply(graph: str, node, operation: str, output_tid: int) -> list[str]:
        common = [
            "rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective "
            "(hshuffle := by native_decide) (hunshuffle := by native_decide) "
            "(hattn := by native_decide)]",
            "unfold applyNodeDistributed",
            "rw [if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), if_neg (by native_decide), applyNodeRingAttn_eq_applyNode_of_not_ring]",
        ]
        side_goals = ["· native_decide", "· native_decide"]
        if operation == "multiref":
            return common + [
                f"· exact applyNode_fw_multiref_at {graph} t {node.rank} {node.ins[0]} "
                f"{self_list(node.outs)} {len(node.outs)} rfl {output_tid} "
                "(by native_decide)", *side_goals,
            ]
        if operation == "to":
            return common + [
                f"· exact applyNode_fw_to_out {graph} t {node.rank} {node.ins[0]} "
                f"{node.outs[0]} []", *side_goals,
            ]
        if operation == "reshape":
            return common + [
                f"· exact applyNode_fw_reshape_out {graph} t {node.rank} {node.ins[0]} "
                f"{node.outs[0]} {self_list(node.params or [])}", *side_goals,
            ]
        if operation == "rms":
            return common + [
                f"· exact applyNode_fw_rms_norm_out_1p {graph} t {node.rank} "
                f"{node.ins[0]} {node.ins[1]} {node.outs[0]}", *side_goals,
            ]
        if operation == "per_head":
            return common + [
                f"· exact applyNode_fw_per_head_mix_precision_linear_out {graph} t "
                f"{node.rank} {node.ins[0]} {node.ins[1]} {node.outs[0]} []", *side_goals,
            ]
        if operation == "allgather":
            return common + [
                f"· exact applyNode_allGatherPrimDimN_out {graph} t {node.rank} "
                f"{self_list(node.ins)} {node.outs[0]} {(node.params or [None])[0]}",
                *side_goals,
            ]
        raise ValueError(f"unsupported ordinary writer operation {operation}")

    def writer(self, side: str, absolute: int, output_tid: int, expression: str,
               operation: str, input_tids: Sequence[int] | None = None) -> str:
        key = (side, absolute, output_tid)
        if key in self.writer_names:
            return self.writer_names[key]
        position = self.position(side, absolute)
        node = self.frame(side)[position]
        if output_tid not in node.outs:
            raise ValueError(f"writer {side}:{absolute} does not produce TID {output_tid}")
        name = f"{self.sid}_{side}Writer_{len(self.writer_names):03d}"
        store = self.store(side)
        final = self.final(side)
        graph = self.graph(side)
        nodes_name = self.nodes_name(side)
        semantic_inputs = tuple(node.ins if input_tids is None else input_tids)
        helper = self.mixed_value(
            name="hout", graph=graph, initial_store=store, final_store=final,
            final_equality="hfinal", nodes_name=nodes_name, nodes=list(self.frame(side)),
            position=position, output_tid=output_tid, input_tids=semantic_inputs,
            written_tids={tid for item in self.frame(side) for tid in item.outs},
            expression=expression,
            apply_lines=self._ordinary_apply(graph, node, operation, output_tid),
        )
        self.declarations.extend([
            f"private theorem {name} ({store} : Store) :",
            f"    {final} {output_tid} = {expression.format(store=final)} := by",
            f"  have hfinal : {final} = {nodes_name}.foldl "
            f"(applyNodeDistributedFaithful {graph}) {store} := by",
            f"    unfold {self.sm_final if side == 'sm' else self.pm_final}",
            "    rfl",
            *(line[2:] if line.startswith("  ") else line for line in helper),
            "  exact hout", "",
        ])
        self.writer_names[key] = name
        return name

    def relation_change(self, fact, store_sm: str, store_pm: str) -> str:
        full, shard = self.shape(fact.full_shape), self.shape(fact.shard_shape)
        if fact.kind == "joined":
            return (f"{store_sm} {fact.sm_tid} = {store_pm} {fact.joined_pm_tid} ∧ "
                    f"({store_sm} {fact.sm_tid}).shape = {full} ∧ "
                    f"({store_pm} {fact.joined_pm_tid}).shape = {full}")
        if fact.kind == "sharded":
            values = ", ".join(f"{store_pm} {tid}" for tid in fact.pm_tids)
            return f"ShardedRel ({store_sm} {fact.sm_tid}) [{values}] {fact.gather_dim} {full} {shard}"
        if fact.kind == "ordinary":
            return (f"GeneratedPatterns.Ordinary2Rel ({store_sm} {fact.sm_tid}) "
                    f"({store_pm} {fact.pm_rank0_tid}) ({store_pm} {fact.pm_rank1_tid}) "
                    f"{full} {shard}")
        if fact.kind == "zigzag":
            return (f"GeneratedPatterns.Zigzag2Rel ({store_sm} {fact.sm_tid}) "
                    f"({store_pm} {fact.pm_rank0_tid}) ({store_pm} {fact.pm_rank1_tid}) "
                    f"({store_pm} {fact.metadata_tid}) {full} {shard}")
        raise ValueError(f"unsupported relation kind {fact.kind}")

    def add_proof(self, fact, name: str):
        if fact.fact_id in self.proofs:
            raise ValueError(f"duplicate proof publication for {fact.fact_id}")
        self.proofs[fact.fact_id] = name

    def emit_alias(self, row: _Row):
        pre, post = row.pres[0], row.posts[0]
        cert, transition = row.certificate, row.transition
        hin = self.proof_of(pre)
        if len(transition.sm_node_indices) != 1:
            raise ValueError("multiref alias must own one SM writer")
        indices = tuple(cert.output_indices)
        sm_i = transition.sm_node_indices[0]
        pm_is = tuple(transition.pm_node_indices)
        if pre.kind in {"ordinary", "zigzag"}:
            if len(pm_is) != 2 or len(indices) != 3:
                raise ValueError("two-rank multiref alias requires three projections")
            writers = (("sm", sm_i, indices[0], post.sm_tid),
                       ("pm", pm_is[0], indices[1], post.pm_rank0_tid),
                       ("pm", pm_is[1], indices[2], post.pm_rank1_tid))
        elif pre.kind == "joined":
            if len(pm_is) != 1 or len(indices) < 2:
                raise ValueError("joined multiref alias requires two projections")
            writers = (("sm", sm_i, indices[0], post.sm_tid),
                       ("pm", pm_is[0], indices[1], post.joined_pm_tid))
        else:
            raise ValueError("multiref alias received unsupported layout")
        names = []
        for side, absolute, projection, tid in writers:
            node = (self.ir.sm_nodes if side == "sm" else self.ir.pm_nodes)[absolute]
            if node.op != "FW_multiref" or node.ins != [pre.sm_tid if side == "sm" else
                    (pre.joined_pm_tid if pre.kind == "joined" else
                     (pre.pm_rank0_tid if node.rank == 0 else pre.pm_rank1_tid))]:
                raise ValueError("multiref literal writer does not match typed pre-fact")
            if cert.arity != len(node.outs) or not 0 <= projection < cert.arity or node.outs[projection] != tid:
                raise ValueError("multiref projection/arity authority mismatch")
            names.append(self.writer(side, absolute, tid, f"{{store}} {node.ins[0]}",
                                     "multiref", (node.ins[0],)))
        name = f"hrel_{row.ordinal:02d}"
        final_sm, final_pm = self.final("sm"), self.final("pm")
        self.lines.extend([
            f"  have {name} : {post.fact_id}.Holds {final_sm} {final_pm} := by",
            f"    change {self.relation_change(pre, final_sm, final_pm)} at {hin}",
            f"    change {self.relation_change(post, final_sm, final_pm)}",
            f"    rw [{', '.join(n + (' smStore' if w[0] == 'sm' else ' pmStore') for n, w in zip(names, writers))}]",
            f"    exact {hin}",
        ])
        self.add_proof(post, name)

    def _weight_authority(self, tid: int, shape: tuple[int, ...], need_shape: bool = True):
        eq = self.authority_fact(
            "tensor_eq",
            lambda f: (f.left_side, f.left_tid, f.right_side, f.right_tid) ==
                      ("sm", tid, "pm", tid), f"weight equality TID {tid}")
        shp = None
        if need_shape:
            shp = self.authority_fact(
                "tensor_shape", lambda f: (f.side, f.tid, tuple(f.shape)) ==
                ("pm", tid, tuple(shape)), f"weight shape TID {tid}")
        return eq, shp

    def _binary_writers(self, row, pre, post, operation, function):
        t = row.transition
        if len(t.sm_node_indices) != 1:
            raise ValueError(f"{operation} requires one SM writer")
        sm_i = t.sm_node_indices[0]
        sm = self.ir.sm_nodes[sm_i]
        if pre.kind in {"ordinary", "zigzag"}:
            if len(t.pm_node_indices) != 2:
                raise ValueError(f"{operation} two-rank layout requires two PM writers")
            sides = (("sm", sm_i, post.sm_tid),
                     ("pm", t.pm_node_indices[0], post.pm_rank0_tid),
                     ("pm", t.pm_node_indices[1], post.pm_rank1_tid))
        elif pre.kind == "joined":
            if len(t.pm_node_indices) != 1:
                raise ValueError(f"{operation} joined layout requires one PM writer")
            sides = (("sm", sm_i, post.sm_tid),
                     ("pm", t.pm_node_indices[0], post.joined_pm_tid))
        else:
            raise ValueError(f"{operation} unsupported layout {pre.kind}")
        names = []
        for side, absolute, out_tid in sides:
            node = (self.ir.sm_nodes if side == "sm" else self.ir.pm_nodes)[absolute]
            if node.op != sm.op or len(node.ins) != 2 or node.outs != [out_tid] or node.params:
                raise ValueError(f"{operation} writer signature mismatch")
            expr = f"{function} ({{store}} {node.ins[0]}) ({{store}} {node.ins[1]})"
            names.append((side, self.writer(side, absolute, out_tid, expr, operation)))
        return sm, names

    def emit_rms(self, row: _Row):
        cert, post = row.certificate, row.posts[0]
        data = _unique((f for f in row.pres if getattr(f, "source", None) != cert.weight_fact),
                       "RMS data role is ambiguous")
        weight = _unique((f for f in row.pres if getattr(f, "source", None) == cert.weight_fact),
                         "RMS weight role is ambiguous")
        hin, hw = self.proof_of(data), self.proof_of(weight)
        sm, writers = self._binary_writers(row, data, post, "rms", "fw_rms_norm")
        if sm.ins[1] != cert.replicated_weight_tid:
            raise ValueError("RMS typed replicated-weight TID disagrees with literal writer")
        rows, hidden = data.full_shape if data.kind == "joined" else data.shard_shape
        name = f"hrel_{row.ordinal:02d}"
        fs, fp = self.final("sm"), self.final("pm")
        rewrites = ", ".join(n + (" smStore" if side == "sm" else " pmStore")
                             for side, n in writers)
        self.lines.extend([
            f"  have {name} : {post.fact_id}.Holds {fs} {fp} := by",
            f"    change {self.relation_change(data, fs, fp)} at {hin}",
            f"    change {fs} {weight.sm_tid} = {fp} {weight.joined_pm_tid} ∧ _ at {hw}",
            f"    change {self.relation_change(post, fs, fp)}",
            f"    rw [{rewrites}]",
        ])
        if data.kind == "joined":
            self.lines.append(f"    exact JoinedRel.rms_norm {rows} {hidden} {hin} {hw}.1")
        else:
            self.lines.extend([
                f"    rw [{hw}.1]",
                f"    exact GeneratedPatterns.Zigzag2Rel.rms_norm {rows} {hidden} {hin} "
                f"(by native_decide) (by native_decide) rfl",
            ])
        self.add_proof(post, name)

    def emit_per_head(self, row: _Row):
        pre, post, cert = row.pres[0], row.posts[0], row.certificate
        hin = self.proof_of(pre)
        sm, writers = self._binary_writers(row, pre, post, "per_head", "fw_per_head_linear")
        tid = cert.replicated_weight_tid
        if any((self.ir.sm_nodes if side == "sm" else self.ir.pm_nodes)[absolute].ins[1] != tid
               for side, absolute in (("sm", row.transition.sm_node_indices[0]),
               *(('pm', i) for i in row.transition.pm_node_indices))):
            raise ValueError("per-head replicated weight binding mismatch")
        if len(pre.full_shape) != 2 or len(post.full_shape) != 3:
            raise ValueError("per-head typed shapes must be rank 2 -> rank 3")
        rows, input_dim = pre.full_shape if pre.kind == "joined" else pre.shard_shape
        _, heads, head_dim = post.full_shape if pre.kind == "joined" else post.shard_shape
        weight_shape = (heads, head_dim, input_dim)
        eq, shp = self._weight_authority(tid, weight_shape)
        heq = self.proof_of(eq); hshape = self.proof_of(shp)
        fs, fp = self.final("sm"), self.final("pm")
        name = f"hrel_{row.ordinal:02d}"
        rewrites = ", ".join(n + (" smStore" if side == "sm" else " pmStore")
                             for side, n in writers)
        self.lines.extend([
            f"  have {name} : {post.fact_id}.Holds {fs} {fp} := by",
            f"    change {self.relation_change(pre, fs, fp)} at {hin}",
            f"    change {fs} {tid} = {fp} {tid} at {heq}",
            f"    change ({fp} {tid}).shape = {self.shape(weight_shape)} at {hshape}",
            f"    change {self.relation_change(post, fs, fp)}",
            f"    rw [{rewrites}]",
        ])
        if pre.kind == "joined":
            self.lines.extend([
                f"    exact JoinedRel.per_head_linear {rows} {input_dim} {heads} {head_dim} "
                f"{hin} {hshape} {heq}"
            ])
        else:
            self.lines.extend([
                f"    rw [{heq}]",
                f"    exact GeneratedPatterns.Zigzag2Rel.per_head_linear {rows} {input_dim} "
                f"{heads} {head_dim} {hin} {hshape}",
                "      (by native_decide) (by native_decide) (by native_decide) "
                "(by native_decide)",
            ])
        self.add_proof(post, name)

    def emit_flatten(self, row: _Row):
        pre, post = row.pres[0], row.posts[0]
        hin = self.proof_of(pre)
        if pre.kind != "zigzag" or len(pre.shard_shape) != 3:
            raise ValueError("hybrid flatten requires zigzag rank-3 input")
        t = row.transition
        if len(t.sm_node_indices) != 1 or len(t.pm_node_indices) != 2:
            raise ValueError("zigzag flatten requires 1xSM + 2xPM")
        entries = (("sm", t.sm_node_indices[0], post.sm_tid, post.full_shape),
                   ("pm", t.pm_node_indices[0], post.pm_rank0_tid, post.shard_shape),
                   ("pm", t.pm_node_indices[1], post.pm_rank1_tid, post.shard_shape))
        writers = []
        for side, absolute, tid, target in entries:
            node = (self.ir.sm_nodes if side == "sm" else self.ir.pm_nodes)[absolute]
            if node.op != "FW_reshape" or tuple(node.params or ()) != tuple(target):
                raise ValueError("flatten literal target disagrees with typed output shape")
            writers.append((side, self.writer(side, absolute, tid,
                f"fw_view {self.shape(target)} ({{store}} {node.ins[0]})", "reshape")))
        ldim, heads, width = pre.shard_shape
        fs, fp = self.final("sm"), self.final("pm")
        name = f"hrel_{row.ordinal:02d}"
        rw = ", ".join(n + (" smStore" if side == "sm" else " pmStore") for side, n in writers)
        self.lines.extend([
            f"  have {name} : {post.fact_id}.Holds {fs} {fp} := by",
            f"    change {self.relation_change(pre, fs, fp)} at {hin}",
            f"    change {self.relation_change(post, fs, fp)}",
            f"    rw [{rw}]",
            f"    exact GeneratedPatterns.Zigzag2Rel.view_3d_to_2d {ldim} {heads} {width} {hin}",
            "      (by native_decide) (by native_decide) (by native_decide)",
        ])
        self.add_proof(post, name)

    def emit_joined_view(self, row: _Row):
        pre, post, cert = row.pres[0], row.posts[0], row.certificate
        hin = self.proof_of(pre)
        t = row.transition
        if len(t.sm_node_indices) != 1 or len(t.pm_node_indices) != 1:
            raise ValueError("joined unary requires one writer on each side")
        writers = []
        for side, absolute, tid in (("sm", t.sm_node_indices[0], post.sm_tid),
                                    ("pm", t.pm_node_indices[0], post.joined_pm_tid)):
            node = (self.ir.sm_nodes if side == "sm" else self.ir.pm_nodes)[absolute]
            if node.op != cert.operator or node.rank != (0 if side == "sm" else cert.pm_rank):
                raise ValueError("joined unary literal operator/rank mismatch")
            if cert.operator == "FW_to":
                expr, op = f"{{store}} {node.ins[0]}", "to"
            elif cert.operator in {"FW_view", "FW_reshape"}:
                expr, op = f"fw_view {self.shape(post.full_shape)} ({{store}} {node.ins[0]})", "reshape"
            else:
                raise ValueError(f"unsupported joined unary operator {cert.operator}")
            writers.append((side, self.writer(side, absolute, tid, expr, op)))
        fs, fp = self.final("sm"), self.final("pm")
        name = f"hrel_{row.ordinal:02d}"
        rw = ", ".join(n + (" smStore" if side == "sm" else " pmStore") for side, n in writers)
        theorem = "JoinedRel.identity" if cert.operator == "FW_to" else "JoinedRel.fw_view"
        self.lines.extend([
            f"  have {name} : {post.fact_id}.Holds {fs} {fp} := by",
            f"    change {self.relation_change(pre, fs, fp)} at {hin}",
            f"    change {self.relation_change(post, fs, fp)}",
            f"    rw [{rw}]",
            f"    exact {theorem} {self.shape(pre.full_shape)} {hin}" if theorem.endswith("identity") else
            f"    exact {theorem} {self.shape(post.full_shape)} {self.shape(pre.full_shape)} {hin}",
        ])
        self.add_proof(post, name)

    def emit_allgather(self, row: _Row):
        pre, post, cert = row.pres[0], row.posts[0], row.certificate
        hin = self.proof_of(pre)
        t = row.transition
        if t.sm_node_indices or len(t.pm_node_indices) != 1:
            raise ValueError("AllGather reconstruction must own one PM-only writer")
        absolute = t.pm_node_indices[0]
        node = self.ir.pm_nodes[absolute]
        k, dim = cert.rank_count, cert.gather_dim
        if (node.op != "AllGatherPrim" or node.rank != 0 or tuple(node.ins) != tuple(pre.pm_tids)
                or node.outs != [post.joined_pm_tid] or tuple(node.params or ()) != (dim,)
                or k != len(pre.pm_tids)):
            raise ValueError("AllGather literal writer disagrees with typed certificate")
        expr = f"allGatherPrimDimN {dim} {k} 0 [" + ", ".join(
            f"{{store}} {tid}" for tid in pre.pm_tids) + "]"
        writer = self.writer("pm", absolute, post.joined_pm_tid, expr, "allgather", pre.pm_tids)
        fs, fp = self.final("sm"), self.final("pm")
        name = f"hrel_{row.ordinal:02d}"
        self.lines.extend([
            f"  have {name} : {post.fact_id}.Holds {fs} {fp} := by",
            f"    change {self.relation_change(pre, fs, fp)} at {hin}",
            f"    have hjoined : {fs} {pre.sm_tid} = {fp} {post.joined_pm_tid} :=",
            f"      (ShardedRel.to_joined_allGather {hin}).trans ({writer} pmStore).symm",
            f"    change {self.relation_change(post, fs, fp)}",
            f"    refine ⟨hjoined, {hin}.full_shape, ?_⟩",
            "    rw [← hjoined]",
            f"    exact {hin}.full_shape",
        ])
        self.add_proof(post, name)

    def emit_shuffle(self, row: _Row):
        """Emit the faithful shuffle using final-store sources.

        The collective theorem is intentionally applied to the named final
        stores.  Writer extraction then identifies the component outputs with
        those exact source applications; no second fold is introduced.
        """
        pre, post, cert = row.pres[0], row.posts[0], row.certificate
        hin = self.proof_of(pre)
        t = row.transition
        if len(t.sm_node_indices) != 1 or len(t.pm_node_indices) != cert.num_ranks:
            raise ValueError("faithful shuffle footprint/rank count mismatch")
        sm_i = t.sm_node_indices[0]
        sm = self.ir.sm_nodes[sm_i]
        pms = tuple(self.ir.pm_nodes[i] for i in t.pm_node_indices)
        if cert.num_ranks != 2 or self.ir.pm_num_ranks != 2:
            raise ValueError("hybrid attention faithful shuffle currently requires typed rank count two")
        if (sm.op != "FW_maybe_shuffle" or any(n.op != sm.op for n in pms)
                or tuple(n.rank for n in pms) != (0, 1)
                or sm.ins[1] != cert.node_metadata_tid
                or any(n.ins[1] != cert.node_metadata_tid for n in pms)):
            raise ValueError("faithful shuffle literal topology/metadata mismatch")
        # The generic middle-writer helper can extract the faithful node value
        # directly.  Its expression mentions all collective inputs and metadata.
        entries = (("sm", sm_i, sm, (sm.ins[0], sm.ins[0]), (sm,)),
                   ("pm", t.pm_node_indices[0], pms[0], (pms[0].ins[0], pms[1].ins[0]), pms),
                   ("pm", t.pm_node_indices[1], pms[1], (pms[0].ins[0], pms[1].ins[0]), pms))
        writers = []
        for side, absolute, node, data, buddies in entries:
            graph, rank = self.graph(side), node.params[1]
            expression = (f"ZigzagCollective.fw_maybe_shuffle_collective [{{store}} {data[0]}, "
                          f"{{store}} {data[1]}] (decodeCuSeqlens ({{store}} {cert.node_metadata_tid})) "
                          f"{node.params[0]} {rank}")
            # Shuffle is the one faithful operation: use a local apply proof,
            # then the same generic one-fold extractor.
            key = (side, absolute, node.outs[0])
            if key not in self.writer_names:
                name = f"{self.sid}_{side}Writer_{len(self.writer_names):03d}"
                position = self.position(side, absolute)
                store, final, nodes_name = self.store(side), self.final(side), self.nodes_name(side)
                apply_lines = [
                    "rw [applyNodeDistributedFaithful_shuffle_out]",
                    "unfold applyNodeFaithfulShuffleValue",
                    f"rw [show {graph}.replicaBuddies {self.node_text(node)} = "
                    f"[{', '.join(self.node_text(x) for x in buddies)}] by native_decide]",
                    "rfl",
                ]
                helper = self.mixed_value(
                    name="hout", graph=graph, initial_store=store, final_store=final,
                    final_equality="hfinal", nodes_name=nodes_name, nodes=list(self.frame(side)),
                    position=position, output_tid=node.outs[0],
                    input_tids=(*data, cert.node_metadata_tid),
                    written_tids={tid for n in self.frame(side) for tid in n.outs},
                    expression=expression, apply_lines=apply_lines)
                self.declarations.extend([
                    f"private theorem {name} ({store} : Store) :",
                    f"    {final} {node.outs[0]} = {expression.format(store=final)} := by",
                    f"  have hfinal : {final} = {nodes_name}.foldl "
                    f"(applyNodeDistributedFaithful {graph}) {store} := by",
                    f"    unfold {self.sm_final if side == 'sm' else self.pm_final}", "    rfl",
                    *(line[2:] if line.startswith("  ") else line for line in helper),
                    "  exact hout", "",
                ])
                self.writer_names[key] = name
            writers.append((side, self.writer_names[key]))
        # Bridge each extracted collective expression back to the faithful
        # graph-level value expected by to_zigzag_shuffle.
        faithful_writers = []
        for number, ((side, _absolute, node, _data, buddies),
                     (_writer_side, writer_name)) in enumerate(zip(entries, writers)):
            graph, store, final = self.graph(side), self.store(side), self.final(side)
            faithful = f"hshuffleWriter_{row.ordinal:02d}_{number}"
            self.lines.extend([
                f"  have {faithful} : {final} {node.outs[0]} = "
                f"applyNodeFaithfulShuffleValue {graph} {final} {self.node_text(node)} := by",
                f"    rw [{writer_name} {store}]",
                "    unfold applyNodeFaithfulShuffleValue",
                f"    rw [show {graph}.replicaBuddies {self.node_text(node)} = "
                f"[{', '.join(self.node_text(x) for x in buddies)}] by native_decide]",
                "    rfl",
            ])
            faithful_writers.append(faithful)
        alias = self.authority_fact("tensor_eq", lambda f:
            (f.left_side, f.left_tid, f.right_side) == ("pm", cert.node_metadata_tid, "pm"),
            "shuffle metadata alias")
        packed = self.authority_fact("packed_cu", lambda f:
            (f.side, f.tid, f.num_ranks, f.total_tokens) ==
            ("pm", alias.right_tid, cert.num_ranks, cert.total_tokens),
            "shuffle packed-cu contract")
        halias, hpacked = self.proof_of(alias), self.proof_of(packed)
        fs, fp = self.final("sm"), self.final("pm")
        name = f"hrel_{row.ordinal:02d}"
        rw = ", ".join(faithful_writers)
        self.lines.extend([
            f"  have {name} : {post.fact_id}.Holds {fs} {fp} := by",
            f"    change {self.relation_change(pre, fs, fp)} at {hin}",
            f"    change {fp} {cert.node_metadata_tid} = {fp} {alias.right_tid} at {halias}",
            f"    change ZigzagCollective.PackedCuSeqlensWF ({fp} {packed.tid}) "
            f"{cert.total_tokens} {cert.num_ranks} at {hpacked}",
            f"    have hpackedActual : ZigzagCollective.PackedCuSeqlensWF "
            f"({fp} {cert.node_metadata_tid}) {cert.total_tokens} {cert.num_ranks} := by",
            f"      rw [{halias}]", f"      exact {hpacked}",
            f"    have core := TrainVerify.Denote.RelationCompiler.Ordinary2Rel.to_zigzag_shuffle",
            f"      {self.ir.sm_graph_ref} {self.ir.pm_graph_ref} {fs} {fp} "
            f"{self.node_text(sm)} {self.node_text(pms[0])} {self.node_text(pms[1])} "
            f"({fp} {cert.node_metadata_tid}) {hin} hpackedActual",
            "      (by native_decide) (by native_decide) (by native_decide)",
            "      rfl rfl rfl rfl rfl (by native_decide) rfl rfl rfl",
            f"    change {self.relation_change(post, fs, fp)}",
            f"    rw [{rw}]",
            "    exact core",
        ])
        self.add_proof(post, name)

    def emit_row(self, row: _Row):
        name = type(row.certificate).__name__
        if name == "FaithfulShuffleCertificate": self.emit_shuffle(row)
        elif name == "MultirefAliasCertificate": self.emit_alias(row)
        elif name == "FrontierRMSNormCertificate": self.emit_rms(row)
        elif name == "PerHeadLinearRelationCertificate": self.emit_per_head(row)
        elif name == "FrontierFlatten3DCertificate": self.emit_flatten(row)
        elif name == "KRankAllGatherReconstructionCertificate": self.emit_allgather(row)
        elif name == "JoinedUnaryViewCertificate": self.emit_joined_view(row)
        else: raise TypeError(f"unsupported hybrid certificate class {name}")

    def render(self) -> str:
        sm_text = ", ".join(self.node_text(n) for n in self.sm_nodes)
        pm_text = ", ".join(self.node_text(n) for n in self.pm_nodes)
        header = [
            f"private def {self.sm_name} : List NodeDecl := [{sm_text}]",
            f"private def {self.pm_name} : List NodeDecl := [{pm_text}]",
            f"@[irreducible] private def {self.sm_final} (s : Store) : Store :=",
            f"  {self.sm_name}.foldl (applyNodeDistributedFaithful {self.ir.sm_graph_ref}) s",
            f"@[irreducible] private def {self.pm_final} (s : Store) : Store :=",
            f"  {self.pm_name}.foldl (applyNodeDistributedFaithful {self.ir.pm_graph_ref}) s", "",
        ]
        body = [
            f"private theorem {self.sid}_publish (smStore pmStore : Store)",
            f"    (hstate : {self.before.state_id}.Holds smStore pmStore) :",
            f"    {self.after.state_id}.Holds ({self.sm_final} smStore) ({self.pm_final} pmStore) := by",
            f"  have hframe : {self.before.state_id}.Holds ({self.sm_final} smStore) "
            f"({self.pm_final} pmStore) := by",
            f"    unfold {self.sm_final} {self.pm_final}",
            f"    apply RelationState.Holds.fold_frame {self.sm_name} {self.pm_name} smStore pmStore hstate",
            "    · native_decide", "    · native_decide", "    · native_decide", "    · native_decide",
        ]
        self.lines = []
        for row in self.rows:
            self.emit_row(row)
        live_fresh = tuple(fid for fid in self.after.fact_ids if fid not in self.before.fact_ids)
        if not live_fresh:
            raise ValueError("hybrid attention post-state has no fresh publication")
        missing = [fid for fid in live_fresh if fid not in self.proofs]
        if missing:
            raise ValueError(f"hybrid attention did not prove live outputs: {missing}")
        body.extend(self.lines)
        body.extend([
            "  intro fact hfact",
            f"  have covered : fact ∈ [{', '.join(live_fresh)}] ++ {self.before.state_id}.facts :=",
            f"    (show {self.after.state_id}.facts ⊆ [{', '.join(live_fresh)}] ++ "
            f"{self.before.state_id}.facts by native_decide) hfact",
            "  simp only [List.mem_append] at covered",
            "  rcases covered with fresh | old",
            "  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh",
            f"    rcases fresh with {' | '.join('rfl' for _ in live_fresh)}",
        ])
        body.extend(f"    · exact {self.proofs[fid]}" for fid in live_fresh)
        body.extend(["  · exact hframe fact old", "",
            f"private def {self.sid} : ClosedDepSegmentCertificate {self.ir.sm_graph_ref} "
            f"{self.ir.pm_graph_ref} {self.before.state_id} {self.after.state_id} where",
            f"  smNodes := {self.sm_name}", f"  pmNodes := {self.pm_name}", "  sound := by",
            "    intro smStore pmStore hstate",
            f"    simpa only [{self.sm_final}, {self.pm_final}] using",
            f"      {self.sid}_publish smStore pmStore hstate", ""])
        return "\n".join(header + self.declarations + body)


def self_list(values: Sequence[int]) -> str:
    return "[" + ", ".join(str(x) for x in values) + "]"


def render_closed_hybrid_attention_component_segment(ir, relation, segment_id: str) -> str:
    """Render a typed hybrid attention fanout as one fold per side."""
    try:
        from .composer import _node_text, _shape_text, _render_mixed_final_value
        from .relation_compiler import (
            FaithfulShuffleCertificate, MultirefAliasCertificate,
            FrontierRMSNormCertificate, PerHeadLinearRelationCertificate,
            FrontierFlatten3DCertificate, KRankAllGatherReconstructionCertificate,
            JoinedUnaryViewCertificate,
        )
    except ImportError:
        from composer import _node_text, _shape_text, _render_mixed_final_value
        from relation_compiler import (
            FaithfulShuffleCertificate, MultirefAliasCertificate,
            FrontierRMSNormCertificate, PerHeadLinearRelationCertificate,
            FrontierFlatten3DCertificate, KRankAllGatherReconstructionCertificate,
            JoinedUnaryViewCertificate,
        )
    classes = {c.__name__: c for c in (
        FaithfulShuffleCertificate, MultirefAliasCertificate,
        FrontierRMSNormCertificate, PerHeadLinearRelationCertificate,
        FrontierFlatten3DCertificate, KRankAllGatherReconstructionCertificate,
        JoinedUnaryViewCertificate,
    )}
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("hybrid attention renderer requires a complete closed chain")
    segment = _unique((s for s in chain.segments if s.segment_id == segment_id),
                      "hybrid attention segment identity is ambiguous")
    if not segment.transition_ids or _duplicates(segment.transition_ids):
        raise ValueError("hybrid attention component requires distinct positive transitions")
    transition_ids = [t.transition_id for t in relation.transition_specs]
    if _duplicates(transition_ids):
        raise ValueError("relation contains duplicate transition identity")
    by_id = {t.transition_id: t for t in relation.transition_specs}
    try:
        transitions = tuple(by_id[tid] for tid in segment.transition_ids)
    except KeyError as exc:
        raise ValueError("segment transition is absent from relation authority") from exc
    fact_sources = [f.source for f in chain.relation_facts]
    fact_ids = [f.fact_id for f in chain.relation_facts]
    if _duplicates(fact_sources) or _duplicates(fact_ids):
        raise ValueError("relation facts have duplicate source or fact identity")
    facts = {f.source: f for f in chain.relation_facts}
    states = {s.state_id: s for s in chain.states}
    before, after = states[segment.pre_state_id], states[segment.post_state_id]
    if _duplicates(before.fact_ids) or _duplicates(after.fact_ids):
        raise ValueError("hybrid framing state contains duplicate facts")
    allowed = {
        "faithful-maybe-shuffle-ordinary-to-zigzag-two-rank",
        "multiref-projection-alias", "rms-norm-zigzag-two-rank",
        "rms-norm-joined-two-rank", "per-head-linear-zigzag-two-rank",
        "per-head-linear-joined", "flatten-3d-zigzag-two-rank",
        "allgather-reconstruction-k-rank", "joined-to-unary",
    }
    if any(t.rule_id not in allowed for t in transitions):
        raise ValueError("hybrid attention contains an unsupported transition family")
    def certificate_refs(source):
        return ((*source.step_triple, source.joined_pm_step)
                if source.joined_pm_step is not None else source.step_triple)
    supported_certificate_types = tuple(classes.values())
    rows = []
    for ordinal, transition in enumerate(transitions):
        matches = [c for c in relation.certificates
                   if type(c) in supported_certificate_types
                   and getattr(c, "rule_id", None) == transition.rule_id
                   and getattr(c, "lean_theorem", None) == transition.lean_theorem
                   and _certificate_digest(c) == transition.certificate_digest]
        cert = _unique(matches, f"transition {transition.transition_id} exact certificate/digest")
        try:
            pres = tuple(facts[x] for x in transition.pre_facts)
            posts = tuple(facts[x] for x in transition.post_facts)
        except KeyError as exc:
            raise ValueError("typed transition fact is not materialized") from exc
        if len(posts) != 1:
            raise ValueError("hybrid transition must have exactly one relation output")
        # The digest is the primary exact identity.  Also check every certificate
        # family whose role fields are directly comparable with transition facts;
        # this gives an actionable failure if an upstream digest is attached to
        # the wrong transition rather than merely failing later on node topology.
        if hasattr(cert, "input_fact") and cert.input_fact not in transition.pre_facts:
            raise ValueError("typed certificate input fact is not a transition pre-role")
        if hasattr(cert, "output_fact") and cert.output_fact not in transition.post_facts:
            raise ValueError("typed certificate output fact is not a transition post-role")
        if hasattr(cert, "output_step_triple"):
            if cert.output_step_triple != certificate_refs(posts[0].source):
                raise ValueError("typed certificate output step triple disagrees with transition")
        if hasattr(cert, "input_step_triple"):
            if not any(cert.input_step_triple == certificate_refs(pre.source) for pre in pres):
                raise ValueError("typed certificate input step triple disagrees with transition")
        if hasattr(cert, "input_relation_step_triple"):
            if not any(cert.input_relation_step_triple == certificate_refs(pre.source) for pre in pres):
                raise ValueError("typed certificate input relation role disagrees with transition")
        if hasattr(cert, "weight_fact") and cert.weight_fact not in transition.pre_facts:
            raise ValueError("typed RMS weight role is not a transition pre-role")
        rows.append(_Row(ordinal, transition, cert, pres, posts))
    # Grammar anchors are semantic, while all fanout cardinalities are derived.
    by_class = {}
    for row in rows:
        by_class.setdefault(type(row.certificate).__name__, []).append(row)
    if len(by_class.get("FaithfulShuffleCertificate", ())) != 1:
        raise ValueError("hybrid attention requires one ordinary-to-zigzag boundary")
    if len(by_class.get("FrontierFlatten3DCertificate", ())) != 1:
        raise ValueError("hybrid attention requires one zigzag flatten boundary")
    if len(by_class.get("KRankAllGatherReconstructionCertificate", ())) != 1:
        raise ValueError("hybrid attention requires one sharded-to-joined boundary")
    rms_layouts = [row.posts[0].kind for row in by_class.get("FrontierRMSNormCertificate", ())]
    if sorted(rms_layouts) != ["joined", "zigzag"]:
        raise ValueError("hybrid attention requires one joined and one zigzag RMS path")
    linear_layouts = [row.posts[0].kind for row in by_class.get("PerHeadLinearRelationCertificate", ())]
    if "joined" not in linear_layouts or "zigzag" not in linear_layouts:
        raise ValueError("hybrid attention requires positive joined and zigzag linear fanouts")
    if not by_class.get("MultirefAliasCertificate") or not by_class.get("JoinedUnaryViewCertificate"):
        raise ValueError("hybrid attention requires positive alias and unary fanouts")
    owned_sm = {i for r in rows for i in r.transition.sm_node_indices}
    owned_pm = {i for r in rows for i in r.transition.pm_node_indices}
    if (not owned_sm <= set(range(*segment.sm_range))
            or not owned_pm <= set(range(*segment.pm_range))):
        raise ValueError("hybrid semantic writer lies outside complete frame")
    return _Emitter(ir, relation, segment, before, after, tuple(rows), _node_text,
                    _shape_text, _render_mixed_final_value).render()
