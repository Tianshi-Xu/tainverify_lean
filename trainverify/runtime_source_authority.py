"""Lossless source identities, independent of Torch and proof admission."""
import json

TENSOR_FIELDS = ("world", "runtime_rank", "microbatch", "source_tid", "version")


def _identity(ref, fields):
    for field in fields:
        if field not in ref or ref[field] is None:
            raise ValueError(f"missing identity field: {field}")
        value = ref[field]
        if field in ("world", "op", "origin"):
            valid = isinstance(value, str) and bool(value)
        else:
            valid = type(value) is int
        if not valid:
            raise ValueError(f"invalid identity field: {field}")
    return [ref[field] for field in fields]


def tensor_export_id(ref):
    """Injective, deterministic encoding of the complete source Tensor key."""
    return "tensor:" + json.dumps(_identity(ref, TENSOR_FIELDS), separators=(",", ":"))


WRITER_FIELDS = ("world", "runtime_rank", "microbatch", "source_cid",
                 "call_instance", "op", "origin")


def writer_export_id(ref):
    return "writer:" + json.dumps(_identity(ref, WRITER_FIELDS), separators=(",", ":"))


def _output_rank(writer):
    """Validate the builder's explicit Move/Broadcast fly-rank convention."""
    ref = writer["ref"]
    transport = writer.get("transport")
    if ref["op"] not in ("MovePrim", "BroadcastPrim"):
        if transport is not None:
            raise ValueError("unexpected transport source")
        return ref["runtime_rank"]
    if not isinstance(transport, dict):
        raise ValueError("missing transport source")
    src, destinations = transport["src"], transport["destinations"]
    if (type(src) is not int or src < 0 or not isinstance(destinations, list)
            or any(type(r) is not int or r < 0 or r == src for r in destinations)
            or len(set(destinations)) != len(destinations)
            or (ref["op"] == "MovePrim" and len(destinations) != 1)):
        raise ValueError("invalid transport source")
    sender = ref["runtime_rank"] == src
    if not sender and ref["runtime_rank"] not in destinations:
        raise ValueError("transport receiver outside destinations")
    local = writer["inputs"] if sender else writer["outputs"]
    remote = writer["outputs"] if sender else writer["inputs"]
    if not local or any(t["runtime_rank"] != ref["runtime_rank"] for t in local):
        raise ValueError("invalid transport local owner")
    expected = [dict(t, runtime_rank=-1-src, version=0) for t in local]
    if remote != expected:
        raise ValueError("invalid transport fly reference")
    return -1-src if sender else ref["runtime_rank"]


def build_snapshot(writers):
    """Intern full refs, retaining the ordered writer/edge stream verbatim."""
    from copy import deepcopy
    writers = deepcopy(writers)
    tensors, seen_writers = {}, {}
    for writer in writers:
        writer["export_id"] = writer_export_id(writer["ref"])
        if writer["export_id"] in seen_writers:
            raise ValueError("duplicate writer identity")
        seen_writers[writer["export_id"]] = writer
        for direction in ("inputs", "outputs"):
            if not isinstance(writer.get(direction), list):
                raise ValueError(f"missing ordered {direction}")
        for ref in writer["inputs"] + writer["outputs"]:
            if ref.get("world") != writer["ref"]["world"]:
                raise ValueError("reference world differs from writer")
            tid = tensor_export_id(ref)
            tensors.setdefault(tid, dict(export_id=tid, ref=ref, writer=None))
        output_rank = _output_rank(writer)
        for ref in writer["outputs"]:
            if ref["runtime_rank"] != output_rank:
                raise ValueError("output owner differs from writer")
            if ref["microbatch"] not in (-1, writer["ref"]["microbatch"]):
                raise ValueError("output microbatch differs from writer")
            tensor = tensors[tensor_export_id(ref)]
            if tensor["writer"] is not None:
                raise ValueError("duplicate writer for tensor")
            tensor["writer"] = writer["export_id"]
    for writer in writers:
        transport = writer.get("transport")
        if transport is None or writer["ref"]["runtime_rank"] == transport["src"]:
            continue
        for ref in writer["inputs"]:
            producer = seen_writers.get(tensors[tensor_export_id(ref)]["writer"])
            if (producer is None or producer.get("transport") != transport
                    or producer["ref"]["runtime_rank"] != transport["src"]
                    or producer["ref"]["op"] != writer["ref"]["op"]):
                raise ValueError("transport reference has inconsistent producer")
    return dict(format="trainverify.runtime-source.v1", scope="source-only",
                proof_admissible=False, writers=writers, tensors=list(tensors.values()),
                reducer_binding="missing", completeness=dict(status="incomplete", missing=[
                    "parameter-reducers", "ordered-adapters", "global-batch", "loss-normalization"]))


def validate_snapshot(snapshot):
    """Check identity interning and both directions of writer/reference links.

    A null writer means only 'not written in this source stream'; it establishes
    neither initialized values nor batch/replica equality. Placement is metadata,
    not an equality key. This validator never admits a proof.
    """
    try:
        if (snapshot["format"] != "trainverify.runtime-source.v1"
                or snapshot["scope"] != "source-only"
                or snapshot["proof_admissible"] is not False):
            raise ValueError("not a source-only snapshot")
        expected = build_snapshot(snapshot["writers"])
        for writer in snapshot["writers"]:
            if writer["export_id"] != writer_export_id(writer["ref"]):
                raise ValueError("writer export id mismatch")
        actual = {}
        for tensor in snapshot["tensors"]:
            tid = tensor_export_id(tensor["ref"])
            if tensor["export_id"] != tid or tid in actual:
                raise ValueError("tensor export id mismatch or duplicate")
            actual[tid] = {k: tensor[k] for k in ("export_id", "ref", "writer")}
        if actual != {t["export_id"]: t for t in expected["tensors"]}:
            raise ValueError("inconsistent writer/reference linkage")
        if "rank_sources" in snapshot:
            from copy import deepcopy
            rebound = deepcopy(snapshot)
            bind_reducers(rebound)
            if any(snapshot.get(k) != rebound[k] for k in
                   ("writers", "reducer_binding") + (() if "adapter_source" in snapshot else ("completeness",))):
                raise ValueError("inconsistent reducer binding")
        elif (snapshot.get("reducer_binding", "missing") != "missing"
              or ("adapter_source" not in snapshot and snapshot.get("completeness", expected["completeness"]) != expected["completeness"])
              or any("reducer" in w for w in snapshot["writers"])):
            raise ValueError("missing generated reducer source")
        if "adapter_source" in snapshot:
            from copy import deepcopy
            rebound = deepcopy(snapshot)
            bind_adapters(rebound, allow_translation_mismatch=True)
            if any(snapshot.get(k) != rebound[k] for k in
                   ("writers", "adapter_binding", "adapter_generated_binding", "adapter_generated_read_binding", "completeness")):
                raise ValueError("inconsistent adapter binding")
        elif (snapshot.get("adapter_binding", "missing") != "missing"
              or snapshot.get("adapter_generated_binding", "missing") != "missing"
              or any("adapter" in w for w in snapshot["writers"])):
            raise ValueError("missing prepared adapter source")
    except (KeyError, TypeError, AttributeError) as exc:
        raise ValueError(f"missing or malformed source reference: {exc}") from exc


ADAPTER_OPS = ("AllGatherPrim", "AllReducePrim", "ReduceScatterPrim", "AllToAllPrim")


def bind_adapters(snapshot, allow_translation_mismatch=False):
    """Replay retained pre-fusion read points; never repair the writer edge order.

    Evidence is a source observation, not authentication of an arbitrary JSON.
    Mismatched translations can be retained for inspection, never marked complete.
    """
    from copy import deepcopy
    try:
        source = snapshot["adapter_source"]
        writers = {writer_export_id(w["ref"]): w for w in snapshot["writers"]}
        if len(writers) != len(snapshot["writers"]):
            raise ValueError("duplicate adapter writer")
        if [writer_export_id(s["ref"]) for s in source] != list(writers):
            raise ValueError("prepared primitive/writer inventory mismatch")
        current, reads, adapters = {}, {}, []
        produced = {tensor_export_id(t) for row in source for t in row["outputs"]}
        def key(t):
            return tuple(t[k] for k in TENSOR_FIELDS[:-1])
        for row in source:
            wid = writer_export_id(row["ref"])
            writer = writers[wid]
            if writer["outputs"] != row["outputs"]:
                raise ValueError("output differs from prepared source writer")
            points = []
            for ref in row["inputs"]:
                tensor_export_id(ref)
                prior = current.get(key(ref))
                if prior is None and tensor_export_id(ref) in produced:
                    raise ValueError("source read precedes its current writer")
                if prior is not None and prior[0] != ref:
                    raise ValueError("source read does not consume current writer version")
                points.append(dict(ref=ref, writer=prior[1] if prior else None))
            reads[wid] = points
            if row["ref"]["op"] in ADAPTER_OPS:
                if writer["adapter_kwargs"] != row["primitive"]["kwargs"]:
                    raise ValueError("adapter parameters differ from primitive source")
                adapters.append(row)
            elif row["ref"]["op"] != "CROSS_DP_WRED" and writer["inputs"] != row["inputs"]:
                raise ValueError("writer read point differs from prepared source")
            for ref in row["outputs"]:
                current[key(ref)] = (ref, wid)
        mismatch = False
        for row in adapters:
            ref, prim = row["ref"], row["primitive"]
            wid = writer_export_id(ref); writer = writers[wid]
            kw = prim["kwargs"]; ranks = kw["ranks"]
            if (not isinstance(ranks, list) or not ranks or len(set(ranks)) != len(ranks)
                    or any(type(r) is not int or r < 0 for r in ranks)):
                raise ValueError("missing or invalid ordered primitive ranks")
            fields = (() if ref["op"] == "AllReducePrim" else
                      ("idim", "odim") if ref["op"] == "AllToAllPrim" else ("dim",))
            parameters = {k: kw[k] for k in fields}
            if any(type(v) is not int for v in parameters.values()):
                raise ValueError("invalid primitive dimensions")
            if prim["kind"] == "AllToAllAllToAllPrim" and prim["forward"] is False:
                parameters = dict(idim=kw["odim"], odim=kw["idim"])
            peers, problem = [], None
            if ref["runtime_rank"] not in ranks:
                problem = "primitive ranks exclude current source writer"
            else:
                for rank in ranks:
                    peer_ref = dict(ref, runtime_rank=rank)
                    candidates = [s for s in adapters if s["ref"] == peer_ref]
                    if len(candidates) != 1 or candidates[0]["primitive"]["kwargs"] != kw:
                        raise ValueError("missing or inconsistent primitive peer occurrence")
                    peer = candidates[0]
                    if len(peer["inputs"]) != 1 or len(peer["outputs"]) != 1:
                        raise ValueError("not-supported: multi-input/output primitive")
                    peers.append(peer)
            ordered = [p["inputs"][0] for p in peers]
            if problem is None and writer["inputs"] != ordered:
                problem = "fused inputs differ from ordered primitive peer read points"
            # Even a retained mismatch must not rewrite the captured local read.
            local = [t for t in writer["inputs"] if t["runtime_rank"] == ref["runtime_rank"]]
            if local != row["inputs"]:
                raise ValueError("adapter does not consume its current source read point")
            writer["adapter"] = deepcopy(dict(ranks=ranks, parameters=parameters,
                ordered_inputs=ordered, outputs=row["outputs"],
                read_points=[p for peer in peers for p in reads[writer_export_id(peer["ref"])]],
                local_read_points=reads[wid], source_writer=wid,
                peer_writers=[writer_export_id(p["ref"]) for p in peers],
                status="translation-mismatch" if problem else "bound", mismatch=problem))
            mismatch |= problem is not None
        snapshot["adapter_binding"] = "translation-mismatch" if mismatch else "complete"
        snapshot["adapter_generated_binding"] = "missing"
        snapshot["adapter_generated_read_binding"] = "missing"
        if "rank_sources" in snapshot:
            generated_mismatch = _bind_generated_adapters(snapshot, adapters, writers)
            snapshot["adapter_generated_binding"] = "translation-mismatch" if generated_mismatch else "complete"
            mismatch |= generated_mismatch
            if mismatch:
                snapshot["adapter_binding"] = "translation-mismatch"
        missing = ([] if snapshot.get("reducer_binding") == "complete" else ["parameter-reducers"])
        if mismatch:
            missing.append("ordered-adapters")
        if snapshot["adapter_generated_read_binding"] != "complete":
            missing.append("generated-adapter-reaching-definitions")
        snapshot["completeness"] = dict(status="incomplete", missing=missing + ["global-batch", "loss-normalization"])
        if snapshot["adapter_generated_read_binding"] == "rejected" and not allow_translation_mismatch:
            raise ValueError("generated reaching definition rejected; see generated_read_missing")
        if mismatch and not allow_translation_mismatch:
            raise ValueError("ordered adapter translation mismatch")
    except (KeyError, TypeError, AttributeError, IndexError, SyntaxError) as exc:
        raise ValueError(f"missing or malformed adapter source: {exc}") from exc


def _bind_generated_adapters(snapshot, adapters, writers):
    """Match exact primitive call names/arguments/outputs to retained rank ASTs.

    Fused backward rows refer to their actual forward autograd call; they are
    not invented backward Python calls. Shared call sites are recorded as such.
    """
    import ast
    calls = {}
    for rank, text in snapshot["rank_sources"].items():
        _rank_reducers(text, int(rank), snapshot["runtime_ndevs"])
        entries = []
        for stmt in ast.walk(ast.parse(text)):
            if not isinstance(stmt, ast.Assign) or not isinstance(stmt.value, ast.Call):
                continue
            call = stmt.value
            signature = ast.unparse(call.func)
            if not signature.startswith("nnscaler.runtime.adapter.") or signature.endswith(".Reducer"):
                continue
            targets = stmt.targets
            if len(targets) == 1 and isinstance(targets[0], (ast.Tuple, ast.List)):
                targets = targets[0].elts
            entries.append(dict(signature=signature, inputs=[ast.unparse(a) for a in call.args],
                                outputs=[ast.unparse(t) for t in targets],
                                kwargs={k.arg: ast.literal_eval(k.value) for k in call.keywords},
                                line=stmt.lineno))
        calls[int(rank)] = entries
    covered, mismatch = set(), False
    signatures = {"nnscaler.runtime.adapter." + name for name in
                  ("all_gather", "all_reduce", "reduce_scatter", "all_to_all",
                   "nn.allgather_reducescatter", "nn.reducescatter_allgather",
                   "nn.allgather_split", "nn.split_allgather", "nn.alltoall_alltoall",
                   "nn.allreduce_identity", "nn.identity_allreduce", "nn.allreduce_allreduce")}
    for row in adapters:
        prim = row["primitive"]; rank = row["ref"]["runtime_rank"]
        matches = [c for c in calls[rank] if c["signature"] == prim["signature"]
                   and c["inputs"] == prim["generated_inputs"]
                   and c["outputs"] == prim["generated_outputs"]]
        if len(matches) != 1:
            raise ValueError("missing or ambiguous generated primitive occurrence")
        call, = matches
        if "ranks" not in call["kwargs"]:
            raise ValueError("missing generated primitive ranks")
        covered.add((rank, call["line"]))
        equal = call["kwargs"] == prim["kwargs"]
        writer = writers[writer_export_id(row["ref"])]
        writer["adapter"]["generated_call"] = dict(call, forward=prim["forward"],
            status="bound" if equal else "translation-mismatch")
        if not equal:
            writer["adapter"]["status"] = "translation-mismatch"
            writer["adapter"]["mismatch"] = "prepared primitive kwargs differ from generated call"
            mismatch = True
    inventory = {(r, c["line"]) for r, entries in calls.items() for c in entries
                 if c["signature"] in signatures}
    if covered != inventory:
        raise ValueError("generated primitive inventory coverage mismatch")
    _bind_generated_readpoints(snapshot, adapters, writers)
    return mismatch


def _bind_generated_readpoints(snapshot, adapters, writers):
    """Direct straight-line methods only; syntax coverage is NOT value authority.

    Each local read is compared to its independently captured prepared writer.
    No ordering is inferred between methods. Autograd BW needs a separate ctx
    correspondence and is explicitly missing rather than borrowing FW values.
    """
    import ast
    rows = {writer_export_id(r["ref"]): r for r in snapshot["adapter_source"]}
    sites, name_methods = {}, {}
    def targets(stmt):
        ts = stmt.targets
        if len(ts) == 1 and isinstance(ts[0], (ast.Tuple, ast.List)):
            ts = ts[0].elts
        return [ast.unparse(t) for t in ts]
    for rank, text in snapshot["rank_sources"].items():
        cls, = [n for n in ast.parse(text).body if isinstance(n, ast.ClassDef) and n.name == "GenModel"]
        methods = [n for n in cls.body if isinstance(n, ast.FunctionDef)]
        for method in methods:
            current, counts = {}, {}
            unsupported = False
            for stmt in method.body:
                if isinstance(stmt, ast.Assign):
                    # Only plain local targets or one flat unpacking are in
                    # this slice. Nested/starred targets and RHS assignment
                    # expressions may rebind names not represented by targets().
                    plain_targets = len(stmt.targets) == 1 and all(
                        isinstance(t, ast.Name) or (
                            isinstance(t, (ast.Tuple, ast.List))
                            and all(isinstance(item, ast.Name) for item in t.elts))
                        for t in stmt.targets)
                    if not plain_targets or any(isinstance(n, ast.NamedExpr) for n in ast.walk(stmt)):
                        unsupported = True
                        continue
                    reads = dict(current)
                    for name in targets(stmt):
                        name_methods.setdefault((int(rank), name), set()).add(method.lineno)
                        counts[name] = counts.get(name, 0) + 1
                        current[name] = dict(line=stmt.lineno, ordinal=counts[name],
                            method=method.name, statement=stmt)
                    sites[(int(rank), stmt.lineno)] = (method.name, reads, unsupported)
                elif isinstance(stmt, ast.Delete):
                    if any(not isinstance(name, ast.Name) for name in stmt.targets):
                        unsupported = True
                        continue
                    for name in stmt.targets:
                        current.pop(name.id, None)
                elif isinstance(stmt, ast.Return):
                    break
                elif isinstance(stmt, ast.Pass):
                    pass
                elif isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant):
                    pass
                else:
                    # Calls with side effects, augmented assignment and control
                    # flow cannot silently preserve a value-authority claim.
                    unsupported = True
    complete, rejected = True, False
    for row in adapters:
        a = writers[writer_export_id(row["ref"])]["adapter"]
        call = a["generated_call"]
        site = sites.get((row["ref"]["runtime_rank"], call["line"]))
        reason = None
        points = []
        if not row["primitive"]["forward"]:
            reason = "unsupported: backward autograd ctx/source correspondence missing; forward syntax only"
        elif site is None or site[2]:
            reason = "unsupported: non-straight-line generated method/call context"
        else:
            method, current, _ = site
            for name, point in zip(call["inputs"], a["local_read_points"]):
                producer = rows.get(point["writer"])
                evidence = producer.get("generated_producer") if producer else None
                if evidence is None:
                    reason = "missing: independently prepared generated producer evidence"
                    break
                if len(name_methods.get((row["ref"]["runtime_rank"], name), ())) != 1:
                    reason = "unsupported: ambiguous producer across methods; call context missing"
                    break
                definition = current.get(name)
                if definition is None:
                    reason = "rejected: generated reaching definition missing before collective read"
                    break
                stmt = definition["statement"]
                value = stmt.value
                def canonical(expr):
                    return ast.dump(ast.parse(expr, mode="eval").body, include_attributes=False)
                if (not isinstance(value, ast.Call)
                        or ast.unparse(value.func) != evidence["signature"]
                        or targets(stmt) != evidence["outputs"]
                        or [canonical(ast.unparse(v)) for v in value.args] != [canonical(v) for v in evidence["inputs"]]
                        or {k.arg: canonical(ast.unparse(k.value)) for k in value.keywords} != {k: canonical(v) for k, v in evidence["kwargs"].items()}):
                    reason = "rejected: generated reaching definition differs from prepared source writer"
                    break
                # Definition ordinal is source occurrence, not a ban on name reuse.
                same_name = [r for r in snapshot["adapter_source"]
                    if r["ref"]["runtime_rank"] == row["ref"]["runtime_rank"]
                    and name in r.get("generated_producer", {}).get("outputs", [])]
                expected_ordinal = next(i + 1 for i, r in enumerate(same_name) if r is producer)
                if definition["ordinal"] != expected_ordinal:
                    reason = "rejected: generated reaching definition source occurrence/version mismatch"
                    break
                points.append(dict(ref=point["ref"], writer=point["writer"],
                    definition_line=definition["line"], definition_ordinal=definition["ordinal"],
                    method=method, read_line=call["line"], name=name))
        a["generated_read_points"] = points
        is_rejected = bool(reason and reason.startswith("rejected:"))
        rejected |= is_rejected
        a["generated_read_binding"] = "rejected" if is_rejected else "missing" if reason else "complete"
        a["generated_read_missing"] = reason
        complete &= reason is None
    snapshot["adapter_generated_read_binding"] = "rejected" if rejected else "complete" if complete else "missing"


def _rank_reducers(text, rank, world_size):
    """Read explicit generated constructor statements; never execute generated code."""
    import ast
    tree = ast.parse(text)
    cls, = [n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == "GenModel"]
    constants = {n.targets[0].id: ast.literal_eval(n.value) for n in cls.body
                 if isinstance(n, ast.Assign) and isinstance(n.targets[0], ast.Name)
                 and n.targets[0].id in ("rank", "world_size")}
    if constants != dict(rank=rank, world_size=world_size):
        raise ValueError("generated rank/world mismatch")
    init, = [n for n in cls.body if isinstance(n, ast.FunctionDef) and n.name == "__init__"]
    params, maps, reducers, active = [], {}, {}, []
    def attr(node):
        if not isinstance(node, ast.Attribute) or not isinstance(node.value, ast.Name) or node.value.id != "self":
            raise ValueError("not-supported: nonliteral generated attribute")
        return node.attr
    for stmt in init.body:
        call = stmt.value if isinstance(stmt, (ast.Expr, ast.Assign)) else None
        if not isinstance(call, ast.Call):
            continue
        fn = ast.unparse(call.func)
        if fn == "self.register_parameter":
            params.append(ast.literal_eval(call.args[0]))
        elif fn == "self.add_full_map":
            name, parent, is_param, logical, shape = map(ast.literal_eval, call.args[:5])
            if not is_param:
                continue
            slices = []
            for sl in call.args[5].elts:
                if ast.unparse(sl.func) != "slice":
                    raise ValueError("not-supported: generated slice")
                start, stop, step = map(ast.literal_eval, sl.args)
                if step is not None:
                    raise ValueError("not-supported: generated slice step")
                slices.append([start, stop])
            if name in maps:
                raise ValueError("duplicate parameter full map")
            maps[name] = dict(parent_tid=parent, name=logical, full_shape=list(shape),
                              indmap=slices, chunks=ast.literal_eval(call.args[6]))
        elif fn == "nnscaler.runtime.adapter.Reducer":
            name = attr(stmt.targets[0])
            if name in reducers:
                raise ValueError("duplicate generated reducer")
            kw = {k.arg: k.value for k in call.keywords}
            reducers[name] = {k: ast.literal_eval(kw[k]) for k in
                              ("ranks", "reduce_op", "zero", "nreplicas")}
            reducers[name]["params"] = []
        elif isinstance(call.func, ast.Attribute) and call.func.attr == "add_param":
            reducers[attr(call.func.value)]["params"].append(attr(call.args[0]))
        elif fn == "self.add_reducer":
            active.append(attr(call.args[0]))
    if len(params) != len(set(params)) or set(params) != set(maps):
        raise ValueError("generated parameter coverage mismatch")
    if len(active) != len(set(active)) or set(active) != set(reducers):
        raise ValueError("generated reducer registration mismatch")
    return params, maps, reducers


def bind_reducers(snapshot):
    """Bind per-weight reducers to existing identities and retained source evidence.

    Only reducer binding can be complete. Ordered adapters and batch/loss
    contracts remain missing. Embedded source text is evidence, not a signature.
    """
    try:
        sources = snapshot["rank_sources"]
        size = snapshot["runtime_ndevs"]
        if set(sources) != {str(r) for r in range(size)}:
            raise ValueError("missing generated rank source")
        tensors = {tensor_export_id(t["ref"]): t for t in snapshot["tensors"]}
        for rank in range(size):
            params, maps, generated = _rank_reducers(sources[str(rank)], rank, size)
            local = [w for w in snapshot["writers"] if w["ref"]["runtime_rank"] == rank]
            weights = {}
            for tensor in tensors.values():
                ref = tensor["ref"]
                if ref["runtime_rank"] == rank and tensor.get("placement", {}).get("is_param"):
                    if ref["source_tid"] in weights:
                        raise ValueError("not-supported: ambiguous parameter identity")
                    weights[ref["source_tid"]] = tensor
            named = {}
            for name in params:
                tid = int(name.rsplit("_", 1)[1])
                tensor = weights[tid]
                mapping = maps[name]; placement = tensor["placement"]
                if (any(mapping[k] != placement[k] for k in ("parent_tid", "name", "full_shape", "indmap"))
                        or mapping["chunks"] != placement["valmap"][1]):
                    raise ValueError("parameter full map differs from expanded source")
                named[name] = tensor["ref"]
            if {r["source_tid"] for r in named.values()} != set(weights):
                raise ValueError("expanded parameter coverage mismatch")
            owners = {}
            for name, red in generated.items():
                for param in red["params"]:
                    if param not in named or param in owners:
                        raise ValueError("generated reducer parameter coverage mismatch")
                    owners[param] = name
            if set(owners) != set(params):
                raise ValueError("missing parameter reducer")
            covered, grad_to_weight, weight_to_grad, current = set(), {}, {}, {}
            for writer in local:
                for gid, wid in writer["parameter_grad_tids"]:
                    if gid in grad_to_weight and grad_to_weight[gid] != wid:
                        raise ValueError("conflicting parameter gradient source")
                    grad_to_weight[gid] = wid
                    weight_to_grad[wid] = gid
                if writer["ref"]["op"] != "CROSS_DP_WRED":
                    for ref in writer["inputs"] + writer["outputs"]:
                        if ref["runtime_rank"] == rank:
                            key = tuple(ref[k] for k in TENSOR_FIELDS[:-1])
                            current[key] = max(current.get(key, -1), ref["version"])
                    continue
                ir = writer["reducer_ir"]
                param, = [n for n, r in named.items() if r["source_tid"] == ir["parameter_tid"]]
                if param in covered:
                    raise ValueError("duplicate parameter reducer writer")
                covered.add(param)
                name = owners[param]; red = generated[name]
                if name != f"wreducer{ir['cid']}" or red["ranks"] != ir["ranks"] or red["nreplicas"] != ir["nreplicas"]:
                    raise ValueError("generated reducer differs from expanded source")
                if (red["reduce_op"] != "sum" or type(red["zero"]) is not int or red["zero"] != 0
                        or type(red["nreplicas"]) is not int or red["nreplicas"] != 1):
                    raise ValueError("not-supported: reducer requires sum/zero0/nreplicas1")
                ranks = red["ranks"]
                if (not isinstance(ranks, list) or rank not in ranks or len(set(ranks)) != len(ranks)
                        or any(type(r) is not int or r < 0 or r >= size for r in ranks)):
                    raise ValueError("invalid ordered reducer ranks")
                inputs = writer["inputs"]
                if len(inputs) != len(ranks) or {t["runtime_rank"] for t in inputs} != set(ranks):
                    raise ValueError("reducer input rank coverage mismatch")
                ordered = [next(t for t in inputs if t["runtime_rank"] == r) for r in ranks]
                grad, = [t for t in inputs if t["runtime_rank"] == rank]
                output, = writer["outputs"]
                key = tuple(grad[k] for k in TENSOR_FIELDS[:-1])
                if (current.get(key) != grad["version"]
                        or weight_to_grad.get(ir["parameter_tid"]) != grad["source_tid"]):
                    raise ValueError("reducer does not consume current gradient")
                if grad_to_weight.get(grad["source_tid"]) != ir["parameter_tid"] or output != dict(grad, version=grad["version"]+1):
                    raise ValueError("parameter gradient binding mismatch")
                writer["reducer"] = dict(kind="CROSS_DP_WRED", ranks=ranks,
                    ordered_inputs=ordered, outputs=writer["outputs"], parameter=named[param],
                    grad_input=grad, grad_output=output,
                    reduce_op=red["reduce_op"], zero=red["zero"], nreplicas=red["nreplicas"])
            if covered != set(params):
                raise ValueError("missing expanded parameter reducer")
        reducers = [w for w in snapshot["writers"] if w["ref"]["op"] == "CROSS_DP_WRED"]
        for writer in reducers:
            binding = writer["reducer"]
            peers = [w for w in reducers if w["reducer_ir"]["cid"] == writer["reducer_ir"]["cid"]
                     and w["reducer_ir"]["parameter_tid"] == writer["reducer_ir"]["parameter_tid"]]
            ordered = []
            for rank in binding["ranks"]:
                peer, = [w for w in peers if w["ref"]["runtime_rank"] == rank]
                if peer["reducer"]["ranks"] != binding["ranks"]:
                    raise ValueError("inconsistent peer reducer ranks")
                ordered.append(peer["reducer"]["grad_input"])
            if binding["ordered_inputs"] != ordered:
                raise ValueError("reducer input differs from peer gradient source")
        snapshot["reducer_binding"] = "complete"
        snapshot["completeness"] = dict(status="incomplete", missing=[
            "ordered-adapters", "global-batch", "loss-normalization"])
    except (KeyError, TypeError, AttributeError, SyntaxError, IndexError) as exc:
        raise ValueError(f"missing or malformed reducer source: {exc}") from exc
