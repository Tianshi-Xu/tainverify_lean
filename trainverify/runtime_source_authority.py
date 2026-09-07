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
                proof_admissible=False, writers=writers, tensors=list(tensors.values()))


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
    except (KeyError, TypeError, AttributeError) as exc:
        raise ValueError(f"missing or malformed source reference: {exc}") from exc
