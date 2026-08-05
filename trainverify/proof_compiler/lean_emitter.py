"""Fail-closed Lean source emission for proof-compiler certificate IR.

This first kernel slice supports unary-map rules over equal/replicated/contiguous
relations whose value semantics are already represented by ProofCompilerRelation.
Unsupported relation/rule/operator shapes are rejected before source generation.
"""
from __future__ import annotations

import json
import re
from typing import Any

from . import compile_job, validate_certificate_dag


class LeanEmissionError(ValueError):
    """The validated Python IR cannot yet be represented faithfully in Lean."""


_NAMESPACE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def _lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def _lean_nat_list(values: list[int]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def _lean_relation(relation: dict[str, Any]) -> str:
    kind = relation.get("kind")
    if kind == "equal":
        return ".equal"
    if kind == "replicated":
        return ".replicated"
    if kind == "contiguous_shard":
        return f"(.contiguousShard {relation['dim']} {relation['parts']})"
    raise LeanEmissionError(f"unsupported kernel relation: {kind}")


def _lean_tensor_list(expressions: list[str]) -> str:
    return "[" + ", ".join(expressions) + "]"


def _graph_decl(name: str, num_ranks: int, nodes: list[dict[str, Any]]) -> str:
    rendered_nodes: list[str] = []
    for node in nodes:
        attrs = node.get("attrs", {})
        if attrs:
            raise LeanEmissionError(
                f"operator attrs are not yet mapped to Lean NodeDecl.params: {node['op']}"
            )
        rendered_nodes.append(
            "{ rank := "
            f"{node['rank']}, op := {_lean_string(node['op'])}, "
            f"ins := {_lean_nat_list(node['ins'])}, outs := {_lean_nat_list(node['outs'])}, "
            "params := [] }"
        )
    nodes_text = "[\n    " + ",\n    ".join(rendered_nodes) + "\n  ]"
    return (
        f"def {name} : GraphDecl where\n"
        f"  numRanks := {num_ranks}\n"
        f"  nodes := {nodes_text}\n"
    )


def emit_lean_certificate(
    job: dict[str, Any],
    library: dict[str, Any],
    result: dict[str, Any],
    *,
    namespace: str = "GeneratedCertificate",
) -> str:
    """Render a kernel-checkable Lean theorem from one validated certificate.

    Seed relations remain explicit theorem hypotheses: verification of an external
    authority artifact/hash is a separate trust-boundary step. Every rule node is
    nevertheless composed by a concrete Lean theorem over actual `denoteGraph`
    tensor values.
    """
    if _NAMESPACE.fullmatch(namespace) is None:
        raise LeanEmissionError("namespace must be a simple Lean identifier")
    if result.get("status") != "certificate":
        raise LeanEmissionError("only successful certificate IR can be emitted")
    if compile_job(job, library) != result:
        raise LeanEmissionError(
            "certificate does not exactly match recompilation of the supplied job/library"
        )
    if result.get("num_ranks") != job.get("num_ranks"):
        raise LeanEmissionError("certificate num_ranks does not match authority job")
    if result.get("target_manifest_sha256") != job.get("target_manifest_sha256"):
        raise LeanEmissionError("certificate target digest does not match authority job")
    if any(node["rank"] != 0 for node in job["sm_nodes"]):
        raise LeanEmissionError("SM graph must contain only rank-0 nodes")

    failure = validate_certificate_dag(
        result["certificate_dag"],
        result["observables"],
        library,
        num_ranks=job["num_ranks"],
        target_manifest_sha256=job["target_manifest_sha256"],
        target_observables=job["observables"],
    )
    if failure is not None:
        raise LeanEmissionError(f"invalid certificate DAG: {failure['reason']}")

    denotations = {entry["op"]: entry for entry in library["denotations"]}
    rules = {entry["name"]: entry for entry in library["rules"]}
    num_ranks = job["num_ranks"]
    certificate_names = {
        node["id"]: f"certificate_{index}"
        for index, node in enumerate(result["certificate_dag"])
    }

    seed_nodes = [
        node for node in result["certificate_dag"] if node["kind"] == "seed_relation"
    ]
    if not seed_nodes:
        raise LeanEmissionError("certificate requires at least one authority seed")

    def sm_value(tid: int) -> str:
        return f"denoteGraph smGraph initSM {tid}"

    def pm_values(mapping: list[dict[str, int]]) -> list[str]:
        return [f"denoteGraph pmGraph initPM {entry['tid']}" for entry in mapping]

    hypotheses: list[str] = []
    body: list[str] = []
    for index, node in enumerate(seed_nodes):
        relation = _lean_relation(node["relation"])
        pm = _lean_tensor_list(pm_values(node["pm_tids"]))
        hypothesis = f"seed_{index}"
        hypotheses.append(
            f"    ({hypothesis} : Holds {num_ranks} {relation} "
            f"({sm_value(node['sm_tid'])}) {pm})"
        )
        body.extend(
            [
                f"  let {certificate_names[node['id']]} : CertifiedRelation {num_ranks} :=",
                f"    {{ relation := {relation}, sm := {sm_value(node['sm_tid'])},",
                f"      pm := {pm}, holds := {hypothesis} }}",
            ]
        )

    seed_ids = {node["id"] for node in seed_nodes}
    for node_index, node in enumerate(result["certificate_dag"]):
        if node["id"] in seed_ids:
            continue
        if node["kind"] != "rule_application":
            raise LeanEmissionError(f"unsupported certificate node kind: {node['kind']}")
        rule = rules.get(node["rule"])
        if rule is None or rule["lean_theorem"] != node["lean_theorem"]:
            raise LeanEmissionError(f"rule is not installed: {node['rule']}")
        if rule.get("kernel_semantics") != {"kind": "unary_map"}:
            raise LeanEmissionError(
                f"rule {node['rule']} lacks supported kernel_semantics unary_map"
            )
        if len(node["premises"]) != 1 or len(rule["input_relations"]) != 1:
            raise LeanEmissionError("unary_map requires exactly one premise")
        if node["output_index"] != 0:
            raise LeanEmissionError("unary_map first slice supports output_index 0 only")
        if len(node["sm_node"]["ins"]) != 1 or len(node["sm_node"]["outs"]) != 1:
            raise LeanEmissionError("unary_map requires unary singleton-output SM node")
        if any(len(pm_node["ins"]) != 1 or len(pm_node["outs"]) != 1 for pm_node in node["pm_nodes"]):
            raise LeanEmissionError("unary_map requires unary singleton-output PM nodes")
        if node["sm_node"].get("attrs", {}) or any(
            pm_node.get("attrs", {}) for pm_node in node["pm_nodes"]
        ):
            raise LeanEmissionError("unary_map attrs are not implemented")

        sm_denotation = denotations.get(rule["sm_op"])
        pm_denotation = denotations.get(rule["pm_op"])
        if sm_denotation is None or pm_denotation is None:
            raise LeanEmissionError("rule operator lacks installed Lean denotation")
        if sm_denotation["lean_definition"] != pm_denotation["lean_definition"]:
            raise LeanEmissionError("unary_map requires identical SM/PM Lean denotations")
        function = sm_denotation["lean_definition"]
        premise = certificate_names[node["premises"][0]]
        certificate = certificate_names[node["id"]]
        semantic = f"semantic_{node_index}"
        relation = _lean_relation(node["relation"])
        sm_output = sm_value(node["sm_tid"])
        pm_output = _lean_tensor_list(pm_values(node["pm_tids"]))
        body.extend(
            [
                f"  have {semantic} : UnaryMapSemantics {function}",
                f"      [{premise}.toRelatedInput] ({sm_output}) {pm_output} := by",
                f"    refine ⟨{premise}.toRelatedInput, rfl, ?_, ?_⟩",
                "    · rfl",
                "    · rfl",
                f"  let {certificate} : CertifiedRelation {num_ranks} :=",
                f"    applyRule {rule['lean_theorem']} [{premise}] rfl",
                f"      ({sm_output}) {pm_output} {semantic}",
                f"  have {certificate}_relation : {certificate}.relation = {relation} := rfl",
            ]
        )

    if len(result["observables"]) != 1:
        raise LeanEmissionError("first kernel slice requires exactly one observable")
    observable = result["observables"][0]
    final_certificate = certificate_names[observable["certificate"]]
    final_relation = _lean_relation(observable["relation"])
    final_sm = sm_value(observable["sm_tid"])
    final_pm = _lean_tensor_list(pm_values(observable["pm_tids"]))
    hypotheses_text = "\n".join(hypotheses)
    body.append(f"  exact {final_certificate}.holds")

    source = [
        "import denote.ProofCompilerRelation",
        "",
        f"namespace TrainVerify.Denote.ProofCompiler.{namespace}",
        "",
        "open TrainVerify.Denote",
        "",
        _graph_decl("smGraph", 1, job["sm_nodes"]).rstrip(),
        "",
        _graph_decl("pmGraph", num_ranks, job["pm_nodes"]).rstrip(),
        "",
        f"def targetManifestSha256 : String := {_lean_string(job['target_manifest_sha256'])}",
        "",
        "theorem compiledCertificate (initSM initPM : Store)",
        hypotheses_text + " :",
        f"    Holds {num_ranks} {final_relation} ({final_sm}) {final_pm} := by",
        *body,
        "",
        f"end TrainVerify.Denote.ProofCompiler.{namespace}",
        "",
    ]
    return "\n".join(source)
