"""Source-derived CP/EP topology, with no torch/NNScaler dependency.

``upstream_root`` is an explicitly trusted repository: derive_topology executes
its immutable ``revision:llm/parallelism.py`` using Python exec. This is NOT a
sandbox. The result describes source-derived rank membership, not observed
runtime process groups or a Lean proof. ZeRO and pipeline sizes are constraints
only; their group membership is deliberately not inferred.

Semantic groups have a zero-based scale-unit index. Their canonical order is
scale unit, then role (scale_unit, cp, ep, data_lane), then ascending first rank.
Singletons and different roles sharing the same physical group are retained.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass, fields, replace
from pathlib import Path
import re
import subprocess
from types import SimpleNamespace
from typing import Any

_ROLES = ("scale_unit", "cp", "ep", "data_lane")
_EVIDENCE = "source-derived-topology"


@dataclass(frozen=True)
class ParallelConfig:
    plan_ngpus: int
    runtime_ngpus: int
    cp_size: int = 0
    ep_size: int = 0
    dp_sharded: bool = False
    moe_expert_num: int | None = None
    zero_group_size: int | None = None
    pipeline_stages: int = 1


@dataclass(frozen=True)
class ParallelGroup:
    role: str
    scale_unit: int
    members: tuple[int, ...]


@dataclass(frozen=True)
class ParallelTopology:
    config: ParallelConfig
    groups: tuple[ParallelGroup, ...]
    eager_groups: tuple[tuple[int, ...], ...]
    source_revision: str
    evidence_kind: str = _EVIDENCE

    def groups_for(self, role: str) -> tuple[ParallelGroup, ...]:
        if role not in _ROLES:
            raise ValueError(f"unknown group role: {role!r}")
        return tuple(group for group in self.groups if group.role == role)

    def group_for_rank(self, role: str, runtime_rank: int) -> ParallelGroup:
        _integer("runtime_rank", runtime_rank, 0)
        if runtime_rank >= self.config.runtime_ngpus:
            raise ValueError("runtime_rank outside runtime world")
        matches = tuple(g for g in self.groups_for(role) if runtime_rank in g.members)
        if len(matches) != 1:
            raise ValueError("rank must belong to exactly one group for this role")
        return matches[0]

    def local_rank(self, role: str, runtime_rank: int) -> int:
        return self.group_for_rank(role, runtime_rank).members.index(runtime_rank)


def _integer(name: str, value: object, minimum: int) -> None:
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum} (not bool)")


def _revision(revision: str) -> None:
    if type(revision) is not str or re.fullmatch(r"[0-9a-fA-F]{40}", revision) is None:
        raise ValueError("revision must be a full 40-hex commit identifier, not an alias")


def _check_config(config: ParallelConfig, *, effective: bool) -> None:
    if type(config) is not ParallelConfig:
        raise ValueError("config must be ParallelConfig")
    for name in ("plan_ngpus", "runtime_ngpus", "pipeline_stages"):
        _integer(name, getattr(config, name), 1)
    for name in ("cp_size", "ep_size"):
        _integer(name, getattr(config, name), 1 if effective else 0)
    if type(config.dp_sharded) is not bool:
        raise ValueError("dp_sharded must be bool")
    if config.moe_expert_num is not None:
        _integer("moe_expert_num", config.moe_expert_num, 1)
    if effective or config.zero_group_size is not None:
        _integer("zero_group_size", config.zero_group_size, 1)
    p, r = config.plan_ngpus, config.runtime_ngpus
    if r % p:
        raise ValueError("runtime_ngpus must be divisible by plan_ngpus")
    zero = r if config.zero_group_size is None else config.zero_group_size
    if r % zero or (r // p) % (r // zero):
        raise ValueError("ZeRO requires runtime % zero == 0 and scale_units % zero_ngroups == 0")
    if not effective:
        return
    cp, ep = config.cp_size, config.ep_size
    if p % cp or p % ep:
        raise ValueError("CP and EP must divide plan_ngpus")
    if config.dp_sharded:
        if cp != 1:
            raise ValueError("dp_sharded requires CP=1")
    elif max(cp, ep) != p:
        raise ValueError("non-sharded plan_ngpus must equal max(CP, EP)")
    if config.moe_expert_num is not None and config.moe_expert_num % ep:
        raise ValueError("moe_expert_num must be divisible by EP")
    if not config.dp_sharded and cp < ep and config.pipeline_stages > 1:
        raise ValueError("pipeline exploration unsupported for CP<EP")


def _semantic_groups(config: ParallelConfig) -> tuple[ParallelGroup, ...]:
    result = []
    p = config.plan_ngpus
    for unit, base in enumerate(range(0, config.runtime_ngpus, p)):
        for role, width in (("scale_unit", p), ("cp", config.cp_size), ("ep", config.ep_size)):
            for offset in range(0, p, width):
                result.append(ParallelGroup(role, unit, tuple(range(base + offset, base + offset + width))))
        for coordinate in range(config.cp_size):
            result.append(ParallelGroup("data_lane", unit, tuple(range(base + coordinate, base + p, config.cp_size))))
    return tuple(result)


def derive_topology(config: ParallelConfig, *, upstream_root: str | Path,
                    revision: str) -> ParallelTopology:
    """Execute explicitly trusted pinned source; independently check its results.

    A present expert count means MoE is enabled. A stages value greater than one
    requests pipeline exploration compatibility, not a stage-placement model.
    No GQA/head-count constraint belongs to this rank-topology API.
    """
    _revision(revision)  # Validate syntax BEFORE any lookup or execution.
    _check_config(config, effective=False)
    command = ["git", "-C", str(upstream_root)]
    kind = subprocess.run(command + ["cat-file", "-t", revision], check=True,
                          capture_output=True, text=True).stdout.strip()
    if kind != "commit":
        raise ValueError("source revision must identify a commit object")
    source = subprocess.run(command + ["show", f"{revision}:llm/parallelism.py"],
                            check=True, capture_output=True, text=True).stdout
    namespace: dict[str, Any] = {"__name__": "_trusted_parallel_topology_source",
                 "__file__": f"{upstream_root}@{revision}:llm/parallelism.py"}
    exec(compile(source, namespace["__file__"], "exec"), namespace)
    args = SimpleNamespace(cp_size=config.cp_size, ep_size=config.ep_size,
                           dp_sharded=config.dp_sharded, moe=config.moe_expert_num is not None,
                           moe_expert_num=config.moe_expert_num)
    namespace["resolve_parallel_sizes"](args, config.plan_ngpus)
    effective = replace(config, cp_size=args.cp_size, ep_size=args.ep_size,
                        zero_group_size=config.runtime_ngpus if config.zero_group_size is None else config.zero_group_size)
    _check_config(effective, effective=True)
    namespace["validate_pipeline_compatibility"](args, [True] if config.pipeline_stages > 1 else [])
    groups = _semantic_groups(effective)
    for rank in range(effective.runtime_ngpus):
        actual_lane = namespace["get_data_lane_group"](rank, effective.plan_ngpus, effective.cp_size)
        expected_lane = next(g.members for g in groups if g.role == "data_lane" and rank in g.members)
        if type(actual_lane) is not tuple or any(type(r) is not int for r in actual_lane) or actual_lane != expected_lane:
            raise ValueError("source data-lane group disagrees with independent topology")
    actual_eager = namespace["build_runtime_process_groups"](
        effective.runtime_ngpus, effective.plan_ngpus, effective.cp_size, effective.ep_size)
    topology = ParallelTopology(effective, groups, tuple(actual_eager), revision)
    validate_topology(topology)
    return topology


def validate_topology(topology: ParallelTopology) -> None:
    """Validate independently using per-rank coordinates, not the emitter.

    Exact ordered membership and canonical group-row order are checked; matching
    counts or a coordinated mutation of semantic and eager groups is insufficient.
    This checks structural validity, not authenticity of a serialized revision.
    """
    if type(topology) is not ParallelTopology:
        raise ValueError("topology must be ParallelTopology")
    _check_config(topology.config, effective=True)
    _revision(topology.source_revision)
    if topology.evidence_kind != _EVIDENCE or type(topology.evidence_kind) is not str:
        raise ValueError("evidence_kind must be source-derived-topology")
    if type(topology.groups) is not tuple or type(topology.eager_groups) is not tuple:
        raise ValueError("group collections must be tuples")
    c = topology.config
    p = c.plan_ngpus
    actual = {}
    keys = []
    for group in topology.groups:
        if type(group) is not ParallelGroup or group.role not in _ROLES:
            raise ValueError("invalid semantic group or role")
        _integer("scale_unit", group.scale_unit, 0)
        if type(group.members) is not tuple or not group.members:
            raise ValueError("members must be a nonempty tuple")
        for rank in group.members:
            _integer("member rank", rank, 0)
            if rank >= c.runtime_ngpus or rank // p != group.scale_unit:
                raise ValueError("rank outside world or scale unit")
            key = (group.role, rank)
            if key in actual:
                raise ValueError("duplicate rank coverage")
            actual[key] = group
        keys.append((group.scale_unit, _ROLES.index(group.role), group.members[0]))
    if keys != sorted(keys):
        raise ValueError("noncanonical semantic group-row order")
    expected_eager = set()
    for rank in range(c.runtime_ngpus):
        unit, offset = divmod(rank, p)
        base = unit * p
        # Independent coordinate characterization: no call to _semantic_groups.
        specifications = {
            "scale_unit": (tuple(base + i for i in range(p)), offset),
            "cp": (tuple(base + (offset // c.cp_size) * c.cp_size + i for i in range(c.cp_size)), offset % c.cp_size),
            "ep": (tuple(base + (offset // c.ep_size) * c.ep_size + i for i in range(c.ep_size)), offset % c.ep_size),
            "data_lane": (tuple(base + offset % c.cp_size + i * c.cp_size for i in range(p // c.cp_size)), offset // c.cp_size),
        }
        for role, (members, local) in specifications.items():
            group = actual.get((role, rank))
            if group is None or group.members != members:
                raise ValueError(f"incorrect ordered {role} membership at rank {rank}")
            if topology.group_for_rank(role, rank) != group or topology.local_rank(role, rank) != local:
                raise ValueError("inconsistent local rank")
            if len(members) > 1:
                expected_eager.add(members)
    for members in topology.eager_groups:
        if type(members) is not tuple or any(type(rank) is not int for rank in members):
            raise ValueError("eager groups must contain integer tuples")
    if topology.eager_groups != tuple(sorted(expected_eager)):
        raise ValueError("source eager groups disagree with independent nontrivial role union")


def topology_to_dict(topology: ParallelTopology) -> dict:
    """Return validated JSON-native data; preserve the exact source revision."""
    validate_topology(topology)
    return {
        "config": asdict(topology.config),
        "groups": [{"role": g.role, "scale_unit": g.scale_unit, "members": list(g.members)}
                   for g in topology.groups],
        "eager_groups": [list(members) for members in topology.eager_groups],
        "source_revision": topology.source_revision,
        "evidence_kind": topology.evidence_kind,
    }


def _object(value: object, names: set[str], location: str) -> dict:
    if type(value) is not dict or set(value) != names:
        raise ValueError(f"{location} must contain exactly {sorted(names)}")
    return value


def _array(value: object, location: str) -> list:
    if type(value) is not list:
        raise ValueError(f"{location} must be a JSON array")
    return value


def topology_from_dict(payload: dict) -> ParallelTopology:
    """Strict schema plus independent structural validation; never replay exec.

    This checks a claimed source-derived topology, not its source provenance.
    Call derive_topology on a trusted repository to establish source agreement.
    """
    data = _object(payload, {f.name for f in fields(ParallelTopology)}, "topology")
    config_data = _object(data["config"], {f.name for f in fields(ParallelConfig)}, "config")
    config = ParallelConfig(**config_data)
    groups = []
    for index, value in enumerate(_array(data["groups"], "groups")):
        group = _object(value, {f.name for f in fields(ParallelGroup)}, f"groups[{index}]")
        groups.append(ParallelGroup(group["role"], group["scale_unit"],
                                    tuple(_array(group["members"], "members"))))
    eager = tuple(tuple(_array(members, "eager members"))
                  for members in _array(data["eager_groups"], "eager_groups"))
    result = ParallelTopology(config, tuple(groups), eager,
                              data["source_revision"], data["evidence_kind"])
    validate_topology(result)
    return result
