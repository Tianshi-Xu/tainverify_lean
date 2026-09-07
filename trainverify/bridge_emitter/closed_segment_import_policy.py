"""Pure theorem/import planning for closed segment families.

This module deliberately does not import the relation compiler: callers pass the
registered rule mapping so dependency flow stays one-way.
"""
from __future__ import annotations

from collections.abc import Mapping
from typing import Any


def plan_closed_segment_imports(
    family: tuple[str, ...],
    lean_theorems: tuple[str, ...] = (),
    registered_rules: Mapping[str, Any] | None = None,
) -> tuple[str, ...]:
    """Return exact ordered theorem modules required by one closed family."""
    registry = {} if registered_rules is None else registered_rules
    if len(family) == 1 and family[0] in registry:
        spec = registry[family[0]]
        if lean_theorems and any(
            theorem not in spec.lean_theorems for theorem in lean_theorems
        ):
            raise ValueError(
                f"registered rule {spec.rule_id} has inconsistent theorem imports"
            )
        return spec.lean_imports

    if family and all(item == "transpose-sharded-k-rank" for item in family):
        if len(lean_theorems) != len(family):
            raise ValueError("transpose segment requires one theorem identity per transition")
        modules: list[str] = []
        for theorem in lean_theorems:
            if ".fw_transposeAxes_1_2_" in theorem:
                module = "denote.KRankTranspose"
            elif ".fw_transposeAxes_2_3_" in theorem:
                module = "denote.KRankTranspose23Extra"
            else:
                raise ValueError("transpose segment theorem has no closed renderer import")
            if module not in modules:
                modules.append(module)
        return tuple(modules)

    theorem_modules: list[str] = []
    for theorem in lean_theorems:
        if ".fw_transposeAxes_1_2_" in theorem:
            module = "denote.KRankTranspose"
        elif ".fw_transposeAxes_2_3_" in theorem:
            module = "denote.KRankTranspose23Extra"
        elif ".fw_matmul_query_axis_rank4" in theorem:
            module = "denote.KRankMatmulQueryAxis"
        elif theorem == "TrainVerify.Denote.bw_linear_dx_column_allGather_rank3":
            module = "denote.KRankBWLinearDxColumnGeneral"
        elif theorem == "TrainVerify.Denote.bw_linear_dw_input_allGatherPrimDimN_dim2_rank3":
            module = "denote.KRankBWLinearDwColumn"
        elif theorem in {
            "TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim1_rank4",
            "TrainVerify.Denote.bw_softmax_allGatherPrimDimN_dim2_rank4",
        }:
            module = "denote.KRankBWSoftmaxGeneral"
        elif theorem in {"TrainVerify.Denote.bw_matmul_fst_head_gather_rank4",
                         "TrainVerify.Denote.bw_matmul_snd_head_gather_rank4"}:
            module = "denote.KRankBWMatmulHead"
        elif theorem == "TrainVerify.Denote.tensorSum_allGather_dim_K":
            module = "denote.KRankBWMultiref"
        elif theorem == "TrainVerify.Denote.bw_layernorm_dx_allGatherPrimDimN_dim1_3d":
            module = "denote.KRankBWLayernorm"
        else:
            continue
        if module not in theorem_modules:
            theorem_modules.append(module)

    mapping = {
        (
            "linear-sharded-k-rank-dim1",
            "linear-sharded-k-rank-dim1",
            "allgather-reconstruction-k-rank",
            "linear-output-sharded-k-rank",
        ): ("denote.KRankLinearGather",),
        (
            "embedding-vocab-sharded-reduction-k-rank",
            "embedding-sharded-ids-k-rank",
            "allreduce-reconstruction-k-rank",
        ): ("denote.EmbeddingSequenceShard", "denote.KRankAllToAll"),
    }
    if (
        len(family) >= 2
        and all(
            item == "linear-reduction-producer-k-rank" for item in family[:-1]
        )
        and family[-1] == "linear-output-sharded-k-rank"
    ):
        family_modules = (
            "denote.KRankLinearReduction",
            "denote.KRankLinearGather",
        )
    else:
        family_modules = mapping.get(family, ())
    return tuple(dict.fromkeys((*theorem_modules, *family_modules)))
