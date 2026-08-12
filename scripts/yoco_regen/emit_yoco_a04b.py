#!/usr/bin/env python3
"""Emit an atomic YOCO-MoE Lean refresh snapshot from trusted authority artifacts."""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import hmac
import json
import multiprocessing.pool
import os
import re
import shutil
import stat
import subprocess
import sys
from pathlib import Path, PurePosixPath

from scripts.yoco_regen.safe_cleanup import create_owned_stage, cleanup_owned_stage
from scripts.yoco_regen.cleanup_errors import CleanupFailureGroup
from scripts.yoco_regen.strict_json import load_strict_json, loads_strict_json
from scripts.yoco_regen.torch_compat import ensure_torch_recompile_limit


ROOT = Path(__file__).resolve().parents[2]
STUBS = Path(__file__).resolve().parent / "stubs"
LLM_REVISION = "9a1be1d5fd1c063d80be82797692cdc7d23cfbef"
NNSCALER_REVISION = "d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf"
ALLOWED_POLICY_IDENTITIES = {
    "__main__.main.<locals>.autodist_wrapper",
    "__mp_main__.main.<locals>.autodist_wrapper",
    "nnscaler_train.main.<locals>.autodist_wrapper",
}
WORLD_KEYS = {
    "model_name", "num_dp", "num_tp", "num_pp", "num_mb", "gbs",
    "num_layers", "num_heads", "hidden_size", "seqlen",
    "n_activated_experts", "n_routed_experts",
}
METADATA_JSON_NAMES = (
    "gen_args.json", "comm_profile_intra_2.json",
    "sm_mgener.json", "pm_mgener.json",
    "sm_provenance.json", "pm_provenance.json",
    "sm_mgener.pkl.receipt.json", "pm_mgener.pkl.receipt.json",
)
AUTHORITY_NAMES = (
    "sm_mgener.pkl", "pm_mgener.pkl",
) + METADATA_JSON_NAMES + ("nnscaler_dp_solver.so", "comp_profile.json")
STATIC_GOAL_MODULES = (
    "trainverify/denote/yoco_goals/BridgeKit.lean",
    "trainverify/denote/yoco_goals/JointWitnessCore.lean",
    "trainverify/denote/yoco_goals/Goal1ExternalContractWitness.lean",
    "trainverify/denote/yoco_goals/Goal_3_Cut.lean",
    "trainverify/denote/yoco_goals/CanonicalGoal4L0Routing.lean",
    "trainverify/denote/yoco_goals/CanonicalGoal4L1Routing.lean",
    "trainverify/denote/yoco_goals/CanonicalGoal4L2Routing.lean",
    "trainverify/denote/yoco_goals/CanonicalL21Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL21Composition.lean",
    "trainverify/denote/yoco_goals/CanonicalL13KVSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL13KVGraph.lean",
    "trainverify/denote/yoco_goals/CanonicalL13KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL13AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL13Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL13Upstream.lean",
    "trainverify/denote/yoco_goals/CanonicalL13ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL14KVSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL14KVGraph.lean",
    "trainverify/denote/yoco_goals/CanonicalL14KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL14AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL14Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL14Upstream.lean",
    "trainverify/denote/yoco_goals/CanonicalL14ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL15KVSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL15KVGraph.lean",
    "trainverify/denote/yoco_goals/CanonicalL15KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL15AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL15Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL15Upstream.lean",
    "trainverify/denote/yoco_goals/CanonicalL15ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL16KVSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL16KVGraph.lean",
    "trainverify/denote/yoco_goals/CanonicalL16KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL16AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL16Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL16Upstream.lean",
    "trainverify/denote/yoco_goals/CanonicalL16ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL17KVSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL17KVGraph.lean",
    "trainverify/denote/yoco_goals/CanonicalL17KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL17AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL17Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL17Upstream.lean",
    "trainverify/denote/yoco_goals/CanonicalL17ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL18KVSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL18KVGraph.lean",
    "trainverify/denote/yoco_goals/CanonicalL18KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL18AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL18Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL18Upstream.lean",
    "trainverify/denote/yoco_goals/CanonicalL18ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL19KVSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL19KVGraph.lean",
    "trainverify/denote/yoco_goals/CanonicalL19KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL19AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL19Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL19Upstream.lean",
    "trainverify/denote/yoco_goals/CanonicalL19ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3KVSemantic.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3KVGraph.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3KAlignment.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3AttentionComposition.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3Output.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3Upstream.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3MoEResidualGate.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3MoENormRouter.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3MoERouter.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3MoEExpertDown.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3MoEDown.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3MoEOutput.lean",
    "trainverify/denote/yoco_goals/Goal1L12Block3MoEComposition.lean",
    "trainverify/denote/yoco_goals/Goal1L12ThirdZigzagBlock.lean",
    "trainverify/denote/yoco_goals/CanonicalL20Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL20Upstream.lean",
    "trainverify/denote/yoco_goals/CanonicalL20AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL20ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL20KVGraph.lean",
    "trainverify/denote/yoco_goals/CanonicalL20KVSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL20KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL21ExpertDown.lean",
    "trainverify/denote/yoco_goals/CanonicalL21Down.lean",
    "trainverify/denote/yoco_goals/CanonicalL21NormRouter.lean",
    "trainverify/denote/yoco_goals/CanonicalL21Router.lean",
    "trainverify/denote/yoco_goals/CanonicalL21ResidualGate.lean",
    "trainverify/denote/yoco_goals/CanonicalL22Attention.lean",
    "trainverify/denote/yoco_goals/CanonicalL22AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL22KSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL22KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL22VSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL22VAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL22Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL22Residual.lean",
    "trainverify/denote/yoco_goals/CanonicalL23Composition.lean",
    "trainverify/denote/yoco_goals/Goal1L22L23HeadComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalKVCacheGraphReductions.lean",
    "trainverify/denote/yoco_goals/CanonicalKVCacheOrdinaryOps.lean",
    "trainverify/denote/yoco_goals/CanonicalKVCacheOrdinaryNorm.lean",
    "trainverify/denote/yoco_goals/CanonicalKVCacheOrdinaryRouterGate.lean",
    "trainverify/denote/yoco_goals/CanonicalKVCacheOrdinaryExpert.lean",
    "trainverify/denote/yoco_goals/CanonicalKVCacheOrdinaryDown.lean",
    "trainverify/denote/yoco_goals/CanonicalKVCacheOrdinaryBoundary.lean",
    "trainverify/denote/yoco_goals/CanonicalKVCacheOrdinaryComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL23Expert.lean",
    "trainverify/denote/yoco_goals/CanonicalL23GateDown.lean",
    "trainverify/denote/yoco_goals/CanonicalL23Down.lean",
    "trainverify/denote/yoco_goals/CanonicalL23Join.lean",
    "trainverify/denote/yoco_goals/CanonicalL23Norm.lean",
    "trainverify/denote/yoco_goals/CanonicalL23Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL23Residual.lean",
    "trainverify/denote/yoco_goals/CanonicalL23Router.lean",
    "trainverify/denote/yoco_goals/CanonicalLossBackboneTail.lean",
    "trainverify/denote/yoco_goals/CanonicalLossBackboneTailGoal2.lean",
    "trainverify/denote/yoco_goals/Goal2FaithfulFull.lean",
    "trainverify/denote/yoco_goals/CanonicalL0OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalGoal1ExternalL0Composition.lean",
    "trainverify/denote/yoco_goals/Goal1L1L11CacheComposition.lean",
    "trainverify/denote/yoco_goals/Goal1ExternalToCacheComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL12ZigzagEntry.lean",
    "trainverify/denote/yoco_goals/CanonicalL12AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL12KVGraph.lean",
    "trainverify/denote/yoco_goals/CanonicalL12KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL12Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL12ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL12Block2KVSemantic.lean",
    "trainverify/denote/yoco_goals/CanonicalL12Block2KVGraph.lean",
    "trainverify/denote/yoco_goals/CanonicalL12Block2KAlignment.lean",
    "trainverify/denote/yoco_goals/CanonicalL12Block2Upstream.lean",
    "trainverify/denote/yoco_goals/CanonicalL12Block2AttentionComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL12Block2Output.lean",
    "trainverify/denote/yoco_goals/CanonicalL12Block2ShardedKVAttention.lean",
    "trainverify/denote/yoco_goals/L12Block2ZigzagMoEResidualGate.lean",
    "trainverify/denote/yoco_goals/L12Block2ZigzagMoENormRouter.lean",
    "trainverify/denote/yoco_goals/L12Block2ZigzagMoERouter.lean",
    "trainverify/denote/yoco_goals/L12Block2ZigzagMoEExpertDown.lean",
    "trainverify/denote/yoco_goals/L12Block2ZigzagMoEDown.lean",
    "trainverify/denote/yoco_goals/L12Block2ZigzagMoEOutput.lean",
    "trainverify/denote/yoco_goals/L12Block2ZigzagMoEComposition.lean",
    "trainverify/denote/yoco_goals/CanonicalL12Block2Composition.lean",
    "trainverify/denote/yoco_goals/L0OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL1OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL1OrdinaryComposition.lean",
    "trainverify/denote/yoco_goals/L1OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL2OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL2OrdinaryComposition.lean",
    "trainverify/denote/yoco_goals/L2OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL3OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL3OrdinaryComposition.lean",
    "trainverify/denote/yoco_goals/L3OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL4OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL4OrdinaryComposition.lean",
    "trainverify/denote/yoco_goals/L4OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL5OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL5OrdinaryComposition.lean",
    "trainverify/denote/yoco_goals/L5OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL6OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL6OrdinaryComposition.lean",
    "trainverify/denote/yoco_goals/L6OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL7OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL7OrdinaryComposition.lean",
    "trainverify/denote/yoco_goals/L7OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL8OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL8OrdinaryComposition.lean",
    "trainverify/denote/yoco_goals/L8OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL9OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/CanonicalL9OrdinaryComposition.lean",
    "trainverify/denote/yoco_goals/L9OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL10OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/PreShufflePMGraphBridge.lean",
    "trainverify/denote/yoco_goals/L0OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L0OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L0OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L0OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L0OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L0OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L0OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L1OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L1OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L1OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L1OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L1OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L1OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L1OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L2OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L2OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L2OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L2OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L2OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L2OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L2OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L3OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L3OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L3OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L3OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L3OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L3OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L3OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L4OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L4OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L4OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L4OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L4OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L4OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L4OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L5OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L5OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L5OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L5OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L5OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L5OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L5OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L6OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L6OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L6OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L6OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L6OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L6OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L6OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L7OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L7OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L7OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L7OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L7OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L7OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L7OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L8OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L8OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L8OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L8OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L8OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L8OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L8OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L9OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L9OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L9OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L9OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L9OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L9OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L9OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L10FaithfulReductionKit.lean",
    "trainverify/denote/yoco_goals/L10OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/L10OrdinaryMoEGraphReductions.lean",
    "trainverify/denote/yoco_goals/L10OrdinaryMoENorm.lean",
    "trainverify/denote/yoco_goals/L10OrdinaryMoERouterGate.lean",
    "trainverify/denote/yoco_goals/L10OrdinaryMoEExpert.lean",
    "trainverify/denote/yoco_goals/L10OrdinaryMoEDown.lean",
    "trainverify/denote/yoco_goals/L10OrdinaryMoEBoundary.lean",
    "trainverify/denote/yoco_goals/L10OrdinaryMoEComposition.lean",
    "trainverify/denote/yoco_goals/L11OrdinaryQKV.lean",
    "trainverify/denote/yoco_goals/CanonicalL11OrdinaryAttention.lean",
    "trainverify/denote/yoco_goals/L12ZigzagMoEResidualGate.lean",
    "trainverify/denote/yoco_goals/L12ZigzagMoENormRouter.lean",
    "trainverify/denote/yoco_goals/L12ZigzagMoERouter.lean",
    "trainverify/denote/yoco_goals/L12ZigzagMoEExpertDown.lean",
    "trainverify/denote/yoco_goals/L12ZigzagMoEDown.lean",
    "trainverify/denote/yoco_goals/L12ZigzagMoEOutput.lean",
    "trainverify/denote/yoco_goals/L12ZigzagMoEComposition.lean",
    "trainverify/denote/yoco_goals/L13ZigzagMoEResidualGate.lean",
    "trainverify/denote/yoco_goals/L13ZigzagMoENormRouter.lean",
    "trainverify/denote/yoco_goals/L13ZigzagMoERouter.lean",
    "trainverify/denote/yoco_goals/L13ZigzagMoEExpertDown.lean",
    "trainverify/denote/yoco_goals/L13ZigzagMoEDown.lean",
    "trainverify/denote/yoco_goals/L13ZigzagMoEOutput.lean",
    "trainverify/denote/yoco_goals/L13ZigzagMoEComposition.lean",
    "trainverify/denote/yoco_goals/L14ZigzagMoEResidualGate.lean",
    "trainverify/denote/yoco_goals/L14ZigzagMoENormRouter.lean",
    "trainverify/denote/yoco_goals/L14ZigzagMoERouter.lean",
    "trainverify/denote/yoco_goals/L14ZigzagMoEExpertDown.lean",
    "trainverify/denote/yoco_goals/L14ZigzagMoEDown.lean",
    "trainverify/denote/yoco_goals/L14ZigzagMoEOutput.lean",
    "trainverify/denote/yoco_goals/L14ZigzagMoEComposition.lean",
    "trainverify/denote/yoco_goals/Goal1ExternalToL14Composition.lean",
    "trainverify/denote/yoco_goals/L15ZigzagMoEResidualGate.lean",
    "trainverify/denote/yoco_goals/L15ZigzagMoENormRouter.lean",
    "trainverify/denote/yoco_goals/L15ZigzagMoERouter.lean",
    "trainverify/denote/yoco_goals/L15ZigzagMoEExpertDown.lean",
    "trainverify/denote/yoco_goals/L15ZigzagMoEDown.lean",
    "trainverify/denote/yoco_goals/L15ZigzagMoEOutput.lean",
    "trainverify/denote/yoco_goals/L15ZigzagMoEComposition.lean",
    "trainverify/denote/yoco_goals/Goal1ExternalToL15Composition.lean",
    "trainverify/denote/yoco_goals/L16ZigzagMoEResidualGate.lean",
    "trainverify/denote/yoco_goals/L16ZigzagMoENormRouter.lean",
    "trainverify/denote/yoco_goals/L16ZigzagMoERouter.lean",
    "trainverify/denote/yoco_goals/L16ZigzagMoEExpertDown.lean",
    "trainverify/denote/yoco_goals/L16ZigzagMoEDown.lean",
    "trainverify/denote/yoco_goals/L16ZigzagMoEOutput.lean",
    "trainverify/denote/yoco_goals/L16ZigzagMoEComposition.lean",
    "trainverify/denote/yoco_goals/Goal1ExternalToL16Composition.lean",
    "trainverify/denote/yoco_goals/L17ZigzagMoEResidualGate.lean",
    "trainverify/denote/yoco_goals/L17ZigzagMoENormRouter.lean",
    "trainverify/denote/yoco_goals/L17ZigzagMoERouter.lean",
    "trainverify/denote/yoco_goals/L17ZigzagMoEExpertDown.lean",
    "trainverify/denote/yoco_goals/L17ZigzagMoEDown.lean",
    "trainverify/denote/yoco_goals/L17ZigzagMoEOutput.lean",
    "trainverify/denote/yoco_goals/L17ZigzagMoEComposition.lean",
    "trainverify/denote/yoco_goals/Goal1ExternalToL17Composition.lean",
    "trainverify/denote/yoco_goals/L18ZigzagMoEResidualGate.lean",
    "trainverify/denote/yoco_goals/L18ZigzagMoENormRouter.lean",
    "trainverify/denote/yoco_goals/L18ZigzagMoERouter.lean",
    "trainverify/denote/yoco_goals/L18ZigzagMoEExpertDown.lean",
    "trainverify/denote/yoco_goals/L18ZigzagMoEDown.lean",
    "trainverify/denote/yoco_goals/L18ZigzagMoEOutput.lean",
    "trainverify/denote/yoco_goals/L18ZigzagMoEComposition.lean",
    "trainverify/denote/yoco_goals/Goal1ExternalToL18Composition.lean",
    "trainverify/denote/yoco_goals/L19ZigzagMoEResidualGate.lean",
    "trainverify/denote/yoco_goals/L19ZigzagMoENormRouter.lean",
    "trainverify/denote/yoco_goals/L19ZigzagMoERouter.lean",
    "trainverify/denote/yoco_goals/L19ZigzagMoEExpertDown.lean",
    "trainverify/denote/yoco_goals/L19ZigzagMoEDown.lean",
    "trainverify/denote/yoco_goals/L19ZigzagMoEOutput.lean",
    "trainverify/denote/yoco_goals/L19ZigzagMoEComposition.lean",
    "trainverify/denote/yoco_goals/Goal1ExternalFinalComposition.lean",
    "trainverify/denote/yoco_goals/Goal_3_FaithfulFull.lean",
    "trainverify/denote/yoco_goals/Goal3L0L11RoutingCertificate.lean",
    "trainverify/denote/yoco_goals/Goal3ToGoal1AncestryShapeBridge.lean",
    "trainverify/denote/yoco_goals/Goal3FaithfulRoutingLate.lean",
    "trainverify/denote/yoco_goals/Goal3FaithfulFullTheorem.lean",
    "trainverify/denote/yoco_goals/Goal3SkipUnshuffleTransport.lean",
    *(f"trainverify/denote/yoco_goals/CanonicalGoal3L{layer}Routing.lean" for layer in range(12, 24)),
    "trainverify/denote/yoco_goals/Goal4EarlyScopedBridge.lean",
    "trainverify/denote/yoco_goals/Goal4L0L11GateScoreCertificate.lean",
    "trainverify/denote/yoco_goals/Goal4FaithfulRoutingStack.lean",
    "trainverify/denote/yoco_goals/Goal4FaithfulRoutingLate.lean",
    "trainverify/denote/yoco_goals/Goal4FaithfulFullTheorem.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulCheckpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL12OutputCheckpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL12BlocksCheckpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL13Attention.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL13Norm.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL13Router.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL13Output.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL13Score.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL13Assemble.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL13Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL14Attention.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL14Norm.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL14Router.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL14Output.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL14Score.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL14Assemble.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL14Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL15Attention.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL15Norm.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL15Router.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL15Output.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL15Score.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL15Assemble.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL15Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL16Attention.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL16Norm.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL16Router.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL16Output.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL16Score.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL16Assemble.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL16Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL17Attention.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL17Norm.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL17Router.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL17Output.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL17Score.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL17Assemble.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL17Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL18Attention.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL18Norm.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL18Router.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL18Output.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL18Score.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL18Assemble.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL18Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL19Attention.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL19Norm.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL19Router.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL19Output.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL19Score.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL19Assemble.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL19Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL20Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL21Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL22Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulL23Checkpoint.lean",
    "trainverify/denote/yoco_goals/Goal4PublicFaithfulLateAncestry.lean",
    *(f"trainverify/denote/yoco_goals/CanonicalGoal4L{layer}Routing.lean" for layer in range(3, 24)),
    "trainverify/denote/yoco_goals/FaithfulStackGather.lean",
    "trainverify/denote/yoco_goals/CanonicalGoal1EmbeddingEntry.lean",
    "trainverify/denote/yoco_goals/Goal_1_FaithfulHead.lean",
    "trainverify/denote/yoco_goals/Goal_2_FaithfulHead.lean",
    "trainverify/denote/yoco_goals/ZigzagBroadcastMul.lean",
    "trainverify/denote/yoco_goals/ZigzagAttentionRel.lean",
    "trainverify/denote/yoco_goals/ZigzagShardedKVRegression.lean",
    "trainverify/denote/yoco_goals/ZigzagElemwiseRel.lean",
    "trainverify/denote/yoco_goals/ZigzagLayoutRel.lean",
    "trainverify/denote/yoco_goals/ZigzagLinearRel.lean",
    "trainverify/denote/yoco_goals/ZigzagMoEGmmRel.lean",
    "trainverify/denote/yoco_goals/ZigzagPointwiseRel.lean",
    "trainverify/denote/yoco_goals/ZigzagRouterRel.lean",
    "trainverify/denote/yoco_goals/ZigzagGoalStatement.lean",
    "trainverify/denote/yoco_goals/GatherOpGears.lean",
    "trainverify/denote/yoco_goals/Goal4LateScopedBridge.lean",
    "trainverify/denote/yoco_goals/RingAttnGears.lean",
    "trainverify/denote/yoco_goals/ZigzagViewRel.lean",
)
GENERATED_GOAL_MODULES = (
    "Goal_1.lean", "Goal_1_Cut.lean", "Goal_2.lean", "Goal_3.lean",
    "Goal_4.lean", "Goal_4_Cut.lean", "Goal_5.lean",
    "Pattern_1.lean", "Pattern_2.lean", "Pattern_3.lean", "Pattern_4.lean",
    "Pattern_5.lean", "Instances.lean", "MainTheorem.lean",
)
REGISTERED_TOP_LEVEL_MODULES = {
    "EmbeddingHiddenShard.lean",
    "ChunkGatherDim0.lean",
    "Gather2Rel.lean",
    "InnerChunkCEShard.lean",
    "InnerChunkCELossShard.lean",
    "MultirefGeneral.lean",
    "MoEFullSplitCommute.lean",
    "PackedCuSeqlensWitness.lean",
    "SlidingWindowReconstruction.lean",
    "TopkGateScoreGather.lean",
}
EXPECTED_GOAL_MODULES = {
    Path(relative_path).name for relative_path in STATIC_GOAL_MODULES
} | set(GENERATED_GOAL_MODULES)
PROOF_REGISTRY_KEYS = {
    "schema_version", "generated_lean_sha256", "goal_sha256", "modules",
    "proof_targets",
}
PROOF_REGISTRY_GOALS = {f"Goal_{index}.lean" for index in range(1, 6)}
REGISTERED_LEGACY_CUT_MODULES = {"Goal_1_Cut.lean", "Goal_4_Cut.lean"}
DEPRECATED_GENERATED_AUXILIARY_MODULES = {
    *(f"Goal_{index}_CutToFull.lean" for index in range(1, 6)),
    "Patterns.lean", "ProofObligations.lean",
}
REGISTERED_SEALED_DEPENDENCY_MODULES = {
    "GatherOpGears.lean", "Goal4LateScopedBridge.lean",
    "RingAttnGears.lean", "ZigzagViewRel.lean",
}
PROOF_MODULE_KEYS = {"source", "sha256"}
FORBIDDEN_PROOF_TOKEN = re.compile(rb"\b(?:sorry(?:Ax)?|axiom|unsafe)\b")
PROOF_REGISTRY_PATH = "scripts/yoco_regen/yoco_proof_registry.json"
LEAN_NAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$")
LEAN_TARGETS = (
    "denote.GeneratedYOCOMoE",
    *(f"denote.yoco_goals.Goal_{index}" for index in range(1, 6)),
    *(f"denote.yoco_goals.Pattern_{index}" for index in range(1, 6)),
    "denote.yoco_goals.Instances", "denote.yoco_goals.MainTheorem",
)
RECEIPT_KEYS = {
    "policy", "plan_ngpus", "runtime_ngpus", "pkl_sha256",
    "patched_parallel_py_sha256", "patched_llm_gemm_py_sha256",
    "comm_profile_sha256", "comp_profile_sha256", "dp_solver_extension_sha256",
    "canonicalized_comment_count", "canonicalized_code_count",
}
RECORD_KEYS = {
    "authority", "policy", "plan_ngpus", "runtime_ngpus", "zero_group_size",
    "cp_size_runtime", "ep_size_runtime", "cp_size_codegen_sentinel",
    "pkl_sha256", "receipt_sha256", "patched_parallel_py_sha256",
    "patched_llm_gemm_py_sha256", "node_count", "signature_counts",
    "comm_profile_sha256", "comp_profile_sha256", "dp_solver_extension_sha256",
    "canonicalized_comment_count", "canonicalized_code_count",
}
HARDWARE_KEYS = {
    "cuda_runtime_version", "nccl_version", "nvidia_driver_version",
    "gpu_inventory", "trainverify_regen_commit",
    "comm_profile_sha256", "comp_profile_sha256",
}
GPU_KEYS = {"index", "name", "total_memory_bytes", "compute_capability"}
META_KEYS = {
    "authority", "model", "max_seq_len", "layers", "cross_layers",
    "precision", "partition_constraints", "llm_train_commit",
    "llm_hardware_patch", "nnscaler_commit", "nnscaler_version",
    "torch_version", "cuda_runtime_version", "nccl_version",
    "nvidia_driver_version", "gpu_inventory", "python_version", "host",
    "trainverify_regen_commit", "comm_profile_sha256", "hardware_sha256",
    "dp_solver_extension_sha256", "comp_profile_sha256", "source_sha256", "sm", "pm",
}


def _strict_int(value, *, minimum: int = 0) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= minimum


def _is_lower_hex(value, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(c in "0123456789abcdef" for c in value)
    )


def _require_exact_keys(value, expected: set[str], label: str) -> None:
    if not isinstance(value, dict) or set(value) != expected:
        actual = set(value) if isinstance(value, dict) else type(value).__name__
        raise RuntimeError(f"{label} schema mismatch: {actual}")


def validate_receipt_schema(receipt: dict, plan: int) -> None:
    _require_exact_keys(receipt, RECEIPT_KEYS, "receipt")
    if (
        receipt["policy"] not in ALLOWED_POLICY_IDENTITIES
        or not _strict_int(receipt["plan_ngpus"], minimum=1)
        or not _strict_int(receipt["runtime_ngpus"], minimum=1)
        or receipt["plan_ngpus"] != plan
        or receipt["runtime_ngpus"] != plan
        or not _is_lower_hex(receipt["pkl_sha256"], 64)
        or not _is_lower_hex(receipt["patched_parallel_py_sha256"], 64)
        or not _is_lower_hex(receipt["patched_llm_gemm_py_sha256"], 64)
        or not _is_lower_hex(receipt["comm_profile_sha256"], 64)
        or not _is_lower_hex(receipt["comp_profile_sha256"], 64)
        or not _is_lower_hex(receipt["dp_solver_extension_sha256"], 64)
        or type(receipt["canonicalized_comment_count"]) is not int
        or receipt["canonicalized_comment_count"] < 0
        or type(receipt["canonicalized_code_count"]) is not int
        or receipt["canonicalized_code_count"] < 0
    ):
        raise RuntimeError("receipt schema values mismatch")


def validate_record_schema(record: dict, plan: int) -> None:
    _require_exact_keys(record, RECORD_KEYS, "provenance record")
    if (
        record["authority"] is not True
        or record["policy"] != "pas_autodist"
        or any(
            not _strict_int(record[key], minimum=1) or record[key] != plan
            for key in (
            "plan_ngpus", "runtime_ngpus", "zero_group_size",
            "cp_size_runtime", "ep_size_runtime",
        ))
        or not _strict_int(record["cp_size_codegen_sentinel"], minimum=0)
        or record["cp_size_codegen_sentinel"] != 0
        or not _is_lower_hex(record["pkl_sha256"], 64)
        or not _is_lower_hex(record["receipt_sha256"], 64)
        or not _is_lower_hex(record["patched_parallel_py_sha256"], 64)
        or not _is_lower_hex(record["patched_llm_gemm_py_sha256"], 64)
        or not _is_lower_hex(record["comm_profile_sha256"], 64)
        or not _is_lower_hex(record["comp_profile_sha256"], 64)
        or not _is_lower_hex(record["dp_solver_extension_sha256"], 64)
        or not _strict_int(record["canonicalized_comment_count"], minimum=0)
        or not _strict_int(record["canonicalized_code_count"], minimum=0)
        or not _strict_int(record["node_count"], minimum=1)
        or not isinstance(record["signature_counts"], dict)
        or not record["signature_counts"]
        or any(
            not isinstance(key, str) or not key
            or not _strict_int(count, minimum=0)
            for key, count in record["signature_counts"].items()
        )
    ):
        raise RuntimeError("provenance record schema values mismatch")


def validate_hardware_schema(hardware: dict) -> None:
    _require_exact_keys(hardware, HARDWARE_KEYS, "hardware metadata")
    inventory = hardware["gpu_inventory"]
    if not isinstance(inventory, list) or len(inventory) != 2:
        raise RuntimeError("GPU inventory must contain exactly two devices")
    normalized = []
    for expected_index, gpu in enumerate(inventory):
        _require_exact_keys(gpu, GPU_KEYS, "GPU inventory entry")
        capability = gpu["compute_capability"]
        if (
            not _strict_int(gpu["index"], minimum=0)
            or gpu["index"] != expected_index
            or not isinstance(gpu["name"], str) or not gpu["name"]
            or not _strict_int(gpu["total_memory_bytes"], minimum=1)
            or not isinstance(capability, list) or len(capability) != 2
            or not _strict_int(capability[0], minimum=8)
            or not _strict_int(capability[1], minimum=0)
        ):
            raise RuntimeError("GPU inventory values mismatch")
        normalized.append((gpu["name"], gpu["total_memory_bytes"], capability))
    if normalized[0] != normalized[1]:
        raise RuntimeError("GPU inventory is not homogeneous")
    for key in ("cuda_runtime_version", "nvidia_driver_version"):
        value = hardware[key]
        if not isinstance(value, str) or not value or any(c not in "0123456789." for c in value):
            raise RuntimeError(f"hardware metadata {key} is invalid")
    nccl = hardware["nccl_version"]
    if (
        not isinstance(nccl, list) or len(nccl) != 3
        or any(not _strict_int(part, minimum=0) for part in nccl)
    ):
        raise RuntimeError("hardware metadata NCCL version is invalid")
    if not _is_lower_hex(hardware["trainverify_regen_commit"], 40):
        raise RuntimeError("hardware metadata regen commit is invalid")
    if not _is_lower_hex(hardware["comm_profile_sha256"], 64):
        raise RuntimeError("hardware metadata communication profile hash is invalid")
    if not _is_lower_hex(hardware["comp_profile_sha256"], 64):
        raise RuntimeError("hardware metadata computation profile hash is invalid")


def hardware_sha256(hardware: dict) -> str:
    validate_hardware_schema(hardware)
    payload = json.dumps(
        hardware, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def validate_expected_hardware(hardware: dict, expected_sha256: str) -> None:
    if not _is_lower_hex(expected_sha256, 64):
        raise RuntimeError("trusted hardware SHA-256 is malformed")
    actual = hardware_sha256(hardware)
    if not hmac.compare_digest(actual, expected_sha256):
        raise RuntimeError("trusted hardware SHA-256 mismatch")


def validate_meta_schema(meta: dict) -> None:
    _require_exact_keys(meta, META_KEYS, "gen_args")
    if (
        meta["authority"] is not True
        or meta["model"] != "YOCO-MoE-A0.4B"
        or not _strict_int(meta["max_seq_len"], minimum=1)
        or meta["max_seq_len"] != 4096
        or not _strict_int(meta["layers"], minimum=1)
        or meta["layers"] != 24
        or not _strict_int(meta["cross_layers"], minimum=1)
        or meta["cross_layers"] != 12
        or meta["precision"] != "fp32"
        or meta["partition_constraints"] != "llm/pcs/all2all_moe.yaml"
        or meta["llm_train_commit"] != LLM_REVISION
        or meta["nnscaler_commit"] != NNSCALER_REVISION
        or meta["llm_hardware_patch"] != "cc12_generic_triton_fallback_v1"
        or any(
            not isinstance(meta[key], str) or not meta[key]
            for key in ("nnscaler_version", "torch_version", "python_version", "host")
        )
        or not _is_lower_hex(meta["hardware_sha256"], 64)
        or not _is_lower_hex(meta["dp_solver_extension_sha256"], 64)
        or not _is_lower_hex(meta["comp_profile_sha256"], 64)
        or not isinstance(meta["source_sha256"], dict)
    ):
        raise RuntimeError("gen_args schema values mismatch")
    hardware = {key: meta[key] for key in HARDWARE_KEYS}
    validate_hardware_schema(hardware)
    if not hmac.compare_digest(meta["hardware_sha256"], hardware_sha256(hardware)):
        raise RuntimeError("gen_args hardware SHA-256 mismatch")
    validate_record_schema(meta["sm"], 1)
    validate_record_schema(meta["pm"], 2)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def digest_bytes(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def _read_regular_at(directory_fd: int, name: str) -> bytes:
    info = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
    if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid():
        raise RuntimeError(f"untrusted snapshot inode: {name}")
    if stat.S_IMODE(info.st_mode) & 0o022:
        raise RuntimeError(f"group/world writable snapshot inode: {name}")
    descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=directory_fd)
    try:
        opened = os.fstat(descriptor)
        if (opened.st_dev, opened.st_ino) != (info.st_dev, info.st_ino):
            raise RuntimeError(f"snapshot inode changed during open: {name}")
        chunks = []
        while chunk := os.read(descriptor, 1 << 20):
            chunks.append(chunk)
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def verify_snapshot_fd(stage_fd: int) -> None:
    top_entries = set(os.listdir(stage_fd))
    expected_top = {
        ".trainverify-stage-owner", "GeneratedYOCOMoE.lean",
        "GeneratedYOCOMoE.manifest.json", "yoco_goals",
    } | REGISTERED_TOP_LEVEL_MODULES
    if top_entries != expected_top:
        raise RuntimeError(f"unexpected snapshot top-level paths: {sorted(top_entries)}")
    if not _read_regular_at(stage_fd, ".trainverify-stage-owner"):
        raise RuntimeError("snapshot ownership marker is empty")
    goals_info = os.stat("yoco_goals", dir_fd=stage_fd, follow_symlinks=False)
    if (
        not stat.S_ISDIR(goals_info.st_mode)
        or goals_info.st_uid != os.getuid()
        or stat.S_IMODE(goals_info.st_mode) & 0o022
    ):
        raise RuntimeError("snapshot yoco_goals is not a trusted directory")
    manifest = loads_strict_json(
        _read_regular_at(stage_fd, "GeneratedYOCOMoE.manifest.json"),
        "GeneratedYOCOMoE.manifest.json",
    )
    ledger = manifest.get("snapshot_sha256") if isinstance(manifest, dict) else None
    if not isinstance(ledger, dict):
        raise RuntimeError("snapshot manifest is missing snapshot_sha256")
    goals_fd = os.open(
        "yoco_goals", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
        dir_fd=stage_fd,
    )
    try:
        goal_entries = set(os.listdir(goals_fd))
        if goal_entries != EXPECTED_GOAL_MODULES:
            raise RuntimeError(f"unexpected yoco_goals paths: {sorted(goal_entries)}")
        expected_ledger = {"GeneratedYOCOMoE.lean"} | {
            f"yoco_goals/{name}" for name in EXPECTED_GOAL_MODULES
        } | REGISTERED_TOP_LEVEL_MODULES
        if set(ledger) != expected_ledger:
            raise RuntimeError("snapshot manifest path ledger is not exact")
        main_content = _read_regular_at(stage_fd, "GeneratedYOCOMoE.lean")
        if ledger.get("GeneratedYOCOMoE.lean") != digest_bytes(main_content):
            raise RuntimeError("snapshot main Lean digest mismatch")
        for name in sorted(REGISTERED_TOP_LEVEL_MODULES):
            if ledger.get(name) != digest_bytes(_read_regular_at(stage_fd, name)):
                raise RuntimeError(f"snapshot top-level Lean digest mismatch: {name}")
        for name in sorted(EXPECTED_GOAL_MODULES):
            digest = ledger.get(f"yoco_goals/{name}")
            if not _is_lower_hex(digest, 64):
                raise RuntimeError(f"invalid snapshot digest: {name}")
            if digest != digest_bytes(_read_regular_at(goals_fd, name)):
                raise RuntimeError(f"snapshot Lean digest mismatch: {name}")
    finally:
        os.close(goals_fd)


def verify_snapshot_stage(stage: Path) -> None:
    stage_fd = os.open(stage, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        verify_snapshot_fd(stage_fd)
    finally:
        os.close(stage_fd)


def _lean_imports(source: Path) -> set[str]:
    imports = set()
    for line in source.read_text(encoding="utf-8").splitlines():
        match = re.match(r"^\s*import\s+(.+?)(?:\s+--.*)?$", line)
        if match:
            imports.update(match.group(1).split())
    return imports


def direct_lean_build(
    project: Path, lake: str, targets: tuple[str, ...], clean_env: dict[str, str],
) -> None:
    """Compile the project-local import closure with at most four Lean workers."""
    sources = {}
    for source in project.rglob("*.lean"):
        if ".lake" in source.parts:
            continue
        relative = source.relative_to(project).with_suffix("")
        module = ".".join(relative.parts)
        if module in sources:
            raise RuntimeError(f"duplicate Lean module source: {module}")
        sources[module] = source
    missing_targets = set(targets) - set(sources)
    if missing_targets:
        raise RuntimeError(f"missing Lean target sources: {sorted(missing_targets)}")
    project_roots = {module.split(".", 1)[0] for module in sources}
    raw_dependencies = {
        module: _lean_imports(source) for module, source in sources.items()
    }
    dependencies = {
        module: imports & set(sources)
        for module, imports in raw_dependencies.items()
    }
    closure = set()

    def visit(module: str) -> None:
        if module in closure:
            return
        missing_local = {
            name for name in raw_dependencies[module]
            if name.split(".", 1)[0] in project_roots and name not in sources
        }
        if missing_local:
            raise RuntimeError(
                f"missing project-local Lean imports for {module}: "
                f"{sorted(missing_local)}"
            )
        closure.add(module)
        for dependency in dependencies[module]:
            visit(dependency)

    for target in targets:
        visit(target)
    build_root = project / ".lake" / "build" / "lib" / "lean"
    build_root.mkdir(parents=True, mode=0o700, exist_ok=True)
    compiled = set()
    pending = set(closure)
    worker_env = dict(clean_env)
    worker_env["LEAN_NUM_THREADS"] = "1"

    def compile_module(module: str) -> None:
        output = build_root / Path(*module.split(".")).with_suffix(".olean")
        output.parent.mkdir(parents=True, mode=0o700, exist_ok=True)
        source = sources[module]
        subprocess.run(
            [
                lake, "env", "lean", "--tstack=65536", "-o",
                str(output.relative_to(project)), str(source.relative_to(project)),
            ],
            cwd=project, check=True, env=worker_env,
        )
        os.chmod(output, 0o400, follow_symlinks=False)
        _regular_owned_digest(output, f"Lean object {module}")

    while pending:
        ready = sorted(
            module for module in pending
            if dependencies[module] & closure <= compiled
        )
        if not ready:
            raise RuntimeError(f"cyclic Lean imports: {sorted(pending)}")
        print(
            f"direct Lean: compiling {len(ready)} modules "
            f"({len(compiled)}/{len(closure)} complete)",
            flush=True,
        )
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            futures = [executor.submit(compile_module, module) for module in ready]
            for future in futures:
                future.result()
        compiled.update(ready)
        pending.difference_update(ready)


def final_snapshot_lean_targets(stage: Path) -> tuple[str, ...]:
    """Return direct elaboration roots covering every sealed Lean source."""
    goal_modules = {
        f"denote.yoco_goals.{path.stem}"
        for path in (stage / "yoco_goals").glob("*.lean")
    }
    top_modules = {
        f"denote.{Path(name).stem}" for name in REGISTERED_TOP_LEVEL_MODULES
    }
    return tuple(sorted(
        set(LEAN_TARGETS) | {"denote.GeneratedYOCOMoE"} | goal_modules | top_modules
    ))


def _reraise_after_cleanup(
    primary: BaseException, stage: Path, marker: str, expected_dev: int, expected_ino: int,
) -> None:
    """Preserve the operation failure and report any independent cleanup failure."""
    try:
        if not cleanup_owned_stage(stage, marker, expected_dev, expected_ino):
            raise RuntimeError("stage identity changed before failure cleanup")
    except BaseException as cleanup_failure:
        raise CleanupFailureGroup(
            "operation and private-stage cleanup both failed",
            [primary, cleanup_failure],
        ) from None
    raise primary.with_traceback(primary.__traceback__)


def validate_lean_snapshot(
    stage: Path, lean_cache_project: Path, emitter_revision: str,
    proof_targets: list[str],
) -> None:
    packages = lean_cache_project.resolve() / ".lake" / "packages"
    packages_info = packages.stat()
    if (
        not stat.S_ISDIR(packages_info.st_mode)
        or packages_info.st_uid != os.getuid()
        or stat.S_IMODE(packages_info.st_mode) & 0o022
    ):
        raise RuntimeError("untrusted Lean package cache")
    validation_root, validation_marker, validation_dev, validation_ino = create_owned_stage(
        stage.parent, ".trainverify-lean-validation-",
    )
    try:
        repo = validation_root / "repo"
        subprocess.run(
            ["git", "clone", "--quiet", "--no-hardlinks", str(ROOT), str(repo)],
            check=True,
        )
        subprocess.run(
            ["git", "-C", str(repo), "checkout", "--quiet", emitter_revision],
            check=True,
        )
        if git_head(repo) != emitter_revision or not git_clean(repo):
            raise RuntimeError("Lean validation source materialization failed")
        project = repo / "trainverify"
        lake_dir = project / ".lake"
        lake_dir.mkdir(mode=0o700)
        os.symlink(packages, lake_dir / "packages", target_is_directory=True)
        denote = project / "denote"
        shutil.rmtree(denote / "yoco_goals")
        shutil.copytree(stage / "yoco_goals", denote / "yoco_goals", symlinks=False)
        shutil.copyfile(stage / "GeneratedYOCOMoE.lean", denote / "GeneratedYOCOMoE.lean")
        for name in REGISTERED_TOP_LEVEL_MODULES:
            shutil.copyfile(stage / name, denote / name)
        lake = shutil.which("lake")
        if lake is None:
            raise RuntimeError("lake executable is unavailable")
        clean_env = {
            "HOME": os.environ["HOME"],
            "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8",
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        }
        direct_lean_build(
            project, lake, final_snapshot_lean_targets(stage), clean_env,
        )
        audit_path = project / "AxiomAudit.lean"
        audit_path.write_text(
            "\n".join(
                ["import denote.yoco_goals.Instances",
                 *(f"#print axioms {target}" for target in proof_targets), ""]
            ),
            encoding="utf-8",
        )
        audit_path.chmod(0o600)
        audited = subprocess.run(
            [lake, "env", "lean", audit_path.name],
            cwd=project,
            check=True,
            env=clean_env,
            text=True,
            capture_output=True,
        )
        validate_print_axioms_output(audited.stdout + audited.stderr, proof_targets)
    except BaseException as primary:
        _reraise_after_cleanup(
            primary, validation_root, validation_marker, validation_dev, validation_ino,
        )
    if not cleanup_owned_stage(
        validation_root, validation_marker, validation_dev, validation_ino,
    ):
        raise RuntimeError("Lean validation stage identity changed before cleanup")


def git_head(path: Path) -> str:
    return subprocess.check_output(
        ["git", "-C", str(path), "rev-parse", "HEAD"], text=True
    ).strip()


def git_clean(path: Path) -> bool:
    return not subprocess.check_output(
        ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"],
        text=True,
    ).strip()


def git_blob(path: Path, revision: str, relative_path: str) -> bytes:
    return subprocess.check_output(
        ["git", "-C", str(path), "show", f"{revision}:{relative_path}"]
    )


def git_archive_digest(path: Path, revision: str) -> str:
    return digest_bytes(subprocess.check_output(
        ["git", "-C", str(path), "archive", "--format=tar", revision]
    ))


def validate_source_checkouts(llm_train: Path, nnscaler: Path) -> None:
    if git_head(llm_train) != LLM_REVISION or git_head(nnscaler) != NNSCALER_REVISION:
        raise RuntimeError("source revision mismatch")
    if not git_clean(llm_train) or not git_clean(nnscaler):
        raise RuntimeError("source checkout is dirty")


def materialize_source(source: Path, revision: str, target: Path) -> None:
    subprocess.run(
        ["git", "clone", "--quiet", "--no-hardlinks", str(source), str(target)],
        check=True,
    )
    subprocess.run(
        ["git", "-C", str(target), "checkout", "--quiet", revision],
        check=True,
    )
    if git_head(target) != revision or not git_clean(target):
        raise RuntimeError(f"private source materialization failed: {target}")


def materialize_static_goal_modules(repo: Path, revision: str, target: Path) -> None:
    for relative_path in STATIC_GOAL_MODULES:
        content = git_blob(repo, revision, relative_path)
        destination = target / Path(relative_path).name
        descriptor = os.open(
            destination,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
            0o400,
        )
        try:
            with os.fdopen(descriptor, "wb", closefd=False) as handle:
                handle.write(content)
                handle.flush()
                os.fsync(handle.fileno())
        finally:
            os.close(descriptor)


def _read_owned_regular(path: Path, label: str) -> bytes:
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        info = os.fstat(descriptor)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.getuid()
            or stat.S_IMODE(info.st_mode) & 0o022
        ):
            raise RuntimeError(f"untrusted {label} inode")
        chunks = []
        while chunk := os.read(descriptor, 1 << 20):
            chunks.append(chunk)
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def _regular_owned_digest(path: Path, label: str) -> str:
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        info = os.fstat(descriptor)
        if (
            not stat.S_ISREG(info.st_mode)
            or info.st_uid != os.getuid()
            or stat.S_IMODE(info.st_mode) & 0o022
        ):
            raise RuntimeError(f"untrusted {label} inode")
        digest = hashlib.sha256()
        while chunk := os.read(descriptor, 1 << 20):
            digest.update(chunk)
        return digest.hexdigest()
    finally:
        os.close(descriptor)


def validate_proof_registry(registry: dict, stage: Path) -> dict[str, dict[str, str]]:
    """Validate a registry against the exact freshly generated statements.

    Blob bytes are checked during materialization; this first phase deliberately
    validates all generated digests before any proof skeleton is replaced.
    """
    _require_exact_keys(registry, PROOF_REGISTRY_KEYS, "proof registry")
    if registry["schema_version"] != 1:
        raise RuntimeError("proof registry schema version mismatch")
    generated_digest = registry["generated_lean_sha256"]
    if not _is_lower_hex(generated_digest, 64):
        raise RuntimeError("proof registry generated digest is invalid")
    if not hmac.compare_digest(
        _regular_owned_digest(stage / "GeneratedYOCOMoE.lean", "generated Lean"),
        generated_digest,
    ):
        raise RuntimeError("proof registry generated Lean digest mismatch")

    goal_digests = registry["goal_sha256"]
    if not isinstance(goal_digests, dict) or set(goal_digests) != PROOF_REGISTRY_GOALS:
        raise RuntimeError("proof registry goal digest schema mismatch")
    for name, expected in goal_digests.items():
        if not _is_lower_hex(expected, 64):
            raise RuntimeError("proof registry goal digest is invalid")
        actual = _regular_owned_digest(stage / "yoco_goals" / name, name)
        if not hmac.compare_digest(actual, expected):
            raise RuntimeError(f"proof registry goal digest mismatch: {name}")

    modules = registry["modules"]
    if not isinstance(modules, dict) or not modules:
        raise RuntimeError("proof registry modules must be a nonempty object")
    missing_goal_overlays = PROOF_REGISTRY_GOALS - set(modules)
    if missing_goal_overlays:
        raise RuntimeError(
            "proof registry is missing generated goal overlays: "
            f"{sorted(missing_goal_overlays)}"
        )
    missing_cut_overlays = REGISTERED_LEGACY_CUT_MODULES - set(modules)
    if missing_cut_overlays:
        raise RuntimeError(
            "proof registry is missing legacy cut overlays: "
            f"{sorted(missing_cut_overlays)}"
        )
    missing_sealed_dependencies = REGISTERED_SEALED_DEPENDENCY_MODULES - set(modules)
    if missing_sealed_dependencies:
        raise RuntimeError(
            "proof registry is missing sealed dependency modules: "
            f"{sorted(missing_sealed_dependencies)}"
        )
    missing_top_helpers = REGISTERED_TOP_LEVEL_MODULES - set(modules)
    if missing_top_helpers:
        raise RuntimeError(
            f"proof registry is missing top-level helpers: {sorted(missing_top_helpers)}"
        )
    for destination, entry in modules.items():
        destination_path = PurePosixPath(destination)
        is_goal_module = destination in EXPECTED_GOAL_MODULES
        is_top_module = destination in REGISTERED_TOP_LEVEL_MODULES
        if (
            not isinstance(destination, str)
            or destination_path.name != destination
            or not (is_goal_module or is_top_module)
        ):
            raise RuntimeError(f"invalid proof registry destination: {destination}")
        _require_exact_keys(entry, PROOF_MODULE_KEYS, "proof registry module")
        source = entry["source"]
        if not isinstance(source, str):
            raise RuntimeError("proof registry source is invalid")
        source_path = PurePosixPath(source)
        expected_source_parent = (
            ("trainverify", "denote", "yoco_goals")
            if is_goal_module else ("trainverify", "denote")
        )
        if (
            source_path.is_absolute()
            or ".." in source_path.parts
            or "." in source_path.parts
            or source_path.parts[:-1] != expected_source_parent
            or source_path.suffix != ".lean"
        ):
            raise RuntimeError(f"invalid proof registry source: {source}")
        if not _is_lower_hex(entry["sha256"], 64):
            raise RuntimeError("proof registry module digest is invalid")
        if is_top_module and os.path.lexists(stage / destination):
            raise RuntimeError(f"proof registry top-level destination already exists: {destination}")
    targets = registry["proof_targets"]
    if (
        not isinstance(targets, list)
        or len(targets) != 5
        or len(set(targets)) != len(targets)
        or any(not isinstance(target, str) or not LEAN_NAME.fullmatch(target)
               for target in targets)
    ):
        raise RuntimeError("proof registry targets are invalid")
    return modules


def _replace_private_regular(path: Path, content: bytes) -> None:
    """Replace one regular file inside an owner-private stage."""
    _regular_owned_digest(path, path.name)
    temporary = path.with_name(f".{path.name}.proof-registry.tmp")
    descriptor = os.open(
        temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o400,
    )
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
    finally:
        os.close(descriptor)
    os.replace(temporary, path)


def _create_private_regular(path: Path, content: bytes) -> None:
    descriptor = os.open(
        path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o400,
    )
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
    finally:
        os.close(descriptor)


def _refresh_snapshot_ledger(stage: Path) -> None:
    manifest_path = stage / "GeneratedYOCOMoE.manifest.json"
    manifest = loads_strict_json(
        _read_owned_regular(manifest_path, "snapshot manifest"),
        "GeneratedYOCOMoE.manifest.json",
    )
    ledger = manifest.get("snapshot_sha256") if isinstance(manifest, dict) else None
    if not isinstance(ledger, dict):
        raise RuntimeError("snapshot manifest is missing snapshot_sha256")
    goal_names = set(os.listdir(stage / "yoco_goals"))
    final_paths = (
        {"GeneratedYOCOMoE.lean"}
        | {f"yoco_goals/{name}" for name in goal_names}
        | REGISTERED_TOP_LEVEL_MODULES
    )
    refreshed = {}
    for relative_path in final_paths:
        candidate = PurePosixPath(relative_path)
        if candidate.is_absolute() or ".." in candidate.parts or "." in candidate.parts:
            raise RuntimeError("snapshot ledger path is invalid")
        refreshed[relative_path] = _regular_owned_digest(
            stage / Path(*candidate.parts), relative_path,
        )
    manifest["snapshot_sha256"] = refreshed
    content = (
        json.dumps(manifest, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")
    _replace_private_regular(manifest_path, content)


def _remove_deprecated_generated_auxiliaries(stage: Path) -> None:
    """Remove generated auxiliaries invalidated by the full-proof overlays.

    The five public production theorems are ancestry-closed full statements
    aggregated by the registry-authenticated MainTheorem.  The raw CutToFull
    naming aliases are not proofs after overlaying those statements.  The raw
    Patterns/ProofObligations skeletons likewise reference cut-era declarations
    that the public overlays intentionally do not export.  None is registry
    authenticated or part of the public import graph.
    """
    goals = stage / "yoco_goals"
    for name in sorted(DEPRECATED_GENERATED_AUXILIARY_MODULES):
        path = goals / name
        if os.path.lexists(path):
            _regular_owned_digest(path, f"deprecated generated certificate {name}")
            path.unlink()


def materialize_registered_proofs(
    repo: Path, revision: str, stage: Path, registry: dict,
) -> None:
    modules = validate_proof_registry(registry, stage)
    _remove_deprecated_generated_auxiliaries(stage)
    contents = {}
    for destination, entry in modules.items():
        content = git_blob(repo, revision, entry["source"])
        if not hmac.compare_digest(digest_bytes(content), entry["sha256"]):
            raise RuntimeError(f"proof registry blob digest mismatch: {destination}")
        match = FORBIDDEN_PROOF_TOKEN.search(content)
        if match:
            raise RuntimeError(
                f"forbidden proof token in {destination}: {match.group().decode('ascii')}"
            )
        contents[destination] = content
    for destination, content in contents.items():
        if destination in REGISTERED_TOP_LEVEL_MODULES:
            _create_private_regular(stage / destination, content)
        elif destination in REGISTERED_LEGACY_CUT_MODULES:
            _create_private_regular(stage / "yoco_goals" / destination, content)
        else:
            _replace_private_regular(stage / "yoco_goals" / destination, content)
    _refresh_snapshot_ledger(stage)


def validate_print_axioms_output(output: str, targets: list[str]) -> None:
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for target in targets:
        escaped = re.escape(target)
        no_axioms = re.search(
            rf"'{escaped}' does not depend on any axioms", output,
        )
        matched = re.search(
            rf"'{escaped}' depends on axioms: \[(.*?)\]", output, re.DOTALL,
        )
        if no_axioms:
            continue
        if not matched:
            raise RuntimeError(f"missing #print axioms result: {target}")
        names = [name.strip() for name in matched.group(1).split(",") if name.strip()]
        rejected = [
            name for name in names
            if name not in allowed and not re.fullmatch(
                r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)+"
                r"\._native\.native_decide\.ax_[0-9_]+✝*",
                name,
            )
        ]
        if rejected or any("sorryAx" in name for name in names):
            raise RuntimeError(f"untrusted axioms for {target}: {rejected or names}")


def load_proof_registry(repo: Path, revision: str) -> dict:
    content = git_blob(repo, revision, PROOF_REGISTRY_PATH)
    registry = loads_strict_json(content, PROOF_REGISTRY_PATH)
    canonical = (
        json.dumps(registry, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")
    if content != canonical:
        raise RuntimeError("proof registry is not canonical JSON")
    return registry


def secure_copy_authority(source: Path, target: Path) -> None:
    """Copy from one locked directory inode; never reopen source paths by name."""
    target.mkdir(mode=0o700)
    directory_fd = os.open(source, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for name in AUTHORITY_NAMES:
            source_fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=directory_fd)
            try:
                info = os.fstat(source_fd)
                if not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid():
                    raise PermissionError(f"untrusted authority inode: {name}")
                if stat.S_IMODE(info.st_mode) & 0o022:
                    raise PermissionError(f"authority inode is group/world writable: {name}")
                destination_fd = os.open(
                    target / name, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o400)
                try:
                    with os.fdopen(os.dup(source_fd), "rb") as src, os.fdopen(
                        os.dup(destination_fd), "wb") as dst:
                        shutil.copyfileobj(src, dst, length=1 << 20)
                        dst.flush()
                        os.fsync(dst.fileno())
                finally:
                    os.close(destination_fd)
            finally:
                os.close(source_fd)
    finally:
        os.close(directory_fd)


def validate_authority(
    authority: Path,
    llm_train: Path,
    nnscaler: Path,
    expected_hardware_sha256: str,
    emitter_revision: str,
):
    files = {name: authority / name for name in AUTHORITY_NAMES}
    meta = load_strict_json(files["gen_args.json"])
    validate_meta_schema(meta)
    validate_expected_hardware(
        {key: meta[key] for key in HARDWARE_KEYS}, expected_hardware_sha256,
    )
    if meta.get("authority") is not True:
        raise RuntimeError("gen_args.json is not marked as production authority")
    if meta.get("llm_train_commit") != LLM_REVISION:
        raise RuntimeError("gen_args llm-train revision mismatch")
    if meta.get("nnscaler_commit") != NNSCALER_REVISION:
        raise RuntimeError("gen_args nnScaler revision mismatch")
    if meta.get("trainverify_regen_commit") != emitter_revision:
        raise RuntimeError("authority/emitter TrainVerify revision mismatch")
    if meta.get("llm_hardware_patch") != "cc12_generic_triton_fallback_v1":
        raise RuntimeError("gen_args llm hardware patch mismatch")

    from scripts.yoco_regen.patch_mgener_dump import patch_source
    from scripts.yoco_regen.patch_llm_cc12_gemm import (
        patch_source as patch_llm_gemm_source,
    )
    from scripts.yoco_regen.comm_profile import profile_sha256
    from scripts.yoco_regen.comp_profile import validate_artifact as validate_comp_profile

    comm_profile_hash = profile_sha256(files["comm_profile_intra_2.json"])
    if comm_profile_hash != meta["comm_profile_sha256"]:
        raise RuntimeError("communication profile hash mismatch")
    comp_profile_hash = validate_comp_profile(files["comp_profile.json"])
    if comp_profile_hash != meta["comp_profile_sha256"]:
        raise RuntimeError("computation profile hash mismatch")
    dp_solver_file = files["nnscaler_dp_solver.so"]
    if dp_solver_file.read_bytes()[:4] != b"\x7fELF":
        raise RuntimeError("dp solver authority artifact is not ELF")
    dp_solver_hash = sha256(dp_solver_file)
    if dp_solver_hash != meta["dp_solver_extension_sha256"]:
        raise RuntimeError("dp solver extension hash mismatch")

    clean_parallel = git_blob(
        nnscaler, NNSCALER_REVISION, "nnscaler/parallel.py").decode("utf-8")
    patched_parallel_hash = digest_bytes(patch_source(clean_parallel).encode("utf-8"))
    clean_llm_gemm = git_blob(
        llm_train, LLM_REVISION, "llm/kernel/gemm.py").decode("utf-8")
    patched_llm_gemm_hash = digest_bytes(
        patch_llm_gemm_source(clean_llm_gemm).encode("utf-8"))
    expected_source_hashes = {
        "nnscaler/fixed_commit_archive.tar": git_archive_digest(
            nnscaler, NNSCALER_REVISION),
        "nnscaler/setup.py": digest_bytes(
            git_blob(nnscaler, NNSCALER_REVISION, "setup.py")),
        "nnscaler/autodist/dp_solver.cpp": digest_bytes(
            git_blob(nnscaler, NNSCALER_REVISION, "nnscaler/autodist/dp_solver.cpp")),
        "nnscaler/autodist/dp_solver.h": digest_bytes(
            git_blob(nnscaler, NNSCALER_REVISION, "nnscaler/autodist/dp_solver.h")),
        "llm/arch/model.py": digest_bytes(
            git_blob(llm_train, LLM_REVISION, "llm/arch/model.py")),
        "llm/pcs/all2all_moe.yaml": digest_bytes(
            git_blob(llm_train, LLM_REVISION, "llm/pcs/all2all_moe.yaml")),
        "llm/kernel/gemm.py.patched_cc12_fallback": patched_llm_gemm_hash,
        "nnscaler/parallel.py.patched": patched_parallel_hash,
        "nnscaler/customized_ops/ring_attention/maybe_shuffle.py": digest_bytes(
            git_blob(
                nnscaler, NNSCALER_REVISION,
                "nnscaler/customized_ops/ring_attention/maybe_shuffle.py")),
    }
    if meta.get("source_sha256") != expected_source_hashes:
        raise RuntimeError("authority source hash ledger mismatch")

    for kind, plan in (("sm", 1), ("pm", 2)):
        record = meta.get(kind, {})
        actual = sha256(files[f"{kind}_mgener.pkl"])
        if record.get("pkl_sha256") != actual:
            raise RuntimeError(f"{kind} pickle hash mismatch")
        if record.get("policy") != "pas_autodist":
            raise RuntimeError(f"{kind} is not a pas_autodist artifact")
        if record.get("plan_ngpus") != plan or record.get("runtime_ngpus") != plan:
            raise RuntimeError(f"{kind} topology mismatch")
        if record.get("patched_parallel_py_sha256") != patched_parallel_hash:
            raise RuntimeError(f"{kind} patched-source hash mismatch")
        if record.get("patched_llm_gemm_py_sha256") != patched_llm_gemm_hash:
            raise RuntimeError(f"{kind} patched llm GEMM source hash mismatch")
        if record.get("comm_profile_sha256") != comm_profile_hash:
            raise RuntimeError(f"{kind} communication profile hash mismatch")
        if record.get("comp_profile_sha256") != comp_profile_hash:
            raise RuntimeError(f"{kind} computation profile hash mismatch")
        if record.get("dp_solver_extension_sha256") != dp_solver_hash:
            raise RuntimeError(f"{kind} dp solver extension hash mismatch")
        receipt_path = files[f"{kind}_mgener.pkl.receipt.json"]
        if record.get("receipt_sha256") != sha256(receipt_path):
            raise RuntimeError(f"{kind} receipt hash mismatch")
        receipt = load_strict_json(receipt_path)
        validate_receipt_schema(receipt, plan)
        if (
            receipt.get("pkl_sha256") != actual
            or receipt.get("policy") not in ALLOWED_POLICY_IDENTITIES
            or receipt.get("patched_parallel_py_sha256") != patched_parallel_hash
            or receipt.get("patched_llm_gemm_py_sha256") != patched_llm_gemm_hash
            or receipt.get("comm_profile_sha256") != comm_profile_hash
            or receipt.get("comp_profile_sha256") != comp_profile_hash
            or receipt.get("dp_solver_extension_sha256") != dp_solver_hash
            or receipt.get("canonicalized_comment_count") != record.get("canonicalized_comment_count")
            or receipt.get("canonicalized_code_count") != record.get("canonicalized_code_count")
        ):
            raise RuntimeError(f"{kind} receipt semantics mismatch")
        provenance = load_strict_json(files[f"{kind}_provenance.json"])
        if provenance != record:
            raise RuntimeError(f"{kind} provenance disagrees with gen_args")
        world = load_strict_json(files[f"{kind}_mgener.json"])
        if set(world) != WORLD_KEYS:
            raise RuntimeError(f"{kind} world metadata has unexpected fields")
        expected_world = {
            "model_name": "YOCO-MoE-A0.4B", "num_dp": 1, "num_tp": plan,
            "num_pp": 1, "num_mb": 1, "gbs": 1, "num_layers": 12,
            "num_heads": 16, "hidden_size": 1024, "seqlen": 4096,
            "n_activated_experts": 8, "n_routed_experts": 64,
        }
        if world != expected_world:
            raise RuntimeError(f"{kind} world metadata mismatch")
    return meta, files


class SequentialPool:
    def __init__(self, processes=None, initializer=None, initargs=()):
        if initializer:
            initializer(*initargs)

    def __enter__(self):
        return self

    def __exit__(self, *_args):
        return False

    def map(self, function, values):
        return [function(value) for value in values]


def configure_runtime(llm_train: Path, nnscaler_repo: Path):
    os.environ["YOCO_LLM_TRAIN_REPO"] = str(llm_train)
    sys.path[:0] = [
        str(STUBS), str(nnscaler_repo), str(llm_train / "llm"),
        str(ROOT), str(ROOT / "Verdict"),
    ]
    import triton_shim  # noqa: F401
    import arch.model as llm_model
    import nnscaler
    import torch

    imported_nnscaler = Path(nnscaler.__file__).resolve()
    imported_llm = Path(llm_model.__file__).resolve()
    if not imported_nnscaler.is_relative_to(nnscaler_repo):
        raise RuntimeError(f"runtime nnScaler is outside pinned checkout: {imported_nnscaler}")
    if not imported_llm.is_relative_to(llm_train / "llm"):
        raise RuntimeError(f"runtime llm-train model is outside pinned checkout: {imported_llm}")
    ensure_torch_recompile_limit(torch)
    multiprocessing.pool.Pool = SequentialPool
    import dill
    import nnscaler_backend.build_graph as build_graph
    import nnscaler_backend.load_graph as load_graph

    build_graph.Pool = SequentialPool
    load_graph.pickle = dill


def graph_to_lean_argv(llm_train, nnscaler, files, stage):
    command = [
        "graph_to_lean",
        "--sm-pkl", str(files["sm_mgener.pkl"]),
        "--pm-pkl", str(files["pm_mgener.pkl"]),
        "--out", str(stage / "GeneratedYOCOMoE.lean"),
        "--module", "denote.GeneratedYOCOMoE",
        "--max-goals", "5", "--split-goals", "--assume-cp-dim0-shuffle",
        "--goals-out-dir", str(stage / "yoco_goals"),
        "--manifest-out", str(stage / "GeneratedYOCOMoE.manifest.json"),
        "--verifier-cache-dir", str(stage / "verifier-cache"),
        "--llm-train-repo", str(llm_train),
        "--llm-train-revision", LLM_REVISION,
        "--nnscaler-repo", str(nnscaler),
        "--nnscaler-revision", NNSCALER_REVISION,
        "--sm-pkl-sha256", sha256(files["sm_mgener.pkl"]),
        "--pm-pkl-sha256", sha256(files["pm_mgener.pkl"]),
    ]
    for name in METADATA_JSON_NAMES:
        command += ["--metadata-json", str(files[name])]
        command += ["--metadata-sha256", f"{name}={sha256(files[name])}"]
    for name in ("nnscaler_dp_solver.so", "comp_profile.json"):
        command += [
            "--artifact-file", f"{name}={files[name]}",
            "--artifact-sha256", f"{name}={sha256(files[name])}",
        ]
    return command


def content_addressed_snapshot_path(requested: Path, manifest_sha256: str) -> Path:
    return requested.parent / f"yoco-a04b-manifest-sha256-{manifest_sha256}"


def require_manifest_digest_fd(directory_fd: int, expected: str) -> None:
    manifest_fd = os.open(
        "GeneratedYOCOMoE.manifest.json",
        os.O_RDONLY | os.O_NOFOLLOW,
        dir_fd=directory_fd,
    )
    try:
        digest = hashlib.sha256()
        while chunk := os.read(manifest_fd, 1024 * 1024):
            digest.update(chunk)
    finally:
        os.close(manifest_fd)
    if not hmac.compare_digest(digest.hexdigest(), expected):
        raise RuntimeError("content-address manifest digest changed before publication")


def require_sealed_regular_modes_fd(directory_fd: int, prefix: str = "") -> None:
    for name in os.listdir(directory_fd):
        relative = f"{prefix}/{name}" if prefix else name
        info = os.stat(name, dir_fd=directory_fd, follow_symlinks=False)
        if info.st_uid != os.getuid():
            raise RuntimeError(f"sealed path is not owner-controlled: {relative}")
        if stat.S_ISREG(info.st_mode):
            if stat.S_IMODE(info.st_mode) != 0o400:
                raise RuntimeError(f"sealed regular file mode is not 0400: {relative}")
        elif stat.S_ISDIR(info.st_mode):
            child_fd = os.open(
                name,
                os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                dir_fd=directory_fd,
            )
            try:
                require_sealed_regular_modes_fd(child_fd, relative)
            finally:
                os.close(child_fd)
        else:
            raise RuntimeError(f"sealed snapshot contains non-regular entry: {relative}")


def seal_snapshot_files(stage: Path) -> None:
    """Make every sealed regular file owner-read-only before publication."""
    for path in [stage, *stage.rglob("*")]:
        info = path.lstat()
        if info.st_uid != os.getuid():
            raise RuntimeError(f"snapshot path is not owner-controlled: {path}")
        if stat.S_ISLNK(info.st_mode):
            raise RuntimeError(f"snapshot contains symlink before sealing: {path}")
        if stat.S_ISREG(info.st_mode):
            os.chmod(path, 0o400, follow_symlinks=False)


def main():
    os.umask(0o077)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--authority-dir", type=Path, required=True)
    parser.add_argument("--llm-train", type=Path, required=True)
    parser.add_argument("--nnscaler", type=Path, required=True)
    parser.add_argument("--snapshot-dir", type=Path, required=True)
    parser.add_argument(
        "--content-addressed", action="store_true",
        help=(
            "derive the no-replace target name from the fresh final manifest SHA-256; "
            "--snapshot-dir supplies only the parent and staging-name placeholder"
        ),
    )
    parser.add_argument(
        "--lean-project", type=Path, required=True,
        help="trusted Lean project providing the prebuilt .lake/packages cache",
    )
    parser.add_argument(
        "--expected-hardware-sha256", required=True,
        help="SHA-256 captured out-of-band from the trusted GPU generation session",
    )
    parser.add_argument(
        "--trust-new-authority", action="store_true",
        help="acknowledge that pinned local pickle generation is the trust root",
    )
    args = parser.parse_args()
    if not args.trust_new_authority:
        parser.error("--trust-new-authority is required before pickle deserialization")
    authority_source = args.authority_dir.resolve()
    llm_source = args.llm_train.resolve()
    nnscaler_source = args.nnscaler.resolve()
    snapshot = args.snapshot_dir.absolute()
    declared_materialization = os.environ.get("TRAINVERIFY_PRIVATE_MATERIALIZATION")
    if (
        not declared_materialization
        or Path(declared_materialization).resolve() != ROOT.resolve()
    ):
        raise RuntimeError("emitter is not running from the declared private materialization")
    root_info = ROOT.stat()
    if root_info.st_uid != os.getuid() or stat.S_IMODE(root_info.st_mode) & 0o077:
        raise RuntimeError("emitter TrainVerify materialization is not owner-private")
    emitter_revision = git_head(ROOT)
    if not git_clean(ROOT):
        raise RuntimeError("emitter TrainVerify checkout is dirty")
    validate_source_checkouts(llm_source, nnscaler_source)
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    stage, stage_marker, stage_dev, stage_ino = create_owned_stage(
        snapshot.parent, f".{snapshot.name}.staged-")
    try:
        (stage / "yoco_goals").mkdir()
        materialize_static_goal_modules(ROOT, emitter_revision, stage / "yoco_goals")
        llm_train = stage / ".llm-train-source"
        nnscaler = stage / ".nnscaler-source"
        materialize_source(llm_source, LLM_REVISION, llm_train)
        materialize_source(nnscaler_source, NNSCALER_REVISION, nnscaler)
        authority = stage / "authority"
        secure_copy_authority(authority_source, authority)
        _, files = validate_authority(
            authority, llm_train, nnscaler, args.expected_hardware_sha256,
            emitter_revision,
        )
        configure_runtime(llm_train, nnscaler)
        sys.argv = graph_to_lean_argv(llm_train, nnscaler, files, stage)
        from verdict.log import setup_logger
        import graph_to_lean

        setup_logger("ERROR")
        graph_to_lean.main()
        proof_registry = load_proof_registry(ROOT, emitter_revision)
        materialize_registered_proofs(
            ROOT, emitter_revision, stage,
            proof_registry,
        )
        shutil.rmtree(stage / "verifier-cache")
        shutil.rmtree(llm_train)
        shutil.rmtree(nnscaler)
        shutil.rmtree(authority)
        if git_head(ROOT) != emitter_revision or not git_clean(ROOT):
            raise RuntimeError("emitter TrainVerify revision changed during emission")
        seal_snapshot_files(stage)
        verify_snapshot_stage(stage)
        validate_lean_snapshot(
            stage, args.lean_project, emitter_revision,
            proof_registry["proof_targets"],
        )
        if git_head(ROOT) != emitter_revision or not git_clean(ROOT):
            raise RuntimeError("emitter TrainVerify revision changed during Lean validation")
        publication_validator = verify_snapshot_fd
        if args.content_addressed:
            expected_manifest_sha256 = sha256(
                stage / "GeneratedYOCOMoE.manifest.json"
            )
            snapshot = content_addressed_snapshot_path(
                snapshot, expected_manifest_sha256
            )

            def validate_content_addressed_snapshot(directory_fd: int) -> None:
                verify_snapshot_fd(directory_fd)
                require_manifest_digest_fd(directory_fd, expected_manifest_sha256)
                require_sealed_regular_modes_fd(directory_fd)

            publication_validator = validate_content_addressed_snapshot

        from scripts.yoco_regen.atomic_publish import publish_validated_directory

        publish_validated_directory(stage, snapshot, publication_validator)
    except BaseException as primary:
        _reraise_after_cleanup(primary, stage, stage_marker, stage_dev, stage_ino)
    print(f"wrote atomic refresh snapshot: {snapshot}")


if __name__ == "__main__":
    main()
