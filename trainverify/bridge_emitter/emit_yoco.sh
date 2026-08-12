#!/usr/bin/env bash
# Regenerate yoco Goal_N bridge via bridge_emitter (2026-07-14).
#
# Usage:  ./emit_yoco.sh <N>
#
# Requires:
#   - denote.yoco_goals.BridgeKit compiled (initGoals_preserved, storeShapes_weaken, ...)
#   - denote.yoco_goals.Goal_N compiled
#   - denote.yoco_goals.Pattern_N compiled (provides prove_goal_N)
#
# Output goes to denote/yoco_goals/Goal${N}Bridge_Auto.lean by default;
# pass --out PATH to override.
#
# Currently proven to work end-to-end on Goal_5 (base, single-tp,
# 1-node SM + 3-node PM including AllReduce). Larger goals (1/2/3/4)
# still need additional POINTWISE dispatch and composition support for
# yoco-specific ops (FW_inner_chunk_ce, FW_multiref,
# FW_topk_routing, FW_all2all_moe_gmm, FW_maybe_unshuffle, etc).

set -euo pipefail

N="${1:-}"
if [[ -z "$N" ]]; then
  echo "usage: $0 <goal_id> [extra emit2.py args...]" >&2
  exit 2
fi
shift || true

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TRAINVERIFY_DIR="$(dirname "$SCRIPT_DIR")"
OUT_DEFAULT="$TRAINVERIFY_DIR/denote/yoco_goals/Goal${N}Bridge_Auto.lean"

cd "$SCRIPT_DIR"

BRIDGE_DENOTE_DIR=denote/yoco_goals \
BRIDGE_GEN_FILE=GeneratedYOCOMoE.lean \
BRIDGE_GEN_DIR=trainverify/denote \
BRIDGE_NAMESPACE=GeneratedBridges \
BRIDGE_EXTRA_OPENS="TrainVerify.Denote.GeneratedGoals TrainVerify.Denote.GeneratedPatterns" \
BRIDGE_PROVE_GOAL_FMT="prove_goal_{n}" \
BRIDGE_EXTRA_IMPORTS="denote.yoco_goals.Pattern_${N}" \
python3 emit2.py "$N" --out "$OUT_DEFAULT" "$@"
