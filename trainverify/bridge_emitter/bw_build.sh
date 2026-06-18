#!/usr/bin/env bash
# Sequential BW bridge builder: emit -> build olean -> verify, in topo order.
# Real errors (NO --quiet). Olean-gated skip. Status TSV.
# Usage: bw_build.sh <worklist.txt> <out.tsv>
set -u
WL="${1:-bridge_emitter/BW_TOPO.txt}"
OUT="${2:-bridge_emitter/BW.tsv}"
cd "$(dirname "$0")/.." || exit 1   # -> trainverify/
DEN="denote/gpt_ly4_regen"
OLDIR=".lake/build/lib/lean/$DEN"
LOG="${OUT%.tsv}.log"
: > "$OUT"; : > "$LOG"
echo "[bw_build] start $(date -u +%H:%M:%S) worklist=$WL" | tee -a "$LOG"

while read -r g; do
  g="$(echo "$g" | tr -d '[:space:]')"
  [ -z "$g" ] && continue
  ol="$OLDIR/Goal${g}Bridge.olean"
  br="$DEN/Goal${g}Bridge.lean"
  if [ -f "$ol" ]; then
    echo -e "${g}\tSKIP_HAVE_OLEAN\t0\t" >> "$OUT"
    echo "[bw_build] goal_${g} SKIP (olean exists)" | tee -a "$LOG"
    continue
  fi
  echo "[bw_build] === goal_${g} EMIT $(date -u +%H:%M:%S) ===" | tee -a "$LOG"
  emitlog="$(python3 bridge_emitter/emit2.py "$g" 2>&1)"
  echo "$emitlog" >> "$LOG"
  if [ ! -f "$br" ]; then
    last="$(echo "$emitlog" | grep -E 'Error|error|Traceback|Unsupported|unknown op' | tail -1)"
    echo -e "${g}\tFAIL_EMIT\t0\t${last}" >> "$OUT"
    echo "[bw_build] goal_${g} FAIL_EMIT: ${last}" | tee -a "$LOG"
    continue
  fi
  sc="$(grep -c 'sorry' "$br")"
  if [ "$sc" != "0" ]; then
    echo -e "${g}\tFAIL_SORRY\t${sc}\t" >> "$OUT"
    echo "[bw_build] goal_${g} FAIL_SORRY count=${sc}" | tee -a "$LOG"
    continue
  fi
  echo "[bw_build] goal_${g} BUILD olean $(date -u +%H:%M:%S)" | tee -a "$LOG"
  blog="$(timeout 900 lake env lean "$br" 2>&1)"
  bex=$?
  echo "$blog" | grep -E 'error|sorry|warning' | head -20 >> "$LOG"
  if [ $bex -ne 0 ]; then
    errhead="$(echo "$blog" | grep -E 'error' | grep -vE 'unknown identifier .goal_[0-9]+_intermediate' | head -1)"
    ordrr="$(echo "$blog" | grep -oE "unknown identifier .goal_[0-9]+_intermediate" | head -1)"
    if [ -n "$errhead" ]; then
      echo -e "${g}\tFAIL_BUILD\t0\t${errhead}" >> "$OUT"
      echo "[bw_build] goal_${g} FAIL_BUILD (real): ${errhead}" | tee -a "$LOG"
    else
      echo -e "${g}\tFAIL_ORDER\t0\t${ordrr}" >> "$OUT"
      echo "[bw_build] goal_${g} FAIL_ORDER: ${ordrr} (prereq bridge not built)" | tee -a "$LOG"
    fi
    continue
  fi
  # lake env lean does NOT write olean by default; need lake build of the module.
  mod="denote.gpt_ly4_regen.Goal${g}Bridge"
  lake build "$mod" >> "$LOG" 2>&1
  if [ -f "$ol" ]; then
    echo -e "${g}\tPASS\t0\t" >> "$OUT"
    echo "[bw_build] goal_${g} PASS (olean built) $(date -u +%H:%M:%S)" | tee -a "$LOG"
  else
    echo -e "${g}\tFAIL_NOOLEAN\t0\tlake build produced no olean" >> "$OUT"
    echo "[bw_build] goal_${g} FAIL_NOOLEAN" | tee -a "$LOG"
  fi
done < "$WL"

echo "[bw_build] done $(date -u +%H:%M:%S)" | tee -a "$LOG"
echo "=== SUMMARY ===" | tee -a "$LOG"
awk -F'\t' '{c[$2]++} END{for(k in c) print k": "c[k]}' "$OUT" | tee -a "$LOG"
