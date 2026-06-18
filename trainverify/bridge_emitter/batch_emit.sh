#!/usr/bin/env bash
# batch_emit.sh — emit bridges for a list of goals, compile each, record pass/fail.
# Usage: batch_emit.sh <goal-list-file> <result-log>
# Does NOT wire into MainTheorem and does NOT touch git. Pure generation + compile check.
set -u
cd "$(dirname "$0")/.." || exit 1   # -> trainverify/
LIST="${1:?need goal list file}"
RESLOG="${2:-bridge_emitter/BATCH_RESULTS.tsv}"
D=denote/gpt_ly4_regen

echo -e "goal\tstatus\tchars\tseconds\tnote" > "$RESLOG"
pass=0; fail=0
while read -r n; do
  [ -z "$n" ] && continue
  out="$D/Goal${n}Bridge.lean"
  t0=$(date +%s)
  # emit2 writes the bridge file then compiles with `lake env lean`; exits 0 on success.
  log=$(python3 bridge_emitter/emit2.py "$n" --quiet 2>&1)
  rc=$?
  t1=$(date +%s); dt=$((t1-t0))
  if [ $rc -ne 0 ]; then
    note=$(echo "$log" | tail -1 | tr '\t' ' ' | cut -c1-200)
    echo -e "${n}\tFAIL_EMIT\t-\t${dt}\t${note}" >> "$RESLOG"
    fail=$((fail+1))
    echo "[${n}] FAIL_EMIT (${dt}s): ${note}"
    continue
  fi
  chars=$(wc -c < "$out" 2>/dev/null | tr -d ' ')
  sc=$(grep -c '\bsorry\b' "$out" 2>/dev/null)
  if [ "${sc:-1}" -ne 0 ]; then
    echo -e "${n}\tFAIL_SORRY\t${chars}\t${dt}\tsorry_count=${sc}" >> "$RESLOG"
    fail=$((fail+1))
    echo "[${n}] FAIL_SORRY (${dt}s) sorry=${sc}"
    continue
  fi
  echo -e "${n}\tPASS\t${chars}\t${dt}\t" >> "$RESLOG"
  pass=$((pass+1))
  echo "[${n}] PASS (${dt}s, ${chars}c)"
done < "$LIST"
echo "================ DONE pass=$pass fail=$fail ================"
