#!/usr/bin/env bash
# batch_emit2.sh — emit bridges for goals in dependency (ascending) order,
# building each bridge's olean right after a successful emit so the NEXT goal's
# probe can import it. Records pass/fail. Does NOT wire MainTheorem, does NOT touch git.
set -u
cd "$(dirname "$0")/.." || exit 1   # -> trainverify/
LIST="${1:?need goal list file}"
RESLOG="${2:-bridge_emitter/BATCH_RESULTS.tsv}"
D=denote/gpt_ly4_regen
OLEAN_DIR=.lake/build/lib/lean/denote/gpt_ly4_regen
mkdir -p "$OLEAN_DIR"

echo -e "goal\tstatus\tchars\tseconds\tnote" > "$RESLOG"
pass=0; fail=0
while read -r n; do
  [ -z "$n" ] && continue
  out="$D/Goal${n}Bridge.lean"
  t0=$(date +%s)
  # emit (writes bridge file, probes, compiles via lake env lean). --no-compile? No: we want its own compile gate too.
  log=$(python3 bridge_emitter/emit2.py "$n" --quiet 2>&1)
  rc=$?
  if [ $rc -ne 0 ]; then
    t1=$(date +%s)
    note=$(echo "$log" | grep -iE 'error|fail|sorry' | head -1 | tr '\t' ' ' | cut -c1-220)
    echo -e "${n}\tFAIL_EMIT\t-\t$((t1-t0))\t${note}" >> "$RESLOG"
    fail=$((fail+1)); echo "[${n}] FAIL_EMIT ($((t1-t0))s): ${note}"
    continue
  fi
  sc=$(grep -c '\bsorry\b' "$out" 2>/dev/null)
  if [ "${sc:-1}" -ne 0 ]; then
    t1=$(date +%s)
    echo -e "${n}\tFAIL_SORRY\t-\t$((t1-t0))\tsorry=${sc}" >> "$RESLOG"
    fail=$((fail+1)); echo "[${n}] FAIL_SORRY sorry=${sc}"
    continue
  fi
  # build olean so downstream probes can import this bridge
  blog=$(timeout 600 lake env lean "$out" -o "$OLEAN_DIR/Goal${n}Bridge.olean" 2>&1)
  brc=$?
  t1=$(date +%s); dt=$((t1-t0))
  chars=$(wc -c < "$out" 2>/dev/null | tr -d ' ')
  if [ $brc -ne 0 ]; then
    note=$(echo "$blog" | grep -iE 'error' | grep -viE 'linter|empty line|setOption' | head -1 | cut -c1-220)
    echo -e "${n}\tFAIL_OLEAN\t${chars}\t${dt}\t${note}" >> "$RESLOG"
    fail=$((fail+1)); echo "[${n}] FAIL_OLEAN (${dt}s): ${note}"
    continue
  fi
  echo -e "${n}\tPASS\t${chars}\t${dt}\t" >> "$RESLOG"
  pass=$((pass+1)); echo "[${n}] PASS (${dt}s, ${chars}c)"
done < "$LIST"
echo "================ DONE pass=$pass fail=$fail ================"
