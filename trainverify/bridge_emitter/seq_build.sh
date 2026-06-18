#!/usr/bin/env bash
# seq_build.sh <worklist> <results.tsv> : emit+olean each goal in order, log real errors
set -u
WL="$1"; OUT="$2"
D=denote/gpt_ly4_regen
OLEAN=.lake/build/lib/lean/denote/gpt_ly4_regen
echo -e "goal\tstatus\tsecs\tnote" > "$OUT"
while read -r n; do
  [ -z "$n" ] && continue
  bf="$D/Goal${n}Bridge.lean"; ol="$OLEAN/Goal${n}Bridge.olean"
  # skip if already good
  if [ -f "$bf" ] && [ "$(grep -c '\bsorry\b' "$bf")" -eq 0 ] && grep -qE "theorem goal_${n}_intermediate" "$bf" && [ -f "$ol" ]; then
    echo -e "${n}\tSKIP_DONE\t0\t" >> "$OUT"; continue
  fi
  t0=$(date +%s)
  rm -f "$bf"
  elog=$(timeout 400 python3 bridge_emitter/emit2.py "$n" --quiet 2>&1)
  if [ ! -f "$bf" ] || [ "$(grep -c '\bsorry\b' "$bf")" -ne 0 ]; then
    note=$(echo "$elog" | grep -iE 'error|Unknown|unsolved|FAIL' | grep -viE linter | head -1)
    echo -e "${n}\tFAIL_EMIT\t$(($(date +%s)-t0))\t${note}" >> "$OUT"; continue
  fi
  blog=$(timeout 600 lake env lean "$bf" -o "$ol" 2>&1)
  if [ -f "$ol" ] && ! echo "$blog" | grep -qE 'error'; then
    echo -e "${n}\tPASS\t$(($(date +%s)-t0))\t" >> "$OUT"
  else
    note=$(echo "$blog" | grep -iE 'error|Unknown|unsolved' | grep -viE linter | head -1)
    echo -e "${n}\tFAIL_OLEAN\t$(($(date +%s)-t0))\t${note}" >> "$OUT"
    rm -f "$ol"
  fi
done < "$WL"
echo "DONE_ALL" >> "$OUT"
