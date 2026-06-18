#!/usr/bin/env bash
# fixpoint_emit.sh — iterate to a fixpoint over a goal list. Each pass, for any
# goal whose bridge isn't yet built, try emit; on success build its olean. Repeat
# passes until a full pass makes no progress. Self-correcting for dependency order.
# Does NOT wire MainTheorem, does NOT touch git.
set -u
cd "$(dirname "$0")/.." || exit 1   # -> trainverify/
LIST="${1:?need goal list}"
RESLOG="${2:-bridge_emitter/FIXPOINT.tsv}"
D=denote/gpt_ly4_regen
OLEAN=.lake/build/lib/lean/denote/gpt_ly4_regen
mkdir -p "$OLEAN"
echo -e "pass\tgoal\tstatus\tseconds\tnote" > "$RESLOG"

has_olean(){ [ -f "$OLEAN/Goal$1Bridge.olean" ]; }
good_bridge(){ [ -f "$D/Goal$1Bridge.lean" ] && [ "$(grep -c '\bsorry\b' "$D/Goal$1Bridge.lean")" -eq 0 ]; }

pass=0
while :; do
  pass=$((pass+1))
  progressed=0
  remaining=0
  echo "===== PASS $pass ====="
  while read -r n; do
    [ -z "$n" ] && continue
    if good_bridge "$n" && has_olean "$n"; then continue; fi   # already done
    remaining=$((remaining+1))
    t0=$(date +%s)
    rm -f "$D/Goal${n}Bridge.lean"
    log=$(timeout 600 python3 bridge_emitter/emit2.py "$n" --quiet 2>&1)
    if ! good_bridge "$n"; then
      note=$(echo "$log" | grep -iE 'Unknown identifier|does not exist|PROBE|unsolved|error' | head -1 | cut -c1-160)
      echo -e "${pass}\t${n}\tFAIL_EMIT\t$(( $(date +%s)-t0 ))\t${note}" >> "$RESLOG"
      continue
    fi
    # emit ok -> build olean
    blog=$(timeout 700 lake env lean "$D/Goal${n}Bridge.lean" -o "$OLEAN/Goal${n}Bridge.olean" 2>&1)
    if has_olean "$n"; then
      echo -e "${pass}\t${n}\tPASS\t$(( $(date +%s)-t0 ))\t" >> "$RESLOG"
      echo "[p${pass}][${n}] PASS"
      progressed=$((progressed+1))
    else
      note=$(echo "$blog" | grep -iE 'error' | grep -viE 'linter' | head -1 | cut -c1-160)
      echo -e "${pass}\t${n}\tFAIL_OLEAN\t$(( $(date +%s)-t0 ))\t${note}" >> "$RESLOG"
      echo "[p${pass}][${n}] FAIL_OLEAN: ${note}"
    fi
  done < "$LIST"
  echo "----- pass $pass: progressed=$progressed remaining_at_start=$remaining -----"
  [ "$progressed" -eq 0 ] && break
done

# final summary
total=$(grep -cvE '^$' "$LIST")
done_n=0; while read -r n; do good_bridge "$n" && has_olean "$n" && done_n=$((done_n+1)); done < "$LIST"
echo "================ FIXPOINT DONE: ${done_n}/${total} built, passes=${pass} ================"
