#!/usr/bin/env bash
# batch_status.sh — summarize the topo batch progress for the cron monitor.
cd /home/argustest/.openclaw/workspace/tainverify_lean/trainverify || exit 1
TSV=bridge_emitter/BATCH_topo.tsv
TODO=/tmp/TODO_topo.txt
total=$(wc -l < "$TODO" 2>/dev/null | tr -d ' ')
pass=$(awk -F'\t' '$2=="PASS"{c++}END{print c+0}' "$TSV" 2>/dev/null)
failemit=$(awk -F'\t' '$2=="FAIL_EMIT"{c++}END{print c+0}' "$TSV" 2>/dev/null)
failol=$(awk -F'\t' '$2=="FAIL_OLEAN"{c++}END{print c+0}' "$TSV" 2>/dev/null)
failsorry=$(awk -F'\t' '$2=="FAIL_SORRY"{c++}END{print c+0}' "$TSV" 2>/dev/null)
done=$((pass+failemit+failol+failsorry))
alive=$(ps -eo pid,args | grep -E 'batch_emit2\.sh /tmp/TODO_topo' | grep -v grep | head -1 | awk '{print $1}')
last=$(tail -1 "$TSV" 2>/dev/null | cut -f1,2)
echo "RUNNING=${alive:-no} done=${done}/${total} pass=${pass} fail_emit=${failemit} fail_olean=${failol} fail_sorry=${failsorry} last=[${last}]"
# list first few real failures (genuine structural gaps)
fails=$(awk -F'\t' '$2 ~ /FAIL/ && $4>10 {print $1}' "$TSV" 2>/dev/null | tr '\n' ' ')
[ -n "$fails" ] && echo "REAL_FAILS(>10s)=${fails}"
