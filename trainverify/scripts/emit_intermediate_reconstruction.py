#!/usr/bin/env python3
"""Parse GeneratedYOCOMoE, categorize the 1151 intermediateGoals by SM
producer op, emit the all_intermediateGoals_list def + per-op sublists."""
import re, sys, json, os
SRC = os.path.join(os.path.dirname(__file__), '..', 'denote', 'GeneratedYOCOMoE.lean')
lines = open(SRC).read().split('\n')

def parse_graph(marker):
    writes={}; started=False
    for l in lines:
        if l.startswith(marker): started=True; continue
        if started:
            s=l.strip()
            if s.startswith('{ rank'):
                mo=re.search(r'op := "OpName\.(\w+)"', s)
                ms=re.search(r'outs := \[([\d, ]*)\]', s)
                if mo and ms:
                    for t in (int(x) for x in ms.group(1).split(',') if x.strip()):
                        writes[t]=mo.group(1)
            elif l.startswith('def '): break
    return writes

sm_writes=parse_graph('def sm : GraphDecl')
order=[]; goals={}
for i,l in enumerate(lines):
    m=re.match(r'def (intermediateGoal_\d+) : LineageGoal', l)
    if m:
        body=lines[i+1]; name=m.group(1)
        ts=int(re.search(r'ts := (\d+)',body).group(1))
        tps=[int(x) for x in re.findall(r'tid := (\d+)',body)]
        rep='replicated := true' in body
        goals[name]=dict(ts=ts,tps=tps,rep=rep); order.append(name)

from collections import OrderedDict
buckets=OrderedDict()
for name in order:
    op=sm_writes.get(goals[name]['ts'],'INIT')
    buckets.setdefault(op,[]).append(name)

if len(sys.argv)>1 and sys.argv[1]=='--json':
    json.dump(dict(order=order,goals=goals,sm_writes=sm_writes,
        buckets=dict(buckets)), sys.stdout); sys.exit(0)

# emit the full list def
def emit_list(name, items):
    out=[f"def {name} : List LineageGoal :="]
    # chunk into lines of ~6
    body=", ".join(items)
    out.append("  [" + body + "]")
    return "\n".join(out)

print(f"-- total: {len(order)}  categories: {len(buckets)}")
for op,names in buckets.items():
    print(f"--   {op}: {len(names)}")
