#!/usr/bin/env python3
"""Check every requested in-source axiom print, plus saved module contracts."""
import pathlib,json,re
B=pathlib.Path(__file__).resolve().parent
M=json.loads((B/'source-manifest.json').read_text());E=json.loads((B/'expected-module-axioms.json').read_text())['modules'];result=[];all_names=set();preserved=0
for r in M['modules']:
 src=(B/'sources'/r['relative_path']).read_text();expected_count=len(re.findall(r'^\s*#(?:print\s+axioms|a)\s',src,re.M))
 log=(B/'logs'/(r['module']+'.log')).read_text();pairs=[]
 for hit in re.finditer(r"^'(.+)' depends on axioms: \[([^\]]*)\]",log,re.M):
  pairs.append((hit[1],[x.strip() for x in hit[2].split(',') if x.strip()]))
 for hit in re.finditer(r"^'(.+)' does not depend on any axioms",log,re.M):pairs.append((hit[1],[]))
 assert len(pairs)==expected_count,(r['module'],expected_count,len(pairs))
 for name,axs in pairs:assert set(axs)<={'propext','Classical.choice','Quot.sound'},(r['module'],name,axs)
 observed=dict(pairs);assert len(observed)==len(pairs),r['module']
 if r['module'] in E:
  assert set(observed)==set(E[r['module']]),r['module']
  assert all(set(axs)==set(E[r['module']][name]) for name,axs in observed.items()),r['module']
  preserved+=len(observed)
 all_names.update(observed)
 result.append({'module':r['module'],'query_count':len(pairs),'axioms':observed,'saved_axiom_contract_equal':r['module'] in E})
report={'status':'verified','module_count':len(result),'printed_axiom_queries':sum(r['query_count'] for r in result),'distinct_declarations_queried':len(all_names),'saved_module_axiom_contracts_equal':len(E),'saved_axiom_queries_preserved':preserved,'modules':result,'scope':'All explicit source #print axioms commands and their #a macro aliases; not a census of every unqueried declaration in imported libraries.'}
(B/'all-module-axioms.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='modules'}))
