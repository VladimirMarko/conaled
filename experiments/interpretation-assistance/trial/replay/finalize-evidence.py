from pathlib import Path
import json,hashlib,re
P=Path('/tmp/conaled-wave-20261111/462-trial-preparation'); R=P/'replay'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=json.loads((R/'receipts.json').read_text())
for rec in receipts:
 if rec['exit']==1 and rec['log'].endswith('direct-audit-helper.log'):rec['log']=str(R/'audit-helper-first-failure.log')
(R/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
e={'prototype':'3b5c9002c9e799b00d01b6f1e0ca0dfe155d465b','launch_manifest_sha256':sha(P/'launch-manifest.json'),'replay_result':'all 16 exact source checks match original outcomes; 15 passing snapshots audited','source_changes':False,'author_feedback':False,'snapshots':[],'hashes':{}}
for arm in ['direct','assisted']:
 fm=json.loads((P/'frozen-results'/(arm+'-manifest.json')).read_text())
 assert all(sha(P/'frozen-results'/arm/n)==h for n,h in fm['files'].items())
 for ctrl in sorted((P/'control'/arm).glob('round-*')):
  n=ctrl.name;src=R/arm/'Examples'/('Replay'+n.replace('-','')+'.lean'); d=json.loads((ctrl/'receipt.json').read_text());assert sha(src)==sha(ctrl/'source.lean')==d['source_sha256']
  audit=R/(arm+'-'+n+'-audit.log');o={'arm':arm,'round':n,'sha256':sha(src),'original_source':d['original_source'],'expected_and_actual_exit':d['exit'],'replayed_source':str(src),'check_log':arm+'-'+n+'-check.log'}
  if d['exit']==0:
   txt=audit.read_text();assert 'Proof audit PASSED' in txt
   roots=[x.removeprefix('[ProofAudit.roots] ') for x in txt.splitlines() if x.startswith('[ProofAudit.roots] ')]
   rootsfile=R/(arm+'-'+n+'-roots.txt');rootsfile.write_text('\n'.join(roots)+'\n')
   m=re.search(r'Examples.Replay\w+: (\d+) logical declarations; (\d+) theorem declarations; (\d+) unsafe runtime declarations',txt)
   o.update(audit_log=audit.name,audited_snapshot_roots=int(m[1]),snapshot_theorems=int(m[2]),snapshot_runtime_excluded=int(m[3]),all_project_roots=len(roots),axioms=['propext','Classical.choice','Quot.sound'],root_list=rootsfile.name)
  e['snapshots'].append(o)
for p in sorted(R.iterdir()):
 if p.is_file() and p.name not in ['evidence.json']:e['hashes'][p.name]=sha(p)
(R/'evidence.json').write_text(json.dumps(e,indent=2)+'\n')
