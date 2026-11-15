import sys,json
v=json.loads(sys.argv[1])

from pathlib import Path
from datetime import datetime, timezone
import os,sys,json,hashlib,importlib.util,subprocess
sys.dont_write_bytecode=True
os.environ["GIT_OPTIONAL_LOCKS"]="0"
b=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104');c=b/'fdsa-control';p=c/'provenance/checkpoint0134-preparation'
def identity(q):
 with q.open('rb') as f:return {'bytes':q.stat().st_size,'sha256':hashlib.file_digest(f,'sha256').hexdigest()}
def write(name,data):
 with (p/name).open('x') as f:json.dump(data,f,indent=2);f.write('\n')
h=json.loads((p/'write-hold.json').read_text())
assert h['all_writers_held'] and not h['compiler_live']
assert identity(c/'checkpoint_compact.py')=={'bytes':10520,'sha256':'5e72098a4b07a80c6861cdaf14f4d2234e33cd7b6a0a79170bae762599cbe078'}
spec=importlib.util.spec_from_file_location('compact_reader',c/'checkpoint_compact.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
repo=b/'conaled'
refs=[{'oid':a[0],'ref':a[1],'symref':a[2]} for a in (line.split(' ',2) for line in mod.git(repo,'for-each-ref','--format=%(objectname) %(refname) %(symref)').splitlines())]
wts=mod.worktrees(repo);assert len(refs)==74 and len(wts)==9
accepted=mod.git(repo,'rev-parse','work/fdsa-book').strip();qualified=mod.git(b/'conaled-ch01-review','rev-parse','HEAD').strip()
assert accepted==h['accepted_head']=='c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5'
assert qualified==h['qualified_candidate']==v['qualified_candidate']
fixed=['README.md','previous-manifest-0133.json','previous-manifest-origin.json','verify-checkpoint.py','write-hold.json','verifier-scope-diff.patch','helper-scope-diffs.patch','capture.py','run-stage.py','independent-inspection-receipt.json']
held={}
for q in sorted(c.rglob('*')):
 if not q.is_file() or '__pycache__' in q.parts:continue
 if p in q.parents and q.name not in fixed:continue
 assert not q.is_symlink(),str(q)
 held[str(q.relative_to(c))]=identity(q)
previous=json.loads((c/'provenance/checkpoint0133-preparation/capture.json').read_text())['held_control']
allowed=['CURRENT.md','STATUS.md','checkpoints.json','reviews/chapter03-round1.md','tickets/FDSA-003.md','tickets/INDEX.md']
changes=[]
for rel,old in previous.items():
 assert rel in held,rel
 if held[rel]!=old:
  assert rel in allowed,rel
  changes.append(rel)
progress=json.loads((c/'provenance/chapter03-activation-20261104/focused-progress-before0134.json').read_text())
runs=[{k:r[k] for k in ['name','candidate','exit']} for r in progress['all_closed_runs']]
assert len(runs)==v['closed_count']==progress['closed_runs']
for r in runs:
 d=c/'provenance'/r['name'];result=json.loads((d/'result.json').read_text());owned=json.loads((d/'owned-terminal.json').read_text())
 assert result['exit_code']==owned['actual_exit']==r['exit']
 assert result['candidate']==owned['candidate']==r['candidate']
 assert identity(d/'full.log')=={'bytes':result['log_size_bytes'],'sha256':result['log_sha256']}
capture={'recorded_utc':datetime.now(timezone.utc).isoformat(),'checkpoint':'conaled-fdsa-0134-random-selection-path-progress','accepted_head':accepted,'qualified_candidate':qualified,'all_writers_held':True,'compiler_live':False,'refs':refs,'worktrees':wts,'held_control':held,'fixed_own_preparation_files':fixed,'declared_prior_control_updates':allowed,'actual_prior_control_updates':sorted(changes),'closed_development_runs':runs,'interrupted_development_runs':progress['interrupted_development_runs'],'scope':progress['checkpoint_scope']}
write('capture.json',capture)
s=os.statvfs(b);allocated=sum(((r['bytes']+s.f_frsize-1)//s.f_frsize)*s.f_frsize for r in held.values());scenario=allocated+96*1024*1024
assert s.f_bfree*s.f_frsize>=scenario+32*1024*1024,'Insufficient current raw checkpoint staging headroom'
preflight={'recorded_utc':datetime.now(timezone.utc).isoformat(),'ordinary_available_bytes':s.f_bavail*s.f_frsize,'raw_free_bytes':s.f_bfree*s.f_frsize,'total_filesystem_bytes':s.f_blocks*s.f_frsize,'held_control_logical_bytes':sum(r['bytes'] for r in held.values()),'held_control_rounded_copy_bytes':allocated,'source_pack_archive_metadata_allowance_bytes':96*1024*1024,'checkpoint_staging_scenario_bytes':scenario,'scenario_is_not_a_formal_upper_bound':True,'unchanged_installation_hydration_guards':True,'compiler_install_or_dependency_hydration_selected':False,'capture':identity(p/'capture.json'),'creator':identity(c/'checkpoint_compact.py'),'verifier':identity(p/'verify-checkpoint.py'),'all_writers_held':True,'compiler_live':False}
write('creation-preflight.json',preflight)
print(json.dumps({'capture':identity(p/'capture.json'),'held_controls':len(held),'refs':len(refs),'worktrees':len(wts),'closed_runs':len(runs),'actual_prior_control_updates':sorted(changes),'space_preflight':preflight},indent=2))
