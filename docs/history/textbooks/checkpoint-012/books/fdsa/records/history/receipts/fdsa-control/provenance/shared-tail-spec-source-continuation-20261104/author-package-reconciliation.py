from pathlib import Path
import subprocess,json,re,hashlib
c=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control');p=c/'provenance/shared-tail-source-integration-20261104';r=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch02-top-down')
L='726cb9a9b9ff4444a7614383de4fb336e8804aa7';J='932438a765340d69fa6402f6abd17def6ec28d13';T='02fc3f3cf34ed9be9d7c3a08a7e5b7cf75896fd9';B='4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8'
def g(*a):return subprocess.check_output(['git','-C',str(r),*a])
def blob(k,s):return g('show',k+':'+s)
def filemeta(z):
 b=z.read_bytes();return {'path':str(z.relative_to(c)),'bytes':len(b),'lines':len(b.splitlines()),'sha256':hashlib.sha256(b).hexdigest()}
rc=json.loads((p/'receipt.json').read_bytes());base=json.loads((p/'baseline.json').read_bytes());res=json.loads((p/'result.json').read_bytes());sc=json.loads((p/'scope-and-continuation.json').read_bytes());old=json.loads((c/'provenance/shared-tail-spec-integration-preparation-20261104/assessment.json').read_bytes())
for a in rc['artifacts']:
 m=filemeta(p/a['path'])
 for key in ['bytes','lines','sha256']:assert m[key]==a[key],a['path']
assert len(rc['artifacts'])==14
for a in rc['original_notes_and_preparations_reverified']:
 assert hashlib.sha256((c/a['path']).read_bytes()).hexdigest()==a['sha256'],a['path']
before={x['ref']:x['object'] for x in base['all_prior_refs']}
after={x['ref']:x['object'] for x in res['refs_after']}
now=dict(line.split(' ',1) for line in g('for-each-ref','--format=%(refname) %(objectname)').decode().splitlines())
assert len(before)==65 and len(after)==66 and after==now
assert all(after[k]==v for k,v in before.items()) and set(after)-set(before)=={'refs/heads/work/fdsa-tail-integration'}
assert after['refs/heads/work/fdsa-tail-integration']==L and after['refs/heads/work/fdsa-book']==J
scope=set(base['six_path_scope'])
def tree(k):
 d={}
 for x in g('ls-tree','-r','-z',k).split(b'\0'):
  if x:
   a,b=x.decode().split('\t',1);d[b]=a
 return d
tj,tl=tree(J),tree(L)
assert len(tj)==1606 and len(tl)==1610
same=[k for k in tj if k not in scope]
assert len(same)==1604 and all(tj[k]==tl[k] for k in same)
assert set(k for k in set(tj)|set(tl) if tj.get(k)!=tl.get(k))==scope
assert g('diff','--binary',J,L)==(p/'source.diff').read_bytes()
cf=(p/'actual-map-conflict.txt').read_bytes();lines=cf.splitlines(keepends=True)
markers=[i+1 for i,s in enumerate(lines) if s.startswith((b'<<<<<<<',b'=======',b'>>>>>>>'))]
assert markers==[611,616,638]
jmap=blob(J,'docs/research/fdsa-reconstruction-map.md')
assert b''.join(lines[:610]+lines[611:615])==jmap
tm=blob(T,'docs/research/fdsa-reconstruction-map.md')
assert tm.endswith(b''.join(lines[616:637]))
st=json.loads((p/'03-conflict-before-resolution.json').read_bytes())
stages=[x.split() for x in st['actual_unmerged_index'].splitlines()]
for row,k in zip(stages,[B,J,T]):assert row[1]==g('rev-parse',k+':docs/research/fdsa-reconstruction-map.md').decode().strip()
for a in res['ancestry_checks']:assert subprocess.run(['git','-C',str(r),'merge-base','--is-ancestor',a['commit'],L]).returncode==0
assert sc['original_findings_to_continue']==old['findings']['continued_ids']
assert sc['additional_correction_history']==old['findings']['additional_corrections']
assert sc['historical_focused_individual_results']==old['historical_focused_results']
assert sc['historical_actual815_positions']==[203,263]
assert sc['full_scope_counts']['public']==61 and sc['full_scope_counts']['private_named']==19 and sc['full_scope_counts']['anonymous_instances']==8
pf=json.loads((c/'provenance/shared-tail-build-preflight-20261104/preflight.json').read_bytes())
for path,d in pf['configuration'].items():
 assert blob(J,path)==blob(L,path) and hashlib.sha256(blob(L,path)).hexdigest()==d['sha256'],path
for f in base['repository_instruction_identities']:
 assert blob(J,f['path'])==blob(L,f['path']) and hashlib.sha256(blob(L,f['path'])).hexdigest()==f['sha256']
print(json.dumps({'candidate':L,'payloads_verified':14,'all15_package_files':[filemeta(z) for z in sorted(p.iterdir()) if z.is_file()],'prior_refs':65,'current_refs':66,'all_prior_refs_exact':True,'all1604_outside_scope_J_paths_exact':True,'source_diff_exact_immutable_J_L':True,'conflict_stage_blobs_match_B_J_T':True,'conflict_marker_lines':markers,'conflict_prefix_and_ours_reconstruct_exact_J':True,'conflict_theirs_is_exact_T_suffix':True,'all_original_history_ancestors':True,'original_finding_ids_and_historical_results_equal_held_preparation':True,'ten_configuration_blobs_exact_J':True,'five_prior_instruction_blobs_exact_J':True,'source_only':True,'no_actual_validation_or_type_credit':True},ensure_ascii=False))
