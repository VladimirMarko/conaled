from pathlib import Path
from collections import Counter
import datetime, hashlib, json, re, subprocess
BASE=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104'); CTRL=BASE/'fdsa-control'; REPO=BASE/'conaled-ch02-top-down'
OWN=CTRL/'provenance/shared-chapter02-standards-source-continuation-20261104'
R='07e480f6ec9958d4975bb90151005b84f2907614'; L='726cb9a9b9ff4444a7614383de4fb336e8804aa7'; Z='4b5dbfa07288acc73f25c27838d3fb2f78e77d71'; C='2da5708478a1d943a9214b5b386ec2db16cd9eca'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','--no-optional-locks','-C',str(REPO),*args])
def rj(p):return json.loads((CTRL/p).read_bytes())
def identity(p):
 b=(CTRL/p).read_bytes();return {'path':p,'bytes':len(b),'lines':len(b.splitlines()),'sha256':sha(b)}
T={};B={}
def tree(c):
 if c not in T:T[c]={v.split(b'\t',1)[1].decode():v.split(b'\t',1)[0].split()[2].decode() for v in git('ls-tree','-r','-z',c).split(b'\0') if v}
 return T[c]
def blob(c,p):
 oid=tree(c)[p]
 if oid not in B:B[oid]=git('cat-file','blob',oid)
 return B[oid]
def mask(s):
 o=list(s);i=depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):o[i:i+2]='  ';depth+=1;i+=2
   elif s.startswith('-/',i):o[i:i+2]='  ';depth-=1;i+=2
   else:
    if s[i]!='\n':o[i]=' '
    i+=1
  elif string:
   if s[i]=='\\' and i+1<len(s):o[i:i+2]='  ';i+=2
   elif s[i]=='"':string=False;o[i]=' ';i+=1
   else:
    if s[i]!='\n':o[i]=' '
    i+=1
  elif s.startswith('/-',i):depth=1;o[i:i+2]='  ';i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;o[i:j]=' '*(j-i);i=j
  elif s[i]=='"':string=True;o[i]=' ';i+=1
  else:i+=1
 assert not depth and not string
 return ''.join(o)
IM={}
def imports(c,p):
 oid=tree(c)[p]
 if oid not in IM:IM[oid]=[x for m in re.finditer(r'^(?:public\s+)?import\s+([^\n]+)',mask(blob(c,p).decode()),re.M) for x in m[1].split()]
 return IM[oid]
def closure(c,root):
 todo=[root];local=set();external=set();edges=set()
 while todo:
  p=todo.pop()
  if p in local:continue
  local.add(p)
  for m in imports(c,p):
   q=m.replace('.','/')+'.lean';edges.add((p,m))
   if q in tree(c):todo.append(q)
   else:external.add(m)
 return local,external,edges
D=rj('provenance/shared-chapter02-statement-evidence-readiness-20261104/inventory.json');P=rj('provenance/shared-chapter02-integration-readiness-20261104/inventory.json')
ledger=rj('provenance/chapter02-standards-source-preparation-20261104/read-ledger.json')
old=rj('provenance/chapter02-standards-source-preparation-20261104/public-type-accounting.json')
parents=git('show','-s','--format=%P',C).decode().strip().split();assert parents==[L,Z]
assert git('show','-s','--format=%T',C).decode().strip()=='fe0bd9f17a5e1a09797be55fd79491e8c363cbd0'
for c in [R,L,Z,'f17cc6b1a2bf44215b16202ed0fcee2b5c130761','312aafb4446b995ff5542041b4e2e074f776db1e','932438a765340d69fa6402f6abd17def6ec28d13']:
 assert subprocess.run(['git','--no-optional-locks','-C',str(REPO),'merge-base','--is-ancestor',c,C],capture_output=True).returncode==0
scope=git('diff','--name-only',R,C).decode().splitlines();assert len(scope)==81 and scope==git('diff','--name-only',R,Z).decode().splitlines()
delta=git('diff','--name-status',L,C).decode().splitlines();assert len(delta)==50 and Counter(x.split('\t')[0] for x in delta)=={'A':47,'M':3}
changed={x.split('\t',1)[1] for x in delta};unchanged_L=set(tree(L))-changed;assert len(unchanged_L)==1607 and all(tree(L)[p]==tree(C)[p] for p in unchanged_L)
roots=set(D['defining_root_closures']);assert len(roots)==71 and roots=={p for p in scope if p.endswith('.lean') and p!='SquareApplications.lean'}
assert all(tree(C)[p]==tree(Z)[p] for p in roots)
source_ids={s['id']:s for s in D['source_ids']};assert len(source_ids)==97
for s in source_ids.values():
 p=s['path'];b=blob(C,p);assert tree(C)[p]==tree(Z)[p]==s['Z_blob'];assert sha(b)==s['sha256'] and len(b)==s['bytes']
for p,e in D['defining_root_closures'].items():
 local,external,edges=closure(C,p);assert local=={source_ids[i]['path'] for i in e['local_source_ids']};assert sorted(external)==e['direct_external_imports'] and len(edges)==e['static_import_edges']
public={r['name']:(r['source'],r['kind']) for r in old['public_named']};public['Examples.UniformQuickSortMean.instFintypeLabel']=('Examples/UniformQuickSortMean.lean','instance')
assert len(public)==1763 and {r[0]:(source_ids[r[1]]['path'],r[2]) for r in D['public_rows']}==public
assert len(old['private_named'])==70 and len(old['anonymous_instances'])==19
prior_rows={r['path']:r for r in ledger['fully_read_current_changed_source']};assert len(prior_rows)==69
retained={}
for k,e in ledger['retained_independent_analysis'].items():
 for row in e.get('whole_file_identity_verified',[]):retained[row['path']]={**row,'prior_axis_source':k}
 if 'documentation_identity_verified' in e:
  row=e['documentation_identity_verified'];retained[row['path']]={**row,'prior_axis_source':k}
assert set(prior_rows)|set(retained)==set(scope)
for p,row in {**retained,**prior_rows}.items():assert sha(blob(Z,p))==row['sha256'],p
notes=['docs/research/'+n for n in ['fdsa-list-merge.md','fdsa-difference-list-costs.md','fdsa-three-way-partition.md','fdsa-permutation-minimum.md','fdsa-permutation-order.md','fdsa-permutation-tail.md']]
assert all(tree(C)[p]==tree(L)[p] for p in notes)
assert tree(C)['docs/research/fdsa-notation-map.md']==tree(Z)['docs/research/fdsa-notation-map.md']
root=P['documentary_recipe']['root'];marker=root['insert_before'];adds=root['add_once_only_23_imports'];assert len(adds)==23
rootL=blob(L,root['path']).decode();rootC=blob(C,root['path']).decode();assert rootL.count(marker)==1
assert rootC==rootL.replace(marker,'\n'.join(adds)+'\n\n'+marker)
assert imports(C,root['path'])==imports(L,root['path'])+[x.split()[1] for x in adds]
assert len(imports(C,root['path']))==len(set(imports(C,root['path'])))
assert set(imports(C,root['path']))==set(imports(Z,root['path']))
sorting=P['documentary_recipe']['sorting_note'];textZ=blob(Z,sorting['path']).decode();textC=blob(C,sorting['path']).decode();assert textZ.count(sorting['replace_exact_opening'])==1
assert textC==textZ.replace(sorting['replace_exact_opening'],sorting['proposed_opening'])
rows=[l for l in textC.splitlines() if re.match(r'^\| C02-\d{3} \|',l)];assert len(rows)==112
assert sha(('\n'.join(rows)+'\n').encode())==sorting['raw_table_rows_sha256']
assert [re.search(r'C02-\d{3}',x)[0] for x in rows]==sorting['row_ids']
mp=P['documentary_recipe']['map'];mapC=blob(C,mp['path']).decode();mapL=blob(L,mp['path']).decode()
assert mapC.count(mp['complete_C2_section_with_only_acceptance_sentence_reconciled'])==1
assert mapC.index(mp['complete_C2_section_with_only_acceptance_sentence_reconciled'])<mapC.index(mp['insert_before'])
assert [l for l in mapC.splitlines() if re.match(r'^\| (?:[1-9][0-9]?|[ABC]) \|',l) and not l.startswith('| 2 |')]==[l for l in mapL.splitlines() if re.match(r'^\| (?:[1-9][0-9]?|[ABC]) \|',l) and not l.startswith('| 2 |')]
assert mapC.count(mp['chapter2_row'])==1
configs=rj(D['actual_producers']['Z815']['pre_inputs'])['identity']['configuration']
for p,expected in configs.items():
 b=blob(C,p);assert tree(C)[p]==tree(L)[p]==tree(Z)[p];assert len(b)==expected['bytes'] and sha(b)==expected['sha256']
policy={r['path']:r for r in P['repository_policy_and_pins']}
for p in ['.agents/skills/example-driven-development/SKILL.md','docs/agents/architectural-quality.md','docs/agents/domain.md']:
 policy[p]={'path':p,'sha256':sha(blob(Z,p))}
for p,row in policy.items():assert tree(C)[p]==tree(L)[p]==tree(Z)[p] and sha(blob(C,p))==row['sha256']
pub,_,_=closure(C,'SquareApplications.lean');pubZ,_,_=closure(Z,'SquareApplications.lean');audit,_,_=closure(C,'ProofAudit.lean')
assert pub==pubZ and len(pub)==1028 and audit==pub|{'ProofAudit.lean'}
project={p for p in tree(C) if p.endswith('.lean') and ('/' not in p or p.startswith(('Applications/','Examples/','SquareKit/')))}
assert project==audit and len(project)==1029
excluded={p for p in tree(C) if p.endswith('.lean')}-project;assert len(excluded)==56
assert excluded=={p for p in tree(Z) if p.endswith('.lean')}-audit and all(tree(C)[p]==tree(Z)[p] for p in excluded)
scope_rows=[]
for p in scope:
 b=blob(C,p);scope_rows.append({'path':p,'current_blob':tree(C)[p],'Z_blob':tree(Z)[p],'L_blob':tree(L).get(p),'sha256':sha(b),'bytes':len(b),'lines':len(b.splitlines()),'retained_Z_source_assessment':'own_full_source_read' if p in prior_rows else retained[p]['prior_axis_source'],'identity_equal_Z':tree(C)[p]==tree(Z)[p]})
rec={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/chapter02_standards','base_R':R,'accepted_predecessor_L':L,'historical_Z':Z,'candidate':C,'tree':git('show','-s','--format=%T',C).decode().strip(),'ordered_parents':parents,'full_scope':D['full_original_scope'],'full_scope_paths':scope_rows,'remaining_merge_delta':{'paths':50,'added':47,'modified':3,'unchanged_predecessor_paths':1607},'all71_defining_sources_exact_Z':True,'all97_relevant_sources_exact_Z':True,'all71_local_external_edge_closures_reconstructed':True,'all1763_public_name_source_kind_rows_exact':True,'private70_and_anonymous19_source_surfaces_unchanged':True,'source_review_retention':{'own69_complete_source_rows_all_match_Z':True,'remaining12_full_scope_paths_exact_retained_original_Foundation_XM01_XD01_analysis':sorted(set(scope)-set(prior_rows)),'six_current_notes_exact_accepted_L_with_later_final_assessments_retained':notes,'unchanged_source_reread_claimed':False,'all_original_semantics_and_findings_retained':True},'root':{'exact_L_prefix_plus23_recipe':True,'same_Z_import_set':True,'ProofAudit_unchanged':True,'static_public_modules':1028,'static_checker_modules':1029,'unchanged_excluded_Lean_files':56,'counts_are_source_graph_only_not_actual_checked_modules':True},'sorting_note':{'only_exact_opening_replaced':True,'all112_rows_byte_identical_Z':True,'table_rows_sha256':sorting['raw_table_rows_sha256'],'all_remaining_math_citations_lineage_and_gate_bytes_exact_Z':True},'map':{'complete_Z_C2_section_with_only_accepted_history_update_exact':True,'all_nonC2_chapter_Appendix_rows_exact_L':True,'full_actual_L_C_and_Z_C_diff_semantically_read_separately':True},'ten_configs_exact_L_Z':True,'policy_inputs_exact_L_Z':sorted(policy),'identity_bound_prior_evidence':[identity('reviews/chapter02-standards-source-preparation-20261104.md'),identity('provenance/chapter02-standards-source-preparation-20261104/read-ledger.json'),identity('provenance/chapter02-standards-source-preparation-20261104/successor-source-reconciliation-4b5dbfa0.json'),identity('provenance/chapter02-standards-source-preparation-20261104/public-type-accounting.json'),identity('provenance/shared-chapter02-integration-readiness-20261104/inventory.json'),identity('provenance/shared-chapter02-statement-evidence-readiness-20261104/inventory.json')],'author_final_package_and_ref_reconciliation':'Pending held final author records; this script reads only immutable source and fixed earlier records.','new_actual_type_full_audit_credit':0,'compiler_cache_process_runtime_output_source_ref_actions':False}
out=OWN/'independent-source-reconciliation.json';assert not out.exists();out.write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({'result':identity(str(out.relative_to(CTRL))),'full_scope':81,'defining_exact_Z':71,'local_closure_exact_Z':97,'public':1763,'static_public_checker_excluded':[1028,1029,56],'receiving_credit':0},indent=2))
