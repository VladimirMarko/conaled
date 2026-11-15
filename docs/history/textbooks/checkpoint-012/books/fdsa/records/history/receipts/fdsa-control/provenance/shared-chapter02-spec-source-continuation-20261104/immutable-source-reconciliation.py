from pathlib import Path
from collections import Counter
import subprocess,json,hashlib,re,datetime
B=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104')
C=B/'fdsa-control';repo=B/'conaled-ch02-top-down'
D=C/'provenance/shared-chapter02-spec-source-continuation-20261104'
Q='2da5708478a1d943a9214b5b386ec2db16cd9eca';L='726cb9a9b9ff4444a7614383de4fb336e8804aa7';Z='4b5dbfa07288acc73f25c27838d3fb2f78e77d71';R='07e480f6ec9958d4975bb90151005b84f2907614'
def git(*a):return subprocess.check_output(['git','-C',str(repo),*a])
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(c,p):return git('show',c+':'+p)
def ident(b):return {'bytes':len(b),'lines':len(b.splitlines()),'sha256':sha(b),'git_blob':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
def meta(p):
 p=Path(p);b=p.read_bytes();return {'path':str(p.relative_to(C)),'bytes':len(b),'lines':len(b.splitlines()),'sha256':sha(b)}
def tree(c):
 ans={}
 for line in git('ls-tree','-r',c).decode().splitlines():
  prefix,path=line.split('\t',1);mode,kind,h=prefix.split();ans[path]={'mode':mode,'kind':kind,'git_blob':h}
 return ans
v=json.loads((C/'provenance/shared-chapter02-integration-readiness-20261104/inventory.json').read_bytes())
priorpath=C/'provenance/chapter02-spec-source-preparation-20261104/current-public-type-disposition-4b5dbfa0.json'
prior=json.loads(priorpath.read_bytes())
assert prior['candidate']==Z and prior['review_base']==R
assert git('show','-s','--format=%P',Q).decode().split()==[L,Z]
assert git('rev-parse',Q+'^{tree}').decode().strip()=='fe0bd9f17a5e1a09797be55fd79491e8c363cbd0'
for a in [R,L,Z]:assert subprocess.run(['git','-C',str(repo),'merge-base','--is-ancestor',a,Q]).returncode==0
tq,tl,tz=tree(Q),tree(L),tree(Z)
rows=v['original_scope']['source_rows_exact_Z'];scope={r['path'] for r in rows}
assert len(scope)==81 and scope==set(git('diff','--name-only',R,Q).decode().splitlines())=={r['path'] for r in prior['current_source_inventory']}
defining={p for p in scope if p.endswith('.lean') and p!='SquareApplications.lean'}
assert len(defining)==71
current=[]
for r in rows:
 p=r['path'];old=blob(Z,p);cur=blob(Q,p);oi=ident(old);ci=ident(cur)
 assert all(oi[k]==r[k] for k in ['bytes','sha256','git_blob']),(p,r,oi)
 if p in defining:assert old==cur
 current.append({'path':p,**ci,'exact_reviewed_Z':old==cur,'exact_accepted_L':p in tl and tq[p]==tl[p]})
ldelta={p for p in set(tq)|set(tl) if tq.get(p)!=tl.get(p)}
expected={r['path'] for r in v['conditional_after_planned_Tail_source_union']['new_defining_modules']}|{'Applications/Resources/Growth.lean','SquareApplications.lean','docs/research/fdsa-reconstruction-map.md','docs/research/fdsa-sorting.md'}
assert len(ldelta)==50 and ldelta==expected
outside=set(tl)-ldelta;assert len(outside)==1607 and all(tq[p]==tl[p] for p in outside)
types=Counter('M' if p in tl else 'A' for p in ldelta);assert dict(types)=={'A':47,'M':3}
numstat=git('diff','--numstat',L,Q).decode().splitlines()
adds=sum(int(x.split('\t')[0]) for x in numstat);dels=sum(int(x.split('\t')[1]) for x in numstat);assert (adds,dels)==(11666,23)
zdelta={p for p in set(tq)|set(tz) if tq.get(p)!=tz.get(p)}
assert len(zdelta)==9 and {p for p in zdelta if p.endswith('.lean')}=={'SquareApplications.lean'}
notes=[r['path'] for r in v['documentary_recipe']['shared_notes']['preserve_five_exact_J_notes']]+['docs/research/fdsa-permutation-tail.md']
assert len(notes)==6 and all(tq[p]==tl[p] for p in notes)
rr=v['documentary_recipe']['root'];anchor=rr['insert_before'];rootL=blob(L,rr['path']).decode();rootQ=blob(Q,rr['path']).decode()
assert rootL.count(anchor)==1
assert rootQ==rootL.replace(anchor,'\n'.join(rr['add_once_only_23_imports'])+'\n\n'+anchor)
imports=lambda s:re.findall(r'^import\s+(\S+)\s*$',s,re.M)
iq,iz,il=imports(rootQ),imports(blob(Z,rr['path']).decode()),imports(rootL)
assert len(iq)==len(set(iq)) and set(iq)==set(iz) and [x for x in iq if x in set(il)]==il
assert blob(Q,'ProofAudit.lean')==blob(L,'ProofAudit.lean')==blob(Z,'ProofAudit.lean')
sr=v['documentary_recipe']['sorting_note'];sZ=blob(Z,sr['path']).decode();sQ=blob(Q,sr['path']).decode()
assert sZ.count(sr['replace_exact_opening'])==1
assert sQ==sZ.replace(sr['replace_exact_opening'],sr['proposed_opening'])
table=[x for x in sQ.splitlines() if re.match(r'^\| C02-\d{3} \|',x)]
assert len(table)==112 and sha(('\n'.join(table)+'\n').encode())==sr['raw_table_rows_sha256']
assert [re.match(r'^\| (C02-\d{3}) \|',x).group(1) for x in table]==sr['row_ids']
mr=v['documentary_recipe']['map'];mL=blob(L,mr['path']).decode();mQ=blob(Q,mr['path']).decode()
section=mr['complete_C2_section_with_only_acceptance_sentence_reconciled']
assert mQ.count(section)==1 and section+mr['insert_before'] in mQ
assert mr['chapter2_row'] in mQ.splitlines()
rowpat=re.compile(r'^\| (\d+|A|B|C) \|')
getrows=lambda s:[x for x in s.splitlines() if rowpat.match(x) and not x.startswith('| 2 |')]
assert getrows(mQ)==getrows(mL)
headL=mL[:mL.index(mr['insert_before'])];headQ=mQ[:mQ.index(section)]
oldrow=next(x for x in mL.splitlines() if x.startswith('| 2 |'))
assert headQ==headL.replace(oldrow,mr['chapter2_row'])
names=prior['per_name_dispositions'];assert len(names)==len({r['name'] for r in names})==1763
assert {r['source'] for r in names}==defining
namehash=sha(('\n'.join(sorted(r['name'] for r in names))+'\n').encode());assert namehash==v['accounting']['all_1763_names_hash']
assert dict(Counter(r['source'] for r in names))==v['accounting']['per_source_public_counts']
pb=prior['private_generated_boundary'];assert len(pb['original_private_named_inventory'])==70 and len(pb['original_anonymous_instance_inventory'])==19
assert {r['source'] for r in pb['original_private_named_inventory']+pb['original_anonymous_instance_inventory']}<=defining
for p in v['repository_policy_and_pins']:
 assert ident(blob(Q,p['path']))['sha256']==p['sha256'] and tq[p['path']]==tl[p['path']]
# Every local Lean blob except the public root is exact Z; its import set is exact Z.
# Thus the already reviewed source import graph is unchanged as a graph despite root order.
static=C/'provenance/chapter02-public-integration-20261104/static-closure.json'
sv=json.loads(static.read_bytes());assert sum(p.endswith('.lean') for p in tq)==sv['tracked_lean_files']==1085
assert all(tq[p]==tz[p] for p in tq if p.endswith('.lean') and p!='SquareApplications.lean')
out={'schema':'fdsa-spec-c2-immutable-source-reconciliation-v1','recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/chapter02_spec','candidate':Q,'review_base':R,'integration_base':L,'historical_source':Z,'tree':'fe0bd9f17a5e1a09797be55fd79491e8c363cbd0','ordered_parents':[L,Z],'all_R_L_Z_actual_ancestors':True,'full_scope':{'paths':81,'obligations':112,'shared_scopes':10,'defining_paths':71,'public_names':1763,'private_named':70,'anonymous_instances':19},'all81_current_source_identities':current,'all71_defining_blobs_exact_reviewed_Z':True,'L_delta':{'paths':50,'added':47,'modified':3,'insertions':adds,'deletions':dels,'all1607_outside_paths_modes_blobs_preserved':True},'Z_delta_exact_paths':sorted(zdelta),'accepted_six_notes':[{ 'path':p,**ident(blob(Q,p))} for p in notes],'root_recipe_exact':True,'all23_added_once_with_existing_order_preserved':True,'root_import_set_exact_Z':True,'ProofAudit_unchanged':True,'sorting_only_exact_opening_change':True,'all112_rows_exact_order_and_hash':sr['raw_table_rows_sha256'],'map_complete_C2_section_exact':True,'map_nonC2_rows_and_prefix_exact_L':True,'shared_map_actual_hunks_semantically_read_tool':'159765','Growth_full_module_read_tool':'ae6584','sorting_actual_diff_read_tool':'c83f04','current1763_names':{'sorted_name_hash':namehash,'per_source_counts':v['accounting']['per_source_public_counts'],'historical_partition_retained_not_credited_for_receiver':dict(Counter(r['disposition'] for r in names)),'source_identity_binding':meta(priorpath)},'private_and_anonymous_exact_source_surfaces_retained':True,'generated_Fintype_helper_history_retained':True,'policy_and_pin_identities_exact':[{'path':p['path'],'sha256':p['sha256']} for p in v['repository_policy_and_pins']],'static_import_graph':{'method':'Every local Lean source except root is exact Z; root import set and unchanged ProofAudit are exact. Retain existing complete graph analysis by this exact identity; no compiler/audit count claimed.','tracked_Lean':1085,'public_source_closure':1028,'checker_source_closure':1029,'unreached_accepted_source_paths':56,'prior_receipt':meta(static)},'recipe':meta(C/'provenance/shared-chapter02-integration-readiness-20261104/inventory.json'),'source_review_boundary':'Exact receiving source facts only; final author command/conflict/ref evidence and complete source report remain pending. No receiving compiler/type/audit credit.','receiving_type_credit':0}
D.mkdir(exist_ok=True)
p=D/'immutable-source-reconciliation.json'
with p.open('x') as f:f.write(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'result':meta(p),'scope':out['full_scope'],'source_comparison':out['L_delta'],'Z_delta':sorted(zdelta)}))
