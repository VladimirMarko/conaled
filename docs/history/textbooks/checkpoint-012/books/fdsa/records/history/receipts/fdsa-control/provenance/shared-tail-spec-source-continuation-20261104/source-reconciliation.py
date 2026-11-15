from pathlib import Path
import subprocess,json,re,hashlib
c=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/fdsa-control')
r=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ch02-top-down')
L='726cb9a9b9ff4444a7614383de4fb336e8804aa7';J='932438a765340d69fa6402f6abd17def6ec28d13';T='02fc3f3cf34ed9be9d7c3a08a7e5b7cf75896fd9';Z='4b5dbfa07288acc73f25c27838d3fb2f78e77d71'
def g(*a):return subprocess.check_output(['git','-C',str(r),*a])
def blob(k,p):return g('show',k+':'+p)
def meta(k,p):
 b=blob(k,p);return {'candidate':k,'path':p,'blob':g('rev-parse',k+':'+p).decode().strip(),'bytes':len(b),'lines':len(b.splitlines()),'sha256':hashlib.sha256(b).hexdigest()}
old=json.loads((c/'provenance/shared-tail-spec-integration-preparation-20261104/assessment.json').read_bytes())
prior=old['independent_source_verification']['successor_source_reconciliation']
paths=['Applications/Probability/PermutationTail.lean','Examples/PermutationTail.lean','Examples/PermutationTailBoundary.lean']
expected=paths+['SquareApplications.lean','docs/research/fdsa-permutation-tail.md','docs/research/fdsa-reconstruction-map.md']
actual=g('diff','--name-only',J,L).decode().splitlines()
assert set(actual)==set(expected)
assert g('show','-s','--format=%P',L).decode().strip().split()==[J,T]
assert g('rev-parse',L+'^{tree}').decode().strip()=='43f1c15166931d4bd3e91e6dbf12059d0da1cfc2'
decl=[];instances=[]
for p in paths:
 b=blob(L,p);assert b==blob(T,p)==blob(Z,p)
 text=b.decode();prefix=re.search(r'^namespace ([A-Za-z0-9_.]+)',text,re.M)[1]
 for n,line in enumerate(text.splitlines(),1):
  m=re.match(r'^(?:@\[[^\]]*\]\s*)?(private )?(?:noncomputable )?(def|theorem|abbrev)\s+([A-Za-z_][A-Za-z_0-9]*)\b',line)
  if m:
   z={'source':p,'line':n,'kind':m[2],'name':prefix+'.'+m[3],'private':bool(m[1])}
   rest='\n'.join(text.splitlines()[n-1:]);header=rest.split(':=',1)[0].rstrip()+'\n'
   z.update(header=header,header_sha256=hashlib.sha256(header.encode()).hexdigest())
   decl.append(z)
  if re.match(r'^(?:local )?instance\s*:',line):instances.append({'source':p,'line':n,'source_header_line':line})
 assert not re.search(r'^example\b',text,re.M)
assert [{k:v for k,v in z.items() if k not in ['header','header_sha256']} for z in decl]==prior['declarations']
assert instances==prior['instances']
public=[z for z in decl if not z['private']]
assert len(public)==61 and sum(z['private'] for z in decl)==19 and len(instances)==8
program=c/old['program']['path'];pb=program.read_bytes()
assert hashlib.sha256(pb).hexdigest()==old['program']['sha256']
names=re.findall(r'^#check\s+@?([A-Za-z_][A-Za-z_0-9.]*)\s*$',pb.decode(),re.M)
assert names==old['authored_scope']['program_names']==[z['name'] for z in public]
allpaths=set(g('ls-tree','-r','--name-only',L).decode().splitlines())
seen={};local=[];external=[]
todo=list(paths)
while todo:
 p=todo.pop()
 if p in seen:continue
 seen[p]=meta(L,p)
 assert blob(L,p)==blob(Z,p)
 for imp in re.findall(r'^import\s+([^\n]+)',blob(L,p).decode(),re.M):
  for name in imp.split():
   if name.startswith('--'):break
   child=name.replace('.','/')+'.lean'
   if child in allpaths:local.append([p,child]);todo.append(child)
   else:external.append([p,name])
assert len(seen)==9 and len(local)==13 and len(set(x[1] for x in external))==19
assert set(seen)==set(prior['closure'])
for p,m in seen.items():
 assert m['sha256']==prior['closure'][p]['sha256']
 if p not in paths:assert blob(L,p)==blob(J,p)
notes=['docs/research/fdsa-permutation-minimum.md','docs/research/fdsa-permutation-order.md']
assert all(blob(J,p)==blob(L,p) for p in notes)
assert blob(L,'SquareApplications.lean')==blob(J,'SquareApplications.lean').replace(b'import Examples.PermutationOrder\n',b'import Examples.PermutationOrder\nimport Examples.PermutationTail\n',1)
mJ=blob(J,'docs/research/fdsa-reconstruction-map.md');mL=blob(L,'docs/research/fdsa-reconstruction-map.md');assert mL.startswith(mJ)
old_hashes={z['part']:z['sha256'] for z in old['proposed_text_identities_not_materialized']}
parts={'SquareApplications.lean':'planned_root','docs/research/fdsa-permutation-tail.md':'planned_note_only','docs/research/fdsa-reconstruction-map.md':'planned_full_map'}
for p,part in parts.items():
 assert hashlib.sha256(blob(L,p)).hexdigest()==old_hashes[part]
assert hashlib.sha256(mL[len(mJ):]).hexdigest()==old_hashes['planned_map_append']
for f in old['retained_own_records']:
 b=(c/f['path']).read_bytes();assert len(b)==f['bytes'] and hashlib.sha256(b).hexdigest()==f['sha256']
grep=subprocess.run(['git','-C',str(r),'grep','-n','-E','^import .*PermutationTail',J,'--','*.lean'],capture_output=True)
assert grep.returncode==1 and not grep.stdout
res={'candidate':L,'tree':g('rev-parse',L+'^{tree}').decode().strip(),'parents':[J,T],'scope':[meta(L,p) for p in actual],'numstat':g('diff','--numstat',J,L).decode(),'declarations':decl,'instances':instances,'counts':{'public':len(public),'private':19,'anonymous_instances':8,'public_theorems':sum(x['kind']=='theorem' for x in public),'public_definitions':sum(x['kind']=='def' for x in public)},'program':old['program'],'program_names':names,'all61_names_order_exact':True,'source_closure':seen,'local_edges':local,'external_edges':external,'external_names':sorted(set(x[1] for x in external)),'all9_sources_exact_Z':True,'six_predecessor_sources_exact_J':True,'two_predecessor_notes_exact_J':True,'root_exact_single_import':True,'map_complete_J_prefix_exact':True,'map_append_lines':len(mL[len(mJ):].splitlines()),'all_three_documentary_hashes_equal_held_proposal':True,'old_J_Tail_importers':[],'retained_own_records_exact':old['retained_own_records'],'source_only':True,'actual_receiving_type_credit':0}
print(json.dumps(res,ensure_ascii=False))
