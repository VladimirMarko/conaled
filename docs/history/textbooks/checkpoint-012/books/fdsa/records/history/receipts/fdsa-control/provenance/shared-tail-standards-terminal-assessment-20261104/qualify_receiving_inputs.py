"""Read secured Tail evidence and immutable Git objects; write only this reviewer receipt."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib, json, re, subprocess
from datetime import datetime, timezone
from collections import Counter

BASE = Path("/workspace/scratch/b4a17a285e23/fdsa-restored-20261104")
CTRL = BASE / "fdsa-control"
P = CTRL / "provenance"
OWN = P / "shared-tail-standards-terminal-assessment-20261104"
REPO = BASE / "conaled-ch02-top-down"
J = "932438a765340d69fa6402f6abd17def6ec28d13"
I = "312aafb4446b995ff5542041b4e2e074f776db1e"
F = "f17cc6b1a2bf44215b16202ed0fcee2b5c130761"
O = "bdac9703aab4b383fa775568d36bf685af329389"
def sha(b): return hashlib.sha256(b).hexdigest()
def js(p): return json.loads(Path(p).read_bytes())
def fp(p):
    p = Path(p); b = p.read_bytes()
    return {"path": str(p.relative_to(CTRL)) if p.is_relative_to(CTRL) else str(p),
            "bytes": len(b), "lines": len(b.splitlines()), "sha256": sha(b)}
def command(*args):
    return subprocess.check_output(["git", "--no-optional-locks", "-C", str(REPO), *args])
trees, blobs = {}, {}
def tree(commit):
    if commit not in trees:
        d = {}
        for record in command("ls-tree", "-r", "-z", commit).split(b"\0"):
            if record:
                meta, name = record.split(b"\t", 1)
                mode, typ, oid = meta.decode().split()
                if typ == "blob": d[name.decode()] = oid
        trees[commit] = d
    return trees[commit]
def source(commit, path):
    key = (commit, path)
    if key not in blobs: blobs[key] = command("show", commit + ":" + path)
    return blobs[key]
def source_fp(commit, path):
    b = source(commit, path)
    return {"bytes": len(b), "sha256": sha(b), "git_blob": tree(commit)[path]}
def mask(text):
    chars = list(text); i = 0; depth = 0; quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i): chars[i:i+2] = [" ", " "]; depth += 1; i += 2
            elif text.startswith("-/", i): chars[i:i+2] = [" ", " "]; depth -= 1; i += 2
            else:
                if chars[i] != "\n": chars[i] = " "
                i += 1
        elif quoted:
            if text[i] == "\\" and i+1 < len(text):
                chars[i] = " "
                if chars[i+1] != "\n": chars[i+1] = " "
                i += 2
            elif text[i] == '"': chars[i] = " "; quoted = False; i += 1
            else:
                if chars[i] != "\n": chars[i] = " "
                i += 1
        elif text.startswith("/-", i): chars[i:i+2] = [" ", " "]; depth = 1; i += 2
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n": chars[i] = " "; i += 1
        elif text[i] == '"': chars[i] = " "; quoted = True; i += 1
        else: i += 1
    assert depth == 0 and not quoted
    return "".join(chars)
def imports(text):
    out = []
    for line in mask(text).splitlines():
        m = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$", line)
        if m:
            words = m.group(1).split()
            assert all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", w) for w in words)
            out.extend(words)
    return out
def closure(commit, roots):
    queue = list(roots); local = {}; edges = []; external = set()
    while queue:
        module = queue.pop()
        path = module.replace(".", "/") + ".lean"
        assert path in tree(commit), (commit, module)
        if path in local: continue
        local[path] = source_fp(commit, path)
        for dep in imports(source(commit, path).decode()):
            is_local = dep.replace(".", "/") + ".lean" in tree(commit)
            edges.append({"from": module, "to": dep, "local": is_local})
            if is_local: queue.append(dep)
            else: external.add(dep)
    return {"local_sources": local, "edges": sorted(edges, key=lambda e: (e["from"], e["to"], e["local"])),
            "external_imports": sorted(external)}
def program(identity):
    rec = identity["program"]; p = Path(rec["path"]); raw = p.read_bytes()
    assert len(raw) == rec["bytes"] and sha(raw) == rec["sha256"]
    text = raw.decode()
    names = re.findall(r"^#check @([A-Za-z_][A-Za-z0-9_.']*)\s*$", text, re.M)
    assert names == rec["names"] and len(names) == len(set(names))
    for setting in ("pp.universes", "pp.explicit", "pp.fullNames"):
        assert len(re.findall(r"^set_option " + re.escape(setting) + r" true\s*$", text, re.M)) == 1
    assert imports(text) == identity["roots"]
    return names
def objects_for(identity, selected):
    paths = identity["local_sources"]
    stems = {".lake/build/lib/lean/" + p[:-5]: p for p in paths}
    mapping = {}
    for key, value in identity["local_compiler_objects_and_traces"].items():
        owners = [p for stem, p in stems.items() if key.startswith(stem + ".")]
        assert len(owners) == 1, (key, owners)
        stem = ".lake/build/lib/lean/" + owners[0][:-5]
        assert key == stem + ".trace" or key == stem + ".olean" or key.startswith(stem + ".olean."), key
        assert value["bytes"] > 0 and re.fullmatch(r"[a-f0-9]{64}", value["sha256"])
        if owners[0] in selected: mapping[key] = value
    for p in selected:
        stem = ".lake/build/lib/lean/" + p[:-5]
        assert stem + ".olean" in mapping and stem + ".olean.hash" in mapping and stem + ".trace" in mapping
    return mapping
def block_inventory(run, identity):
    names = program(identity); p = P / run
    data = (p / "native-records/output.log").read_bytes()
    text = data.decode()
    rule = r"(?m)^@?((?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*)(?:\.\{[^}]*\})?[ \t]*:"
    matches = list(re.finditer(rule, text))
    assert [m.group(1) for m in matches] == names
    idx = js(p / "output-blocks.json"); result = []
    for n, m in enumerate(matches):
        start = len(text[:m.start()].encode())
        end = len(text[:matches[n+1].start()].encode()) if n+1 < len(matches) else len(data)
        raw = data[start:end]
        d = {"ordinal": n+1, "name": m.group(1),
             "start_line": data[:start].count(b"\n")+1,
             "end_line": data[:end].count(b"\n"),
             "byte_start": start, "byte_end_exclusive": end,
             "bytes": len(raw), "sha256": sha(raw)}
        assert d == idx["blocks"][n], (run, n+1)
        result.append(d)
    assert len(result) == len(idx["blocks"]) and result[0]["byte_start"] == 0
    assert sum(d["bytes"] for d in result) == len(data)
    return result

L = "726cb9a9b9ff4444a7614383de4fb336e8804aa7"
T = "02fc3f3cf34ed9be9d7c3a08a7e5b7cf75896fd9"

def bind_closed(run, candidate, native_command):
    p=P/run;start=js(p/'start.json');end=js(p/'result.json')
    ns=js(p/'native-records/start.json');ne=js(p/'native-records/result.json')
    assert start['candidate']==start['initial_head']==end['candidate']==end['final_head']==candidate
    assert start['initial_status']==end['final_status']==''
    assert end['exit_code']==0 and end['state']=='passed' and not end['progress_bookkeeping_errors']
    assert ne['exit_code']==0 and ne['passed'] and not ne['timed_out'] and ne['recorder_error'] is None
    assert ns['command']==ne['command']==native_command
    assert ns['lean_threads']==ne['lean_threads']=='1'
    assert ns['cwd']==ne['cwd']==start['cwd']==str(BASE/'conaled-ch01-review')
    outercmd=['python3',str(CTRL/'tooling/unified-native-kit-4.35.0/conaled_native.py'),'--state',str(BASE/'conaled-native-state'),'run','--project',str(BASE/'conaled-ch01-review'),'--threads','1','--']+native_command
    assert start['command']==end['command']==outercmd
    outer=(p/'full.log').read_bytes();native=(p/'native-records/output.log').read_bytes()
    assert len(outer)==end['log_size_bytes'] and sha(outer)==end['log_sha256'] and outer.count(native)==1
    rec=js(p/'closed-evidence-reconciliation.json');owned=js(p/'owned-terminal.json')
    assert rec['owned_terminal']==owned and owned['actual_exit']==0 and owned['candidate']==candidate
    assert rec['complete_log_closed'] and rec['actual_result']==end
    assert outer.index(native)==rec['native_output_is_exact_outer_body_at_byte_offset']
    for v in rec['copied']:
        b=(p/'native-records'/v['name']).read_bytes()
        assert len(b)==v['bytes'] and sha(b)==v['sha256']
        assert Path(v['origin']).parent==Path(rec['native_origin'])
    verify=js(p/'verification.json')
    assert verify['candidate']==candidate and verify['result']=='passed' and verify['mode']=='incremental'
    assert sha((p/'verification.json').read_bytes())==end['verification_record_sha256']
    a=outer.index(native)
    return {'run':run,'start':fp(p/'start.json'),'result':fp(p/'result.json'),'owned':fp(p/'owned-terminal.json'),'closed_copy_record':fp(p/'closed-evidence-reconciliation.json'),'native_start':fp(p/'native-records/start.json'),'native_result':fp(p/'native-records/result.json'),'outer':fp(p/'full.log'),'native':fp(p/'native-records/output.log'),'verification':fp(p/'verification.json'),'started_utc':start['started_utc'],'completed_utc':end['completed_utc'],'outer_prefix':outer[:a].decode(),'outer_suffix':outer[a+len(native):].decode()}
rootpath=P/'shared-tail-inherited-type-qualification-20261104/comparison.json'
assert sha(rootpath.read_bytes())=='dc52b0cc515a7d058832f2a39bcf16147a62cfe9ffaf60281d7e76a077849387'
root=js(rootpath);observed={}
for name,rec in root['observation_files'].items():
    p=Path(rec['path']);b=p.read_bytes();assert len(b)==rec['bytes'] and sha(b)==rec['sha256']
    observed[name]=js(p);assert observed[name]['observed_utc']==rec['observed_utc']
prefixes=[('Tail61',L),('TailJ53',L),('TailI314',L),('TailF145',L),('J53',J),('J314',J),('J145',J),('I314',I),('I145',I),('F145',F)]
assert set(observed)=={p+'_'+s for p,_ in prefixes for s in ['pre','post']}
for prefix,candidate in prefixes:
    pre,post=observed[prefix+'_pre'],observed[prefix+'_post']
    assert pre['identity']==post['identity'] and post['unchanged']
    assert pre['identity']['candidate']==candidate and pre['identity']['clean']
    assert post['compared_to']['sha256']==fp(root['observation_files'][prefix+'_pre']['path'])['sha256']
    ident=pre['identity'];program(ident)
    assert len(re.findall(r'^#',Path(ident['program']['path']).read_text(),re.M))==len(ident['program']['names'])
    actualclosure=closure(candidate,ident['roots'])
    assert actualclosure['local_sources']==ident['local_sources']
    assert actualclosure['external_imports']==ident['direct_external_imports_of_local_closure']
    objects_for(ident,set(actualclosure['local_sources']))
ids={name:rec['identity'] for name,rec in observed.items()};current=ids['Tail61_pre']
source_receipt=P/'shared-tail-standards-source-continuation-20261104/independent-source-reconciliation.json'
assert sha(source_receipt.read_bytes())=='b6a55de4fd14358833075dab828976a0f4c1459b3c610b9b54eeb63f64376ece'
src=js(source_receipt)
public=[v['name'] for v in src['declarations'] if v['visibility']=='public']
assert len(public)==61 and public==program(current)
assert command('rev-parse',L+'^{tree}').decode().strip()==src['tree']=='43f1c15166931d4bd3e91e6dbf12059d0da1cfc2'
assert command('show','-s','--format=%P',L).decode().strip().split()==[J,T]
assert sorted(command('diff','--name-only',J,L).decode().splitlines())==sorted(src['scope'])
curclosure=closure(L,current['roots'])
assert len(curclosure['local_sources'])==9 and len(curclosure['edges'])==39 and len(curclosure['external_imports'])==19
assert len(objects_for(current,set(curclosure['local_sources'])))==27
common_fields=[k for k in ids['J53_pre'] if k!='candidate']
assert len(common_fields)==10
for producer,receiver,chain,expected_sources,expected_objects,label in [('J53','TailJ53',[],6,18,'J53'),('I314','TailI314',['J314'],27,81,'I314')]:
    base=ids[producer+'_pre']
    assert sorted(common_fields)==sorted(root[label]['all_exact_non_candidate_fields_compared'])
    for p in [producer,receiver]+chain:
        for phase in ['pre','post']:
            for key in common_fields: assert ids[p+'_'+phase][key]==base[key],(label,p,phase,key)
    assert len(base['local_sources'])==expected_sources and len(base['local_compiler_objects_and_traces'])==expected_objects
    assert sorted(base['local_compiler_objects_and_traces'])==root[label]['complete_artifact_keys']
eligible_roots=['Applications.Resources.ListCalls','Examples.FunctionalNotation','Examples.ListCalls','Examples.ListLibrary']
fclosure=closure(F,eligible_roots);selected=set(fclosure['local_sources'])
assert len(selected)==23 and len(fclosure['edges'])==58 and len(fclosure['external_imports'])==32
assert fclosure==closure(I,eligible_roots)==closure(J,eligible_roots)==closure(L,eligible_roots)
assert fclosure['external_imports']==root['F110']['direct_external_imports']
root_edges=[{'from':a,'to':b,'local':b.replace('.','/')+'.lean' in tree(F)} for a,b in root['F110']['source_import_edges']]
assert fclosure['edges']==sorted(root_edges,key=lambda e:(e['from'],e['to'],e['local']))
projections={}
for prefix in ['F145','I145','J145','TailF145']:
    for phase in ['pre','post']:
        key=prefix+'_'+phase;ident=ids[key]
        projected={k:ident[k] for k in ['clean','project','program','configuration','dependencies','runtime']}
        projected['local_sources']={p:ident['local_sources'][p] for p in sorted(selected)}
        projected['local_compiler_objects_and_traces']=objects_for(ident,selected)
        projected['roots']=eligible_roots
        projected['direct_external_imports_of_local_closure']=fclosure['external_imports']
        projections[key]=projected
assert all(p==projections['F145_pre'] for p in projections.values())
assert len(projections['F145_pre']['local_compiler_objects_and_traces'])==69
assert sorted(projections['F145_pre']['local_compiler_objects_and_traces'])==root['F110']['complete_artifact_keys']
for candidate in [F,I,J,L]:
    for path,rec in current['configuration'].items():
        b=source(candidate,path);assert len(b)==rec['bytes'] and sha(b)==rec['sha256']
assert [len(current[k]) for k in ['configuration','dependencies','runtime']]==[10,9,12]
for ident in ids.values():
    for key in ['configuration','dependencies','runtime']:assert ident[key]==current[key]
    assert all(d['status']=='' for d in ident['dependencies'].values())
manifest=json.loads(source(L,'lake-manifest.json'))
assert {p['name']:p['rev'] for p in manifest['packages']}=={n:d['head'] for n,d in current['dependencies'].items()}
assert source(L,'lean-toolchain').decode().strip()=='leanprover/lean4:v4.35.0'
full=bind_closed('shared-tail-full-attempt1-20261104',L,['./check.sh','--candidate','HEAD'])
actual=bind_closed('shared-tail-complete-public-statements61-20261104-attempt1',L,['lake','env','lean',current['program']['path']])
assert full['verification']['sha256']==actual['verification']['sha256']
for prefix in ['Tail61','TailJ53','TailI314','TailF145']:
    assert full['completed_utc']<observed[prefix+'_pre']['observed_utc']<actual['started_utc']<actual['completed_utc']<observed[prefix+'_post']['observed_utc']
runs={'61':'shared-tail-complete-public-statements61-20261104-attempt1','53':'shared-order-complete-public-statements53-20261104-attempt1','314':'shared-four-complete-public-statements314-20261104-attempt1','145':'foundation-complete-public-statements145-20261104-attempt1'}
blocks={n:block_inventory(runs[n],ids[p+'_pre']) for n,p in [('61','Tail61'),('53','J53'),('314','I314'),('145','F145')]}
positions=list(range(20,84))+list(range(100,146));selectedblocks=[blocks['145'][p-1] for p in positions]
names61=[b['name'] for b in blocks['61']];names53=[b['name'] for b in blocks['53']];names314=[b['name'] for b in blocks['314']];names110=[b['name'] for b in selectedblocks]
for key,names in [('current61',names61),('J53',names53),('I314',names314),('F110',names110)]:assert names==root[key]['names']
assert positions==root['F110']['positions_1_based']
insertion=[b['name'] for b in blocks['145'][:19]+blocks['145'][83:99]]
assert len(insertion)==35 and names314[-35:]==insertion
allnames=names61+names53+names314+names110
assert len(allnames)==len(set(allnames))==538
assert [p for p in ids['F145_pre']['local_sources'] if ids['F145_pre']['local_sources'][p]!=ids['TailF145_pre']['local_sources'][p]]==['Applications/Sorting/Merge.lean']
prior_records={
 'J_final':(P/'shared-order-standards-terminal-assessment-20261104/final-standards-assessment-932438a7.json','ec4bd6e8f30d81dc7676e105d5095ba4390f86548e143c8b0ecb2b7284d9d414'),
 'J_ledger':(P/'shared-order-standards-terminal-assessment-20261104/actual53-read-ledger.json','801098585a98ff633f744e86513d037ed45fc1390f88bedcf80041a019d9fa08'),
 'J_report':(CTRL/'reviews/permutation-order-standards-final-20261104.md','27379408402ad18d6c5e401f2c4e3854263d0a386ee5161759875a7be21b8d10'),
 'I_final':(P/'shared-four-standards-terminal-assessment-20261104/actual314-complete-standards-assessment.json','9c281a08f07b5be0bbc46e7f8eb68fee907b23c536aeb44f4bb3e4bfde0525f4'),
 'I_ledger':(P/'shared-four-standards-terminal-assessment-20261104/actual314-read-ledger.json','5e61784905b0f5a6134b64808b84970bb4e5024b05ba2cf5aa836b16fd56fa01'),
 'F_report':(CTRL/'reviews/shared-foundations-standards-terminal-assessment-20261104.md','5931dafe30f68151d81621ded0274643fb8145c5c57e644b6cca284fc634e141'),
 'F_ledger':(P/'shared-foundations-standards-terminal-assessment-20261104/actual145-read-progress.json','ef690b8f502c1ac4b70cd956cf682d2faa080b4b36151afc7cd05cd8a3a77a0b')}
for p,h in prior_records.values():assert sha(p.read_bytes())==h
jfinal=js(prior_records['J_final'][0]);assert jfinal['outcome']=='Passed' and jfinal['candidate']==J
l53,l314,l145=[js(prior_records[k][0]) for k in ['J_ledger','I_ledger','F_ledger']]
assert l53['candidate']==J and l53['complete'] and l53['actual_full_types_read']==53
assert l314['candidate']==I and l314['all_bytes_read'] and l314['complete_actual_types_read']==314 and l314['finding_count']==0
assert l145['candidate']==F and l145['read_progress']['complete'] and l145['read_progress']['types']==145 and not l145['findings']
for ledger,number,style in [(l53,'53','J'),(l314,'314','I'),(l145,'145','F')]:
    b=(P/runs[number]/'native-records/output.log').read_bytes();lines=b.splitlines(keepends=True);nextline=1
    assert sha(b)==(ledger['native_sha256'] if style=='J' else ledger['native']['sha256'])
    for chunk in ledger['read_chunks' if style=='J' else 'chunks']:
        a,z=(chunk['first'],chunk['last']) if style in ['J','I'] else (chunk['native_line_start'],chunk['native_line_end'])
        assert a==nextline;nextline=z+1;piece=b''.join(lines[a-1:z]);assert len(piece)==chunk['bytes'] and sha(piece)==chunk['sha256']
        if style=='I':assert chunk['read']
        if style=='F':assert chunk['read_status']=='complete bounded untruncated read'
    assert nextline==len(lines)+1
progress=js(OWN/'read-progress.json')
for kind,run in [('types',runs['61']),('full','shared-tail-full-attempt1-20261104')]:
    b=(P/run/'native-records/output.log').read_bytes();lines=b.splitlines(keepends=True);nextline=1
    chunks=sorted([v for v in progress['read_chunks'] if v['kind']==kind],key=lambda x:x['first_line'])
    for chunk in chunks:
        a,z=chunk['first_line'],chunk['last_line'];assert a==nextline;nextline=z+1;piece=b''.join(lines[a-1:z])
        assert sha(b)==chunk['file_sha256'] and len(piece)==chunk['bytes'] and sha(piece)==chunk['sha256'] and chunk['exit']==0
    assert nextline==len(lines)+1
native61=(P/runs['61']/'native-records/output.log').read_text();ls=native61.splitlines();ell=[]
for n,line in enumerate(ls,1):
    if '⋯' in line:
        assert line.count('⋯')==1
        if '@Fin.instOfNat' in line:category='Fin.instOfNat NeZero proof instance'
        else:
            assert re.fullmatch(r'\s*⋯\)+',line) and '@instOfNatAtLeastTwo' in '\n'.join(ls[max(0,n-6):n])
            category='ENNReal instOfNatAtLeastTwo proof instance'
        ell.append({'line':n,'category':category})
assert len(ell)==52 and Counter(v['category'] for v in ell)=={'Fin.instOfNat NeZero proof instance':43,'ENNReal instOfNatAtLeastTwo proof instance':9}
assert [e['line'] for e in ell]==js(P/runs['61']/'output-blocks.json')['ellipsis_lines']
log=(P/'shared-tail-full-attempt1-20261104/native-records/output.log').read_text();oldlog=(P/'shared-order-full-attempt1-20261104/native-records/output.log').read_text()
rowrule=r'^  (\S+): (\d+) logical declarations; (\d+) theorem declarations; (\d+) unsafe runtime declarations$'
def rows(s):
    allrows=re.findall(rowrule,s,re.M);assert len(allrows)==len({r[0] for r in allrows});return {n:[int(a),int(b),int(c)] for n,a,b,c in allrows}
newrows,oldrows=rows(log),rows(oldlog);assert len(newrows)==981 and len(oldrows)==978
assert all(newrows[n]==v for n,v in oldrows.items())
assert [sum(v[i] for v in newrows.values()) for i in range(3)]==[45809,25533,0]
added={n:v for n,v in newrows.items() if n not in oldrows}
assert added=={'Examples.PermutationTail':[29,20,0],'Examples.PermutationTailBoundary':[49,39,0],'Applications.Probability.PermutationTail':[24,23,0]}
assert log.count('Transitive axiom union: [propext, Classical.choice, Quot.sound]')==1
assert 'PASS: all 983 modules checked; exhaustive axiom audit passed.' in log
assert 'Integrity guard: hashed 2946 artifacts; 0 modules inconsistent' in log
warn=lambda s:Counter(l for l in s.splitlines() if l.startswith('warning: '))
newwarn=warn(log)-warn(oldlog);removed=warn(oldlog)-warn(log)
assert sum(newwarn.values())==7 and not removed and all('PermutationTail' in l and 'module' in l.lower() for l in newwarn)
assert root['conditions_retained_verbatim']==jfinal['original_reuse_conditions_retained_verbatim']
receipt={
 'reviewer':'/root/chapter02_standards','axis':'Standards','candidate':L,'recorded_utc':datetime.now(timezone.utc).isoformat(),
 'method':'Independent immutable-Git closure and complete saved observation-key comparison; every current output range and prior same-reader semantic-ledger range rehashed. No compiler, runtime recorder, live outputs, source or refs touched.',
 'root_comparison':fp(rootpath),'retained_source_assessment':fp(source_receipt),'current_read_ledger':fp(OWN/'read-progress.json'),
 'observation_files':{k:fp(v['path']) for k,v in root['observation_files'].items()},'all10_pre_post_pairs_identical':True,'all4_current_pairs_surround_actual61_after_full':True,
 'full_gate':full,'actual61':actual,'current61_closure':curclosure,'current61_artifact_keys':sorted(current['local_compiler_objects_and_traces']),
 'current61_blocks':blocks['61'],'current61_ellipsis':ell,'current61_ellipsis_counts':dict(Counter(v['category'] for v in ell)),
 'retained_pinned_ellipsis_api_assessment':jfinal['current_public_types']['pinned_api_reads'],'pinned_api_reuse_reason':'Identical compiler/runtime and exact mathlib revision to the fully read J evidence; every current occurrence independently classified in its full type.',
 'J53':{'producer':J,'receiver':L,'names':names53,'closure':closure(L,ids['TailJ53_pre']['roots']),'artifact_keys':sorted(ids['TailJ53_pre']['local_compiler_objects_and_traces']),'all10_noncandidate_fields_equal_across4_observations':True,'producer_blocks':blocks['53']},
 'I314':{'producer':I,'via_accepted':J,'receiver':L,'names':names314,'closure':closure(L,ids['TailI314_pre']['roots']),'artifact_keys':sorted(ids['TailI314_pre']['local_compiler_objects_and_traces']),'all10_noncandidate_fields_equal_across6_observations':True,'producer_blocks':blocks['314']},
 'F110':{'producer':F,'via_accepted':[I,J],'receiver':L,'names':names110,'positions':positions,'closure':fclosure,'artifact_keys':sorted(projections['F145_pre']['local_compiler_objects_and_traces']),'all8_selected_projections_equal':True,'producer_blocks':selectedblocks,'excluded35_names':insertion,'excluded_dependency_difference':'Applications/Sorting/Merge.lean','fresh35_I314_positions':[280,314]},
 'prior_same_reader_records':{k:fp(v[0]) for k,v in prior_records.items()},'all_producer_native_bytes_and_read_chunks_reconciled':True,
 'configuration':current['configuration'],'clean_dependency_observations':current['dependencies'],'runtime_components':current['runtime'],
 'full_audit':{'checked':983,'defining_rows':981,'kernel_safe':45809,'theorems':25533,'unsafe':0,'axioms':['propext','Classical.choice','Quot.sound'],'all978_predecessor_rows_exact':True,'new_rows':added},
 'warnings':{'prior_count':sum(warn(oldlog).values()),'current_count':sum(warn(log).values()),'new_only_import_advisories':dict(newwarn),'removed':dict(removed)},
 'qualified_public_account':{'current61':61,'J53':53,'I314':314,'F110':110,'distinct_total':538},'conditions_retained_verbatim':root['conditions_retained_verbatim'],
 'mechanical_result':'PASS; independently authored final semantic Standards disposition remains separate.',
 'limits':'Fingerprints supplement actual trusted stable-checkout guarded full gates and exclusive owned runs. They do not certify hostile-input/cache authenticity. Three receiving programs were observed, not executed anew. This gives statement-inspection qualification only, not a new producer audit or automatic acceptance.',
 'navigation_boundaries':progress['navigation_boundaries']}
target=OWN/'independent-execution-and-type-reconciliation.json';assert not target.exists();target.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'saved':fp(target),'public':receipt['qualified_public_account'],'audit':receipt['full_audit'],'ellipsis':receipt['current61_ellipsis_counts'],'warnings':receipt['warnings']},indent=2))
