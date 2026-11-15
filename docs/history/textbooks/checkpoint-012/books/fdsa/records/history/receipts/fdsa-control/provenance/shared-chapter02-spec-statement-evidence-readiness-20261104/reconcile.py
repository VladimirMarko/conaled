"""Read only immutable Git and secured records; write only this review's result."""
import collections
import datetime
import hashlib
import json
import pathlib
import re
import subprocess

CTRL = pathlib.Path(__file__).resolve().parents[2]
REPO = CTRL.parent / 'conaled-ch02-top-down'
OWN = pathlib.Path(__file__).resolve().parent
PKG = CTRL / 'provenance/shared-chapter02-statement-evidence-readiness-20261104'
def read(path):
    return (CTRL / path).read_bytes()
def sha(data):
    return hashlib.sha256(data).hexdigest()
def js(path):
    return json.loads(read(path))
def ident(path):
    a = read(path)
    return dict(path=path, bytes=len(a), LF_count=a.count(b'\n'), sha256=sha(a))
def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args])
def tree(commit):
    out = {}
    for row in git('ls-tree', '-r', '-z', commit).split(b'\0'):
        if row:
            meta, path = row.split(b'\t', 1)
            out[path.decode()] = meta.split()[2].decode()
    return out
def names(program):
    return re.findall(r'^#check\s+@?([\w.]+)\s*$', program, re.M)
def imports(text):
    # Independent comment/string erasure; preserve newlines for command starts.
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2
            elif text.startswith('-/', i): depth -= 1; i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            if text[i] == '\\': i += 2
            elif text[i] == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i); i = len(text) if end < 0 else end
        elif text.startswith('/-', i): depth = 1; out.append(' '); i += 2
        elif text[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(text[i]); i += 1
    return [x for row in re.findall(r'^(?:public\s+)?import\s+([^\n]+)', ''.join(out), re.M) for x in row.split()]

j = json.loads((PKG / 'inventory.json').read_bytes())
bound = json.loads((PKG / 'bound-inputs.json').read_bytes())
bound_verified = []
for e in bound['files']:
    a = read(e['path'])
    assert (len(a), a.count(b'\n'), sha(a)) == (e['bytes'], e['lines'], e['sha256']), e['path']
    bound_verified.append(ident(e['path']))
old = js('provenance/chapter02-spec-source-preparation-20261104/current-public-type-disposition-4b5dbfa0.json')
rows = j['public_rows']
assert len(rows) == len(old['per_name_dispositions']) == 1763
assert len({r[0] for r in rows}) == 1763
original = {r['name']: r for r in old['per_name_dispositions']}
sources = {r['id']: r for r in j['source_ids']}
ids = {r[0]: n for n, r in enumerate(rows, 1)}
groups = {k: set(v['name_ids']) for k, v in j['groups'].items()}
dispositions = {'qualified_historical_actual_type_fully_read': 'historical920', 'actual_current_type_fully_read_and_qualified': 'actualZ815', 'accepted_R_declaration_exact_source_segment_retained': 'acceptedR28'}
for r in rows:
    o = original[r[0]]
    assert (sources[r[1]]['path'], r[2], r[3], r[4]) == (o['source'], o['kind'], dispositions[o['disposition']], o.get('historical_run'))
for key, group in j['groups'].items():
    assert len(groups[key]) == len(group['name_ids']) == group['count']
    assert sha(('\n'.join(sorted(rows[n-1][0] for n in groups[key]))+'\n').encode()) == group['sorted_names_final_LF_sha256']
    assert group['credit_granted'] == 0
for k in ['historical920', 'actualZ815', 'acceptedR28']:
    assert groups[k] == {n for n, r in enumerate(rows, 1) if r[3] == k}
assert set.union(*(groups[k] for k in ['historical920','actualZ815','acceptedR28'])) == set(range(1,1764))

program_records, program_ids = {}, {}
for key, p in j['producer_programs'].items():
    data = read(p['path']); text = data.decode(); ns = names(text)
    assert sha(data) == p['sha256']
    assert len(ns) == len(set(ns)) == p['public_names']
    order = [ids[n] for n in ns]
    assert order == p['program_order_name_ids']
    assert imports(text) == p['imports']
    assert [list(x) for x in re.findall(r'^set_option\s+(pp\.\w+)\s+(\w+)',text,re.M)] == p['printing_options']
    for pos, n in enumerate(order,1): assert rows[n-1][5][key] == pos
    program_ids[key] = order
    program_records[key] = dict(identity=ident(p['path']), names=len(ns), ordered_names_sha256=sha(('\n'.join(ns)+'\n').encode()), actual_run_bound=p['actual_run_bound'])
for n, row in enumerate(rows,1):
    for program, pos in row[5].items(): assert program_ids[program][pos-1] == n
F = set(program_ids['F145'][19:83] + program_ids['F145'][99:145])
M = {n for n in program_ids['I314'] if sources[rows[n-1][1]]['path']=='Examples/MergeCosts.lean'}
I = set(program_ids['I314']) - M
J, T = set(program_ids['J53']), set(program_ids['Tail61'])
expected = {'F110_unchanged_closure_conditional':F,'I242_unchanged_closure_conditional':I,'J53_unchanged_closure_conditional':J,'Tail61_prepared_only_conditional':T,'I72_Growth_changed':M,'actual405_same_closure_conditional':F|I|J,'possible466_including_unexecuted_Tail61':F|I|J|T,'complete_predecessor538_name_union':F|set(program_ids['I314'])|J|T,'conditional1297_remainder_not_a_run':set(range(1,1764))-(F|I|J|T)}
for k, s in expected.items(): assert groups[k] == s
assert len(F)+len(I)+len(J)+len(T) == len(F|I|J|T) == 466
assert len(M)==72 and M <= set(program_ids['Z815'])
partition = {}
for key in ['historical920','actualZ815','acceptedR28']:
    s=groups[key]; partition[key] = dict(total=len(s),in_predecessor538=len(s&expected['complete_predecessor538_name_union']),outside_predecessor538=len(s-expected['complete_predecessor538_name_union']),same_closure405=len(s&(F|I|J)),conditional466=len(s&(F|I|J|T)),conditional1297=len(s-(F|I|J|T)))
assert partition == j['group_partition']

commits=j['commits']; Z=commits['historical_C2_Z']; L=commits['frozen_unaccepted_Tail_L']; R=commits['original_full_review_base_R']
trees={c:tree(c) for c in [Z,L,R,commits['accepted_F'],commits['accepted_I'],commits['accepted_J']]}
texts={}
for sid,s in sources.items():
    path=s['path']; data=git('show',f'{Z}:{path}'); texts[path]=data.decode()
    assert (trees[Z][path],len(data),sha(data),trees[L].get(path),trees[R].get(path)) == (s['Z_blob'],s['bytes'],s['sha256'],s['L_blob'],s['R_blob']),path
for s in old['current_source_inventory']:
    data=git('show',f'{Z}:{s["path"]}')
    assert (len(data),sha(data)) == (s['bytes'],s['sha256'])
graph={p:imports(t) for p,t in texts.items()}
def closure(root):
    seen=set(); ext=set(); todo=[root]
    while todo:
        path=todo.pop()
        if path in seen: continue
        seen.add(path)
        for module in graph[path]:
            target=module.replace('.','/')+'.lean'
            if target in trees[Z]:
                assert target in graph,(root,target)
                todo.append(target)
            else: ext.add(module)
    return seen,ext,sum(len(graph[x]) for x in seen)
roots={sources[r[1]]['path'] for r in rows}; by_path={v['path']:k for k,v in sources.items()}
assert len(roots)==71 and roots==set(j['defining_root_closures'])
closures={p:closure(p) for p in roots}
for p,(local,external,edges) in closures.items():
    record=j['defining_root_closures'][p]
    assert sorted(by_path[x] for x in local)==record['local_source_ids']
    assert sorted(external)==record['direct_external_imports']
    assert edges==record['static_import_edges']
    assert sum(sources[r[1]]['path']==p for r in rows)==record['public_names']
assert set.union(*(v[0] for v in closures.values()))==set(texts)
assert sorted(set.union(*(v[1] for v in closures.values())))==j['complete_external_import_union']
root_relations=collections.Counter('exact' if trees[L].get(p)==trees[Z][p] else 'new' if p not in trees[L] else 'changed' for p in roots)
assert root_relations=={'exact':24,'new':46,'changed':1}
growth='Applications/Resources/Growth.lean'
affected={p:sum(sources[r[1]]['path']==p for r in rows) for p,cl in closures.items() if growth in cl[0]}
assert affected==j['Growth']['future_full_union_affected_root_counts'] and sum(affected.values())==388
for label,selected,commit in [('F110',F,commits['accepted_F']),('I242',I,commits['accepted_I']),('J53',J,commits['accepted_J']),('Tail61',T,L)]:
    for n in selected:
        p=sources[rows[n-1][1]]['path']
        assert all(trees[commit].get(x)==trees[Z][x] for x in closures[p][0]),(label,p)
assert {x for x in closures['Examples/MergeCosts.lean'][0] if trees[commits['accepted_I']].get(x)!=trees[Z][x]}=={growth}

snapshots={}; producers={}
for key,p in j['actual_producers'].items():
    pre=js(p['pre_inputs']); post=js(p['post_inputs']); a=pre['identity']
    assert a==post['identity'] and a['candidate']==p['candidate'] and a['clean']
    assert a['program']['sha256']==j['producer_programs'][key]['sha256']
    assert a['program']['names']==[rows[n-1][0] for n in program_ids[key]]
    data=read(p['native_log'])
    assert (len(data),data.count(b'\n'),sha(data))==(p['native_bytes'],p['native_lines'],p['native_sha256'])
    counts=dict(roots=len(a['roots']),sources=len(a['local_sources']),objects_hashes_traces=len(a['local_compiler_objects_and_traces']),configs=len(a['configuration']),dependencies=len(a['dependencies']),runtime_components=len(a['runtime']))
    assert counts==p['observed_counts']; snapshots[key]=a
    producers[key]=dict(pre=ident(p['pre_inputs']),post=ident(p['post_inputs']),native=ident(p['native_log']),counts=counts,exact_saved_pre_post=True)
comparisons={}
z=snapshots['Z815']
for key in ['F145','I314','J53']:
    b=snapshots[key]; declared=j['saved_Z_vs_other_producer_comparisons'][key]
    common=set(z['local_sources'])&set(b['local_sources']); changed=sorted(p for p in common if z['local_sources'][p]!=b['local_sources'][p])
    keys=set(z['local_compiler_objects_and_traces'])&set(b['local_compiler_objects_and_traces']); different=sorted(p for p in keys if z['local_compiler_objects_and_traces'][p]!=b['local_compiler_objects_and_traces'][p])
    dep={p:{'Z':z['dependencies'][p],'other':b['dependencies'][p]} for p in z['dependencies'] if z['dependencies'][p]!=b['dependencies'][p]}
    for field,value in [('common_sources',len(common)),('source_differences',changed),('common_artifact_keys',len(keys)),('exact_artifact_keys',len(keys)-len(different)),('different_artifact_keys',different),('configs_exact',z['configuration']==b['configuration']),('runtime_exact',z['runtime']==b['runtime']),('actual_dependency_record_differences',dep)]: assert declared[field]==value,(key,field)
    assert len(dep)==9 and all(v['Z']['head']==v['other']['head'] and v['Z']['status']==v['other']['status']=='' and v['Z']['path']!=v['other']['path'] for v in dep.values())
    comparisons[key]=dict(common_sources=len(common),changed_sources=changed,common_artifact_keys=len(keys),exact_artifact_keys=len(keys)-len(different),different_artifact_keys=different,all_nine_actual_dependency_paths_differ=True,configs_exact=True,runtime_exact=True)
gaps=j['observation_coverage_gaps']
assert sorted(set(texts)-set(z['local_sources']))==gaps['outside_Z815_local_sources']
assert sorted(set(texts)-set.union(*(set(a['local_sources']) for a in snapshots.values())))==gaps['outside_all_four_recent_snapshot_local_sources']
assert sorted(set(j['complete_external_import_union'])-set(z['direct_external_imports_of_local_closure']))==gaps['additional_external_imports_beyond_Z815']

historical=[]; old_names=[]; qualified=set(); excluded=set()
for h in j['historical12_producers']:
    data=read(h['program']); ns=names(data.decode()); order=[ids[n] for n in ns]
    assert sha(data)==h['program_sha256'] and order==h['program_order_name_ids']
    assert [list(x) for x in re.findall(r'^set_option\s+(pp\.\w+)\s+(\w+)',data.decode(),re.M)]==h['actual_printing_options']
    old_names+=order; qualified.update(h['historical_qualified920_name_ids']); excluded.update(h['excluded_or_reinspected_name_ids'])
    historical.append(dict(run=h['run'],candidate=h['candidate'],names=len(order),program_sha256=sha(data),printing_options=h['actual_printing_options'],qualified920=len(h['historical_qualified920_name_ids']),excluded=len(h['excluded_or_reinspected_name_ids']),terminal_boundary=h['terminal_boundary']))
assert len(old_names)==len(set(old_names))==941 and qualified==groups['historical920'] and len(excluded)==21
assert excluded==set(j['old941_to920']['seven_Growth_names_ids']+j['old941_to920']['fourteen_missing_terminal_name_ids'])==set(program_ids['Z815'][793:814])
assert program_ids['Z815'][814]==j['old941_to920']['explicit_named_instance_position815']
assert rows[program_ids['Z815'][814]-1][0]=='Examples.UniformQuickSortMean.instFintypeLabel'
ledger=js('provenance/chapter02-spec-source-preparation-20261104/actual815-read-progress-complete-before-disposition.json')
data=read(j['actual_producers']['Z815']['native_log']); lines=data.splitlines(keepends=True); next_line=1
for chunk in ledger['chunks']:
    lo,hi=chunk['native_lines']; selected=b''.join(lines[lo-1:hi])
    assert lo==next_line and (len(selected),sha(selected))==(chunk['bytes'],chunk['sha256']); next_line=hi+1
assert len(ledger['chunks'])==44 and next_line==11651 and ledger['semantic_type_numbers_fully_assessed']==list(range(1,816))
for record in ledger['semantic_records']:
    data=read(record['path']); assert (len(data),sha(data))==(record['bytes'],record['sha256'])
assert len(ledger['semantic_records'])==21

result=dict(recorded_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),reviewer='/root/chapter02_spec',scope=j['full_original_scope'],commits=commits,receiving_credit=0,findings=[],all_assertions_passed=True,bound_inputs_rehashed=len(bound_verified),bound_inputs=bound_verified,original_disposition=ident('provenance/chapter02-spec-source-preparation-20261104/current-public-type-disposition-4b5dbfa0.json'),all_1763_rows_source_kind_group_run_and_program_positions_match=True,all_81_original_source_identities_match=True,programs=program_records,group_counts={k:len(s) for k,s in groups.items()},partition=partition,static_closure=dict(defining_roots=len(roots),local_sources=len(texts),external_names=len(j['complete_external_import_union']),root_relations=dict(root_relations),growth_affected_roots=affected,growth_affected_names=388),all72_merge_costs=[dict(name=rows[n-1][0],source=sources[rows[n-1][1]]['path'],kind=rows[n-1][2],positions=rows[n-1][5]) for n in sorted(M)],producer_saved_inputs=producers,saved_Z_comparisons=comparisons,historical12=historical,historical941_to920=dict(original941=941,retained920=920,excluded21=21,reinspected_Z_positions=[794,814],added_instance_position=815),own_Z815_complete_read_ledger_rebound=dict(ledger=ident('provenance/chapter02-spec-source-preparation-20261104/actual815-read-progress-complete-before-disposition.json'),chunks=44,semantic_record_files=21,native_lines=11650,native_bytes=874568,types=815,new_type_read_or_receiving_credit=False),observation_coverage_gaps=gaps,boundary='Mechanical complete mapping/source/input reconciliation retaining prior full semantic reads; no new compiler, runtime scan, source/ref change, receiving candidate, type transfer, or acceptance.')
output=OWN/'reconciliation.json'
assert not output.exists(), 'Never overwrite a prior result'
output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(path=str(output),bytes=output.stat().st_size,sha256=sha(output.read_bytes()),rows=1763,groups=result['group_counts'],all_assertions_passed=True)))
