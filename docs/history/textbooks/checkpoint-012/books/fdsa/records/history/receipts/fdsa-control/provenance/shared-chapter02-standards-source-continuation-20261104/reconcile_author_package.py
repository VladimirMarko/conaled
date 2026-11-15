from pathlib import Path
import datetime,hashlib,json,re,subprocess
BASE=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104');CTRL=BASE/'fdsa-control';REPO=BASE/'conaled-ch02-top-down';P=CTRL/'provenance/shared-chapter02-source-integration-20261104';OWN=CTRL/'provenance/shared-chapter02-standards-source-continuation-20261104'
C='2da5708478a1d943a9214b5b386ec2db16cd9eca';L='726cb9a9b9ff4444a7614383de4fb336e8804aa7';Z='4b5dbfa07288acc73f25c27838d3fb2f78e77d71';R='07e480f6ec9958d4975bb90151005b84f2907614'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','--no-optional-locks','-C',str(REPO),*a])
def j(n):return json.loads((P/n).read_bytes())
def ident(p):
 b=p.read_bytes();return {'path':str(p.relative_to(CTRL)),'bytes':len(b),'lines':len(b.splitlines()),'sha256':sha(b)}
receipt=j('receipt.json');assert receipt['candidate']==C
for row in receipt['payloads_excluding_receipt']:
 b=(P/row['path']).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'];assert len(b.splitlines())==row['lines'] or row['path']=='baseline-L-tree.bin' and row['lines']==0 and b.count(b'\n')==0
assert len(receipt['payloads_excluding_receipt'])==35
base=j('baseline.json');result=j('result.json');ms=j('merge-state.json');res=j('resolution-plan.json');bound=j('bound-inputs.json')
assert base['HEAD']==base['accepted_L']==L and base['incoming_Z']==Z and base['intended_branch_absent']
assert base['status_porcelain_v1']==base['index_diff']==base['working_diff']==''
current_refs=dict(line.split(' ',1) for line in git('for-each-ref','--format=%(refname) %(objectname)').decode().splitlines())
oldrefs=base['existing_refs'];assert len(oldrefs)==66 and len(current_refs)==67
assert all(current_refs[k]==v for k,v in oldrefs.items()) and set(current_refs)-set(oldrefs)=={'refs/heads/work/fdsa-chapter02-integration'} and current_refs['refs/heads/work/fdsa-chapter02-integration']==C
assert current_refs['refs/heads/work/fdsa-book']==L and result['preservation']['post_refs']==current_refs
bases=git('merge-base','--all',L,Z).decode().splitlines();assert bases==base['actual_merge_bases']==result['actual_merge']['actual_merge_bases'] and len(bases)==7
for x in result['ancestor_checks']:
 assert x['candidate']==C and x['actual_exit']==0
 assert subprocess.run(['git','--no-optional-locks','-C',str(REPO),'merge-base','--is-ancestor',x['ancestor'],C],capture_output=True).returncode==0
assert git('ls-tree','-rz','--full-tree',L)==(P/'baseline-L-tree.bin').read_bytes()
for stem,exit_value in [('branch',0),('merge',1),('commit',0)]:
 start=j(stem+'-start.json');end=j(stem+'-result.json');assert end['exit']==exit_value and start['argv']==end['argv'] and start['started_utc']==end['started_utc']
assert j('add-result.json')['exit']==0 and j('precommit-check.json')['diff_check']['exit']==0
assert ms['HEAD']==L and ms['MERGE_HEAD']==Z and len(ms['stages'])==6
expected_conflicts=['SquareApplications.lean','docs/research/fdsa-reconstruction-map.md'];assert ms['conflicts']==expected_conflicts
for q in ms['stages']:
 b=(P/q['saved']).read_bytes();assert b==git('cat-file','blob',q['blob']) and len(b)==q['bytes'] and sha(b)==q['sha256']
 if q['stage']==2:assert b==git('show',L+':'+q['path'])
 if q['stage']==3:assert b==git('show',Z+':'+q['path'])
map_text=git('show',L+':docs/research/fdsa-reconstruction-map.md').decode();assert len(res['map_replacements'])==9
for q in res['map_replacements']:
 assert map_text.count(q['old'])==1,q['label'];map_text=map_text.replace(q['old'],q['new'])
assert map_text.encode()==git('show',C+':docs/research/fdsa-reconstruction-map.md')
for q in res['source_files_written']:
 before=(P/q['pre_resolution_copy']).read_bytes();after=(P/q['resolved_copy']).read_bytes();assert len(before)==q['before_bytes'] and sha(before)==q['before_sha256'];assert len(after)==q['after_bytes'] and sha(after)==q['after_sha256'];assert after==git('show',C+':'+q['path'])
for label,left in [('source_diff',L),('full_R_diff_identity',R)]:
 b=git('diff','--binary',left,C);assert len(b)==result[label]['bytes'] and sha(b)==result[label]['sha256']
 if label=='source_diff':assert b==(P/'source.diff').read_bytes()
assert git('diff','--name-status',R,C)==(P/'full-scope-name-status.txt').read_bytes()
for k in ['all81_source_rows','all97_statement_closure_sources']:
 for q in result[k]:
  b=git('show',C+':'+q['path']);assert len(b)==q['bytes'] and sha(b)==q['sha256'];assert git('rev-parse',C+':'+q['path']).decode().strip()==q['git_blob']
assert len(result['all81_source_rows'])==81 and len(result['all97_statement_closure_sources'])==97
textZ=git('show',Z+':docs/research/fdsa-sorting.md').decode();textC=git('show',C+':docs/research/fdsa-sorting.md').decode()
alias_rows=re.findall(r'^\| `([^`]+)` \| `([^`]+)` \| `([^`]+)` \|',textC,re.M)
# The full source/document correspondence is retained by exact unchanged bytes;
# recorded aliases are individually matched to their unchanged referenced sources.
for q in result['documentary']['alias_definitions']:
 assert git('rev-parse',C+':'+q['path']).decode().strip()==q['candidate_blob']==git('rev-parse',Z+':'+q['path']).decode().strip()
assert len(result['documentary']['alias_definitions'])==60
aliases={q['alias'] for q in result['documentary']['alias_definitions']}
def refs(text):return sorted({m for m in re.findall(r'`([^`]+)`',text) if '.' in m and m.split('.',1)[0] in aliases})
assert refs(textC)==refs(textZ) and len(refs(textC))==448
assert sha(('\n'.join(refs(textC))+'\n').encode())==result['documentary']['alias_reference_LF_sha256']
current_bound_mismatches=[]
for q in bound['files']:
 b=(CTRL/q['path']).read_bytes()
 if len(b)!=q['bytes'] or sha(b)!=q['sha256']:current_bound_mismatches.append(q['path'])
assert not current_bound_mismatches,current_bound_mismatches
assert len(bound['files'])==68
# Saved worktree metadata only; no other worktree's files or outputs are opened.
def wt(s):
 d={}
 for block in s.strip().split('\n\n'):
  lines=block.splitlines();path=lines[0].removeprefix('worktree ');d[path]={x.split(' ',1)[0]:x.split(' ',1)[1] for x in lines[1:] if x.startswith(('HEAD ','branch '))}
 return d
before=wt(base['worktrees_porcelain']);after=wt(result['preservation']['worktrees_porcelain']);assert len(before)==len(after)==15
active=str(BASE/'conaled-ch01-review');assert [p for p in before if before[p]!=after[p]]==[active]
assert after[active]=={'HEAD':C,'branch':'refs/heads/work/fdsa-chapter02-integration'}
record={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/chapter02_standards','candidate':C,'status':'Independent author history/package/source reconciliation passed; no receiving validation credit','all35_payloads_match_receipt':True,'all68_bound_inputs_exact':True,'all66_prior_refs_preserved_new67th_only':True,'accepted_book_still_L':True,'ordered_parents_L_Z':git('show','-s','--format=%P',C).decode().strip().split(),'actual_seven_merge_bases':bases,'all_recorded_ancestry_checks_independently_reproduced':True,'baseline_and_actual_commands':{'baseline_clean':True,'branch':0,'ordinary_ort_merge':1,'actual_conflicts':expected_conflicts,'all6_stage_payloads_exact_blob_and_stage2L_stage3Z':True,'add':0,'staged_diff_check':0,'commit':0,'no_merge_simulation_by_reviewer':True},'all9_map_replacements_reproduce_entire_current_map':True,'all3_resolution_pre_post_payloads_bound':True,'all81_scope_and97_closure_rows_independently_match':True,'all60_alias_source_blobs_exact_Z':True,'all448_alias_qualified_references_exact_Z':True,'saved_other14_worktree_HEAD_branch_records_unchanged':True,'tracked_preservation':{'existing_L_paths':1610,'unchanged_L_paths':1607,'outside_original81_scope_L_paths':1576,'all_outside_scope_preserved':True},'full_R_diff':result['full_R_diff_identity'],'L_diff':result['source_diff'],'author_package_inputs':[ident(P/n) for n in ['handoff.md','receipt.json','result.json','baseline.json','bound-inputs.json','merge-state.json','resolution-plan.json','author-readback.json']],'read_boundary':'Complete handoff/receipt, actual commands, complete stage metadata and nine replacement texts read; full large source/hash arrays independently reconstructed. Prior full source/semantic assessments retained by exact bytes. No claim of a fresh human read of all2727result JSON lines or all12061source.diff lines.','receiving_type_full_audit_credit':0,'reviewer_compiler_process_cache_source_ref_changes_or_runtime_output_captures':False}
out=OWN/'independent-author-package-reconciliation.json';assert not out.exists();out.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(ident(out),indent=2))
