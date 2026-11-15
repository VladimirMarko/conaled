"""Record completed acceptance and accurate local coverage; no Git/build action."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
B=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104'); C=B/'fdsa-control'
H=C/'provenance/chapter03-acceptance-20261105'; P=B/'conaled-ch01-review'
N='298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2'; TREE='ecb69c3918715cbe0682028cd8697dfcf3e463f9'
OLD='c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5'; Q='2da5708478a1d943a9214b5b386ec2db16cd9eca'
F=C/'provenance/chapter03-final-complete-full-attempt1-20261105'
T=C/'provenance/chapter03-final-complete-statements1391-attempt1-20261105'
I=C/'provenance/chapter03-immediate-verification-20261105'
S=C/'provenance/chapter03-final-statement-inputs-20261105'
def read(p): return json.loads(p.read_text())
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def ident(p):
    z=p.read_bytes(); return {'path':str(p),'bytes':len(z),'sha256':hashlib.sha256(z).hexdigest()}
def save(p,d):
    with p.open('x') as f: json.dump(d,f,indent=2); f.write('\n')
def git(p,*a): return subprocess.check_output(['git','-C',str(p),*a],text=True)
G=read(H/'root-gate-reconciliation.json'); FF=read(H/'fast-forward-result.json')
assert git(B/'conaled','rev-parse','HEAD').strip()==git(P,'rev-parse','HEAD').strip()==N
assert git(B/'conaled','rev-parse','HEAD^{tree}').strip()==TREE
assert FF['accepted_commit']==N and FF['accepted_tree']==TREE and FF['old']==OLD and FF['actual_exit']==0
assert read(H/'fast-forward-actual-tool.json')['exit_code']==0
assert G['all_required_preacceptance_gates_passed'] and G['all_source_writers_held']
bindings={r['path']:r for r in G['bound_files']}
for r in list(bindings.values()): assert ident(Path(r['path']))==r
extra=[H/x for x in ['root-gate-reconciliation.json','root-gate-actual-terminal.json','fast-forward-preflight.json','fast-forward-start.json','fast-forward-command-result.json','fast-forward-result.json','fast-forward-actual-tool.json','immediate-preflight.json']]
for d in (F,T,I):
    extra += [d/x for x in ['result.json','owned-terminal.json','actual-tool-terminal.json','closed-evidence-reconciliation.json','verification.json','full.log','native-records/start.json','native-records/result.json','native-records/output.log','actual-tool-launch.json','actual-closure-tool.json']]
    r=read(d/'result.json'); n=read(d/'native-records/result.json'); o=read(d/'owned-terminal.json'); a=read(d/'actual-tool-terminal.json')
    assert r['exit_code']==n['exit_code']==o['actual_exit']==a['exit_code']==0
    assert r['candidate']==r['final_head']==N and not r['final_status']
    assert a['chunk_id']==o['terminal_tool_chunk'] and n['lean_threads']=='1'
    assert not n['timed_out'] and n['recorder_error'] is None
    assert (d/'verification.json').read_bytes()==(F/'verification.json').read_bytes()
for p in extra: bindings[str(p)]=ident(p)
assert (P/'.lake/verification.json').read_bytes()==(F/'verification.json').read_bytes()
assert read(I/'native-records/result.json')['command']==['./check.sh','--verify-candidate','HEAD']
ids=re.findall(r'^\| (C03-\d{3}) \|',(C/'research/chapter03-obligations.md').read_text(),re.M)
assert ids==[f'C03-{n:03}' for n in range(1,84)]
axes={}
for axis,report,final,hold,receipt in [
    ('Standards','reviews/chapter03-standards.md','provenance/chapter03-standards-review-20261104/final1391-qualification-298.json','provenance/chapter03-standards-review-20261104/write-hold-final298.json','standards-completion-readback-receipt.json'),
    ('Spec','reviews/chapter03-spec.md','provenance/chapter03-spec-review-20261104/continuation-0136-015-final.json','provenance/chapter03-spec-review-20261104/final-bound-inputs.json','spec-completion-readback-receipt.json')]:
    axes[axis]={'outcome':G['axes'][axis]['outcome'],'unresolved':0,'full_saved_readback_and_hold':True,'candidate':N,'original_task_base':Q,'report':ident(C/report),'final_record':ident(C/final),'hold':ident(C/hold),'completion_readback_receipt':ident(H/receipt)}
A={'format':1,'recorded_utc':now(),'accepted_utc':FF['completed_utc'],'accepted_commit':N,'accepted_tree':TREE,'previous_accepted_commit':OLD,'original_whole_task_base':Q,'accepted_branch':'work/fdsa-book','approved_candidate_branch':'work/fdsa-ch03-integration','obligations':83,'obligation_ids':ids,'original_scope_paths':84,'original_formal_modules':80,'chapter03_formal_modules':78,'chapter03_public_names':1370,'accepted_XR_public_names':21,'actual_public_names':1391,'frozen_obligations':ident(C/'research/chapter03-obligations.md'),'correspondence_document':ident(P/'docs/research/fdsa-selection.md'),'independent_axes':axes}
A['full_check']={**G['full_check'],'candidate':N,'command':['./check.sh','--candidate','HEAD'],'directory':str(F),'result':ident(F/'result.json'),'owned_terminal':ident(F/'owned-terminal.json'),'closure':ident(F/'closed-evidence-reconciliation.json'),'verification':ident(F/'verification.json'),'audit_reconciliation':ident(F/'root-audit-reconciliation.json'),'complete_closed_log':True}
A['actual_public_types']={'candidate':N,'actual_exit':0,'count':1391,'chapter03_names':1370,'accepted_XR_names':21,'program':ident(S/'Statements1391-complete.lean'),'result':ident(T/'result.json'),'owned_terminal':ident(T/'owned-terminal.json'),'closure':ident(T/'closed-evidence-reconciliation.json'),'stable_pre_post_identity':True,'observation_reconciliation':ident(S/'observation-reconciliation.json'),'index':ident(S/'actual-type-block-index.json'),'comparison':ident(S/'prior-type-block-comparison.json'),'semantic_qualification':'Both independent axes completed all1391 current statements;1362 exact raw reuses and29 changed blocks fully assessed.'}
A['root_gate']=ident(H/'root-gate-reconciliation.json')
A['immediate_verification']={'candidate':N,'actual_exit':0,'command':['./check.sh','--verify-candidate','HEAD'],'lean_threads':'1','directory':str(I),'result':ident(I/'result.json'),'owned_terminal':ident(I/'owned-terminal.json'),'actual_terminal':ident(I/'actual-tool-terminal.json'),'closure':ident(I/'closed-evidence-reconciliation.json'),'full_log':ident(I/'full.log'),'matching_full_verification':True,'verification':ident(I/'verification.json'),'complete_closed_log_readback':'58f272 actual0'}
A['fast_forward']={**FF,'result':ident(H/'fast-forward-result.json'),'actual_tool_result':ident(H/'fast-forward-actual-tool.json'),'preflight':ident(H/'fast-forward-preflight.json'),'start':ident(H/'fast-forward-start.json')}
A.update({'bound_files':list(bindings.values()),'chapter03_accepted':True,'all27_chapters_and_appendices_complete':False,'whole_project_audit_counts_not_new_book_results':True,'prior_accepted_chapters_and_XR_preserved':True,'historical_failed_and_incomplete_run_outcomes_preserved':True,'nix_waiver_only':True,'exact_pins_proof_rules_native_profile_and_validation_gates_unchanged':True,'no_push_or_GitHub_mutation':True,'checkpoint_durability_status_at_recording':'Pending creation, verification, upload and exposure of0137. Record actual durability separately without changing this acceptance evidence.','next_chapter':'Chapter4 Binary Trees; source work begins after acceptance checkpoint is durable.'})
coverage={'recorded_utc':A['recorded_utc'],'candidate':N,'original_task_base':Q,'frozen_obligations':A['frozen_obligations'],'status':'All83 obligations accepted through the exact candidate and two independent whole-scope axes','rows':[{'id':x,'status':'accepted','candidate':N} for x in ids],'acceptance_record':'provenance/chapter03-acceptance-20261105/acceptance.json','preserved_source_matrix':'provenance/chapter03-spec-review-20261104/obligation-assessment-83-final298.json','historical_source_matrix_status_not_rewritten':True}
previous=read(C/'provenance/chapter03-activation-20261104/focused-progress-before0136.json')
oldrows={r['name']:r for r in previous['all_closed_runs']}; assert len(oldrows)==102
runs=[]
for op in sorted((C/'provenance').glob('*/owned-terminal.json')):
    d=op.parent
    if not (d.name.startswith('chapter03-') or d.name.startswith('affine-recurrence-')): continue
    o=read(op); r=read(d/'result.json'); native=read(d/'native-records/result.json')
    assert r['candidate']==r['final_head']==o['candidate'] and not r['final_status']
    assert r['exit_code']==o['actual_exit']==native['exit_code']
    if d.name not in oldrows:
        actual=read(d/'actual-tool-terminal.json')
        assert actual['exit_code']==o['actual_exit'] and actual['chunk_id']==o['terminal_tool_chunk']
    z=ident(d/'full.log'); assert z['bytes']==r['log_size_bytes'] and z['sha256']==r['log_sha256']
    row={'name':d.name,'candidate':r['candidate'],'exit':r['exit_code'],'owned_session':o['owned_session'],'terminal_tool_chunk':o['terminal_tool_chunk'],'full_log_bytes':z['bytes'],'full_log_sha256':z['sha256']}
    if d.name in oldrows: assert row==oldrows[d.name]
    runs.append(row)
assert len(runs)==107 and set(oldrows)<={r['name'] for r in runs}
newruns=[r for r in runs if r['name'] not in oldrows]; assert len(newruns)==5
progress={'recorded_utc':A['recorded_utc'],'accepted_head':N,'qualified_candidate':N,'original_task_base':Q,'obligations':83,'chapter03_accepted':True,'closed_runs':107,'all_closed_runs':runs,'new_closed_runs_since0136':newruns,'interrupted_development_runs':previous['interrupted_development_runs'],'transport_terminal_unavailable_runs':previous['transport_terminal_unavailable_runs'],'compiler_live':False,'all_source_writers_held':True,'checkpoint_scope':'Chapter3 accepted at exact298 after successful full normal check/audit,1391 actual statement qualifications, independent Standards andSpec PASS with zero unresolved findings, and immediate verification followed by guarded local fast-forward. All83 originalQ obligations,84paths,80formalmodules (78C3+2XR),1370C3+21acceptedXR public names. Historical full preparation38 SIGKILL remains failed with unknown cause; old drift2 unknown and trace1 recorded native failure without transport terminal remain unchanged.107 actual owned closures secured. Standalone current recovery with exact74refs9worktrees and unchanged298-entry native kit; later chapters remain pending.'}
note='''## Chapter 3 accepted; checkpoint 0137 preparation — 2026-11-05

Chapter 3 Selection is accepted on `work/fdsa-book` at `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2` (tree `ecb69c3918715cbe0682028cd8697dfcf3e463f9`). The fixed original base remains Q `2da5708478a1d943a9214b5b386ec2db16cd9eca`; all 83 obligations are accepted. The scope contains 78 Chapter 3 modules and 1,370 public names, plus the two separately accepted XR modules and 21 names. All 1,391 current statements completed actual qualification and independent review.

The final full normal check passed: 1,109 checked modules, 1,107 audit rows, 50,135 kernel-safe declarations including 29,316 theorems, zero unsafe declarations, and exactly `propext`, `Classical.choice`, `Quot.sound`. These are whole-project counts. Both independent Standards and Spec axes passed with zero unresolved findings, retaining both corrected findings and the original scope. Immediate `./check.sh --verify-candidate HEAD` actually passed; the exact local fast-forward completed at 2026-11-05T01:57:13.031861+00:00, 8.368546 seconds after verification completion. The other 73 references and all worktree statuses were preserved.

Acceptance and item-level coverage are recorded in `provenance/chapter03-acceptance-20261105/acceptance.json` and `coverage.json`. All 107 owned executions are closed with actual terminals. The earlier failed audit and the two separately recorded incomplete histories retain their original outcomes. All exact pins, proof restrictions, native profile, normal/fresh rules and resource guards remain mandatory. No push or GitHub mutation occurred.

Checkpoint 0137 creation, verification, upload and exposure are pending. All source and review writers remain held; Chapter 4 preparation is read-only until durability is secured. Chapter 4 Binary Trees is next, with all 76 frozen obligations and 11 exercises retained. Earlier dated entries below describe their historical states.

'''
updates={}
for rel in ['CURRENT.md','STATUS.md','tickets/FDSA-003.md','tickets/INDEX.md','reviews/chapter03-round1.md']:
    text=(C/rel).read_text(); assert '## Chapter 3 accepted; checkpoint 0137 preparation' not in text
    first,rest=text.split('\n',1); out=first+'\n\n'+note+rest.lstrip('\n')
    if rel=='tickets/FDSA-003.md':
        for sentence in ['Definitions and proofs implemented without admissions or additional axioms.','Checked uses and statement review retained.','Applicable immutable-candidate build and exhaustive proof audit passed.','Independent Standards and Spec reviews have no unresolved findings.']:
            target='- [ ] '+sentence; assert out.count(target)==1; out=out.replace(target,'- [x] '+sentence)
    if rel=='tickets/INDEX.md':
        target='| FDSA-003 | Selection | in progress | FDSA-002 |'; assert out.count(target)==1
        out=out.replace(target,'| FDSA-003 | Selection | accepted; checkpoint 0137 pending | FDSA-002 |')
    updates[rel]=out
text=(C/'reviews/README.md').read_text()
target='Chapter 1 is accepted at 07e480f6ec9958d4975bb90151005b84f2907614.\nThe shared foundation and all subsequent chapters remain pending. Do not interpret a saved checkpoint or a\nsuccessful focused Lean command as whole-chapter acceptance.\n'
assert target in text
updates['reviews/README.md']=text.replace(target,'Chapter 1, the shared foundation, Chapter 2 and the separate XR prefix have\nrecorded acceptance. Chapter 3 is now accepted at\n298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2; its complete evidence is in\n`provenance/chapter03-acceptance-20261105/acceptance.json`. Remaining book\nobligations retain their local ticket gates. A saved checkpoint or successful\nfocused Lean command does not by itself establish whole-chapter acceptance.\n')
progresspath=C/'provenance/chapter03-activation-20261104/focused-progress-before0137.json'
for p in [H/'acceptance.json',H/'coverage.json',progresspath,H/'control-update-preflight.json',H/'control-update-result.json']: assert not p.exists(),str(p)
save(H/'control-update-preflight.json',{'recorded_utc':A['recorded_utc'],'before':{rel:ident(C/rel) for rel in updates},'accepted_commit':N,'project_source_changes':False,'pending_checkpoint_upload':True})
save(H/'acceptance.json',A); save(H/'coverage.json',coverage); save(progresspath,progress)
for rel,out in updates.items(): (C/rel).write_text(out)
save(H/'control-update-result.json',{'recorded_utc':now(),'after':{rel:ident(C/rel) for rel in updates},'acceptance':ident(H/'acceptance.json'),'coverage':ident(H/'coverage.json'),'progress':ident(progresspath),'completed_ticket_gates':5,'last_combined_durability_gate_pending':True})
print(json.dumps({'acceptance':ident(H/'acceptance.json'),'coverage':ident(H/'coverage.json'),'progress':ident(progresspath),'actual_closed_runs':len(runs),'new_runs':newruns,'updated_canonical_controls':list(updates),'chapter03_accepted':True,'checkpoint_durability_pending':True},indent=2))
