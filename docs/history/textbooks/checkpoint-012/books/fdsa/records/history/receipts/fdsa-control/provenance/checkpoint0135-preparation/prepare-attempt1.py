
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,tarfile,difflib
b=Path('/workspace/scratch/b4a17a285e23/fdsa-restored-20261104');c=b/'fdsa-control'
old=c/'provenance/checkpoint0134-preparation';p=c/'provenance/checkpoint0135-preparation'
oldname='conaled-fdsa-0134-random-selection-path-progress';name='conaled-fdsa-0135-selection-trace-and-statement-progress'
def ident(q):
 with q.open('rb') as f:return {'bytes':q.stat().st_size,'sha256':hashlib.file_digest(f,'sha256').hexdigest()}
def put(q,s):
 with q.open('x') as f:f.write(s)
def write(q,v):put(q,json.dumps(v,indent=2)+'\n')
expected={'verify-checkpoint.py':{'bytes':14509,'sha256':'a789802715353faea3eda0749f0ef2ab5973062e4c95241be139e5bcfa0beadc'},'capture.py':{'bytes':4806,'sha256':'d45520e954cccad0c4bd9f0bb5dd6b831bce09e21e4d2dd08ba01ece3a6e22a6'},'run-stage.py':{'bytes':2394,'sha256':'374d9a679e31563aad9e85337fe80a22e68c7f032cc6c655049cb12b73ebbacd'}}
for n,x in expected.items():assert ident(old/n)==x,n
archive=b/'checkpoints'/(oldname+'.tar.gz')
assert ident(archive)=={'bytes':38083636,'sha256':'2d70445d6636cb3e86828e5838e978b6282eb2fdfd24bdbd3e38eb6710fbcb70'}
u=json.loads((old/'upload.json').read_text());post=json.loads((old/'post-upload-hash.json').read_text())
assert u['status']=='succeeded' and u['library_file_id']=='libfile_5ec3dbda67688191af137be4694522b1' and post['post_upload_hash_matched']
with tarfile.open(archive,'r:gz') as tf:
 member=tf.getmember(oldname+'/MANIFEST.json');mf=tf.extractfile(member).read();j=json.loads(mf)
assert j['checkpoint']==oldname and len(j['refs'])==74 and len(j['worktrees'])==9
assert not p.exists()
p.mkdir();(p/'previous-manifest-0134.json').write_bytes(mf)
def change_ids(s):
 for a,z in [('conaled-fdsa-0134-random-selection-path-progress',name),('conaled-fdsa-0133-selection-integration-and-endpoint-progress',oldname),('checkpoint0134-preparation','checkpoint0135-preparation'),('checkpoint0133-preparation','checkpoint0134-preparation'),('previous-manifest-0133.json','previous-manifest-0134.json'),('focused-progress-before0134.json','focused-progress-before0135.json')]:s=s.replace(a,z)
 return s
ver=change_ids((old/'verify-checkpoint.py').read_text())
anchor='                    "reviews/chapter03-round1.md"}'
assert ver.count(anchor)==1
ver=ver.replace(anchor,'                    "reviews/chapter03-round1.md", "reviews/chapter03-standards.md",\n                    "reviews/chapter03-spec.md"}')
transport_gate='''# Keep the completed failed command distinct from its missing transport terminal.
transport = capture["transport_terminal_unavailable_runs"]
assert len(transport) == 1
for item in transport:
    assert item["name"] == "chapter03-random-selection-trace-focused-attempt1-20261104"
    directory = control / "provenance" / item["name"]
    reconciliation_path = control / item["reconciliation"]
    expected_reconciliation = {key: item[key] for key in ("bytes", "sha256")}
    assert identity(reconciliation_path) == expected_reconciliation
    assert actual["fdsa-control/" + item["reconciliation"]] == expected_reconciliation
    reconciliation = read(reconciliation_path)
    assert reconciliation["candidate"] == item["candidate"] == "0fa717b8c150e0ae6edb9d538dd2b86d73f02b2d"
    assert reconciliation["owned_session"] == item["original_exec_session_id"] == 81642
    assert reconciliation["transport_terminal_exit"] is None
    assert reconciliation["transport_terminal_tool_chunk"] is None
    assert item["transport_terminal_exit"] is None
    assert reconciliation["actual_qualified_command_exit_from_completed_native_recorder"] == 1
    assert reconciliation["outer_recorder_recorded_child_exit"] == 1
    assert not reconciliation["owned_terminal_credit"]
    assert not reconciliation["focused_pair_pass"] and not reconciliation["chapter_acceptance_credit"]
    assert reconciliation["complete_native_and_outer_logs_preserved"]
    assert reconciliation["project_lock_observation"]["exclusive_nonblocking_acquired_and_released"]
    assert reconciliation["project_lock_observation"]["global_process_absence_not_claimed"]
    assert not (directory / "owned-terminal.json").exists()
    assert item["name"] not in {row["name"] for row in capture["closed_development_runs"]}
    assert item["name"] not in {row["name"] for row in interrupted}
    result = read(directory / "result.json")
    native = read(directory / "native-records/result.json")
    assert result["candidate"] == result["final_head"] == item["candidate"] and not result["final_status"]
    assert result["exit_code"] == native["exit_code"] == item["recorded_native_exit"] == 1
    assert native["lean_threads"] == "1" and not native["timed_out"] and native["recorder_error"] is None
    assert native["command"] == result["command"][result["command"].index("--") + 1:]
    for relative, row in reconciliation["records"].items():
        expected_identity = {key: row[key] for key in ("bytes", "sha256")}
        assert identity(control / relative) == expected_identity
        assert actual["fdsa-control/" + relative] == expected_identity
    outer_bytes = (directory / "full.log").read_bytes()
    body = (directory / "native-records/output.log").read_bytes()
    prefix = (directory / "outer-prefix.log").read_bytes()
    suffix = (directory / "outer-suffix.log").read_bytes()
    assert [len(prefix), len(body), len(suffix)] == [127, 12920, 157]
    assert outer_bytes == prefix + body + suffix
    assert identity(directory / "full.log") == {"bytes": result["log_size_bytes"], "sha256": result["log_sha256"]}

'''
anchor='kit = control / "tooling/unified-native-kit-4.35.0"'
assert ver.count(anchor)==1;ver=ver.replace(anchor,transport_gate+anchor)
anchor='          "interrupted_runs_preserved_without_terminal_or_credit": len(interrupted),'
assert ver.count(anchor)==1
ver=ver.replace(anchor,anchor+'\n          "known_recorded_failures_without_transport_terminal": len(transport),')
cap=change_ids((old/'capture.py').read_text())
anchor="'reviews/chapter03-round1.md','tickets/FDSA-003.md','tickets/INDEX.md'"
assert cap.count(anchor)==1
cap=cap.replace(anchor,"'reviews/chapter03-round1.md','reviews/chapter03-standards.md','reviews/chapter03-spec.md','tickets/FDSA-003.md','tickets/INDEX.md'")
anchor="'interrupted_development_runs':progress['interrupted_development_runs'],"
assert cap.count(anchor)==1
cap=cap.replace(anchor,anchor+"'transport_terminal_unavailable_runs':progress['transport_terminal_unavailable_runs'],")
stage=change_ids((old/'run-stage.py').read_text())
for fname,data in [('verify-checkpoint.py',ver),('capture.py',cap),('run-stage.py',stage)]:
 compile(data,fname,'exec');put(p/fname,data)
diff=''.join(difflib.unified_diff((old/'verify-checkpoint.py').read_text().splitlines(True),ver.splitlines(True),fromfile='checkpoint0134/verify-checkpoint.py',tofile='checkpoint0135/verify-checkpoint.py'))
put(p/'verifier-scope-diff.patch',diff)
diffs=''.join(''.join(difflib.unified_diff((old/n).read_text().splitlines(True),s.splitlines(True),fromfile='checkpoint0134/'+n,tofile='checkpoint0135/'+n)) for n,s in [('capture.py',cap),('run-stage.py',stage)])
put(p/'helper-scope-diffs.patch',diffs)
readme="""# Checkpoint 0135 preparation

This standalone compact recovery retains accepted Chapter2 and XR unchanged.
Original Chapter3 whole-task base remains Q2da5708; XR is the separately
accepted shared exception and receiving comparison point. All83 obligations
and conditional accepted source/input reuse remain within the same fullscope.

No compiler outcome or current draft/hold status is predicted by this helper
preparation. Final progress must bind the actual sources, type observations,
independent review progress, every owned terminal and all remaining gates.
The current trace-attempt1 has complete native and recorded-child failure1,
but its original transport terminal is unavailable. Its full original records
must be preserved separately from the owned-terminal-gated closed-run list.
No owned terminal, focused pass or acceptance credit may be synthesized.
The older drift-attempt2 remains separately unknown at the child level.

Verifier changes retain all existing payload/ref/worktree/accepted C2/XR/
closed-owned-run/drift-unknown/native-kit gates. All74 prior refs remain with
the existing allowed ancestry-preserving advances and no additions. A new
strict gate binds the exact trace transport-loss reconciliation, all original
closed records, one-thread command, complete prefix/body/suffix logs and
absence of an owned terminal. It requires the distinct known recorded failure
and null transport outcome, without adding it to either old classification.
The two specifically authorized in-progress Chapter3 independent report paths
join the explicit mutable control allowlist; no accepted review is mutable.
Capture adds that distinct transport record field. Stage runner identifiers
alone change. Exact scope diffs are provided for independent inspection.

All writers must hold before capture/creation/verification/upload. Every stage
requires its own actually observed terminal. Final Chapter3 actual type
qualification, complete normal check and exhaustive audit, independent
Standards and Spec, immediate verify and exact accepted fast-forward remain.
Root owns the sole serial one-thread compiler; pins/profile, proof restrictions,
normal/fresh and resource guards are unchanged. No compiler, restore, fsck,
installation, hydration or acceptance action is selected for packaging.

Recovery requires no earlier task checkpoint. The unchanged external public
baseline asset has its immutable URL and exact restoration checks.
"""
put(p/'README.md',readme)
files={n:ident(p/n) for n in ['verify-checkpoint.py','capture.py','run-stage.py','verifier-scope-diff.patch','helper-scope-diffs.patch','README.md']}
assert ident(c/'checkpoint_compact.py')=={'bytes':10520,'sha256':'5e72098a4b07a80c6861cdaf14f4d2234e33cd7b6a0a79170bae762599cbe078'}
assert ident(c/'restore_compact.py')=={'bytes':5244,'sha256':'23cdb74849a049df746c9f03af0e90ab261fd4fdc97bf2ea8f8088ffe9159376'}
origin={'recorded_utc':datetime.now(timezone.utc).isoformat(),'previous_archive':{'path':str(archive),**ident(archive)},'previous_upload_library_file_id':u['library_file_id'],'previous_post_upload_hash_matched':True,'exact_root_manifest_member':oldname+'/MANIFEST.json','extracted_manifest':ident(p/'previous-manifest-0134.json'),'previous_verified_receipt':{'path':str(old/'integrity.json'),**ident(old/'integrity.json')},'previous_capture':{'path':str(old/'capture.json'),**ident(old/'capture.json')},'preparation_files':files,'original_creator':ident(c/'checkpoint_compact.py'),'original_restorer':ident(c/'restore_compact.py'),'changes':'Identifier updates, separate strict known-native-failure/missing-transport-terminal gate, two explicitly mutable in-progress Chapter3 independent report paths. Existing gates retained.','parent_full_verifier_read':['f2f641','a597ae'],'parent_helpers_read':'537b32','capture_not_started':True,'current_source_snapshot_not_claimed':True,'independent_inspection_pending':True}
write(p/'previous-manifest-origin.json',origin)
print(json.dumps({'directory':str(p),'files':files,'previous_manifest':ident(p/'previous-manifest-0134.json'),'capture_started':False,'independent_inspection_pending':True},indent=2))
