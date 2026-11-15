from pathlib import Path
from collections import Counter
import json,re,hashlib,subprocess
B=Path("/workspace/scratch/b4a17a285e23/fdsa-restored-20261104");C=B/"fdsa-control";D=C/"provenance/shared-tail-spec-terminal-20261104"
L="726cb9a9b9ff4444a7614383de4fb336e8804aa7";J="932438a765340d69fa6402f6abd17def6ec28d13"
def sha(b):return hashlib.sha256(b).hexdigest()
def meta(p):
 p=Path(p);b=p.read_bytes();return {"path":str(p.relative_to(C)) if p.is_relative_to(C) else str(p),"bytes":len(b),"lines":len(b.splitlines()),"sha256":sha(b)}
def read(p):return json.loads(Path(p).read_bytes())
fd=C/"provenance/shared-tail-full-attempt1-20261104";jd=C/"provenance/shared-order-full-attempt1-20261104"
raw=(fd/"native-records/output.log").read_bytes();old=(jd/"native-records/output.log").read_bytes()
assert sha(raw)=="bd5bd2c170cac6a84f855806595fce60981b86eb1660c52c0d3a7a0b9d149749"
assert sha(old)=="3910b2bd1613b6f4b7473549bee3fdc4c5bdf1cd6230f40cb3a3904ccf03e16a"
txt=raw.decode();prev=old.decode()
rx=re.compile(r"^  (\S+): (\d+) logical declarations; (\d+) theorem declarations; (\d+) unsafe runtime declarations$",re.M)
def rows(t):
 matches=rx.findall(t);d={m[0]:list(map(int,m[1:])) for m in matches};assert len(d)==len(matches);return d
current=rows(txt);prior=rows(prev)
assert len(current)==981 and len(prior)==978 and all(current[k]==v for k,v in prior.items())
new={k:v for k,v in current.items() if k not in prior}
assert new=={"Examples.PermutationTail":[29,20,0],"Examples.PermutationTailBoundary":[49,39,0],"Applications.Probability.PermutationTail":[24,23,0]}
totals=[sum(v[i] for v in current.values()) for i in range(3)]
assert totals==[45809,25533,0]
assert "Transitive axiom union: [propext, Classical.choice, Quot.sound]" in txt
assert "Proof audit PASSED: every kernel-safe project declaration uses only the three permitted foundational axioms." in txt
assert "PASS: all 983 modules checked; exhaustive axiom audit passed." in txt
assert "Integrity guard: hashed 2946 artifacts; 0 modules inconsistent" in txt
warnings=lambda t:Counter(x for x in t.splitlines() if x.startswith("warning: "))
cw,pw=warnings(txt),warnings(prev)
assert sum(cw.values())==591 and sum(pw.values())==584 and not(pw-cw)
added=list((cw-pw).elements());assert len(added)==7
assert all("imports "+chr(96) in x and "designed for use with the module system" in x for x in added)
assert all(re.match(r"warning: (Applications/Probability/PermutationTail|Examples/PermutationTail(?:Boundary)?)\.lean:",x) for x in added)
warning_sources=sorted({re.match(r"warning: (.*?\.lean):",x).group(1) for x in pw})
source_ids={}
for p in warning_sources:
 a=subprocess.check_output(["git","-C",str(B/"conaled-ch02-top-down"),"rev-parse",J+":"+p]).decode().strip()
 b=subprocess.check_output(["git","-C",str(B/"conaled-ch02-top-down"),"rev-parse",L+":"+p]).decode().strip()
 assert a==b,p
 source_ids[p]=a
rc=read(fd/"audit-row-and-warning-comparison.json")
assert rc["full_audit_rows"]==current and rc["new_audit_rows"]==new and rc["all_prior_audit_rows_exact"]==978
assert rc["warnings"]=={"prior_count":584,"current_count":591,"removed_headers":[],"added_headers":added}
outer=(fd/"full.log").read_bytes();result=read(fd/"result.json");nresult=read(fd/"native-records/result.json")
assert outer.count(raw)==1 and sha(outer)==result["log_sha256"] and len(outer)==result["log_size_bytes"]
assert result["candidate"]==result["final_head"]==L and result["exit_code"]==nresult["exit_code"]==0 and result["final_status"]==""
assert nresult["passed"] and not nresult["timed_out"] and nresult["recorder_error"] is None
assert read(fd/"owned-terminal.json")["actual_exit"]==0
verification=read(fd/"verification.json")
assert verification["candidate"]==L and verification["mode"]=="incremental" and verification["result"]=="passed"
assert "Lean (version 4.35.0" in verification["compiler"] and "eb6cafb7290e8bd5f2937522d8d804f58f02bafc" in verification["compiler"]
assert len(verification["dependencies"])==9
jtypes=read(C/"provenance/shared-order-spec-terminal-20261104/actual53-complete-type-assessment.json")
for a in jtypes["pinned_API_reads"]:print("API_RECORD",json.dumps(a))
print("AUDIT",json.dumps({"rows":len(current),"totals":totals,"new":new,"warnings":len(added),"old_warning_sources_exact":len(source_ids)}))
out={"reviewer":"Independent Spec","candidate":L,"accepted_predecessor":J,"full_log_read_ledger":meta(D/"full-log-read-complete.json"),
 "raw_logs":[meta(fd/"full.log"),meta(fd/"native-records/output.log"),meta(jd/"native-records/output.log")],
 "full_native_lines_read":2484,"all_outer_wrappers_read":True,"closed_metadata_read_tools":["0a47a7","825541","665084"],
 "all981_audit_rows_reparsed":True,"all978_predecessor_rows_exact":True,"new_audit_rows":new,
 "kernel_safe_declarations":45809,"theorems":25533,"unsafe_runtime_excluded":0,"checked_modules":983,
 "permitted_axiom_union":["propext","Classical.choice","Quot.sound"],
 "postguard":{"supported_artifacts":2946,"inconsistent_modules":0},
 "preguard":{"supported_artifacts":2937,"expected_new_cold_Tail_modules":3},
 "build":{"actual_built":["Applications.Probability.PermutationTail","Examples.PermutationTailBoundary","Examples.PermutationTail","SquareApplications"],"lake_jobs":10028,"lake_jobs_are_not_audit_counts":True,"incremental_compilation_seconds":292.38,"audit_seconds":244.85},
 "warnings":{"current":591,"retained_exact_J_headers":584,"added_module_import_advisories":added,"removed_or_changed_headers":[],"all_prior_warning_source_blobs_equal":source_ids},
 "verification":meta(fd/"verification.json"),
 "closed_evidence":[meta(fd/p) for p in ["request.json","start.json","result.json","owned-terminal.json","native-records/start.json","native-records/result.json","closed-evidence-reconciliation.json","audit-and-build-summary.json","audit-row-and-warning-comparison.json"]],
 "mode":"Normal incremental; exact pins/checker/profile retained, no fresh trigger, prior accepted full fresh baseline retained.",
 "original_source_private_generated_scope_retained":True,
 "outcome":"Full gate evidence passed and completely assessed; combined final Spec outcome awaits separately saved current/inherited statement qualifications and final readback."}
p=D/"full-gate-assessment.json";assert not p.exists();p.write_text(json.dumps(out,indent=2)+"\n");print("SAVED",json.dumps(meta(p)))
