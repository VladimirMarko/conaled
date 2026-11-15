from pathlib import Path
import json,hashlib,re,subprocess,datetime
BASE=Path("/workspace/scratch/b4a17a285e23/fdsa-restored-20261104")
C=BASE/"fdsa-control"; REPO=BASE/"conaled-ch02-top-down"
D=C/"provenance/shared-order-spec-terminal-20261104"
J="932438a765340d69fa6402f6abd17def6ec28d13"
I="312aafb4446b995ff5542041b4e2e074f776db1e"
F="f17cc6b1a2bf44215b16202ed0fcee2b5c130761"
def sha(b):return hashlib.sha256(b).hexdigest()
def meta(p):
 p=Path(p);b=p.read_bytes()
 return {"path":str(p),"bytes":len(b),"lines":len(b.splitlines()),"sha256":sha(b)}
def read(p):return json.loads(Path(p).read_bytes())
def git(*args):return subprocess.check_output(["git","-C",str(REPO),*args])
def blob(c,p):return git("show",c+":"+p)
def source_id(b):
 return {"bytes":len(b),"sha256":sha(b),"git_blob":hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()}
trees={}
def closure(candidate,roots):
 if candidate not in trees:trees[candidate]=set(git("ls-tree","-r","--name-only",candidate).decode().splitlines())
 todo=list(roots); sources={}; edges=[];external=set()
 while todo:
  mod=todo.pop()
  path=mod.replace(".","/")+".lean"
  if path in sources:continue
  raw=blob(candidate,path);sources[path]=source_id(raw)
  for line in raw.decode().splitlines():
   line=line.split("--",1)[0].strip()
   m=re.match(r"^(?:(?:public|meta)\s+)?import\s+(.+)$",line)
   if not m:continue
   for imported in m.group(1).split():
    assert re.fullmatch(r"[A-Za-z0-9_'.]+",imported),(path,line)
    edges.append([mod,imported])
    if imported.replace(".","/")+".lean" in trees[candidate]:todo.append(imported)
    else:external.add(imported)
 return {"sources":sources,"external":sorted(external),"edges":sorted(edges)}
cmp_path=C/"provenance/shared-order-inherited-type-qualification-20261104/comparison.json"
cmp=read(cmp_path)
assert cmp["recipient"]==J and cmp["accepted_predecessor"]==I and cmp["Foundation_producer"]==F
obs={}
for label,m in cmp["observation_files"].items():
 p=Path(m["path"]);r=p.read_bytes()
 assert len(r)==m["bytes"] and sha(r)==m["sha256"],label
 v=json.loads(r);assert v["observed_utc"]==m["observed_utc"];obs[label]=v
expected_identity={"candidate","clean","project","program","configuration","dependencies","runtime","roots","local_sources","local_compiler_objects_and_traces","direct_external_imports_of_local_closure"}
for label,v in obs.items():
 a=v["identity"];assert set(a)==expected_identity
 expect=J if label.startswith("J") else I if label.startswith("I") else F
 assert a["candidate"]==expect and a["clean"] is True
 assert len(a["configuration"])==10 and len(a["dependencies"])==9 and len(a["runtime"])==12
 assert all(x["status"]=="" for x in a["dependencies"].values())
for pair in ["J53","J314","J145","I314","I145","F145"]:
 a,b=obs[pair+"_pre"],obs[pair+"_post"]
 assert a["identity"]==b["identity"] and b["unchanged"] is True,pair
 pm=meta(cmp["observation_files"][pair+"_pre"]["path"])
 assert b["compared_to"]["path"]==pm["path"] and b["compared_to"]["bytes"]==pm["bytes"] and b["compared_to"]["sha256"]==pm["sha256"]
def dt(s):return datetime.datetime.fromisoformat(s)
r53=C/"provenance/shared-order-complete-public-statements53-20261104-attempt1"
full=read(C/"provenance/shared-order-full-attempt1-20261104/result.json")
tr=read(r53/"result.json");tn=read(r53/"native-records/result.json")
assert tr["exit_code"]==tn["exit_code"]==0 and tn["passed"] is True and not tn["timed_out"] and tn["recorder_error"] is None
assert tr["candidate"]==tr["final_head"]==J and tr["final_status"]==""
assert read(r53/"start.json")["initial_head"]==J and read(r53/"start.json")["initial_status"]==""
assert tn["lean_threads"]=="1" and tr["progress_bookkeeping_errors"]==[]
for group in ["J53","J314","J145"]:
 assert dt(full["completed_utc"])<dt(obs[group+"_pre"]["observed_utc"])<dt(tr["started_utc"])<dt(tr["completed_utc"])<dt(obs[group+"_post"]["observed_utc"])
s53=obs["J53_pre"]["identity"]; si=obs["I314_pre"]["identity"];sj=obs["J314_pre"]["identity"]
# Every receiving/producer I314 key is compared, except the explicitly bound candidate identifier.
for key in expected_identity-{"candidate"}:assert si[key]==sj[key],key
assert len(si["local_sources"])==27 and len(si["local_compiler_objects_and_traces"])==81
# Compare three independently derived immutable import graphs to the recorded input maps.
closure_records={}
for label,candidate,identity in [("J53",J,s53),("I314",I,si),("J314",J,sj)]:
 cr=closure(candidate,identity["roots"])
 assert cr["sources"]==identity["local_sources"],label
 assert cr["external"]==identity["direct_external_imports_of_local_closure"],label
 expected=set()
 for p in cr["sources"]:
  for ext in [".olean",".olean.hash",".trace"]:expected.add(".lake/build/lib/lean/"+p[:-5]+ext)
 assert set(identity["local_compiler_objects_and_traces"])==expected,label
 for p,m in identity["configuration"].items():
  raw=blob(candidate,p);assert {"bytes":len(raw),"sha256":sha(raw)}==m
 closure_records[label]=cr
assert closure_records["I314"]==closure_records["J314"]
froots=["Applications.Resources.ListCalls","Examples.FunctionalNotation","Examples.ListCalls","Examples.ListLibrary"]
fclosures={candidate:closure(candidate,froots) for candidate in [F,I,J]}
assert fclosures[F]==fclosures[I]==fclosures[J]
fc=fclosures[J];assert len(fc["sources"])==23 and len(fc["edges"])==58 and len(fc["external"])==32
assert sorted(cmp["F110"]["source_import_edges"])==fc["edges"] and cmp["F110"]["direct_external_imports"]==fc["external"]
fkeys=set()
for p in fc["sources"]:
 for ext in [".olean",".olean.hash",".trace"]:fkeys.add(".lake/build/lib/lean/"+p[:-5]+ext)
assert len(fkeys)==69 and sorted(fkeys)==cmp["F110"]["complete_artifact_keys"]
assert sorted(si["local_compiler_objects_and_traces"])==cmp["I314"]["complete_artifact_keys"]
def project110(ident):
 assert set(fc["sources"])<=set(ident["local_sources"])
 assert fkeys<=set(ident["local_compiler_objects_and_traces"])
 assert set(froots)<=set(ident["roots"])
 return {**{k:ident[k] for k in ["clean","project","program","configuration","dependencies","runtime"]},
         "roots":froots,"local_sources":{p:ident["local_sources"][p] for p in sorted(fc["sources"])},
         "local_compiler_objects_and_traces":{p:ident["local_compiler_objects_and_traces"][p] for p in sorted(fkeys)},
         "direct_external_imports_of_local_closure":fc["external"]}
proj={k:project110(obs[k]["identity"]) for k in ["F145_pre","F145_post","I145_pre","I145_post","J145_pre","J145_post"]}
assert all(v==proj["F145_pre"] for v in proj.values())
for k in proj:assert proj[k]["local_sources"]==fc["sources"]
# Same qualified profile and actual dependency records also connect the new53 and inherited input observations.
for ident in [si,sj,obs["F145_pre"]["identity"],obs["J145_pre"]["identity"]]:
 for key in ["configuration","dependencies","runtime","project"]:assert s53[key]==ident[key],key
# Every program and every printed producer block has exact bytes and original order.
type_runs={
 "J53":r53,
 "I314":C/"provenance/shared-four-complete-public-statements314-20261104-attempt1",
 "F145":C/"provenance/foundation-complete-public-statements145-20261104-attempt1"}
blocks={};run_records={}
for label,folder in type_runs.items():
 ix=read(folder/"output-blocks.json");program=Path(ix["program"]["path"]).read_bytes()
 assert len(program)==ix["program"]["bytes"] and sha(program)==ix["program"]["sha256"]
 names=re.findall(r"^#check\s+@(\S+)\s*$",program.decode(),re.M)
 for option in ["set_option pp.universes true","set_option pp.explicit true","set_option pp.fullNames true"]:assert option in program.decode()
 assert names==[b["name"] for b in ix["blocks"]]
 ident=obs[label+"_pre"]["identity"]
 assert names==ident["program"]["names"] and sha(program)==ident["program"]["sha256"]
 raw=(folder/"native-records/output.log").read_bytes();assert sha(raw)==ix["native_output"]["sha256"] and len(raw)==ix["native_output"]["bytes"]
 lines=raw.splitlines(keepends=True);end=0
 for b in ix["blocks"]:
  actual=b"".join(lines[b["start_line"]-1:b["end_line"]])
  assert actual==raw[b["byte_start"]:b["byte_end_exclusive"]] and b["byte_start"]==end
  assert len(actual)==b["bytes"] and sha(actual)==b["sha256"];end=b["byte_end_exclusive"]
 assert end==len(raw)
 result=read(folder/"result.json");native=read(folder/"native-records/result.json")
 assert result["exit_code"]==native["exit_code"]==0 and native["passed"] is True and native["recorder_error"] is None and not native["timed_out"]
 assert result["candidate"]==result["final_head"]==ident["candidate"] and result["final_status"]==""
 assert dt(obs[label+"_pre"]["observed_utc"])<dt(result["started_utc"])<dt(result["completed_utc"])<dt(obs[label+"_post"]["observed_utc"])
 blocks[label]=ix["blocks"]
 run_records[label]={"program":meta(ix["program"]["path"]),"native_output":meta(folder/"native-records/output.log"),"index":meta(folder/"output-blocks.json"),"result":meta(folder/"result.json"),"native_result":meta(folder/"native-records/result.json"),"all_block_bytes_and_order_checked":True}
positions=list(range(20,84))+list(range(100,146));fselected=[blocks["F145"][i-1] for i in positions]
assert positions==cmp["F110"]["positions_1_based"] and [b["name"] for b in fselected]==cmp["F110"]["names"]
assert [b["name"] for b in blocks["I314"]]==cmp["I314"]["names"]
names=[b["name"] for b in blocks["J53"]+blocks["I314"]+fselected];assert len(names)==len(set(names))==477
source=read(C/"provenance/shared-order-spec-source-continuation-20261104/source-assessment.json")
decl=source["declaration_inventory"]["named_declarations"]
print("DECLARATION_SAMPLE",json.dumps(decl[0]))
# Explicit prior semantic-read records are revalidated, not replaced by a second reading or a count.
prior=read(C/"provenance/shared-four-spec-terminal-20261104/final-disposition.json")
assert prior["outcome"]=="PASS" and prior["candidate"]==I and prior["actual314"]["every_full_actual_type_read"] is True and prior["qualified110"]["same_reviewer_actual_producer_type_read_retained"] is True
retained=[]
for entry in prior["source_and_historical_evidence"]+prior["new_own_evidence"]:
 actual=meta(C/entry["path"])
 assert actual["bytes"]==entry["bytes"] and actual["sha256"]==entry["sha256"],entry["path"]
 retained.append(actual)
out={"reviewer":"Independent Spec","recipient":J,"I_producer":I,"F_producer":F,
"source_scope_unchanged":True,"read_only_method":"Independent immutable Git closure reconstruction and complete saved-record equality; no compiler, runtime capture or output mutation.",
"comparison_record":meta(cmp_path),"observation_records":{k:meta(v["path"]) for k,v in cmp["observation_files"].items()},
"actual53":{"source_count":6,"object_count":18,"full_identity_pre_post_exact":True,"all53_full_types_read_in_separate_ledger":True,"new_native_warnings":0},
"I314":{"all_non_candidate_identity_fields_compared":sorted(expected_identity-{"candidate"}),"full_four_way_equality":True,"closure":closure_records["J314"],"supported_artifact_keys":sorted(si["local_compiler_objects_and_traces"]),"complete_record_count":81},
"F110":{"producer_positions":positions,"selected_blocks":fselected,"closure":fc,"supported_artifact_keys":sorted(fkeys),"all_six_F_I_J_projected_records_exact":True,"excluded35_have_actual_I314_types":True},
"J53_closure":closure_records["J53"],"common_counts":{"configs":10,"actual_clean_dependency_records":9,"runtime_components":12},
"programs_and_actual_producers":run_records,"current_distinct_account":477,"retained_prior_semantic_evidence":retained,
"actual_run_ownership_basis":"Qualified stock native full J guard/build/postguard/audit precedes all three exclusive pre observations; one actual53 run; all three exact post observations follow; producer I/F full and type lineage retained.",
"fingerprint_boundary":"This compares every supported selected artifact/hash/trace key and exact dependency path, with no normalization or whole-environment equivalence claim.",
"conditions":cmp["conditions_retained_verbatim"],
"semantic_transfer":"Mechanical prerequisite satisfied independently. Current full53 semantic review and explicit final Spec REUSE disposition are recorded separately; this script alone is not an approval."}
p=D/"independent-input-reconciliation.json";assert not p.exists();p.write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n")
print(json.dumps({"result":meta(p),"I314_sources":len(closure_records["J314"]["sources"]),"I314_edges":len(closure_records["J314"]["edges"]),"I314_external":len(closure_records["J314"]["external"]),"F110_sources":23,"F110_edges":58,"F110_external":32,"current_distinct":477}))
