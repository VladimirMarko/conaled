from pathlib import Path
from collections import Counter
import json,hashlib,re,subprocess,datetime
BASE=Path("/workspace/scratch/b4a17a285e23/fdsa-restored-20261104")
C=BASE/"fdsa-control"; REPO=BASE/"conaled-ch02-top-down"
D=C/"provenance/shared-tail-spec-terminal-20261104"
L="726cb9a9b9ff4444a7614383de4fb336e8804aa7"
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
trees={};closure_cache={}
def closure(candidate,roots):
 key=(candidate,tuple(roots))
 if key in closure_cache:return closure_cache[key]
 if candidate not in trees:trees[candidate]=set(git("ls-tree","-r","--name-only",candidate).decode().splitlines())
 todo=list(roots);sources={};edges=[];external=set()
 while todo:
  mod=todo.pop();path=mod.replace(".","/")+".lean"
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
 ans={"sources":sources,"external":sorted(external),"edges":sorted(edges)}
 closure_cache[key]=ans
 return ans
cmp_path=C/"provenance/shared-tail-inherited-type-qualification-20261104/comparison.json"
cmp=read(cmp_path)
assert (cmp["recipient"],cmp["accepted_predecessor"],cmp["I_producer"],cmp["Foundation_producer"])==(L,J,I,F)
obs={}
for label,m in cmp["observation_files"].items():
 p=Path(m["path"]);raw=p.read_bytes()
 assert len(raw)==m["bytes"] and sha(raw)==m["sha256"],label
 v=json.loads(raw);assert v["observed_utc"]==m["observed_utc"];obs[label]=v
fields={"candidate","clean","project","program","configuration","dependencies","runtime","roots","local_sources","local_compiler_objects_and_traces","direct_external_imports_of_local_closure"}
pairs=["Tail61","TailJ53","TailI314","TailF145","J53","J314","J145","I314","I145","F145"]
closure_records={}
for pair in pairs:
 pre,post=obs[pair+"_pre"],obs[pair+"_post"]
 assert pre["identity"]==post["identity"] and post["unchanged"] is True
 pm=meta(cmp["observation_files"][pair+"_pre"]["path"])
 assert post["compared_to"]=={k:pm[k] for k in ["path","bytes","sha256"]}
 ident=pre["identity"];assert set(ident)==fields and ident["clean"] is True
 candidate=L if pair.startswith("Tail") else J if pair.startswith("J") else I if pair.startswith("I") else F
 assert ident["candidate"]==candidate
 assert (len(ident["configuration"]),len(ident["dependencies"]),len(ident["runtime"]))==(10,9,12)
 assert all(v["status"]=="" for v in ident["dependencies"].values())
 cr=closure(candidate,ident["roots"])
 assert cr["sources"]==ident["local_sources"] and cr["external"]==ident["direct_external_imports_of_local_closure"],pair
 # Compare every recorded supported artifact key. At these secured observations the complete keysets are the three supported extant artifacts per source; no private/server key was recorded or discarded.
 expected={".lake/build/lib/lean/"+p[:-5]+ext for p in cr["sources"] for ext in [".olean",".olean.hash",".trace"]}
 assert set(ident["local_compiler_objects_and_traces"])==expected,pair
 assert all(v["bytes"]>0 and re.fullmatch("[0-9a-f]{64}",v["sha256"]) for v in ident["local_compiler_objects_and_traces"].values())
 for p,m in ident["configuration"].items():
  raw=blob(candidate,p);assert {"bytes":len(raw),"sha256":sha(raw)}==m,(pair,p)
 closure_records[pair]=cr
s61=obs["Tail61_pre"]["identity"]
for pair in pairs:
 ident=obs[pair+"_pre"]["identity"]
 for k in ["configuration","dependencies","runtime","project"]:assert ident[k]==s61[k],(pair,k)
for a,b in [("J53","TailJ53"),("I314","J314"),("I314","TailI314")]:
 for key in fields-{"candidate"}:assert obs[a+"_pre"]["identity"][key]==obs[b+"_pre"]["identity"][key],(a,b,key)
 assert closure_records[a]==closure_records[b]
froots=["Applications.Resources.ListCalls","Examples.FunctionalNotation","Examples.ListCalls","Examples.ListLibrary"]
fcs={cand:closure(cand,froots) for cand in [F,I,J,L]}
assert all(v==fcs[F] for v in fcs.values())
fc=fcs[L];assert (len(fc["sources"]),len(fc["edges"]),len(fc["external"]))==(23,58,32)
fkeys={".lake/build/lib/lean/"+p[:-5]+ext for p in fc["sources"] for ext in [".olean",".olean.hash",".trace"]}
assert len(fkeys)==69
assert sorted(cmp["F110"]["source_import_edges"])==fc["edges"]
assert cmp["F110"]["direct_external_imports"]==fc["external"]
def projection(ident):
 assert set(fc["sources"])<=set(ident["local_sources"]) and fkeys<=set(ident["local_compiler_objects_and_traces"])
 assert set(froots)<=set(ident["roots"])
 return {**{k:ident[k] for k in ["clean","project","program","configuration","dependencies","runtime"]},
 "roots":froots,"local_sources":{p:ident["local_sources"][p] for p in sorted(fc["sources"])},
 "local_compiler_objects_and_traces":{p:ident["local_compiler_objects_and_traces"][p] for p in sorted(fkeys)},
 "direct_external_imports_of_local_closure":fc["external"]}
fps=[projection(obs[p+"_"+t]["identity"]) for p in ["F145","I145","J145","TailF145"] for t in ["pre","post"]]
assert all(v==fps[0] for v in fps) and fps[0]["local_sources"]==fc["sources"]
def dt(s):return datetime.datetime.fromisoformat(s)
runs={
 "Tail61":C/"provenance/shared-tail-complete-public-statements61-20261104-attempt1",
 "J53":C/"provenance/shared-order-complete-public-statements53-20261104-attempt1",
 "I314":C/"provenance/shared-four-complete-public-statements314-20261104-attempt1",
 "F145":C/"provenance/foundation-complete-public-statements145-20261104-attempt1"}
block_records={};run_records={}
for label,folder in runs.items():
 index=read(folder/"output-blocks.json");program=Path(index["program"]["path"]).read_bytes()
 assert meta(index["program"]["path"])["sha256"]==index["program"]["sha256"] and len(program)==index["program"]["bytes"]
 names=re.findall(r"^#check\s+@(\S+)\s*$",program.decode(),re.M)
 for option in ["set_option pp.universes true","set_option pp.explicit true","set_option pp.fullNames true"]:assert option in program.decode()
 ident=obs[label+"_pre"]["identity"]
 assert names==[b["name"] for b in index["blocks"]]==ident["program"]["names"]
 assert sha(program)==ident["program"]["sha256"] and len(program)==ident["program"]["bytes"]
 assert re.findall(r"^import\s+(\S+)\s*$",program.decode(),re.M)==ident["roots"]
 raw=(folder/"native-records/output.log").read_bytes();lines=raw.splitlines(keepends=True)
 assert len(raw)==index["native_output"]["bytes"] and sha(raw)==index["native_output"]["sha256"]
 pattern=re.compile(r"^@?("+r"|".join(re.escape(n) for n in sorted(names,key=len,reverse=True))+r")(?:\.\{[^}]*\})?\s*:",re.M)
 starts=[(m.group(1),len(raw[:len(raw.decode()[:m.start()].encode())].splitlines())) for m in pattern.finditer(raw.decode())]
 assert [n for n,_ in starts]==names
 end=0
 for n,b in enumerate(index["blocks"]):
  part=b"".join(lines[b["start_line"]-1:b["end_line"]])
  assert b["byte_start"]==end and part==raw[b["byte_start"]:b["byte_end_exclusive"]]
  assert len(part)==b["bytes"] and sha(part)==b["sha256"]
  assert starts[n][1]+1==b["start_line"]
  end=b["byte_end_exclusive"]
 assert end==len(raw)
 result=read(folder/"result.json");native=read(folder/"native-records/result.json");start=read(folder/"start.json");ns=read(folder/"native-records/start.json")
 assert result["exit_code"]==native["exit_code"]==0 and native["passed"] is True and native["timed_out"] is False and native["recorder_error"] is None
 assert result["candidate"]==result["final_head"]==start["initial_head"]==ident["candidate"]
 assert result["final_status"]==start["initial_status"]==""
 assert native["lean_threads"]==ns["lean_threads"]=="1"
 assert native["command"]==ns["command"]==["lake","env","lean",ident["program"]["path"]]
 assert native["cwd"]==ns["cwd"]==ident["project"]
 assert result["command"][-4:]==native["command"]
 assert result["command"][result["command"].index("--threads")+1]=="1"
 assert dt(obs[label+"_pre"]["observed_utc"])<dt(result["started_utc"])<dt(result["completed_utc"])<dt(obs[label+"_post"]["observed_utc"])
 outer=(folder/"full.log").read_bytes();assert len(outer)==result["log_size_bytes"] and sha(outer)==result["log_sha256"]
 assert outer.count(raw)==1
 block_records[label]=index["blocks"]
 run_records[label]={"program":meta(index["program"]["path"]),"native_output":meta(folder/"native-records/output.log"),"outer_output":meta(folder/"full.log"),"index":meta(folder/"output-blocks.json"),"result":meta(folder/"result.json"),"native_result":meta(folder/"native-records/result.json"),"full_order_and_every_block_byte_hash_independently_checked":True}
full_folder=C/"provenance/shared-tail-full-attempt1-20261104"
full=read(full_folder/"result.json");full_native=read(full_folder/"native-records/result.json")
verification=read(full_folder/"verification.json")
assert full["exit_code"]==full_native["exit_code"]==0 and full_native["passed"] and not full_native["timed_out"] and full_native["recorder_error"] is None
assert full["candidate"]==full["final_head"]==L and full["final_status"]==""
assert read(full_folder/"start.json")["initial_head"]==L and read(full_folder/"start.json")["initial_status"]==""
assert full_native["lean_threads"]=="1" and full_native["command"]==["./check.sh","--candidate","HEAD"]
assert verification["candidate"]==L and verification["result"]=="passed" and verification["mode"]=="incremental"
assert verification["dependencies"]=={k:v["head"] for k,v in s61["dependencies"].items()}
assert sha((full_folder/"verification.json").read_bytes())==full["verification_record_sha256"]
tr=read(runs["Tail61"]/"result.json")
for p in ["Tail61","TailJ53","TailI314","TailF145"]:
 assert dt(full["completed_utc"])<dt(obs[p+"_pre"]["observed_utc"])<dt(tr["started_utc"])<dt(tr["completed_utc"])<dt(obs[p+"_post"]["observed_utc"])
positions=list(range(20,84))+list(range(100,146))
selected=[block_records["F145"][i-1] for i in positions]
groups={"current61":[b["name"] for b in block_records["Tail61"]],"J53":[b["name"] for b in block_records["J53"]],"I314":[b["name"] for b in block_records["I314"]],"F110":[b["name"] for b in selected]}
for group,names in groups.items():assert cmp[group]["names"]==names
assert positions==cmp["F110"]["positions_1_based"]
allnames=sum(groups.values(),[]);assert len(allnames)==len(set(allnames))==538
for group,pair in [("current61","Tail61"),("J53","TailJ53"),("I314","TailI314")]:
 assert cmp[group]["local_sources"]==len(obs[pair+"_pre"]["identity"]["local_sources"])
 assert cmp[group]["complete_artifact_keys"]==sorted(obs[pair+"_pre"]["identity"]["local_compiler_objects_and_traces"])
assert cmp["F110"]["complete_artifact_keys"]==sorted(fkeys)
# Revalidate own complete producer semantic dispositions and the exact records they retain.
retained=[]
for rel,candidate in [("provenance/shared-order-spec-terminal-20261104/final-disposition.json",J),("provenance/shared-four-spec-terminal-20261104/final-disposition.json",I)]:
 prior=read(C/rel);assert prior["outcome"]=="PASS" and prior["candidate"]==candidate
 retained.append(meta(C/rel))
 for group in ["new_own_records","source_and_historical_evidence","new_own_evidence"]:
  for entry in prior.get(group,[]):
   actual=meta(C/entry["path"]);assert actual["bytes"]==entry["bytes"] and actual["sha256"]==entry["sha256"],entry["path"]
   retained.append(actual)
# Frozen source receipt and correction stay unchanged; source assessment is not reset.
for rel,h in [
 ("reviews/permutation-tail-spec-source-continuation-20261104.md","977d1f38916c6e3c0eba1e4949bc4ceefc41766482229d1eadef4884dc461b70"),
 ("provenance/shared-tail-spec-source-continuation-20261104/source-assessment.json","862f2b48e0212d7e08137f3f88946df3772be4b1e5e36dfa41874b0c513b8388"),
 ("provenance/shared-tail-spec-source-continuation-20261104/header-metadata-correction.json","f39acf9998c66b8766183d8470c66c7b90b5d1bfaa478986cc28bf1687140e36"),
 ("provenance/foundation-spec-terminal-assessment-20261104/actual145-read-progress.json","ab4ba79877f9d85d3fe4f08d271312ed2f37922e60886e67a653afaea1e62a23")]:
 m=meta(C/rel);assert m["sha256"]==h;retained.append(m)
out={"reviewer":"Independent nonauthor Spec","recipient":L,"predecessor":J,"I_producer":I,"F_producer":F,
 "method":"Independent immutable Git closure reconstruction, complete saved-record equality and all executed producer block bytes/order; no compiler, runtime capture, live-output inspection or mutation.",
 "comparison_record":meta(cmp_path),"all20_saved_observation_files":{k:meta(v["path"]) for k,v in cmp["observation_files"].items()},
 "all10_pre_post_identity_pairs_exact":True,"all_receiving_pairs_after_full_and_around_actual61":True,
 "actual61":{"local_sources":9,"complete_artifact_keys":27,"identity_fields":sorted(fields),"program_and_closed_run_qualified":True},
 "J53":{"source_count":6,"artifact_count":18,"all_non_candidate_fields_compared":sorted(fields-{"candidate"}),"all_four_J_L_records_exact":True},
 "I314":{"source_count":27,"artifact_count":81,"all_non_candidate_fields_compared":sorted(fields-{"candidate"}),"all_six_I_J_L_records_exact":True},
 "F110":{"positions":positions,"source_count":23,"artifact_count":69,"four_roots":froots,"all_eight_F_I_J_L_projected_records_exact":True,"excluded35_separately_in_actual_I314":True},
 "independently_reconstructed_closures":{"Tail61":closure_records["Tail61"],"J53":closure_records["TailJ53"],"I314":closure_records["TailI314"],"F110":fc},
 "all_complete_supported_artifact_keys":{"Tail61":sorted(s61["local_compiler_objects_and_traces"]),"J53":cmp["J53"]["complete_artifact_keys"],"I314":cmp["I314"]["complete_artifact_keys"],"F110":sorted(fkeys)},
 "common_exact_fields":{"configs":10,"actual_clean_dependency_records":9,"runtime_components":12,"dependency_paths_not_normalized":True},
 "programs_and_actual_producer_records":run_records,"exact_name_groups":groups,"current_distinct_account":538,
 "retained_prior_complete_semantic_and_source_evidence":retained,
 "qualified_lineage":"Successful guarded stock-native complete L build/audit precedes all receiving pre observations; sole actual61 run and matching post observations. Prior accepted J/I/F full and type lineage retained. Fingerprints supplement those qualified executions.",
 "conditions":cmp["conditions_retained_verbatim"],
 "boundary":"Stored public-statement evidence only; all original full source/private/generated scope, final axes and immediate verification remain. No whole-environment equivalence or hostile-input authenticity claim; no blanket transfer by source equality.",
 "semantic_disposition":"Mechanical prerequisites independently satisfied. Complete current61 semantic reading and final Spec disposition remain separate saved records."}
p=D/"independent-input-reconciliation.json";assert not p.exists();p.write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n")
print(json.dumps({"result":meta(p),"account":{k:len(v) for k,v in groups.items()},"closure_counts":{k:{"sources":len(v["sources"]),"edges":len(v["edges"]),"external_names":len(v["external"])} for k,v in out["independently_reconstructed_closures"].items()}))
