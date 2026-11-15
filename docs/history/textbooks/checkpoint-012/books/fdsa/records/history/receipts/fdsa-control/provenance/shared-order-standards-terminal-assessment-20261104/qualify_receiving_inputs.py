"""Read secured J evidence and immutable Git objects; write only this reviewer receipt."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib, json, re, subprocess
from datetime import datetime, timezone
from collections import Counter

BASE = Path("/workspace/scratch/b4a17a285e23/fdsa-restored-20261104")
CTRL = BASE / "fdsa-control"
P = CTRL / "provenance"
OWN = P / "shared-order-standards-terminal-assessment-20261104"
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
def bind_closed(run, candidate, native_command):
    p = P / run; start = js(p/"start.json"); end = js(p/"result.json")
    ns = js(p/"native-records/start.json"); ne = js(p/"native-records/result.json")
    assert start["candidate"] == start["initial_head"] == end["candidate"] == end["final_head"] == candidate
    assert start["initial_status"] == end["final_status"] == ""
    assert end["exit_code"] == 0 and end["state"] == "passed"
    assert ne["exit_code"] == 0 and ne["passed"] and not ne["timed_out"] and ne["recorder_error"] is None
    assert ns["command"] == ne["command"] == native_command
    assert ns["lean_threads"] == ne["lean_threads"] == "1"
    assert ns["cwd"] == ne["cwd"] == start["cwd"] == str(BASE/"conaled-ch01-review")
    outer = (p/"full.log").read_bytes(); native = (p/"native-records/output.log").read_bytes()
    assert len(outer) == end["log_size_bytes"] and sha(outer) == end["log_sha256"] and outer.count(native) == 1
    rec = js(p/"closed-evidence-reconciliation.json")
    for v in rec["copied"]:
        local = p/"native-records"/v["name"]; b = local.read_bytes()
        assert len(b) == v["bytes"] and sha(b) == v["sha256"] and b == Path(v["origin"]).read_bytes()
    verify = js(p/"verification.json")
    assert verify["candidate"] == candidate and verify["result"] == "passed" and verify["mode"] == "incremental"
    assert sha((p/"verification.json").read_bytes()) == end["verification_record_sha256"]
    return {"run":run, "start":fp(p/"start.json"), "result":fp(p/"result.json"),
            "native_start":fp(p/"native-records/start.json"), "native_result":fp(p/"native-records/result.json"),
            "outer":fp(p/"full.log"), "native":fp(p/"native-records/output.log"), "verification":fp(p/"verification.json"),
            "started_utc":start["started_utc"],"completed_utc":end["completed_utc"]}

rootpath=P/"shared-order-inherited-type-qualification-20261104/comparison.json"
root=js(rootpath)
assert sha(rootpath.read_bytes())=="db26dc39cfe7fabb2f62391769eaf620d0ac758d5cda08536074a3897b40195b"
observed={}
for name, rec in root["observation_files"].items():
    p=Path(rec["path"]); b=p.read_bytes()
    assert len(b)==rec["bytes"] and sha(b)==rec["sha256"]
    observed[name]=js(p)
    assert observed[name]["observed_utc"]==rec["observed_utc"]
for prefix, candidate in [("J53",J),("J314",J),("J145",J),("I314",I),("I145",I),("F145",F)]:
    pre,post=observed[prefix+"_pre"],observed[prefix+"_post"]
    assert pre["identity"]==post["identity"] and post["unchanged"]
    assert pre["identity"]["candidate"]==candidate and pre["identity"]["clean"]
    assert post["compared_to"]["sha256"]==fp(root["observation_files"][prefix+"_pre"]["path"])["sha256"]
    program(pre["identity"])
ids={name:v["identity"] for name,v in observed.items()}
current=ids["J53_pre"]
current_closure=closure(J,current["roots"])
assert current_closure["local_sources"]==current["local_sources"]
assert current_closure["external_imports"]==current["direct_external_imports_of_local_closure"]
assert len(current_closure["local_sources"])==6 and len(current_closure["edges"])==26
assert len(objects_for(current,set(current["local_sources"])))==18
source_assessment=js(P/"shared-order-standards-integration-20261104/source-assessment.json")
public=[v["name"] for v in source_assessment["inventory"] if v["visibility"]=="public"]
assert len(public)==53 and set(public)==set(program(current))
assert command("rev-parse",J+"^{tree}").decode().strip()=="fc0af937b0b323d5216b3d7533af52edc70ea411"
assert command("show","-s","--format=%P",J).decode().strip().split()==[I,O]
assert sorted(command("diff","--name-only",I,J).decode().splitlines())==sorted(v["path"] for v in source_assessment["scope"])

for prefix, candidate in [("J314",J),("I314",I),("J145",J),("I145",I),("F145",F)]:
    ident=ids[prefix+"_pre"]; actual=closure(candidate,ident["roots"])
    assert actual["local_sources"]==ident["local_sources"]
    assert actual["external_imports"]==ident["direct_external_imports_of_local_closure"]
    objects_for(ident,set(actual["local_sources"]))
common_fields=[k for k in ids["I314_pre"] if k!="candidate"]
assert sorted(common_fields)==sorted(root["I314"]["all_exact_identity_fields_compared"])
for key in common_fields:
    assert all(ids[name][key]==ids["I314_pre"][key] for name in ["I314_post","J314_pre","J314_post"]), key
assert len(ids["I314_pre"]["local_sources"])==27 and len(ids["I314_pre"]["local_compiler_objects_and_traces"])==81
assert sorted(ids["I314_pre"]["local_compiler_objects_and_traces"])==sorted(root["I314"]["complete_artifact_keys"])

eligible_roots=["Applications.Resources.ListCalls","Examples.FunctionalNotation","Examples.ListCalls","Examples.ListLibrary"]
fclosure=closure(F,eligible_roots); selected=set(fclosure["local_sources"])
assert len(selected)==23 and len(fclosure["edges"])==58 and len(fclosure["external_imports"])==32
assert fclosure==closure(I,eligible_roots)==closure(J,eligible_roots)
assert fclosure["external_imports"]==root["F110"]["direct_external_imports"]
assert all(isinstance(v,list) and len(v)==2 for v in root["F110"]["source_import_edges"])
root_edges=[{"from":a,"to":b,"local":b.replace(".","/")+".lean" in tree(F)} for a,b in root["F110"]["source_import_edges"]]
assert fclosure["edges"]==sorted(root_edges,key=lambda e:(e["from"],e["to"],e["local"]))
projections={}
for prefix in ["F145","I145","J145"]:
    for phase in ["pre","post"]:
        key=prefix+"_"+phase;ident=ids[key]
        projected={k:ident[k] for k in ["clean","project","program","configuration","dependencies","runtime"]}
        projected["local_sources"]={p:ident["local_sources"][p] for p in sorted(selected)}
        projected["local_compiler_objects_and_traces"]=objects_for(ident,selected)
        projected["roots"]=eligible_roots
        projected["direct_external_imports_of_local_closure"]=fclosure["external_imports"]
        projections[key]=projected
assert all(p==projections["F145_pre"] for p in projections.values())
assert len(projections["F145_pre"]["local_compiler_objects_and_traces"])==69
assert sorted(projections["F145_pre"]["local_compiler_objects_and_traces"])==sorted(root["F110"]["complete_artifact_keys"])
for candidate in [F,I,J]:
    for path, rec in current["configuration"].items():
        raw=source(candidate,path);assert len(raw)==rec["bytes"] and sha(raw)==rec["sha256"]
assert len(current["configuration"])==10 and len(current["dependencies"])==9 and len(current["runtime"])==12
for ident in ids.values():
    for key in ["configuration","dependencies","runtime"]:
        assert ident[key]==current[key], key
    assert all(d["status"]=="" for d in ident["dependencies"].values())
manifest=json.loads(source(J,"lake-manifest.json"))
assert {p["name"]:p["rev"] for p in manifest["packages"]}=={n:d["head"] for n,d in current["dependencies"].items()}
assert source(J,"lean-toolchain").decode().strip()=="leanprover/lean4:v4.35.0"

full=bind_closed("shared-order-full-attempt1-20261104",J,["./check.sh","--candidate","HEAD"])
actual=bind_closed("shared-order-complete-public-statements53-20261104-attempt1",J,["lake","env","lean",current["program"]["path"]])
assert full["verification"]["sha256"]==actual["verification"]["sha256"]
for prefix in ["J53","J314","J145"]:
    assert full["completed_utc"]<observed[prefix+"_pre"]["observed_utc"]<actual["started_utc"]<actual["completed_utc"]<observed[prefix+"_post"]["observed_utc"]
b53=block_inventory("shared-order-complete-public-statements53-20261104-attempt1",current)
b314=block_inventory("shared-four-complete-public-statements314-20261104-attempt1",ids["I314_pre"])
b145=block_inventory("foundation-complete-public-statements145-20261104-attempt1",ids["F145_pre"])
eligible_positions=list(range(20,84))+list(range(100,146))
eligible=[b145[i-1] for i in eligible_positions]
names110=[b["name"] for b in eligible]
names314=[b["name"] for b in b314]; names53=[b["name"] for b in b53]
assert names314==root["I314"]["names"] and names110==root["F110"]["names"]
assert eligible_positions==root["F110"]["positions_1_based"]
insertion=[b["name"] for b in b145[:19]+b145[83:99]]
assert len(insertion)==35 and names314[-35:]==insertion
assert not(set(names53)&set(names314) or set(names53)&set(names110) or set(names314)&set(names110))
assert len(set(names53+names314+names110))==477
full_f=ids["F145_pre"]["local_sources"];full_j=ids["J145_pre"]["local_sources"]
assert set(full_f)==set(full_j)
excluded_differences=[p for p in full_f if full_f[p]!=full_j[p]]
assert excluded_differences==["Applications/Sorting/Merge.lean"]

ledger314p=P/"shared-four-standards-terminal-assessment-20261104/actual314-read-ledger.json"
ledger145p=P/"shared-foundations-standards-terminal-assessment-20261104/actual145-read-progress.json"
l314,l145=js(ledger314p),js(ledger145p)
assert l314["candidate"]==I and l314["all_bytes_read"] and l314["complete_actual_types_read"]==314 and l314["finding_count"]==0
assert l145["candidate"]==F and l145["read_progress"]["complete"] and l145["read_progress"]["types"]==145 and not l145["findings"]
for ledger,run,style in [(l314,"shared-four-complete-public-statements314-20261104-attempt1","I"),(l145,"foundation-complete-public-statements145-20261104-attempt1","F")]:
    raw=(P/run/"native-records/output.log").read_bytes();lines=raw.splitlines(keepends=True);nextline=1
    assert sha(raw)==ledger["native"]["sha256"]
    for chunk in ledger["chunks"]:
        a,z=(chunk["first"],chunk["last"]) if style=="I" else (chunk["native_line_start"],chunk["native_line_end"])
        assert a==nextline;nextline=z+1;piece=b"".join(lines[a-1:z])
        assert len(piece)==chunk["bytes"] and sha(piece)==chunk["sha256"]
        assert chunk["read"] if style=="I" else chunk["read_status"]=="complete bounded untruncated read"
    assert nextline==len(lines)+1

raw53=(P/"shared-order-complete-public-statements53-20261104-attempt1/native-records/output.log").read_bytes()
lines53=raw53.decode().splitlines();ellipsis=[]
for n,line in enumerate(lines53,1):
    if "⋯" in line:
        assert line.count("⋯")==1
        if "@Fin.instOfNat" in line: category="Fin.instOfNat NeZero proof instance"
        else:
            assert line.strip()=="⋯)))" and "@instOfNatAtLeastTwo" in "\n".join(lines53[max(0,n-6):n])
            category="ENNReal instOfNatAtLeastTwo proof instance"
        ellipsis.append({"line":n,"category":category})
assert len(ellipsis)==118
assert [v["line"] for v in ellipsis]==js(P/"shared-order-complete-public-statements53-20261104-attempt1/output-blocks.json")["ellipsis_lines"]
assert Counter(v["category"] for v in ellipsis)=={"Fin.instOfNat NeZero proof instance":114,"ENNReal instOfNatAtLeastTwo proof instance":4}
log=(P/"shared-order-full-attempt1-20261104/native-records/output.log").read_text()
rows=re.findall(r"^  (\S+): (\d+) logical declarations; (\d+) theorem declarations; (\d+) unsafe runtime declarations$",log,re.M)
assert len(rows)==978 and len({r[0] for r in rows})==978
assert [sum(int(r[i]) for r in rows) for i in (1,2,3)]==[45707,25451,0]
assert log.count("Transitive axiom union: [propext, Classical.choice, Quot.sound]")==1
oldlog=(P/"shared-four-full-attempt1-20261104/native-records/output.log").read_text()
warn=lambda text:Counter(line for line in text.splitlines() if line.startswith("warning: "))
newwarn=warn(log)-warn(oldlog);removedwarn=warn(oldlog)-warn(log)
assert sum(newwarn.values())==13 and not removedwarn
assert all("PermutationOrder" in line and "module" in line.lower() for line in newwarn)
priorprep=P/"shared-four-foundation110-reuse-preparation-20261104/inventory.json"
prior=js(priorprep)
def condition_lists(v):
    if isinstance(v,list):
        if len(v)==10 and all(isinstance(x,dict) and "id" in x and "condition" in x for x in v): yield v
        for x in v: yield from condition_lists(x)
    elif isinstance(v,dict):
        for x in v.values(): yield from condition_lists(x)
assert root["conditions_retained_verbatim"] in list(condition_lists(prior))
receipt={
 "reviewer":"/root/chapter02_standards","axis":"Standards","candidate":J,"accepted_predecessor":I,"Foundation_producer":F,
 "recorded_utc":datetime.now(timezone.utc).isoformat(),
 "method":"Independent immutable Git closure, full-key saved observations, terminal/output-block and same-reader producer-ledger reconciliation. No compiler/runtime recorder/live output capture.",
 "root_receipt":fp(rootpath),"own_source_assessment":fp(P/"shared-order-standards-integration-20261104/source-assessment.json"),
 "observation_files":{k:fp(v["path"]) for k,v in root["observation_files"].items()},
 "all_six_pre_post_identity_pairs_unchanged":True,"all_three_receiving_pairs_surround_actual53_after_full":True,
 "actual_full":full,"actual53":actual,"current53_closure":current_closure,
 "current53_artifact_keys":sorted(current["local_compiler_objects_and_traces"]),
 "inherited314":{"candidate":I,"receiver":J,"names":names314,"closure":closure(J,ids["J314_pre"]["roots"]),"complete_artifact_keys":sorted(ids["J314_pre"]["local_compiler_objects_and_traces"]),"all10_noncandidate_identity_fields_equal":True,"producer_native":fp(P/"shared-four-complete-public-statements314-20261104-attempt1/native-records/output.log"),"producer_blocks":fp(P/"shared-four-complete-public-statements314-20261104-attempt1/output-blocks.json"),"same_reader_ledger":fp(ledger314p),"all15_read_chunks_rehashed":True},
 "inherited110":{"candidate":F,"receiver":J,"via_accepted_I":I,"names":names110,"positions":eligible_positions,"closure":fclosure,"complete_artifact_keys":sorted(projections["F145_pre"]["local_compiler_objects_and_traces"]),"all_six_F_I_J_selected_projections_equal":True,"producer_native":fp(P/"foundation-complete-public-statements145-20261104-attempt1/native-records/output.log"),"producer_blocks":eligible,"same_reader_ledger":fp(ledger145p),"all10_full145_read_chunks_rehashed":True,"original_preparation":fp(priorprep),"conditions_preserved":root["conditions_retained_verbatim"]},
 "configuration":current["configuration"],"clean_pinned_dependencies":current["dependencies"],"qualified_runtime_components":current["runtime"],
 "current53_blocks":b53,"ellipsis_contexts":ellipsis,"ellipsis_counts":dict(Counter(v["category"] for v in ellipsis)),
 "insertion35_fresh_I314_positions":[280,314],"insertion35_names":insertion,"insertion_excluded_F_dependency_difference":excluded_differences,
 "full_audit":{"checked_modules":980,"defining_rows":978,"kernel_safe":45707,"theorems":25451,"unsafe":0,"axioms":["propext","Classical.choice","Quot.sound"]},
 "warnings":{"prior_warning_count":sum(warn(oldlog).values()),"current_warning_count":sum(warn(log).values()),"new_only13_import_advisories":dict(newwarn),"removed":dict(removedwarn)},
 "distinct_public_count":477,"public_account":{"current53":53,"qualified_I314":314,"qualified_F110":110},
 "retained_reader_reports":{"I":fp(CTRL/"reviews/shared-four-standards-final-20261104.md"),"F":fp(CTRL/"reviews/shared-foundations-standards-terminal-assessment-20261104.md")},
 "mechanical_result":"PASS; final semantic Standards disposition is authored separately.",
 "limits":"Fingerprints supplement actual trusted stable-checkout full gates and owned inspection runs; they do not independently certify compiler/cache authenticity. No new audit or execution is claimed for the two receiving program-only observations.",
 "bookkeeping_boundary":{"truncated_locator_tool":"c706c5","credit":"No complete-read credit taken from truncated locator. Bounded metadata reread56913f and the independent comparisons above establish the needed identities.","first_read_only_edge_schema_failure":fp(OWN/"qualification-bookkeeping-note.json")}
}
target=OWN/"independent-execution-and-type-reconciliation.json"
assert not target.exists()
target.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+"\n")
print(json.dumps({"saved":fp(target),"counts":receipt["public_account"],"audit":receipt["full_audit"],"ellipsis":receipt["ellipsis_counts"],"warnings":receipt["warnings"]},ensure_ascii=False,indent=2))

