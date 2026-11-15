from pathlib import Path
import json,hashlib,datetime
B=Path("/workspace/scratch/b4a17a285e23/fdsa-restored-20261104");C=B/"fdsa-control";D=C/"provenance/shared-tail-spec-terminal-20261104"
L="726cb9a9b9ff4444a7614383de4fb336e8804aa7";J="932438a765340d69fa6402f6abd17def6ec28d13";I="312aafb4446b995ff5542041b4e2e074f776db1e";F="f17cc6b1a2bf44215b16202ed0fcee2b5c130761"
def read(p):return json.loads(Path(p).read_bytes())
def meta(p):
 p=Path(p);b=p.read_bytes();return {"path":str(p.relative_to(C)) if p.is_relative_to(C) else str(p),"bytes":len(b),"lines":len(b.splitlines()),"sha256":hashlib.sha256(b).hexdigest()}
def save(name,v):
 p=D/name;assert not p.exists();p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+"\n");return meta(p)
src=read(C/"provenance/shared-tail-spec-source-continuation-20261104/source-assessment.json")
inp=read(D/"independent-input-reconciliation.json");types=read(D/"actual61-complete-type-assessment.json");gate=read(D/"full-gate-assessment.json")
assert inp["current_distinct_account"]==538 and types["all_native_bytes_and_lines_fully_read"]
assert types["all61_headers_once_in_exact_program_order"] and len(types["type_blocks"])==61 and len(types["ellipsis_contexts"])==52 and not types["findings"]
apis=read(C/"provenance/shared-order-spec-terminal-20261104/actual53-complete-type-assessment.json")["pinned_API_reads"]
answers=[
"Executed F145, I314, J53 and currentL61 program hashes, full ordered names and complete full-name/explicit/universe profile were independently checked. No prepared-only input supplies output credit.",
"Actual closed producer/native/outer results and all original complete semantic-read ledgers remain exact. Current61 output has every full type and all52 ellipsis contexts read. No count or summary substitutes for types.",
"All producer and receiving clean pre/post identities are secured. Immutable defining source/import closures and every relevant configuration are independently reconstructed; candidate identity is the sole excluded field for same-program J53/I314 comparisons.",
"Exact stock Lean4.35.0, matching Lake, native-kit1.0.0 qualified launcher/adapter and one-thread execution remain. Ten configs, nine complete clean actual dependency records with exact paths, and12 runtime components match across producers and recipient.",
"Current L guarded full build, postguard and exhaustive audit precede all four receiving pre observations. Sole actual61 is surrounded by all four unchanged post pairs. Matching complete supported artifact/hash/trace keysets supplement stable qualified ownership; no stale output or fingerprint-only trust.",
"Same independent Spec reviewer retains the complete original F/I/J source and actual-type assessments and independently assesses this new L mapping. Separate Standards axis remains required; this is the Spec disposition only.",
"Only original F14520–83 and100–145 are transferred as F110. The35 insertion names remain separately inspected by actualI314 and are not included in the F projection.",
"Original F/0a7ef078 preparation is explicitly extended through accepted I/J to immutable L, with source graphs and all actual F/I/J/L projected input pairs reconciled here. No automatic successor coverage is claimed.",
"New receiving disposition identifies the producer runs, exact recipient, every selected name and output positions. All old programs/receipts remain byte-identical; no prepared command or pending scope was silently removed.",
"Transfer supplies explicit public-statement evidence only. Full private/generated source scope and current L full audit are retained; both final axes and immediate qualified candidate verification precede acceptance. Accepted Chapter1 remains accepted; no fresh trigger is invented."
]
semantic={"schema":"fdsa-spec-tail-inherited-semantic-v1","reviewer":"Independent nonauthor Spec","recipient":L,
"outcome":"Qualified for Spec statement-inspection purposes at exact L",
"current61_complete_semantic_read":meta(D/"actual61-complete-type-assessment.json"),
"input_qualification":meta(D/"independent-input-reconciliation.json"),
"producer_semantic_records":[meta(C/"provenance/shared-order-spec-terminal-20261104/final-disposition.json"),meta(C/"provenance/shared-order-spec-terminal-20261104/actual53-complete-type-assessment.json"),meta(C/"provenance/shared-order-spec-terminal-20261104/inherited-semantic-disposition.json"),meta(C/"provenance/shared-four-spec-terminal-20261104/final-disposition.json"),meta(C/"provenance/shared-four-spec-terminal-20261104/actual314-complete-type-assessment.json"),meta(C/"provenance/shared-four-spec-terminal-20261104/actual314-type-read-progress.json"),meta(C/"provenance/foundation-spec-terminal-assessment-20261104/actual145-read-progress.json"),meta(C/"reviews/shared-foundations-spec-final-20261104.md")],
"same_reviewer_complete_prior_type_readings_retained":True,
"account":{"actual_L61":61,"qualified_J53":53,"qualified_I314":314,"qualified_F110":110,"distinct":538},
"F110_exact_positions":inp["F110"]["positions"],
"excluded35_insertion_names_separate_actual_I314":True,
"original_full_scope_preserved":src["original_scope"],
"all_REUSE_conditions":[{"id":c["id"],"condition_retained_verbatim":c["condition"],"Spec_disposition":answers[i]} for i,c in enumerate(inp["conditions"])],
"current_ellipsis_assessment":{"all52_complete_contexts_read":True,"classification_counts":types["ellipsis_counts"],"pinned_API_reads_rehashed_and_reread_tool":"f43bf1","pinned_API_reads":apis,"conclusion":"Only displayed numeral Prop-class proof terms are elided; no public binder, premise, carrier, function, measure or result is hidden."},
"receiving_lineage":"All four exact pre observations follow full L success and surround sole actual61 with matching posts; actual J/I/F producer outputs and prior complete semantic reads remain exact. No other compiler invocation in this stage.",
"no_full_environment_or_hostile_artifact_equivalence_claim":True,
"malformed_historical_F_file_boundary":"The previously disclosed truncated ENOSPC actual145-complete-assessment.json is not parsed or credited; accepted F final report and valid complete read ledger remain authoritative.",
"unresolved_findings":[],
"acceptance_or_immediate_verify_performed_by_reviewer":False}
sm=save("inherited-semantic-disposition.json",semantic)
findings={k:{"historical_source_and_finding_records_preserved":True,"current_L_disposition":"Resolved: retained exact source correction now confirmed by the complete current L build, all relevant actual full types and exhaustive private/generated audit."} for k in src["original_findings_retained"] if k!="C02-DOC-003"}
findings["C02-DOC-003 / Tail"]={"current_L_disposition":"Resolved for the Tail portion by exact receiving source application and confirmed against secured current evidence; no unrelated global C2 closure inferred."}
findings["C02-TYPE-001 / Tail receiving"]={"current_L_disposition":"Historical Z resolution retained; concrete receiving input-lineage gap independently resolved by actualL61 and full input qualification."}
final={"schema":"fdsa-spec-permutation-tail-final-v1","utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"reviewer":"Independent nonauthor Spec",
"candidate":L,"accepted_predecessor":J,"I_producer":I,"foundation_producer":F,"outcome":"PASS",
"frozen_requirements":src["frozen_requirements"],"full_original_scope":src["original_scope"],
"source_assessment_retained":meta(C/"provenance/shared-tail-spec-source-continuation-20261104/source-assessment.json"),
"effective_header_correction_retained":meta(C/"provenance/shared-tail-spec-source-continuation-20261104/header-metadata-correction.json"),
"actual61":{"all61_full_types_read":True,"native_lines":1073,"native_bytes":84784,"all52_ellipsis_contexts_assessed":True,"qualified_exclusive_run_and_complete_pre_post":True,"public_theorems":46,"public_definitions":15,"private_theorems":19,"anonymous_local_instances":8},
"full_gate":{"outer_native_owned_exit0":True,"initial_final_clean_L":True,"mode":"incremental normal","checked_modules":983,"audit_rows":981,"kernel_safe":45809,"theorems":25533,"unsafe_excluded":0,"axioms":["propext","Classical.choice","Quot.sound"],"native_full_read_lines":2484,"outer_full_read_bytes":284574,"postguard_artifacts":2946,"inconsistent_modules":0,"warnings":{"current":591,"unchanged_J":584,"new_module_import_advisories":7},"verification":gate["verification"]},
"statement_account":semantic["account"],"semantic_transfer":sm,
"complete_original_findings":findings,"six_API_ite_and_three_NNReal_transport_corrections":"Original identities retained; no invented additional findings; complete L proof/type/audit confirmation.",
"unresolved_Spec_findings":[],
"new_own_evidence":[meta(D/n) for n in ["actual61-complete-type-assessment.json","full-log-read-progress.json","full-log-read-complete.json","independent-input-reconciliation.py","reconciliation-bookkeeping.json","independent-input-reconciliation-corrected.py","independent-input-reconciliation.json","independent-full-gate-reconciliation.py","full-gate-assessment.json","inherited-semantic-disposition.json"]],
"final_report":meta(C/"reviews/permutation-tail-spec-final-20261104.md"),
"supersession":"Only exact-L receiving-validation-pending status is superseded; all prior source, F/I/J/C2/XR/XP/tree and other held reports remain unchanged. No whole Chapter2 acceptance is asserted.",
"coordinator_remaining_actions":["Separate final Standards verdict for exact L.","Immediate qualified ./check.sh --verify-candidate HEAD at exact clean L.","Authorized exact local accepted fast-forward and durability checkpoint after all gates."],
"reviewer_source_ref_compiler_process_runtime_output_cache_ticket_actions":False,
"readback_status":"Final artifact readback and explicit write hold are recorded separately after completion."}
fm=save("final-disposition.json",final)
print(json.dumps({"semantic":sm,"final":fm,"report":final["final_report"]}))
