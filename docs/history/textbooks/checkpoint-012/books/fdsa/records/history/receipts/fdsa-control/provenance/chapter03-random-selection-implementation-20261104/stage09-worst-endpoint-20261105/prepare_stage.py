"""Source/statement/case bookkeeping only; never invoke a Lean compiler."""

from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess

here = Path(__file__).parent
own = here.parent
base = own.parents[1]
wt = base.parent / "conaled-ch02-random-pivot"
previous = own / "trace-correction1-20261104"
start = json.loads((here / "starting-state.json").read_text())
old = json.loads((previous / "precommit-assessment.json").read_text())


def binding(path):
    path = Path(path)
    data = path.read_bytes()
    return {"path": str(path), "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def git(*args):
    return subprocess.check_output(["git", "-C", str(wt), *args], text=True).strip()


def dump(name, data):
    target = here / name
    assert not target.exists(), str(target)
    target.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
    return binding(target)


assert git("rev-parse", "HEAD") == start["candidate"] == "2b5ff20504d8811587859e6eb3351cb1598a4504"
assert git("diff", "--name-only") == ""
preserved = []
for group in ["prior_own_files", "actual_trace_pass_records", "actual_trace_type_records", "trace_statement_input_records"]:
    for old_binding in start[group]:
        now = binding(old_binding["path"])
        assert now["bytes"] == old_binding["bytes"] and now["sha256"] == old_binding["sha256"], now
        preserved.append(now)
for entry in start["source_files"]:
    now = binding(wt / entry["path"])
    assert now["bytes"] == entry["bytes"] and now["sha256"] == entry["sha256"], now

new_paths = ["Applications/Resources/RandomSelectionWorst.lean", "Examples/RandomSelectionWorst.lean"]
decl_pattern = re.compile(r"^(?:(private)\s+)?(theorem|def)\s+([A-Za-z_][\w']*)", re.M)
directive_pattern = re.compile(r"^(?:import |set_option |namespace |open |universe |variable |noncomputable section|section |end(?: |$)|omit |include ).*$", re.M)


def header_end(text, offset):
    depth = 0
    for i in range(offset, len(text)):
        if depth == 0 and text.startswith(":=", i):
            return i
        if depth == 0 and text.startswith("\n  |", i):
            return i
        if text[i] in "([{":
            depth += 1
        elif text[i] in ")]}" :
            depth -= 1
    raise AssertionError("No declaration body")


reviews = {
    "Resources.RandomSelection.inverse_factorial_step": "Private scalar algebra for every natural m. The restricted ENNReal inverse-product theorem is used with finite Nat-cast side conditions, then factorial_succ. No order/carrier or probability premise. Used by the actual recursive endpoint mass induction.",
    "Resources.RandomSelection.EndpointTrace": "Recursive Prop on the recorded trace, for arbitrary payload LinearOrder, rank and list including duplicates. Records a valid actual index, exact current length, EndpointPivot, the actual stepRun child, and singleton terminal/end-of-trace. No Nodup, desired target equation, mass, work bound or source-cost field. Empty trace is false. It is an observation predicate, not a replacement executor. Mixed-duplicate positive case is essential.",
    "Resources.RandomSelection.endpointTrace_nil": "For every rank and input, no empty structural path. Used by derived target validity and the valid-singleton nonempty-trace client; actual empty run remains unchanged.",
    "Resources.RandomSelection.endpointTrace_empty_input": "For every rank and recorded trace, no structural endpoint path on the empty input because no valid occurrence exists. No claim of nontermination or undefined actual run. Connected empty boundary retains actual trace mass1 and source2 from prior modules.",
    "Resources.RandomSelection.endpointTrace_singleton": "For any ordered payload x, valid rank0 on [x] has the structural trace[(1,0)]. Establishes actual stepRun return and singleton terminal; no Inhabited or distinctness premise. Base case and concrete/public singleton client establish satisfiability.",
    "Resources.RandomSelection.endpointTrace_child": "Every actual endpoint-policy index whose stepRun returns child(j,ys) can prepend its exact current size/index to a structural child trace. Child rank need not be k-1 in this general interface; mixed duplicates demonstrate k2->k0. No independence or cost assumptions.",
    "Resources.RandomSelection.endpointTrace_target": "For every structural path, the initial sorted-index specification succeeds with some payload. Derived by following actual stepRun_semantics along the structural trace; no target equality is stored in the definition. Does not infer Nodup, factorial mass or triangular work. Used by endpointTrace_valid and invalid-domain clients.",
    "Resources.RandomSelection.endpointTrace_valid": "Structural singleton-ending success entails k<xs.length, for arbitrary lists including duplicates. Derived target success contradicts out-of-range lookup none. Used by the general invalid-boundary client and its nonempty singleton specialization.",
    "Resources.RandomSelection.endpoint_outcome": "Private well-founded construction for EVERY arbitrary Nodup input and EVERY k<length. Empty case impossible; singleton actual atom1; nonsingleton uses exists_endpoint_child (minimum while positive, maximum at zero) with exact one-element decrement and valid predecessor. Builds only existing prepend of the actual child; run_child_atom supplies the fresh1/n factor. Derives exact complete atom1/n!, n trace entries and 2W=n(n+1). Neither mass nor runtime is a premise. Recursion decreases by actual stepRun_child.",
    "Resources.RandomSelection.exists_endpoint_worst": "Public universal witness for every arbitrary distinct input and every valid worker rank. Derived finite-factorial inverse nonzero gives actual support, then checked traceLaw_atom gives exact PROJECTED trace probability1/n!. Retains exact full atom, n entries, double-volume equality, W=n(n+1)/2 and actual sorted-index value. T is separately bounded between triangular W and9W+2 using run_source_bridge. No assumption of independence, probability, complexity, sorted input, endpoint requested rank, or unbounded carrier. Universal scan-max client and unsorted endpoint-rank cases consume it.",
    "Resources.RandomSelection.range_endpoint_worst": "For EVERY positive natural size n and EVERY k<n, instantiate the universal theorem on Nodup List.range n. Keep actual support, full/trace mass1/n!, n entries, exact triangular W, triangular source bounds, n*n<=2*T and T<=11*(n*n). Positivity n>0 is explicit and used for the finite upper constant. Does not assert this trace maximizes exact T. Connected range4 rank2 and unbounded-family clients consume it.",
    "Resources.RandomSelection.unbounded_endpoint_source_family": "For EVERY finite bound B, choose n=B+1>B and retain FOR EVERY k<n an actual supported structural endpoint outcome, exact projected mass1/n!, triangular W, B<T and quadratic source lower/upper inequalities. Inputs are actual natural ranges, so no claim that all payload types admit arbitrary distinct sizes. B<T follows initial-scan and source transport, not an assigned abstract cost. Connected large-family client retains all valid ranks.",
    "Examples.RandomSelectionWorst.inverse_nat_product": "Private finite-Nat ENNReal scalar normalization with restricted inverse side conditions. Used only after actual recursive atom factorization for range4, not as an assumed probability rule.",
    "Examples.RandomSelectionWorst.singleton_endpoint": "Generic x: actual structural singleton trace, no empty structural path, actual trace atom1 and W1. Consumes endpointTrace_singleton, endpointTrace_nil and prior checked trace law.",
    "Examples.RandomSelectionWorst.middle_endpoint_trace": "Unsorted Int[3,1,2], k1, exact trace[(3,1),(2,0),(1,0)]. Uses endpointTrace_child twice with checked actual steps and policy switch min1->max3; singleton2 terminates. Non-vacuous interior-rank use of structural definition.",
    "Examples.RandomSelectionWorst.middle_endpoint_probability": "Connects the structural interior path to passed actual full outcome value2/source33, projected trace mass1/6, W6. Source33 is not relabelled as triangular6. Uses middle_endpoint_trace and the previous checked actual PMF bridge cases.",
    "Examples.RandomSelectionWorst.signed_endpoint_trace": "Int[3,-2,8,0,5], k3, exact trace[(5,1),(4,2),(3,0),(2,0),(1,0)]. Each policy and actual step established; singleton5 terminal. Exercises multiple positive-rank steps before zero.",
    "Examples.RandomSelectionWorst.signed_endpoint_probability": "Connects that structural path to actual full outcome value5/source67, exact trace mass1/120 and W15. Uses the unchanged passed negative full/trace atom examples.",
    "Examples.RandomSelectionWorst.distinct_scan_maximum": "Universal arbitrary-Nodup/all-valid-rank application: combines the new supported factorial witness and exact triangular W with the existing upper bound for every supported s. The maximum is for W only. Does not claim this outcome maximizes exact T.",
    "Examples.RandomSelectionWorst.unsorted_endpoint_ranks": "Both requested endpoint ranks0 and2 on unsorted Int[3,1,2] have actual supported witness, trace mass1/6 and W6 via the universal theorem. Complements rather than replaces the arbitrary-rank theorem and middle-rank case.",
    "Examples.RandomSelectionWorst.range_four_exact": "Independent new Nat range4/k2 path[(4,0),(3,0),(2,1),(1,0)] has structural policy, full value2/source48 atom1/24, projected trace atom1/24 and W10. Actual local costs15+13+11+9=48 derived through stepRun_eq and run_child_atom; projected mass via supported traceLaw_atom. No assumed or separately assigned runtime.",
    "Examples.RandomSelectionWorst.range_four_bounds": "Consumes range_endpoint_worst at n4/k2 to obtain actual structural supported witness with mass1/24, W10,16<=2*T and T<=176. This is the family bound client, distinct from the sharper exact trace/source48 calculation.",
    "Examples.RandomSelectionWorst.large_family_every_rank": "For every B, obtain n>B and retain every k<n. The actual positive trace support and factorial mass have a complete supported outcome witness with B<T and the same quadratic source inequalities. Uses unbounded_endpoint_source_family and traceLaw_support, not a finite-test substitute.",
    "Examples.RandomSelectionWorst.empty_endpoint_boundary": "Every empty input/rank has no structural endpoint path, although its actual empty trace still has mass1. Uses endpointTrace_empty_input and prior empty trace law; source2 remains untouched.",
    "Examples.RandomSelectionWorst.invalid_endpoint_boundary": "For every input and every k>=length, no singleton-ending structural endpoint trace. Uses the derived endpointTrace_valid; does not remove or weaken the existing total invalid run.",
    "Examples.RandomSelectionWorst.invalid_singleton_endpoint_boundary": "Concrete invalid Nat[7],k1: no structural endpoint path at[(1,0)], while its actual projected trace has mass1 and prior actual source11. Consumes general invalid-boundary theorem and passed actual trace case.",
    "Examples.RandomSelectionWorst.equal_block_endpoint_boundary": "Valid Nat[4,4,4],k1 has actual one-step trace mass1/3 and W3, but cannot satisfy the singleton-ending structural trace because it terminates at size3. Uses actual checked duplicate step; does not claim all duplicate inputs lack structural paths.",
    "Examples.RandomSelectionWorst.mixed_duplicate_endpoint_boundary": "Nat[1,1,2],k2 is not Nodup yet has structural endpoint trace[(3,0),(1,0)]. Actual full value2/source23 and projected trace atom1/3, W4 and W!=6. Uses endpointTrace_child and actual atom/support/trace bridges. Explicitly prevents deriving triangular/factorial laws from structure alone.",
}

inventory = []
for entry in old["complete_declaration_inventory"]:
    row = dict(entry)
    row["stage09_source_unchanged"] = True
    row["stage09_new"] = False
    inventory.append(row)
sources = list(start["source_files"])
new_names = []
new_private = []
new_definitions = []
for rel in new_paths:
    text = (wt / rel).read_text()
    namespace = re.search(r"^namespace (\S+)", text, re.M)[1]
    matches = list(decl_pattern.finditer(text))
    rows = []
    for index, match in enumerate(matches):
        name = namespace + "." + match[3]
        finish = header_end(text, match.start())
        next_start = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        row = {
            "name": name, "kind": match[2], "private": bool(match[1]),
            "header": text[match.start():finish].strip(), "path": rel,
            "source_line": text[:match.start()].count("\n") + 1,
            "source_context_directives": directive_pattern.findall(text[:match.start()]),
            "declaration_source_sha256": hashlib.sha256(text[match.start():next_start].encode()).hexdigest(),
            "stage09_new": True,
            "intended_claim_and_scope_review": reviews[name],
            "actual_elaborated_type_status": "Not yet run; complete explicit-@ input prepared for sole root compiler.",
            "actual_focus_status": "Uncompiled first candidate; source assessment is not a compiler result.",
        }
        if match[2] == "def":
            row["definition_body"] = text[finish:next_start].strip()
            new_definitions.append(name)
        (new_private if match[1] else new_names).append(name)
        rows.append(row)
    inventory += rows
    data = (wt / rel).read_bytes()
    sources.append({"path": rel, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
        "git_blob": hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest(),
        "public_names": [r["name"] for r in rows if not r["private"]],
        "private_helpers": [r["name"] for r in rows if r["private"]],
        "line_count": text.count("\n")})
assert len(reviews) == 28 and len(new_names) == 25 and len(new_private) == 3
assert len(inventory) == 335
public = old["public_targets"] + new_names
private = old["authored_private_helpers"] + new_private
assert len(public) == len(set(public)) == 314
assert len(private) == len(set(private)) == 21

old_input = (previous / "Statements289-trace-correction1.lean").read_text()
assert re.findall(r"^#check @(\S+)$", old_input, re.M) == old["public_targets"]
input_text = "import Examples.RandomSelectionWorst\n" + old_input + "\n" + "\n".join("#check @" + name for name in new_names) + "\n"
input_path = here / "Statements314-stage09.lean"
assert not input_path.exists()
input_path.write_text(input_text)
assert re.findall(r"^#check @(\S+)$", input_text, re.M) == public
old_options = re.findall(r"^set_option .*$", old_input, re.M)
assert re.findall(r"^set_option .*$", input_text, re.M) == old_options

diffs = []
diff_receipts = []
for rel in new_paths:
    result = subprocess.run(["git", "-C", str(wt), "diff", "--no-index", "--", "/dev/null", rel], capture_output=True, text=True)
    assert result.returncode == 1 and not result.stderr, result
    diffs.append(result.stdout)
    diff_receipts.append({"path": rel, "exit": result.returncode, "reason": "Expected git no-index difference exit1 for a new source file; not compiler failure."})
diff_path = here / "source.diff"
assert not diff_path.exists()
diff_path.write_text("".join(diffs))

assessment = {
    "recorded_utc": datetime.now(timezone.utc).isoformat(),
    "stage": "C03-064/C03-075 universal endpoint path, actual factorial trace probability and source-cost family",
    "state": "Complete source first candidate; UNCOMPILED. No new acceptance or review loop.",
    "fixed_task_base": start["fixed_task_base"], "starting_candidate": start["candidate"],
    "source_files": sources, "public_targets": public, "authored_private_helpers": private,
    "complete_declaration_inventory": inventory,
    "new_public_count": 25, "new_private_count": 3, "new_header_count": 28,
    "public_count": 314, "private_count": 21, "authored_header_count": 335,
    "authored_definition_count": 26, "new_definitions": new_definitions,
    "authored_inductive_constructors": [],
    "count_boundary": "Authored public/private source headers, not generated declarations or kernel audit roots.",
    "all16_previous_sources_byte_identical": True,
    "all307_previous_headers_contexts_and25_definition_bodies_preserved": True,
    "all_existing289_public_and18_private_claims_cases_expected_values_preserved": True,
    "prior_record_bindings_verified": preserved,
    "full_core_read_chunk": "7cf849", "full_examples_read_chunk": "faa16d",
    "subsequent_core_only_delta": "In hvolume, explicitly included already-present hmul in nlinarith arguments; no header, hypothesis, case or mathematical change.",
    "expected_cases": [binding(here / "expected-cases.json"), binding(here / "mixed-duplicate-precode.json")],
    "precode_model_files": [binding(here / "expected_worst_paths.py"), binding(here / "mixed_duplicate_model.py")],
    "first14_case_run_receipt_boundary": "The earlier execution response was truncated across context; its terminal receipt is not claimed here. The complete output JSON exists, is hash-bound, and was fully read at abe3e1. It is independent pre-code expectation evidence, not Lean validation. No expensive original719 matrix was rerun.",
    "additional_mixed_case_actual_exit": 0, "additional_mixed_case_tool_chunk": "916fbc",
    "plan": binding(here / "plan.md"),
    "statement_input": binding(input_path), "print_options": old_options,
    "all_previous289_checks_order_and_print_profile_retained": True,
    "complete_public_input_includes_structural_definition": True,
    "private_statement_assessment": "All three new private helper headers and source derivations reviewed above; no fabricated mangled-name/type output. Scalar helpers precede Ordered context; endpoint_outcome has explicit arbitrary-ordered-payload/Nodup/valid-rank assumptions.",
    "quantifier_assessment": "No sorted-input or endpoint-requested-rank narrowing. Universal witness quantifies arbitrary LinearOrder payload/list and every k<length with Nodup. Range family quantifies every n>0 and every k<n; unbounded family retains forall k<n after existential n>B. No Inhabited, finite carrier, Countable payload, independence, assumed probability or assumed runtime bound.",
    "definition_assessment": "EndpointTrace is the only new definition. It is a structural Prop following actual stepRun and EndpointPivot with singleton termination. Existing run, traceLaw, scan/source laws and all25 old definitions are byte-identical. Mixed duplicates have a positive structural case and all-equal size3 has a negative one; structure alone never yields Nodup/triangular/factorial facts.",
    "actual_probability_assessment": "First derive full Outcome mass from run_child_atom and actual fresh-current-occurrence recursion; finite factorial inverse is nonzero, supplying support; only then use checked on-support traceLaw_atom for exact projected TRACE mass. No artificial independence, unrelated larger-side process or assigned distribution.",
    "actual_cost_assessment": "W exactly triangular and maximal by the existing universal scan bound. T is the same actual source observation, transported with W<=T<=9W+2 and explicit quadratic family bounds. No exact T maximum assertion. Abstract uniform draw remains free in this tariff; no random-bit/wall-time claim.",
    "source_diff": binding(diff_path), "diff_capture_receipts": diff_receipts,
    "static_forbidden_construct_scan_chunk": "2dd15a",
    "static_forbidden_construct_result": "Only mandatory autoImplicit false/warningAsError true option lines; no sorry/admit/axiom/unsafe/native_decide/implemented_by or linter suppression in either new source.",
    "unstaged_tracked_whitespace_check_chunk": "12635c",
    "whitespace_boundary": "The initial git diff --check sees only tracked changes; staged whitespace check for both new files is still required before commit.",
    "actual_prior_trace_pass": {"candidate": start["candidate"], "run": "chapter03-random-selection-trace-focused-attempt2-20261104", "owner": 43908, "exit": 0, "terminal": "df8dde", "complete_root_closure": "f58786", "author_full_read": "3b8a0e"},
    "actual_prior23_type_pass": {"owner": 72126, "exit": 0, "terminal": "5525da", "root_assessment_read": "3b8a0e"},
    "failed_and_interrupted_histories": "All prior own and bound run records preserved. Trace attempt1 has known native/recorded failure1 but original transport terminal null; drift attempt2 has unknown terminal outcome. No historical session is polled or relabelled.",
    "source_boundary": "Original Karp1994 remains inaccessible; no source quotation or recovery invented. This proof is derived from the existing actual model against the frozen83-row scope.",
    "author_compiler_actions": False, "actual_new_pair_pass": False, "actual_new_type_output": False,
    "no_environment_dependency_cache_output_profile_change": True,
    "no_wholechapter_acceptance": True,
    "requested_focus": ["Applications.Resources.RandomSelectionWorst", "Examples.RandomSelectionWorst"],
    "remaining_validation": "Root serial focused pair, actual explicit types, complete immutable candidate validation/audit and both independent axes in the existing whole-Chapter3 loop. This source handoff claims none of these future gates passed.",
}
assessment_binding = dump("precommit-assessment.json", assessment)
preparation = {
    "recorded_utc": datetime.now(timezone.utc).isoformat(),
    "starting_candidate": start["candidate"], "candidate": None, "tree": None,
    "state": "Prepared complete explicit-@ input; UNEXECUTED by author.",
    "input": binding(input_path), "public_targets": public, "public_count": 314,
    "authored_private_helpers": private, "private_count": 21, "authored_definition_count": 26,
    "source_files": sources, "print_options": old_options,
    "old289_names_order_and_options_preserved": True,
    "assessment": assessment_binding, "author_compiler_actions": False, "actual_type_output": False,
}
prep_binding = dump("Statements314-stage09-preparation.json", preparation)
print(json.dumps({"assessment": assessment_binding, "preparation": prep_binding,
    "input": binding(input_path), "new_sources": sources[-2:],
    "public": len(public), "private": len(private), "headers": len(inventory),
    "preserved_records": len(preserved), "new_public_names": new_names}, indent=2, ensure_ascii=False))
