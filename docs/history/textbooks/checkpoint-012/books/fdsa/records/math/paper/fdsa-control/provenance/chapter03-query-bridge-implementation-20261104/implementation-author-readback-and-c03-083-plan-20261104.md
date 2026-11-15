# Implementation-author readback and bounded C03-083 composition plan

Role: implementation author in the existing root-owned FDSA review loop, not an independent reviewer. This is a readback and a future implementation plan, not a new acceptance decision. Recorded 2026-11-04T20:34:49.074Z.

## Exact readback boundary

Readback candidate: **47f12b48b93a1e223b9f743e067685f12f4da5b1**.
Tree: **19186fe71dbfdcc639a6bf7da778dd14fd8684ff**.
Branch: work/fdsa-ch03-query-lower-bounds.
Worktree: /workspace/scratch/b4a17a285e23/fdsa-restored-20261104/conaled-ordinary-merge.

HEAD, index, and status were observed before this readback; the worktree was clean. No source, index, commit, import, dependency, toolchain, gate, ticket, or canonical control write was made. No Lean/Lake/build/install/hydrate/cache command or old-session poll was run. This new uniquely named provenance file is the only authorized write in this continuation. Existing records, including the original candidate01 handoff and its manifest, are immutable.

I read the corrected CoordinateReadAll core, unchanged connected examples, the CoordinateQueries model and lower bounds, CoordinateSensitivity's list/coordinate adapter and domains, both complete root correction record sets, the retained preparation-count failure, and the complete focused attempt3 outer log and its native/terminal/reconciliation records. The mathematical requirements remain the 83-entry inventory, specifically C03-081–083 at the end of research/chapter03-obligations.md; no obligation is removed or marked accepted here.

### Correction 1: private reserved-binder rename

The original author candidate edd0132b491858feda3307da70817e157dcad151 failed focused attempt1 because the private helper used reserved syntax **prefix** as a binder. Root's correction1 at **67f4add7bf99a20829cee1f7ec2265121546c879**, tree a22761ee6eafce221ff1a5cb68c7f604744bad99, alpha-renamed that binder and its uses to **prior**. The raw private header bytes therefore changed; its quantifier domains, hypotheses, and conclusion did not change. All public blocks and the other five files remained exact.

The preceding preparation failure is preserved as C03-READALL-PREP-001: tool bdd621 exited 1 after expecting 15 occurrences where the actual private-helper token count was 9. The saved read-only reconciliation eea8c2 exited 0 at the original clean HEAD and original source hash; only an empty new provenance directory existed. No source/stage/commit/compiler action occurred in that failed preparation. I read and retain this failure, rather than recasting it as a successful preparation.

### Correction 2: private proof normalization

Root's correction2 at the readback candidate adds Function.comp_def to the private nil-case simplification and changes unnecessary simpa to simp for its query decision equation. These are the exact two proof edits in root-correction2-20261104/source.diff. The already-renamed private header remains exact from correction1; all public statements and examples remain exact from the original candidate. No linter suppression, new premise, altered tariff, or weakened conclusion was introduced.

### Complete focused attempt3 result

The saved root-owned invocation was the one-thread native-profile build of Applications.Selection.CoordinateReadAll and Examples.CoordinateReadAll at exact 47f12b48. It closed with actual recorder/native exits 0/0, owned session **85675**, terminal **113824**, and root's recorded closure **af5d98**. The complete outer log is **3,451 bytes**, SHA256 **1f6172a3f1fbf28e5dbd5b3ba82b8cff45ce52364a5f69398cc155cce70d06b1**. I read that entire log and independently checked its bytes/hash and its exact decomposition into the 121-byte prefix, 3,174-byte native body, and 156-byte suffix.

Both requested modules built successfully. The log retains the existing module-system import notices; they are not hidden or described as absent. This is focused compilation evidence only. The copied verification.json names the previous accepted XR candidate c1cefe45f5e1b54ffa0fdd9e72b4a8a0c76b6fd5, not 47f12b48. Its presence supplies no new full-candidate verification, exhaustive type inspection, axiom audit, independent review, or Chapter 3 acceptance.

### Unchanged public/private scope

The preserved Statements95-candidate01.lean input exactly matches the current source inventory:

| Module | Top-level public declarations | Public constructors | Public inspection names | Private helpers |
| --- | ---: | ---: | ---: | ---: |
| Applications.Selection.CoordinateSensitivity | 7 | 0 | 7 | 2 |
| Applications.Selection.CoordinateQueries | 22 | 2 | 24 | 0 |
| Applications.Selection.CoordinateReadAll | 16 | 0 | 16 | 1 |
| Examples.CoordinateSensitivity | 13 | 0 | 13 | 0 |
| Examples.CoordinateQueries | 24 | 0 | 24 | 0 |
| Examples.CoordinateReadAll | 11 | 0 | 11 | 0 |
| Total | 93 | 2 | 95 | 3 |

The two constructor names are Applications.Selection.CoordinateQueries.Runs.done and Runs.query. The complete private helper inventory is CoordinateSensitivity.exists_above, CoordinateSensitivity.exists_below, and source-local CoordinateQueries.readPlan_run_from. Their generated private kernel names remain subject to actual elaborated inspection.

I compared current source with the original author commit: removing only the private readPlan_run_from block leaves CoordinateReadAll byte-identical, and all other five source files are byte-identical. All 23 prior provenance files fingerprinted by root's correction1 starting-state record still match. The prepared 27-name and 95-name explicit-@ inputs and all six printer options remain unchanged; this readback does not execute those inputs or infer their printed output.

### This readback's own read-only failures and reconciliation

These attempts caused no file mutation or compiler action and are retained here explicitly.

1. Tool chunk ad7cdc read CoordinateQueries successfully, then returned shell exit 2 because research paths were searched relative to the source worktree. The paths were corrected to fdsa-control; the three obligation rows were subsequently read in full.
2. Tool chunk a4a884 used Path('.') rather than an absolute current directory in the first static inventory script. The Python process raised FileNotFoundError for fdsa-control/provenance/.../Statements95-candidate01.lean. A later independent git ls-tree command in that shell returned 0, so the shell's 0 did not mean the Python check passed. No count or preservation claim is based on that attempt.
3. Tool chunk 6c3748 correctly located the files but its top-level-declaration-only count assertion failed with (93, 3). Read-only reconciliation bceb06 identified the exact two missing inspection names as the authored Runs constructors; no source or inventory scope was changed to force the expected count.
4. Successful read-only check aa560f counted top-level declarations and source constructors separately, reconciled the exact 95-name set with the prepared input, checked all three private helpers, compared the six source identities, checked the 23 prior records, and reconciled the complete focused log. The machine-readable appendix records that successful result.

## Pending actual worker API: announcement, not passed code

The worker author /root/chapter03_mom_continue confirmed the following intended shape by agent message during this readback. All worker names and laws in this section remain **announced, pending, and uncompiled**. No worker source has been imported, cherry-picked, copied, or declared passed.

~~~lean
Resources.Selection.selectRunWith
  (groupSize cutoff : Nat)
  (hd : 2 ≤ groupSize) (hc : 1 ≤ cutoff)
  (k : Nat) (xs : List α) :
  Resources.Measured (Option α) Nat
~~~

The announcement gives .1 as the optional selected value and .2 as the actual source-call observation. The intended book wrapper is selectRun k xs = selectRunWith 5 20 ... k xs. Measured itself is already the existing pair abbreviation; no replacement execution framework is needed.

The planned worker value theorem identifies .1 with (Applications.Selection.ordered xs)[k]?. A planned selectRun_some_iff connects some a with the existing occurrence-based RankedAt xs k a. The worker author explicitly confirmed no Nodup/injectivity requirement on execution or value correctness, including duplicate lists, and approved an Int-only getD 0 projection for the old lower-bound consumer. The announced invalid-rank branch returns (none, xs.length + 2), including empty cost 2; this is an expected case to check against the eventual actual source, not current verification evidence.

The mandatory pending cost theorem has intended shape (selectRun k xs).2 ≤ Resources.SelectionRecurrence.F xs.length for k < xs.length. Its final checked name, exact binders, result-carrier projections, typeclass assumptions, and source-call tariff must be read from the checked candidate and actual printed statements when root authorizes integration. No theorem assumption merely stating this target bound will substitute for the worker's proof from actual execution.

## Concrete composition design

Names below are proposed local names, not existing or compiled declarations. The book parameters are fixed to 5 and 20. The optional generic wrapper may expose other valid groupSize/cutoff values for totality and value laws, but the F majorant and linear upper bound are claimed only for the book wrapper.

### 1. Fixed measured protocol and result projection

Define a measured-result frontend for a fixed natural rank k, allowing empty/invalid-rank executions to be described separately:

~~~lean
-- Proposed shape only; implement after root supplies the checked worker.
def observedSelect (k : Nat) :
    Protocol n Int (Resources.Measured (Option Int) Nat) :=
  readAll (Resources.Selection.selectRun k)

def selectedValue (k : Nat) : Protocol n Int Int :=
  fun history =>
    match observedSelect (n := n) k history with
    | Sum.inl observation => Sum.inl (observation.1.getD 0)
    | Sum.inr i => Sum.inr i
~~~

The operation's arguments are only public n/k, the fixed worker, and the transcript. It contains no input argument, supplied full input list, answer oracle, or input-dependent advice. readAll passes history.reverse.map Prod.snd to that worker only after its plan is exhausted. List.ofFn input appears on theorem right-hand sides as the proved identity of the values obtained, never as an uncharged input to the operation.

The selectedValue adapter projects the final measured observation and preserves query decisions. It is a proof-facing view of the same worker invocation. Prove its equality with readAll (fun observed => (selectRun k observed).1.getD 0) by unfolding the existing operation equations. This gives existing readAll laws without introducing another framework or treating a second unrelated algorithm as the lower-bound consumer. The fixed fallback 0 is independent of the input; valid-rank correctness must prove that the optional answer is some before this projection is used.

### 2. Actual total run and correspondence

Apply the already focused-passed readAll_run to the actual fixed selectRun function. The exact target for every input is:

~~~text
Runs (observedSelect k) input []
  (List.ofFn (fun i => (i, input i)))
  (selectRun k (List.ofFn input)).
~~~

Package actual totality using readAll_total. Use readAll_run_iff and deterministic uniqueness for every terminating empty-history run, not just this witness. Prove that a selectedValue run with trace/result corresponds to an observedSelect run with the same trace and the projected final value. The concrete readAll characterization supplies both directions; no unproved termination or coversQueries premise is needed.

The primitive Runs.query remains the only place where an unknown input coordinate is read. The worker consumes the resulting list; all later list reads occur on acquired data and belong to the worker's declared source-call observation.

### 3. Semantic correctness and exact domains

For the lower-bound API, take k : Fin n. This makes k.val < n and n > 0 explicit consequences. Transfer List.length_ofFn to the worker's valid-rank law, obtain some a, and prove RankedAt (List.ofFn input) k.val a. The projection must then yield exactly a. This proves Selects (selectedValue k.val) k for **every** integer input, including duplicate values. Totality also remains on every input.

Use Function.Injective input only for the distinct-input lower-bound witness. It supplies (List.ofFn input).Nodup through the existing List.nodup_ofFn_ofInjective adapter used by CoordinateSensitivity. Do not silently restrict Selects to Nodup inputs: C03-082 explicitly requires correctness to survive replay on a changed coordinate, including inputs with duplicates. Occurrence ranks and zero-based k.val remain the same as in the existing lower-bound source.

At n=0 there is no k : Fin n and no selection lower-bound claim. The natural-rank observed frontend still has an actual zero-query run; once checked, the worker's announced empty result/cost can be exposed as a separate diagnostic case. Similarly, k ≥ n is not silently treated as a valid selection rank.

### 4. Actual acquisition/source-call observation contract

For the actual measured run, define the declared combined observation as:

~~~text
T(input, k) = (selectRun k (List.ofFn input)).2
W_c(trace, observation) = queryWork (fun _ _ => c) trace + observation.2.
~~~

Here c : Nat is a fixed declared charge per coordinate query, and .2 is the actual worker observation returned by that execution. First prove, for every actual observedSelect run:

~~~text
trace = List.ofFn (fun i => (i, input i))
observation = selectRun k (List.ofFn input)
trace.length = n
queryWork (fun _ _ => c) trace = c*n
W_c(trace, observation) = c*n + T(input, k).
~~~

Thus the source-call component is identified with the actual worker result, not chosen as an arbitrary resource or bounded by a free hypothesis. The acquisition coverage inequality queryWork ≤ W_c follows by Nat arithmetic from the definition and nonnegative actual source calls. If the existing Runs.resource_lower_bound is reused, its coversQueries argument must be discharged by this concrete proved inequality, not retained as a premise of the final algorithm bridge.

This declared model charges coordinate acquisition and the worker's measured source calls. The existing frontend model does not charge transcript bookkeeping, plan indexing, history-length calculation, final result projection, or physical time/memory. No full source-call or physical-runtime bound for an implementation of those frontend operations is inferred. Charging them as well would require a separate actual observation proof. This boundary must remain visible in the eventual public theorem documentation and optimality statement.

### 5. Actual cost ≤ F and the uniform affine upper bound

The known scalar source at exact 9d4b622ff74ec012d49733ccc0c4c0849b57ade4 was read without importing it. Its actual source names are F, F_monotone, F_rounded, and exists_affine_bound in Resources.SelectionRecurrence. F has base 483 for n ≤ 20 and recurrence children (n+4)/5 and (7*n+39)/10, with toll 19*n+54. It explicitly states that it is not an execution count.

The future bridge must consume the checked worker proof that actual T ≤ F(n) on a valid rank. That proof must be derived by the worker from actual measured helper/recursive calls, their size decrease and balance bounds, and the exact scalar recurrence. The scalar's monotonicity supports replacing actual child sizes by the rounded upper bounds. The coordinate bridge may use that completed theorem; it may not assume the target inequality or an affine bound on an arbitrary unconnected function.

Once that worker proof exists, derive for every actual book-protocol run at k : Fin n:

~~~text
W_c = c*n + T
    ≤ c*n + F(n)
    ≤ (c+A)*n + B.
~~~

Obtain A and B from the proved scalar exists_affine_bound. A and B are chosen before c, n, k, input, trace, and observation; they must not depend on a particular input, rank, or execution. c may be any natural constant for the exact/upper laws. For a uniform asymptotic statement, c is fixed independently of n. For n ≥ 1, absorb B to obtain W_c ≤ (c+A+B)*n, followed by the existing natural-bound-to-IsBigO machinery if needed. No finite worst-case supremum is presumed.

### 6. Lower bound and optimality comparison

For the actual readAll frontend, c ≥ 1 gives n ≤ c*n ≤ W_c on every input, even with duplicates, because it genuinely reads every coordinate. This is a property of that algorithm's execution.

For arbitrary deterministic correct total competitors in the existing coordinate model, preserve the original weaker domain: on each distinct input, Runs.queries_all and Runs.length_lower_bound give at least n query occurrences. Runs.work_lower_bound applies a positive per-query tariff; for a constant c, the length bound and queryWork_constant also give c*n ≤ queryWork. Repeated queries are charged repeatedly. Totality and the increasing Int input provide a concrete nonvacuous worst-case witness for every k : Fin n. Existing positive-size families (m+1) and linear_worst_case_bound avoid a fictitious Fin 0 rank or an assumed maximum over an infinite input space.

Combine this model-wide Ω(n) acquisition lower bound with the book algorithm's proved O(n) combined observation to state asymptotic optimality in this declared deterministic coordinate-query model. Do not infer a lower bound for arbitrary call tariffs admitting free bulk input, randomized competitors, or physical runtime. The actual source-call bridge is the concrete equality and upper bound in the preceding section, not an abstract correctness transfer.

## Planned connected examples and nonvacuity checks

| Case | Expected semantic/acquisition behavior | Required connection to actual worker |
| --- | --- | --- |
| n=0, natural k=0 | Actual empty trace, acquisition 0; outside valid-rank lower bound | Check the announced (none,2) branch from source; total W is then 2 |
| n=1, k=0 | One actual read; returned value is input 0 | Actual measured worker output and source count, not a replacement singleton algorithm |
| [8,3,5], valid ranks 0/1/2 | Results 3/5/8, exactly 3 reads, acquisition 3*c | Read each coordinate then run the book worker on the observed list |
| [4,4,4], valid ranks | Result 4 with multiplicity allowed, still 3 reads | No Nodup premise on worker correctness or totality |
| Distinct increasing input | Generic correct competitors must cover all coordinates | Reuse the existing actual witness construction and trace replay lower bound |
| Sizes 20 and 21, valid extreme/middle ranks | Exact cutoff boundary; base versus nested worker execution | Actual worker call observations satisfy its checked F theorem |
| Grouped sizes above cutoff with full/short final group | Same actual observation contract | Exercise measured chop/map and nested recursion through the real worker |

Existing repeated-plan [0,1,0] examples already protect per-occurrence charging; the book algorithm's readAll frontend itself has no repeated coordinate. Closed source-call numerals beyond the worker's announced empty case will be computed/proved from its checked source only, not guessed in this plan. Existence witnesses precede every-run bounds, and malformed supplied histories remain outside actual empty-history correctness claims.

## Resume gate and final hold

The next authorized implementation step requires root to supply the exact checked worker commit, source identities, actual API/printed statements, cost theorem, and authorization to integrate its dependencies. Read that source and its tariff before creating the new composition module and connected examples. Do not import/cherry-pick from the in-progress worker now. The six query source files, their public scope, and all saved evidence remain held.

After implementation, root still owns serial focused compilation, complete printed public/private inspection, full Chapter 3 check/audit, independent Standards/Spec review, and immediate verification. This plan is not a completed actual-selector bridge and grants no new acceptance credit. C03-083 and all 83 obligations remain in their existing status.

All own writes stop after this single provenance record is created and its preservation check completes. This bounded author slot can then be released.

## Successful read-only evidence appendix

The following values come from successful read-only check aa560f. Source-name counts are inventory counts, not exhaustive kernel audit totals.

~~~json
{
  "candidate": "47f12b48b93a1e223b9f743e067685f12f4da5b1",
  "tree": "19186fe71dbfdcc639a6bf7da778dd14fd8684ff",
  "index_sha256": "c0ca315976e13535a66ac222a28367aeb55497c8aaa51dd877d5cc3d9884504a",
  "clean": true,
  "counts": {
    "Applications/Selection/CoordinateQueries.lean": {
      "top_level_public": 22,
      "public_constructors": 2,
      "public_inspection_names": 24,
      "private": 0
    },
    "Applications/Selection/CoordinateReadAll.lean": {
      "top_level_public": 16,
      "public_constructors": 0,
      "public_inspection_names": 16,
      "private": 1
    },
    "Applications/Selection/CoordinateSensitivity.lean": {
      "top_level_public": 7,
      "public_constructors": 0,
      "public_inspection_names": 7,
      "private": 2
    },
    "Examples/CoordinateQueries.lean": {
      "top_level_public": 24,
      "public_constructors": 0,
      "public_inspection_names": 24,
      "private": 0
    },
    "Examples/CoordinateReadAll.lean": {
      "top_level_public": 11,
      "public_constructors": 0,
      "public_inspection_names": 11,
      "private": 0
    },
    "Examples/CoordinateSensitivity.lean": {
      "top_level_public": 13,
      "public_constructors": 0,
      "public_inspection_names": 13,
      "private": 0
    }
  },
  "private_names": [
    "Applications.Selection.CoordinateQueries.readPlan_run_from",
    "Applications.Selection.CoordinateSensitivity.exists_above",
    "Applications.Selection.CoordinateSensitivity.exists_below"
  ],
  "all95_public_blocks_preserved": true,
  "five_other_sources_identical": true,
  "all23_prior_provenance_files_unchanged": 23,
  "prepared27_and95_unchanged": true,
  "source_identities": {
    "Applications/Selection/CoordinateQueries.lean": {
      "bytes": 11106,
      "sha256": "ca1c0d339500e77aa14ca47420b9f7a11f213bbcd8ac113c3281c7f9690e6409",
      "blob": "49aa4bdf4beb2533fe273c3267ae031d862dbcf7"
    },
    "Applications/Selection/CoordinateReadAll.lean": {
      "bytes": 7611,
      "sha256": "ab2fd8949fe4a73e909cac90f99329fcd3b508e1b221e4411449a535f48f41ff",
      "blob": "e05374c65ff8dafaf6035ca6792271f70522c9ce"
    },
    "Applications/Selection/CoordinateSensitivity.lean": {
      "bytes": 6717,
      "sha256": "224724056815f73aff552ead23b7dd83af4078ad61009169e1b474f4b94476e6",
      "blob": "aa11abfc1bc0aba12c564b3f974f1b2dfed097b0"
    },
    "Examples/CoordinateQueries.lean": {
      "bytes": 8079,
      "sha256": "d90bd28ec4496105d9c5da80171a4c96a5ace119c0e178ded48f4f84ca8ad16d",
      "blob": "cdc5b93e5a5ebe720a30812a90b3a8cd388edaba"
    },
    "Examples/CoordinateReadAll.lean": {
      "bytes": 5626,
      "sha256": "8290a02bee2fb078439842c26a6cb46ec231aeb092b30659c8a3b674cc54b603",
      "blob": "b561b9fa3a67d6962e997659955d0c29eb846526"
    },
    "Examples/CoordinateSensitivity.lean": {
      "bytes": 3726,
      "sha256": "ed3d3d7cd41c97169893fdb5cf95e336a560f6f042ee70cea0a24ad7a6691828",
      "blob": "83ae3945dc67c142333d41317ae39a38ee3e2b7a"
    }
  },
  "record_identities": {
    "provenance/chapter03-query-bridge-implementation-20261104/root-correction1-20261104/candidate.json": {
      "bytes": 1609,
      "sha256": "010be09ec5ce559a6f524193a6b6071cd7b6d88147d28566f902c8c2bc2bb1e7"
    },
    "provenance/chapter03-query-bridge-implementation-20261104/root-correction1-20261104/git-commands.json": {
      "bytes": 631,
      "sha256": "1b4cf190e8a7f60080a45094395def65e1e3490b2412576359a2977172fc1b63"
    },
    "provenance/chapter03-query-bridge-implementation-20261104/root-correction1-20261104/preparation-count-assertion-failure.json": {
      "bytes": 712,
      "sha256": "15a03eccceb7f752858829d5131d807c9a4f0bf58c44d726fffbeba7d3e0fdda"
    },
    "provenance/chapter03-query-bridge-implementation-20261104/root-correction1-20261104/source.diff": {
      "bytes": 2053,
      "sha256": "6c60ea51b6e6e59f20547524a11f995d30e17f100fd597d2c4a31ab8d226ccc6"
    },
    "provenance/chapter03-query-bridge-implementation-20261104/root-correction1-20261104/starting-state.json": {
      "bytes": 6421,
      "sha256": "9c3fd7e899f60d9bef09505660e88271505bc9be3ed15b1b56ce5e5b3018fca2"
    },
    "provenance/chapter03-query-bridge-implementation-20261104/root-correction2-20261104/candidate.json": {
      "bytes": 846,
      "sha256": "46cc3a461aaa8cf7b06ab970079bba6736c9afa2d8f1980e8ff4a2985826a77e"
    },
    "provenance/chapter03-query-bridge-implementation-20261104/root-correction2-20261104/git-commands.json": {
      "bytes": 646,
      "sha256": "a3629e9e3f9e994ace6f4b1ad7edfa8bb6ea4d09863489bbd2bcb732c30d2ed5"
    },
    "provenance/chapter03-query-bridge-implementation-20261104/root-correction2-20261104/source.diff": {
      "bytes": 1063,
      "sha256": "30e47544b855b2693121de8098754e69eb47c5c80804d186a19e3cdd2d38ddf8"
    },
    "provenance/chapter03-query-bridge-implementation-20261104/root-correction2-20261104/starting-state.json": {
      "bytes": 1597,
      "sha256": "82988901134dcc052295514bc1e4e30df6ac1fc42fc6e28368c99fa873892d90"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/closed-evidence-reconciliation.json": {
      "bytes": 2224,
      "sha256": "2761c47d7168bbdf5ef1e2156a52a308246da432833efa109e0e459d6f2ae272"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/full.log": {
      "bytes": 3451,
      "sha256": "1f6172a3f1fbf28e5dbd5b3ba82b8cff45ce52364a5f69398cc155cce70d06b1"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/launch.json": {
      "bytes": 174,
      "sha256": "d965bbee8a0d5136d90bedfff003ab931ea5bcdf9e7bc89c3e98f54b77d67e45"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/native-records/output.log": {
      "bytes": 3174,
      "sha256": "e160c47f59c9c0e499a8d00e2ffbca82fa8aae6f643682b39faf6951aeda380e"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/native-records/result.json": {
      "bytes": 631,
      "sha256": "c72a9f7cb15b84552c7b465aed414460f2233de037fba508bfb80be1b4b13e42"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/native-records/start.json": {
      "bytes": 479,
      "sha256": "195b52ec2cc13da616c8b2637d377269bf21a2443db1a6ee8cd662fa2cd13bd9"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/outer-prefix.log": {
      "bytes": 121,
      "sha256": "f89522046dc8c9059ed497449ec98aef84601e1a1cc2bc6f3d1f3f6211a5475d"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/outer-suffix.log": {
      "bytes": 156,
      "sha256": "907943387ab8e594a36442c2f5331bf76e3717397a58dc57b416a9e32221965f"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/owned-terminal.json": {
      "bytes": 260,
      "sha256": "9554f7e850542a9feb093f8577861c3770f2d9f87aef50b1bb2b30a2cc8228c1"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/progress.json": {
      "bytes": 263,
      "sha256": "646afdae0a0bee41f5281c6105bd9c34d5beb887ee5fcedda59bba6216560807"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/request.json": {
      "bytes": 795,
      "sha256": "d623903a0e6b121778107984dbc7b4efa91ebe56ee90a818e07444e72d2e34f1"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/result.json": {
      "bytes": 1322,
      "sha256": "80d1e6f9248b3511bf0473c75aab8d98a350a0d794c7f68a5299dfe6d0e3783f"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/start.json": {
      "bytes": 988,
      "sha256": "4d6196e9f1716a58389d0084939872528243c31601ad13d36e4fb5404a8770a4"
    },
    "provenance/chapter03-coordinate-readall-focused-attempt3-20261104/verification.json": {
      "bytes": 867,
      "sha256": "70459831c371d1c496c29b3e1edd0352d41d64a00d1ec8f2a3600ee6880f05c9"
    }
  },
  "focused_pass": {
    "full_log_bytes": 3451,
    "full_log_sha256": "1f6172a3f1fbf28e5dbd5b3ba82b8cff45ce52364a5f69398cc155cce70d06b1",
    "native_bytes": 3174,
    "exact_prefix_native_suffix_reconciliation": true,
    "actual_exit": 0,
    "candidate": "47f12b48b93a1e223b9f743e067685f12f4da5b1",
    "preserved_verification_candidate_is_prior_XR_not_a_new_full_check": true
  }
}
~~~

