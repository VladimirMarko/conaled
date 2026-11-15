# XD01 — Independent Spec source assessment

Recorded 4 November 2026 by `/root/xd01_spec`. This reviewer did not author the
XD01 implementation, examples, source note, mapping, or attribution correction.
This is the Spec axis in the existing implementation/review loop. The independent
Standards axis is separate; its conclusions are not adopted here.

**Outcome: Blocked pending required validation and the final integrated candidate.**
The complete immutable source assessment is finished with **zero new concrete
Spec findings and zero unresolved mathematical/source-coverage findings**.
The retained low-severity finding **XD01-DOC-001 is independently confirmed fixed
in this source candidate**, using the recovered primary bytes. This is not a
passing acceptance result, a Lean elaboration result, or a chapter closure.

## 1. Immutable scope and requirements

| Item | Identity |
| --- | --- |
| Fixed original unit base | `a14977b9e316cc484ffad8a470d26b15615956c0` |
| Source candidate assessed | `62809ced86c561c7a6cce8b71e727177a3f17fb8` |
| Verified merge base | `a14977b9e316cc484ffad8a470d26b15615956c0` |
| Original implementation | `ffeaf8aed84184f49a13acb5c84e1fd608c9b7e8` |
| Correction successor | `62809ced86c561c7a6cce8b71e727177a3f17fb8` |
| Frozen requirements | `reviews/difference-list-cost-requirements.md` |
| Requirements SHA-256 | `cb215a33cce3dd258cca37b9d703522d19caf2da76767c01e573d268b3e92c4e` |
| Accepted Chapter 1, retained separately | `07e480f6ec9958d4975bb90151005b84f2907614` |
| First pending foundation acceptance, unchanged | `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |

The inspected command is `git diff BASE...CANDIDATE` using the full SHAs above.
The base is an ancestor, so the endpoint and three-dot task diffs agree. The
history contains exactly the implementation and its one-file provenance
correction beyond the base. No task path was omitted. The source-only checkout
`conaled-difference-list-costs` was clean at this exact candidate on entry and
at the final identity observation. Candidate content was read with `git show`,
so later development work does not silently alter the assessed snapshot.

| Changed path | Source assessment |
| --- | --- |
| `Applications/Resources/DifferenceListCosts.lean` | All 221 lines, definitions and proof bodies read |
| `Examples/DifferenceListCosts.lean` | All 234 lines, expected cases and derivations read |
| `SquareApplications.lean` | Full candidate entrypoint and exact one-import addition inspected |
| `docs/research/fdsa-difference-list-costs.md` | All 213 lines, formulas, provenance and limitations read |
| `docs/research/fdsa-reconstruction-map.md` | Full candidate mapping and exact 22-line XD01 addition inspected |

The complete patch, frozen requirements copy, source hashes, dependency blobs,
standards identities and explicit declaration inventory are preserved in
`provenance/difference-list-costs-spec-source-20261104/`. The static inventory is
**42 core declarations and 30 example declarations, 72 explicit public
source declarations total**. This is not a kernel audit count. No elaborated
public-type readback has yet been supplied for this unit.

The review read `REQUEST.md`, `CURRENT.md`, `STATUS.md`, `tickets/INDEX.md`, the
full XD01 requirements, original preflight, candidate handoff and retained
provenance correction. It also read the complete C02-088 scope clarification
and C02-108–112 rows. The Nix-only exception is recognized; exact pins and all
other mathematical and acceptance requirements remain. Chapter 1's recorded
acceptance is preserved. Historical draft status sentences in the old snapshot
are not a claim that Chapter 1 has become unaccepted after recovery.

Applicable instructions read include AGENTS, implement, code-review, the
review-and-fix procedure, architectural quality, domain guidance, GLOSSARY,
ADR0001/0010, example-driven-development and its worked example, review
heuristics, and README's actual normal/fresh and proof-boundary rules. This
assignment continues the enclosing loop and creates no additional review layer.

## 2. Reused definitions and actual execution boundary

The unchanged `Resources.Measured`, `pure`, `bind`, `CallCount.tick` and
`Resources.run` definitions were read. `bind` invokes its continuation on the
actual first returned value and adds observations in execution order. `tick`
adds one to the resulting natural observation. `run` is the existing recursive
list executor, with the next state obtained from the actual previous step.
XD01's `buildFrom` delegates to that executor instead of defining another one.

The imported project files `Measured`, `CallCount`, `Workload`, and
`SquareKit.ListFusion`, together with `lean-toolchain` and `lake-manifest.json`,
have identical Git blobs at the unit base, candidate, accepted Chapter 1 and
first foundation candidate. This supports source reconciliation; it is not
substitute compilation evidence. The inspected Batteries checkout is clean
for tracked files at `66e469188fe07963e5cf666c7d4433f45b8131c5`, matching all
four manifests. Both `DList.Basic` and `DList.Lemmas` were read in full.

`Builder α` remains an ordinary function from a list suffix to a measured list.
Its observation is a declared natural count. The interface adds no payload
order, equality, finiteness or inhabitance requirement and remains universe
polymorphic. `Rep` and `AppCost` quantify over every suffix separately; neither
predicate is used to smuggle in the other. Their hypotheses are meaningful:
empty/singleton constructors satisfy them, and the generic composition/push
laws establish them for the returned callbacks. The full builder laws then
derive their final contracts from these constructors instead of assuming them.

The fixed creation tariff captures already supplied callback references. It
neither applies those callbacks nor charges their prior construction. The
application tariff counts identity/singleton/composition invocations. It does
not count the executor's list traversal, scanner comparisons or control,
physical allocations, machine instructions or host-runtime sharing. These
boundaries are consistently stated in the source and note.

## 3. Per-claim assessment of the reusable core

Every source declaration is included in the following groups. Names are under
`Resources.DifferenceListCosts`. These are source judgments, pending the
compiler's explicit type elaboration and the integrated audit.

| Declarations | Intended mathematics and inspected connection |
| --- | --- |
| `Builder`, `Rep`, `AppCost` | Ordinary callback alias; fixed ordered prefix at all suffixes; independent uniform application cost at all suffixes. No accidental payload instances or existential cost witness hides the contract. |
| `empty`, `singleton`, `empty_apply`, `singleton_apply` | Actual charged callbacks return the original suffix or one prepended payload, each with count one. Equations include arbitrary suffixes. |
| `empty_rep`, `empty_appCost`, `singleton_rep`, `singleton_appCost` | Constructive satisfiable base contracts; zero-length prefix and one-element prefix preserve order and multiplicity. |
| `compose`, `compose_value`, `compose_cost` | Actual `g` application precedes `f`; `f` receives `value(g suffix)`. The unconditioned cost equation retains that value-dependent second invocation and both observations plus one. |
| `compose_rep` | Value order is prefix of `f` followed by prefix of `g`, via list append associativity. This agrees with ordinary function composition, despite the opposite application order. |
| `compose_appCost` | Universal suffix hypotheses justify the cost of `f` at the actual intermediate list. Natural addition permits the displayed `k+l+1` order; no equality of values is used to infer a cost. |
| `createEmpty`, `createSingleton`, `createCompose`, and all three `_eq` laws | Each returns the corresponding callback with construction count one; no application or prior creation is included. All supplied callbacks and payloads remain arbitrary. |
| `pushRun`, `pushRun_eq` | Existing measured bind sequences a singleton creation and a composition creation, hence count two and actual callback `compose f (singleton a)`. |
| `pushRun_rep`, `pushRun_appCost` | Append exactly one payload to the represented prefix and add two application entries. Both derive from the general composition laws under their separate premises. |
| `buildFrom`, `buildFrom_nil`, `buildFrom_cons` | Existing executor runs actual pushes from the supplied seed; nil costs zero. The successor equation passes the returned callback to the actual remaining execution. |
| `buildFrom_cost` | Construction is exactly twice the number of items for every supplied seed; no seed creation or application contract is assumed or charged. |
| `buildFrom_rep` | The arbitrary seed prefix is followed by items in their original order. The induction carries both seed and prefix and uses the actual composed next seed. |
| `buildFrom_appCost` | Final application count is `k+2*n` at every suffix, assuming only the seed's separate uniform `AppCost`. The proof carries the changed seed and its updated count. |
| `build`, `build_cost`, `build_rep`, `build_appCost` | Actual initial charged identity creation followed by `buildFrom`; exact prefix is the input list, and construction and each later application both have count `2*n+1`. Empty input remains covered. |
| `toDList`, `toDList_apply`, `toList_toDList` | Existing Batteries record receives the actual erased callback. Its invariant follows from `Rep` at arbitrary and empty suffixes; the toList law returns the precise prefix. |
| `toDList_eq_ofList` | Existing `ofList_toList` gives equality of DList values after erasing observations. It does not equate histories or measured costs. |
| `toDList_compose` | Uses the proved prefix law, DList append/toList, and `ofList_toList` to preserve append order and duplicates. |
| `toDList_pushRun` | Uses ordinary DList push/toList and representation equality. The pinned fused push has the same value; its application/construction cost is not identified with this explicit compositional model. |

No claim assumes correctness or the final work bound that it is intended to
establish. The generic seed/callback hypotheses are exactly interface contracts
for externally supplied values. The corresponding closed builder family
supplies them from actual constructors. Every count uses the natural-number
observation model explicitly; there is no cost claim about arbitrary erased
functions merely because they satisfy the extensional D invariant.

## 4. Connected cases and all example declarations

Names are under `Examples.DifferenceListCosts`. The general client programs are
actual measured binds, and their value and cost projections are proved
separately through the public laws.

| Frozen case and declarations | Independent expectation and checked-source connection |
| --- | --- |
| Ordered composition: `ordered_composition`, `standard_composition_value` | Prefixes `[1]` then `[2]` with suffix `[9]` produce `[1,2,9]`, count three. The concrete proof uses public `compose_rep` and `compose_appCost`; the general standard-DList client uses public representation laws and standard append. Order would be distinguishable if composition were reversed. |
| Arbitrary expensive captures: `expensive_capture` | Supplied callbacks have independent counts `p` and `q`, including zero. Creation is one; later application is `p+q+1`. The proof uses `compose_cost`, preserving actual execution before commutative arithmetic. |
| One materialization: `materialize`, `materialize_eq`, `construction_application_split` | One actual construction followed by application; value is `items ++ suffix`, count `4*n+2`. Public `build_rep`, `build_cost`, `build_appCost` supply the two phases separately, each `2*n+1`. |
| Two materializations: `materializeTwice`, `materializeTwice_eq` | Construct once, invoke the returned callback twice on the two actual suffixes, retain both lists, and add all three counts for `6*n+3`. The second result is not replaced by the first cached list. |
| Concrete duplicates: `duplicate_values`, `duplicate_values_twice` | `[3,1,3]` preserves duplicates and the nonempty suffixes. The public combined laws give fourteen and twenty-one; the generic split law gives seven for each phase at length three. The independent expected values/counts are also stated before the source declarations and in the note. |
| Empty/singleton: `empty_payload_boundary`, `singleton_boundary` | Empty programs at payload type `Empty` cost two and three for one/two applications; singleton at arbitrary payload and suffix costs six. These exercise the universal public laws without an inhabitant or equality structure for the payload type. |
| Supplied singleton seed: `extendSingleton`, `extendSingleton_eq` | Extend an already supplied singleton callback by `n` items, then apply it: value `(a::items) ++ suffix`, count `4*n+1`. The proof uses both seed-general laws, explicitly excluding its earlier creation. |
| Fused value bridge: `fused_push_value` | Actual compositional push application agrees with Batteries' fused push application at every suffix, using the actual record's erased function. It does not claim a cost equality. |
| Charged identity: `identity_value_cost` | For every callback and suffix, composition with charged identity preserves the value and adds two invocation entries. No `Rep` or uniform-cost premise is needed. A measured-builder Monoid identity is not installed. |
| Linear empty-prefix history: `padded`, `padded_rep`, `padded_appCost`, `padded_empty_value` | Each extension actually composes with charged identity; prefix and DList value remain empty while application count is `2*n+1` for all suffixes. Induction uses public composition contracts. |
| Output-length boundary: `no_bound_from_output_length` | For every natural affine coefficient/intercept, the concrete witness `n=B+1` has empty output but cost greater than `K*0+B`. This is a proved family boundary, not an unqualified machine-runtime theorem or an assumed impossibility of all analysis. |
| Shared self-composition: `doubled`, `doubled_creation`, `doubled_rep` | The measured recursive program captures the previously returned callback twice in one new composition. Creation count is `n+1`; the represented prefix remains empty. It counts actual creation events in the declared program, without claiming heap-pointer behavior. |
| Self-composition application: `doubled_application_add_one`, `doubled_appCost` | Both actual invocations appear in `compose_cost`. The induction is applied at the original suffix and at the actual intermediate callback result. First proving cost plus one equals `2^(n+1)` justifies the natural-subtraction corollary `2^(n+1)-1`. |
| Construct/apply shared history: `materializeDoubled`, `materializeDoubled_eq` | Actual measured bind combines construction and application, giving unchanged suffix and `n+2^(n+1)` total; no discarded cost or memoized output is introduced. |
| Concrete shared boundary: `four_shared_closure_extensions`, `four_shared_closure_extensions_materialized` | Four extensions create five callbacks, later application on `[9]` has count thirty-one, and total construction/application is thirty-six. These derive through the public exact family laws. |

These groups account for all 30 example declarations. The expected constants
were retained; none was chosen to hide an execution reversal or omit a phase.
The source connections establish nonvacuous uses of both value and cost
contracts. They do not replace universal theorems, elaborated-type inspection,
or the exhaustive audit.

## 5. Documentation, public reachability and retained chapter scope

The entrypoint's sole new import is `Examples.DifferenceListCosts`, which itself
imports the core. Thus both new modules are intended to enter the normal public
closure and audit. Actual source-policy/closure verification remains a required
full-check result rather than an assertion that this manual inspection ran it.

The note's tables and formulas agree with the declared programs: creation and
one application each `2*n+1`, combined once `4*n+2`, combined twice `6*n+3`,
seeded extension `4*n+1`, shared history creation `n+1`, application
`2^(n+1)-1`, and combined `n+2^(n+1)`. Its claim that the application history
can exceed the number of creation events is supported by actual self-composition.
The mapping adds only this shared groundwork and accurately leaves unit
validation pending. No earlier coverage is deleted by the task diff.

The July 27, 2026 book PDF was rehashed at its supplied exact identity. Its
printed pp.21–22 were inspected through the recovered text. The source asc
starts from a singleton-prefix callback and applies to `[last]`; its continuation
composes the accumulated callback with a singleton. The candidate distinguishes
that source path from its reusable identity-seeded builder. It keeps the later
conditional `2*r-3` count for actual ascending runs of length at least two as
Chapter 2 work. Empty/singleton scanning bypasses that path.

The separate C02-110/111 source correspondence and C02-112 complete mutual
scanner/control/descending/emitted-run/merge-dispatch bounds remain mandatory.
C02-109's repeated append versus cons/reverse implementation is also a separate
chapter obligation; the old source note does not close it by presenting XD01.
The parent now has additional chapter work, but this review does not silently
incorporate or approve that work. The shared-unit boundary matches the frozen
requirements and does not weaken the 112-obligation chapter specification.

## 6. Retained finding XD01-DOC-001

**Previous issue:** the initial preflight and original source note attributed
`Natural_Mergesort.thy` to the separate Isabelle revision. The exact candidate
contains the recorded documentation-only correction; the original history and
preflight remain preserved with their explicit erratum.

The raw regenerable inputs were initially absent in the recovered workspace.
The parent restored the exact public primary files into
`provenance/xd01-primary-source-20261104/`. This reviewer then independently
rehashed the archive and separate theory, read the tar member directly, verified
that the extracted reading copy has identical bytes, and inspected the actual
Natural_Mergesort source including its header and singleton-seeded recurrence.
No inference from a filename or the author's earlier assurance replaces those
checks.

| Primary input | Bytes | Independently verified SHA-256 |
| --- | ---: | --- |
| Dated AFP `afp-Efficient-Mergesort-2026-10-26.tar.gz` | 5,506 | `148ba9c80cf876a77219b1209dfa5df9bafe1aef1388bc84fc7088ff9c550708` |
| Exact member `Efficient-Mergesort/Natural_Mergesort.thy` | 6,723 | `2fd5d686d7702385cc76f84e153034fe9b460ec94c0f751a56e5bd5ea017fe51` |
| Separate `Sorting.thy` at `f86f290225eebcc52c1ae7dba2e098f405f51c21` | 14,846 | `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca` |

The AFP theory actually imports `HOL-Data_Structures.Sorting`. The separate
file declares theory `Sorting`; its exact commit-pinned retrieval record is
retained. The corrected note distinguishes these origins, records both hashes,
and explicitly says that the October AFP archive postdates the July book. It
makes no unsupported identical-July-source claim. Disposition for this Spec
source round: **fixed and independently confirmed**. The stable finding ID and
its original evidence remain; final integrated review still must retain this
correction.

## 7. Validation and final continuation

| Gate | Status in this source assessment |
| --- | --- |
| Full frozen unit requirements and five-path source scope | Completely assessed |
| Every explicit public declaration and connected case | Source statement/derivation assessment complete, zero new findings |
| Source provenance correction | Independently confirmed against exact primary bytes |
| XD01 focused Lean build and public elaborated-type inspection | Pending; no successful result supplied |
| Final integrated candidate and conflict resolutions | Pending assessment of that immutable successor and affected inputs |
| Full candidate source-policy/coverage/build/exhaustive audit | Pending for XD01 integration |
| Matching successful `.lake/verification.json` | Pending |
| Both independent axes on the final same candidate | Pending; this report is only the Spec source round |
| Immediate qualified `./check.sh --verify-candidate HEAD` before acceptance | Pending |

The parent reports a live first XD01 focused invocation in its development
checkout. No terminal outcome is assumed here. This reviewer started no compiler,
ran no audit, polled no parent or historical session, and changed no candidate,
ref, index, dependency, cache, accepted branch, foundation record, or other
reviewer's file. Only this Spec report and its assigned provenance were written.

No new tooling, dependency or compiler configuration change is in this unit.
The README's normal-versus-fresh triggers must be applied to the final candidate
with the retained accepted native fresh baseline; this report does not demand
an expensive fresh rerun merely because of recovery. It also does not waive any
required gate. The first foundation acceptance remains prior work under the
user's exact instructions and is not replaced by this assessment.

Continue this same Spec record after compiler repairs and integration, retaining
the fixed base/scope or explicitly recording the workflow's justified base
transition. Reassess the full unit with particular attention to changed proof
inputs, public types, import/map resolutions, XD01-DOC-001, and actual terminal
validation evidence. Approval of this old source snapshot would not approve a
new tip; this report presently grants no approval at all.

**Final source-round result:** base `a14977b9e316cc484ffad8a470d26b15615956c0`,
candidate `62809ced86c561c7a6cce8b71e727177a3f17fb8`; new Spec findings **0**,
unresolved mathematical/source findings **0**, retained fixed provenance
finding **XD01-DOC-001**; overall Spec outcome **Blocked pending validation**.
