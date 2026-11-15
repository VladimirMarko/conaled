# XD01 independent Standards assessment — frozen source candidate

Date: 2026-11-04. Reviewer: `/root/foundation_continuation`, assigned the
independent Standards axis. This reviewer did not author the XD01 core,
connected examples, documentation, or original provenance correction.

**Overall outcome: Blocked. Source assessment complete; zero new concrete
findings and zero unresolved source findings. HOLD for compilation and the
remaining immutable integrated-candidate gates.** This is not final approval,
unit acceptance, or Chapter 2 acceptance. The separate foundation candidate
and its retained Standards assessments are unaffected.

## 1. Immutable identity and complete scope

| Item | Recorded identity |
| --- | --- |
| Fixed original unit base | `a14977b9e316cc484ffad8a470d26b15615956c0` |
| Frozen reviewed candidate | `62809ced86c561c7a6cce8b71e727177a3f17fb8` |
| Merge base | `a14977b9e316cc484ffad8a470d26b15615956c0` |
| Candidate tree | `a34f8c4a74db112e5e30003b226150b5ede0f0d0` |
| Original source draft | `ffeaf8aed84184f49a13acb5c84e1fd608c9b7e8` |
| Branch | `work/fdsa-builder-costs` |
| Source-only review worktree | `conaled-difference-list-costs` under the recovered workspace |
| Frozen requirements SHA-256 | `cb215a33cce3dd258cca37b9d703522d19caf2da76767c01e573d268b3e92c4e` |
| Separate accepted Chapter 1 tip | `07e480f6ec9958d4975bb90151005b84f2907614` |
| Separate first pending acceptance | Foundation `f17cc6b1a2bf44215b16202ed0fcee2b5c130761` |

The authoritative exact unit requirements are
[difference-list-cost-requirements.md](difference-list-cost-requirements.md),
read in full. The governing [request](../REQUEST.md), local
[XD01 ticket](../tickets/FDSA-XD01.md), C02-109–112 scope clarification, complete
[design preflight](../research/difference-list-cost-preflight.md), complete
[candidate handoff](difference-list-cost-candidate.md), and complete
[provenance erratum](difference-list-provenance-correction.md) were also read.
The historical preflight must be read with that erratum.

The review uses the exact endpoint diff
`git diff a14977b9e316cc484ffad8a470d26b15615956c0 62809ced86c561c7a6cce8b71e727177a3f17fb8`.
The fixed base is an ancestor, so the corresponding three-dot scope is the
same. The complete difference is five paths, 691 added lines, with no removed
lines. Both commits were inspected: the original feature and the one-file
provenance correction. The checkout was clean at initial inspection and at
evidence capture. There are no task-change exclusions within the five-path
scope. Unchanged inherited Chapter 1 work is context, not a new XD01 approval.

| Complete changed path | Bytes | Candidate SHA-256 |
| --- | ---: | --- |
| `Applications/Resources/DifferenceListCosts.lean` | 10,086 | `567683626b9a46d07c465ceb44faaafc941e2dc1c83491b093599ca7f8c698a5` |
| `Examples/DifferenceListCosts.lean` | 9,315 | `09165e6a1ccb0b0e45b7ddc6083883aa5bf67bc931c59ff44707d1726ffbe102` |
| `SquareApplications.lean` | 8,328 | `45449f16d4004eee544182a3cd3f8364d4c7d68430be14ef0426b61617e8280a` |
| `docs/research/fdsa-difference-list-costs.md` | 10,679 | `fd01432541c9b27ad83def6192e4a3b75d6b77ae7490ec11a2bf665324f1246e` |
| `docs/research/fdsa-reconstruction-map.md` | 17,221 | `50411c5753aa57bda40dc374a736b0b3c66f360fe5002e51d5473a8f2183fdf9` |

All five complete candidate files, not just the handoff descriptions, were
read from their frozen Git objects. The two Lean files contain 72 explicit
source-level declarations: 42 in the core and 30 in the examples. This is an
inspection inventory, **not** an elaborated declaration count or proof-audit
result. The dedicated [inspection identity record](../provenance/difference-list-costs-standards-source-20261104/identity.json)
retains file, requirement, guidance, dependency-source, and primary-input hashes.

## 2. Applicable standards and method

The complete applicable instructions were read: `AGENTS.md`; the code-review
skill and its heuristic list; the implementation skill and shared review loop;
the example-driven-development skill's statement-review guidance; architectural
quality and domain guidance; `GLOSSARY.md`; the ADR index and ADRs 0001/0010;
the shared language direction; and README's development, build/audit, and
proof/execution rules. The enclosing ticket/integration workflow was retained
without starting another review hierarchy. Source-level requirement coverage
below supports the Standards methodology assessment; it does not replace the
independent Spec axis.

The explicit Nix exception in `REQUEST.md` supersedes the shell-only rule.
It does not change Lean/Lake 4.35.0, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, the nine manifest pins, the proof
restrictions, immutable-candidate checks, independent axes, or immediate final
verification. No compiler, Lake, checker, cache, or environment mutation was
performed by this reviewer.

For statement review I inspected every explicit definition and theorem,
including the proofs and the examples' connections to public laws. I checked
quantifier scope, payload universes, hypotheses, semantic projections, callback
order, arithmetic boundaries, and what each named client actually executes.
Elaborated-type inspection is still pending with compilation; this report does
not assert that inferred types or proof scripts have passed Lean.

Relevant unchanged implementations were inspected at the frozen candidate:
`Resources.Measured`, `Resources.CallCount`, `Resources.Workload`, and the
existing ordered-summary batch/fusion laws. The complete pinned Batteries
`DList.Basic` and `DList.Lemmas` sources were read from revision
`66e469188fe07963e5cf666c7d4433f45b8131c5`, using the available dependency tree
read-only.

## 3. Architecture and reuse assessment

The core is an ordinary domain module in `Applications/Resources`, with
connected clients in `Examples`. It introduces the requested function alias
`Builder α := List α → Measured (List α) Nat`, not a competing DList datatype,
expression language, interpreter, state executor, cost typeclass, or measured
Monoid instance. Existing `Measured`, `pure`, `bind`, `CallCount.tick`, and
`run` provide the construction and sequencing mechanisms.

`Rep` and `AppCost` are separate ordinary predicates. Value representation does
not require or imply an application bound, and cost reasoning does not demand
a representation premise when it is unnecessary. Public operations work over
arbitrary `α : Type u`; no payload equality, order, or inhabitance is added.
The empty-payload client is a meaningful boundary witness for that generality.

The value bridge constructs the existing Batteries record using the erased
application function. Its invariant follows from `Rep` at the arbitrary suffix
and at `[]`. Its equality and composition/push results consume the existing
`ofList_toList`, `toList_append`, and `toList_push` laws. They introduce no
replacement library semantics and carry no cost information into DList equality.

`buildFrom` is exactly an instance of existing `run`, and `buildFrom_cons`
uses `run_cons`. The local induction for the all-suffix `Rep` theorem composes
the public prefix law at each actual seed. Existing `run_state`,
`run_value_fusion`, and `batch_decode` provide related erased fold statements,
but do not directly provide this quantified suffix relation without additional
invariant/decode packaging. This short contract induction is not a second
executor or a duplicate generic fusion framework. Cost inductions establish
new observations independently of those value laws.

The concrete Nat tariff is the required model, not an unjustified loss of a
previously generic observation interface. The shared executor remains generic.
The model does not claim compiler allocation, runtime evaluation, physical
memory, or transport of these new proofs to arbitrary mathematical settings.
Native Lean clients remain direct.

Applying the review heuristics produced no concrete architecture or maintenance
finding. The wrapper names identify model operations and useful contracts;
recurrence proofs serve different propositions; the standard DList conversion
has a concrete external interface purpose. No speculative framework or
unrelated responsibility is introduced.

## 4. Complete core statement assessment

The following rows cover all core declarations. The observations are source
assessments pending elaboration, not independent kernel verification.

| Declarations | Intended contract and assessment |
| --- | --- |
| `Builder`, `Rep`, `AppCost` | Ordinary suffix callback; `Rep` fixes an ordered prefix for every suffix, while `AppCost` fixes one Nat observation for every suffix. Quantifiers are in the required order. Neither assumes a final workload bound. |
| `empty`, `singleton`, `empty_apply`, `singleton_apply` | Actual callbacks return the supplied suffix or one cons and charge one application entry. No constructor/suffix traversal charge is silently inferred. |
| `empty_rep`, `empty_appCost`, `singleton_rep`, `singleton_appCost` | Separate, satisfiable base contracts; the empty constructor needs no payload value. |
| `compose`, `compose_value`, `compose_cost` | Execute `g suffix`, then apply `f` to that actual result, then charge the composition entry. The cost equation retains `(g suffix).2 + (f (g suffix).1).2 + 1`. It does not evaluate `f` at the original or empty suffix. |
| `compose_rep` | Prefix order is `prefixF ++ prefixG`, despite execution order `g` then `f`. It uses both all-suffix value contracts and append associativity; order and duplicates are retained. |
| `compose_appCost` | Uses the two uniform contracts at their actual arguments. The result is `k+l+1`; commuting Nat costs is justified and does not alter value order. No `Rep` premise is needed. |
| `createEmpty`, `createSingleton`, `createCompose`, their three `_eq` laws | Return the requested callback with one creation observation. Definitions do not apply a supplied callback, traverse a suffix, or repeat the supplied callback's prior construction. The fixed capture tariff is explicit. |
| `pushRun`, `pushRun_eq`, `pushRun_rep`, `pushRun_appCost` | Two actual creation operations through `bind`; prefix extends on the right by `[a]`; application observation increases by two. Value and cost premises remain separate. |
| `buildFrom`, `buildFrom_nil`, `buildFrom_cons` | Existing ordered executor with the supplied seed; zero construction charge on empty items, and two plus the actual continuation's construction observation on cons. Seed creation and executor traversal are outside this tariff. |
| `buildFrom_cost` | `2 * items.length` for every supplied callback, with no representation or application-cost premise. The induction is over actual construction steps. |
| `buildFrom_rep` | Given `Rep f prefix`, returns the all-suffix representation of `prefix ++ items`; the evolving seed and prefix are generalized in the induction. |
| `buildFrom_appCost` | Given `AppCost f k`, returns the all-suffix cost `k + 2 * items.length`; no final cost is assumed and no value-erasure theorem supplies the count. |
| `build`, `build_cost`, `build_rep`, `build_appCost` | Actual initial `createEmpty` followed by the same seed-general construction. Construction and each application separately cost `2n+1`; the represented prefix is exactly `items`. |
| `toDList`, `toDList_apply`, `toList_toDList`, `toDList_eq_ofList` | Erase only observation, prove the existing invariant, recover the original application value and prefix, and identify the standard value representation using its existing equality law. All statements remain conditional only on `Rep`. |
| `toDList_compose`, `toDList_pushRun` | Existing DList append and fused push receive the same ordered value. These are representation equalities; there is no statement equating their construction or application tariffs. |

In particular, the general dependent cost equation appears before its uniform
specialization. This matters for a supplied callback whose observation depends
on the length of its argument: the second invocation would see the list
produced by the first. The inspected source retains that dependency throughout;
the constant-cost theorem is justified by its explicit all-suffix premises.

## 5. Connected examples and negative boundaries

All 30 explicit declarations in the example module were inspected, including
the measured program definitions and every proof. The expected results agree
with the frozen pre-code calculations. Proof connections below are source
connections; their successful Lean elaboration remains pending.

| Retained client or family | Public connection and independently assessed consequence |
| --- | --- |
| `ordered_composition` | Applies `compose_rep` and `compose_appCost` to singleton contracts. Prefixes `[1]`, `[2]` at suffix `[9]` produce `[1,2,9]` and three application entries. This distinguishes append order. |
| `standard_composition_value` | Uses `toList_toDList` and the standard append law to compare the represented composition with ordinary DList append. Its premises are the two actual `Rep` contracts. |
| `expensive_capture` | Supplied callbacks return observations `p` and `q`; creation is one, application is `p+q+1` via the actual dependent cost equation. `p=0` or `q=0` is permitted and no positive-cost assumption is hidden. |
| `materialize`, `materialize_eq`, `construction_application_split` | An actual `bind` combines construction with one application. The proof uses `build_rep`, `build_cost`, and `build_appCost`; total is `4n+2`, with the separate components each `2n+1`. |
| `materializeTwice`, `materializeTwice_eq` | One construction followed by two actual applications, then a pure pair of both results. The proof charges both arbitrary suffixes via `build_appCost`, yielding `6n+3`. No cached materialized list replaces the second invocation. |
| `duplicate_values`, `duplicate_values_twice` | Instantiate those general client theorems on `[3,1,3]`; preserve order, duplicate occurrences, and distinct nonempty suffixes. Expected totals are 14 and 21. |
| `empty_payload_boundary`, `singleton_boundary` | Empty input at payload type `Empty` gives totals 2 and 3 for one/two applications. Singleton plus arbitrary suffix gives total 6. These are applications of the universal programs, not merely isolated reductions of an unrelated function. |
| `extendSingleton`, `extendSingleton_eq` | Consume all three seed-general laws. A supplied singleton seed represents `[a]`, has application cost one, and requires no new seed-creation charge; extending `n` items then applying costs `4n+1`. |
| `fused_push_value` | Directly compares the measured push's returned list with pinned Batteries' actual fused `fun suffix => f (a :: suffix)` application. Reduction is appropriate here: it verifies the independent external interface's value, and asserts no cost equality. |
| `identity_value_cost` | An arbitrary callback composed with charged identity returns the same value but gains two application entries. The proof keeps its actual observation; no measured Monoid identity is asserted. |
| `padded`, `padded_rep`, `padded_appCost`, `padded_empty_value` | Repeated composition with identity preserves the empty prefix and standard decoded value while application grows as `2n+1`. Both general composition contracts are used. |
| `no_bound_from_output_length` | For every Nat `K` and `B`, picks `n=B+1` and uses the proved padded cost to exceed `K*0+B`. Together with the preceding value law this is a nonvacuous common-empty-output counterexample. It is not a claim that source-generated push chains lack bounds. |
| `doubled`, `doubled_creation`, `doubled_rep` | Exactly one recursive construction, followed by one `createCompose f f`, captures the supplied callback twice. Creation is `n+1`; the empty-prefix contract is preserved. |
| `doubled_application_add_one`, `doubled_appCost` | The induction invokes its hypothesis at both the original suffix and the actual inner result. The proved equality `application+1=2^(n+1)` justifies the later Nat subtraction `2^(n+1)-1`. No unproved rational or predecessor manipulation is used. |
| `materializeDoubled`, `materializeDoubled_eq` | Actual construction/application bind yields the original suffix with total `n+2^(n+1)`, using creation and successor application laws separately. |
| `four_shared_closure_extensions`, `four_shared_closure_extensions_materialized` | Instantiate the general family: five creation events, application 31 returning `[9]`, and combined total 36. The counts observe unfolded invocations, not only the five distinct construction events. |

The arbitrary seed and supplied-cost premises are demonstrably satisfiable:
the base callbacks provide witnesses and the generic/Empty clients instantiate
them. The negative families expose genuine distinctions rather than proving
only an implication with unusable assumptions. No extra examples are required
merely to mirror each helper's proof syntax.

## 6. Source and license provenance; XD01-DOC-001

The book input is the pinned July 27, 2026 edition, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Its printed pp.21–22 show the singleton-seeded ascending worker and the prose
distinguishing repeated ordinary append from difference-list composition and
later application. The saved extracted passage was compared with the resource
scope; the candidate does not redistribute the book or claim that this shared
model proves the whole source scanner.

The original compact recovery deliberately omitted regenerable primary reading
copies. During this review root recovered the exact small inputs into
`provenance/xd01-primary-source-20261104/`. This reviewer independently read and
hashed the actual bytes, inspected archive membership, and read the entire
`Natural_Mergesort.thy` member. This is direct current confirmation, not reliance
only on the older author's assertion.

| Recovered input | Bytes | Independently confirmed SHA-256 |
| --- | ---: | --- |
| `afp-Efficient-Mergesort-2026-10-26.tar.gz` | 5,506 | `148ba9c80cf876a77219b1209dfa5df9bafe1aef1388bc84fc7088ff9c550708` |
| Exact member `Efficient-Mergesort/Natural_Mergesort.thy` | 6,723 | `2fd5d686d7702385cc76f84e153034fe9b460ec94c0f751a56e5bd5ea017fe51` |
| Separate commit-pinned `Sorting.thy` | 14,846 | `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca` |

The archive member equals the saved reading copy byte-for-byte. The archive's
ROOT identifies the AFP session and includes `Natural_Mergesort`; the theory
credits Christian Sternagel and imports `HOL-Data_Structures.Sorting`. Its actual
worker starts from `(#) a`, extends by composition with singleton prefixes,
and eventually applies to `[last]`. The separately recovered Isabelle file
has its own `Sorting` theory header and author, and matches the hash associated
with revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`.

The correction commit changes only the research note's attribution paragraph.
The current note correctly separates those two origins, records the dated AFP
archive/member hashes, and discloses that the October archive postdates the
July book. The earlier preflight remains byte-for-byte historical evidence at
SHA-256 `a0bd75c09ea1208c880dc87d5e8abe88be207c1e411b118519e7cf6237984232`, with
its erroneous attribution explicitly corrected by the retained erratum. It
has not been silently rewritten or used as a current incorrect attribution.

The retained source inventory records Isabelle's BSD-3-Clause provenance and
the AFP entry's BSD selection, with notice-retention requirements for later
translations. I did not re-fetch those license pages. The actual pinned
Batteries files retain their Apache 2.0 headers. The five changed candidate
paths add the original measured interface, its examples, imports, and notes;
they do not vendor or copy the AFP/Isabelle implementation into this unit.
The source/notice boundary is therefore explicit, and no concrete provenance
or license-record defect was found in this scope.

### Stable finding disposition

| ID | Prior severity and issue | Current independent Standards disposition |
| --- | --- | --- |
| `XD01-DOC-001` | Low; the original note/preflight attributed the AFP theory to the separate Isabelle revision. | **Fixed in frozen candidate `62809ced...`; source correction independently confirmed.** Exact archive/member and separate theory identities, actual headers, one-file correction diff, and retained erratum agree. This disposition does not waive any unit validation gate or substitute for the Spec axis. |

No new finding identifiers were issued. The absence of a compiler result is a
validation blocker, not a newly invented source defect. The historical
uncompiled labels are accurate for this reviewed frozen candidate.

## 7. Public integration and retained chapter scope

`SquareApplications.lean` adds `import Examples.DifferenceListCosts`.
That example module imports the new core, so both added Lean files are present
in the public source import chain. Both set `autoImplicit false` and
`warningAsError true`. Source inspection found no admission, new axiom, unsafe
or partial definition, native-evaluation shortcut, or kernel-bypass option.
This direct inspection is not the exhaustive transitive proof audit.

The research note accurately separates creation, application, and scanner
observations. The reconstruction-map addition is limited to the shared unit,
marks it as uncompiled, and points to the remaining chapter work. Earlier
Chapter 1 status wording inherited from the old unit base is historical context;
it is not evidence overturning accepted Chapter 1 or approving a later merge.

The candidate does not claim to close the actual `asc` correspondence or
C02-112's scanner/control, descending construction, emitted-run construction,
and merge dispatch. Its later `2r-3` target explicitly requires a run of length
at least two, the actual singleton seed, and `r-2` extensions. Empty/singleton
runs bypass that worker path. Ordinary repeated append versus cons/reverse
remains C02-109. Source comparison counters are not silently enlarged by the
closure tariff. These deferrals match the frozen XD01 scope rather than
silently narrowing it.

## 8. Validation evidence and continuation boundary

The read-only source inspection established the exact clean candidate, the
ancestor/base relationship, all five file hashes, the requirement hash, the
actual import chain, the unchanged tooling/dependency pins, and the primary
input identities above. `git diff --check` against the fixed unit base returned
exit 0 with no diagnostics. No build, proof audit, or candidate verification
command was run by this reviewer.

| Gate | Status for frozen XD01 `62809ced...` |
| --- | --- |
| Complete independent Standards source assessment | Complete; no new or unresolved source findings |
| Prior provenance finding | Fixed and independently source-confirmed |
| Focused Lean elaboration of both new modules | Pending for this frozen candidate |
| Elaborated public statement/type inspection | Pending |
| Reconciliation with accepted Chapter 1 and cumulative development | Separate integration work; not approved by this source assessment |
| Full immutable integrated-candidate build, source/coverage checks, exhaustive audit | Pending |
| Matching closed terminal log, actual exit, native command record, success verification record | Pending for the final integrated candidate |
| Both independent axes passing on the same final candidate | Pending |
| Immediate qualified `./check.sh --verify-candidate HEAD` before acceptance | Pending |

These source-only additions change no compiler, dependency, check tooling, or
configuration. They do not by themselves trigger a new fresh baseline under
README. The already accepted native fresh baseline is not invalidated by
workspace recovery. The coordinator must apply the actual normal-versus-fresh
rules to the final stable inputs and any concrete new trigger; focused success
will not replace a full candidate check/audit in either mode.

If root composes this draft into cumulative development and makes compiler
corrections, continue this same full five-path scope and finding record. Pin the
new integrated candidate and applicable base explicitly; inspect every source
change, affected dependency, public type, and integration resolution. Reuse
this completed source reasoning where its inputs remain identical. Do not
substitute a narrow proof-fix diff or a different draft for the full unit scope.

Immediately before eventual acceptance, the approved candidate must have both
independent passing axes, all applicable successful terminal evidence, a clean
matching source/dependency state, and the required immediate verification.
This report provides none of those missing terminal results by implication.

## 9. Final source-stage outcome

- Fixed base: `a14977b9e316cc484ffad8a470d26b15615956c0`.
- Reviewed candidate: `62809ced86c561c7a6cce8b71e727177a3f17fb8`.
- Scope: all five changed paths, with complete formal source and statement
  inspection, architecture/reuse assessment, connected-case assessment, public
  entrypoint review, and independently confirmed provenance correction.
- New findings: **0**. Unresolved source findings: **0**. Retained
  `XD01-DOC-001`: **fixed with source evidence**. Worst unresolved issue: none.
- Overall Standards outcome: **Blocked pending required validation — HOLD**.

The foundation Standards source report and recovery preflight remain unchanged.
Its first outstanding acceptance at `f17cc6b...` still requires actual terminal
evidence before that independent axis can pass. This reviewer remains available
for that continuation and for later XD01 correction/evidence assessment.
