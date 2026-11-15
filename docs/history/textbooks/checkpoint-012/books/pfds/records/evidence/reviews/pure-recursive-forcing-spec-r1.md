# Local10019 — independent Spec review, round1

## Outcome

**Blocked.** The mathematical/source review is complete for the frozen candidate below. There are **two unresolved documentation findings** and **one separate acceptance-evidence blocker**. I found no defect in the inspected formal statement/proof chain for the bounded pure-domain nontermination and cache-reuse requirements. That assessment is not acceptance and does not replace the missing full build, exhaustive audit or final candidate verification.

| ID | Severity | Status | Summary |
| --- | --- | --- | --- |
| PURE-SPEC-DOC-001 | Medium | Unresolved | The current pure-suspension implementation record overgeneralizes exceptional exit into preservation of an uncached thunk. |
| PURE-SPEC-DOC-002 | Low | Unresolved | The incorporated foundation record still says the local10019 source claim is unproved, despite the new theorem and focused evidence. |
| PURE-SPEC-VAL-001 | Acceptance blocker | Unresolved | No complete-candidate build/audit verification record or immediate final verification exists for this candidate. |

This is the first independent Spec acceptance review, by `/root/pure_suspension_review/spec`, within the existing review loop. I did not read the parallel Standards report or coordinate substantive conclusions with its author. Contributor/author preparation was treated as evidence to inspect, not as independent approval. No compiler, build, dependency, source, Git/index/ref or external tracker mutation was performed. Only this assigned report was written.

## Immutable scope and requirements

Workspace root: `/workspace/scratch/ca9a61d0bf30`.
Candidate checkout: `/workspace/scratch/ca9a61d0bf30/validation-purity`.

- Candidate: `ea8afa12706d30cdc69ece1a172d5f21a3ea1809`.
- Incorporated ticket base: `a3feaff319ad5fad912fb8bdc113f33fea4e2a60`.
- Original complete integration base: `b422800fb5b6dc1253823057c0ea71644274d77c`.
- Ticket scope: 49 changed files and 6 commits.
- Complete integration scope: 58 changed files and 10 commits.
- Exclusions: none.

I independently checked HEAD, clean status, both merge bases, both changed-file sets, both ordered commit lists and every manifest file hash. All matched `session/validation/pure-suspension-candidate-r1.json`. Its SHA-256 is `32df55521cb1c88e900398a069e3697a43b40ce556a34ec6b5477d3a14a879c5`. Neither base is an accidental divergent-branch comparison. The review covers the complete integration scope, including the inherited relocation/force-observation changes and the four direct FRP imports. The later, separately owned write-count development is not part of this candidate or this review.

The three full saved requirement documents were read and their fingerprints checked:

| Requirement document under `session/requirements` | SHA-256 |
| --- | --- |
| `REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `pure-recursive-forcing.md`, version1 | `57ddefb472b9393a3fe890f880ad4eb94893f5aa6bd8be912da2d7dfa4f4ec55` |

Applicable guidance includes the frozen `AGENTS.md`, its architecture/domain/language and ADR pointers, the existing review-loop procedure, `code-review` and example-driven statement review. The user's local-ticket and durable-checkpoint instructions supersede the repository's GitHub tracker default. This report neither accepts local10014 nor moves Chapter2, Chapter4, AppendixA or whole-book/thesis coverage to complete.

## Findings

### PURE-SPEC-DOC-001 — exceptional exit is described too broadly

**Severity:** Medium. **Disposition:** unresolved on this candidate. **Kind:** inaccurate explanation of the preserved raw semantics; no corresponding Lean theorem defect found.

**Locations:** `docs/research/pfds-pure-suspensions.md:90` and `docs/research/pfds-pure-suspensions.md:134`.

The first location says exceptional exit leaves the thunk uncached. The second makes the same generic assertion, including an identical retry, in the section that explicitly discusses unrestricted raw value-cell persistence and effectful reentry. The actual raw guarantee is that this pending memoize frame performs no successful write when it unwinds; it retains the memory reached by the body. It does not roll back an inner successful write or require the relevant cell still to be a thunk.

Concrete candidate evidence:

- `Applications/Suspensions/Machine.lean`, `raised_skips_memoize`, retains the supplied current memory.
- `Applications/Suspensions/Pure/Forcing.lean`, `raise_memoize`, relates the actual no-write exit and retains the current represented memory; the public statement does not assert a blanket raw thunk-preservation law.
- Unchanged `Examples/SuspensionMachine.lean`, `outer_exception_preserves_inner`, has an actual outer raised outcome with a value already cached at the same suspension address by an inner successful force. `outer_exception_then_hit` handles the outer exception and then observes a hit on that cache.
- `Examples/SuspensionValuePersistence.lean`, `Exceptions.raised_body_can_repeat`, establishes the unchanged thunk and identical six-step retry for its specific captured fixed-exception body. It does not quantify over arbitrary effectful bodies.

**Requirement:** version1 requires preserving the full effectful machine and its outer-exception counterexample, and stating exactly which successful reuse facts follow. Thesis AppendixA's exception convention preserves reached effects. The surrounding record must not invite an unconditional rollback or retry interpretation that the retained formal examples refute.

**Requested correction:** describe the general exit as skipping that frame's own successful cache write while retaining reached memory, including a cache an inner evaluation may already have installed. Describe the unchanged thunk and identical retry as the behavior of the checked fixed-exception client. Keep the pure-domain theorem and the unrestricted counterexample distinct; no semantic or proof weakening is requested.

### PURE-SPEC-DOC-002 — stale proof-status claim in the incorporated foundation record

**Severity:** Low. **Disposition:** unresolved on this candidate. **Kind:** contradictory current coverage/proof-status documentation.

**Location:** `docs/research/pfds-suspensions.md:123`.

This current implementation record says local10019/TU.A.4.PURE remains unproved. The same candidate now contains `source_reentry_not_terminates`, the actual empty-source cyclic application and focused terminal evidence for them. Its new `pfds-pure-suspensions.md` describes those results. Proof implementation/focused compilation and independent acceptance are different states; the former is no longer absent even though the latter remains blocked.

This is within the retained integration scope even though the sentence predated the bounded ticket diff. It is an undated present-tense statement in a current repository implementation record, not a dated preparatory snapshot whose historical wording must be retained.

**Requirement:** preserve accurate book/thesis coverage and local-ticket status; distinguish focused evidence from complete acceptance without erasing implemented progress.

**Requested correction:** link the pure-suspension implementation record and state that the precise pure-domain implication and connected source case now have focused evidence, while local10019 remains unaccepted pending its full gate/audit, independent reviews and final verification. Continue to require both local10014 and local10019 for the relevant AppendixA/Chapter4 acceptance. Do not change the historic preparation reports into retrospective approvals.

### PURE-SPEC-VAL-001 — exact complete-candidate acceptance evidence is absent

**Severity:** acceptance blocker. **Disposition:** unresolved. **Kind:** validation evidence, separate from source findings.

At inspection, the frozen checkout had no `.lake/verification.json`. The manifest explicitly records `acceptance: false` and says its own full gate/audit/final verification has not started. All supplied successful target checks are focused development checks. No prior candidate's verification record can establish acceptance of `ea8afa12706d30cdc69ece1a172d5f21a3ea1809`.

**Applicable requirement:** version1 and `docs/agents/review-loop.md`, candidate-validation section, require the stock isolated `./check.sh --candidate HEAD` with the applicable full build and exhaustive proof/axiom audit, preserved exact-candidate verification evidence, both independent axes, and immediate `./check.sh --verify-candidate HEAD` before acceptance. The public entrypoint and inherited integration changes require this same complete gate.

**Remedy:** after any corrections, capture the actual new immutable candidate, retain the full original integration scope and all findings, and supply its successful stock gate/audit record and logs. Both reviewers must assess that candidate and matching evidence. Run and preserve immediate final verification against the approved exact commit before acceptance. Do not treat the separate prerequisite901 run, prior foundation reviews, focused output reuse, or input-hash matching alone as this gate.

The runtime-interrupted prerequisite checks and their recovery records are separate from this acceptance scope. Their missing terminal status is not a successful result and does not convert a later run into evidence for this candidate. Local10014 and Chapter2 remain independently unaccepted.

## Independent source and mathematical assessment

### Source boundary

I visually inspected the primary thesis AppendixA pages133,134 and135, including the forcing rules, exception convention, modified Rule137/SRec and the self-forcing remark. The central source locator is printed135 / physical PDF147. I also inspected the supplied book's printed32 suspension/capture/cache description and the available official 1990 Standard ML Definition section6.6/Rec and Rule137 renders (`research-pfds/sml90/page-68.png`, `page-69.png`, `page-74.png`). The latter renders display reconstructed pagination; the section/rule identities, not later-edition numbering, are the relevant inherited references.

Source identities remain the recorded exact assets:

- Book: `b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41`.
- Thesis: `f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072`.
- Official 1990 Definition reconstruction: `2ad9e869db05f5a4316bc60b7170fb00789410436651c1a8f425a88098e8e9d1`.

No manuscript or source-page copy is added to this report or repository. Available source locators and metadata are in `session/research/union-source-identities.json`, `sml90-source-identity.json` and `suspension-foundation-inventory.md`.

The theorem deliberately concerns the stated inherited Core fragment with explicit pure restrictions. It is not a full Standard ML parser, full initial basis, type-safety theorem, converse adequacy result or global complexity theorem. Those are not smuggled into this bounded requirement. The original raw transition still permits effectful reentry and overwrites. No blackhole marker or exception-cache transition has been substituted.

### Domain restrictions are hereditary and have meaningful boundaries

`Pure/Syntax.lean` predicates the existing `Core.Expr` and `Core.Pattern`. Reference allocation, read, assignment, reference patterns and generative exception declarations are excluded. Functions, data, strict application, ordered matching, recursive declarations, suspension patterns, fixed exception packets, raise and handlers remain. Effect purity alone is not presented as source well-formedness.

`CodeAllowed` additionally checks nested recursive form: function/delay RHSs and distinct names at each recursive declaration. `ValueAllowed`, `EnvAllowed` and `GroupAllowed` inspect stored code and earlier captures without an infinite traversal of freshly unrolled group members. The member/body-environment preservation theorems then justify actual unrolling. The duplicate-name creation client demonstrates why a shadowed allocated delay is absent from effective SRec targets; this is a concrete reason for the distinctness premise.

The predicate does not assume typing, nonempty function matches, identifier classification, termination or acyclicity. Admitted malformed application and wrong return-mode clients retain actual faults. A source theorem over this domain cannot be silently advertised as a preservation theorem for the published effectful extension.

Primitive laws are separate and inspect actual operation results. `OperationCompatible` ranges over every immutable world and related input pair. It contains no desired expression-evaluation result, heap adequacy or no-reentry premise. `OperationPreserves` independently prevents returned values from introducing excluded code or tokens. Positive identity/integer/Boolean operations make the laws usable; the negative returned-reference-closure example shows compatibility alone is insufficient. The pointer-equality discriminator uses two actual allocations with one pure meaning and proves address-renaming equivariance does not imply this stronger compatibility law. It is expressly an excluded diagnostic operation, not a claim that SML suspension types admit equality.

### Finite descriptors, immutable meanings and raw cells remain separate

`Pure/Value.lean` stores the original RHS list and earlier environment in a finite group descriptor. Member construction reverses the source list consistently with the raw creation fold's prepend order, and every member keeps that same descriptor. Body entry extends the earlier capture with those members. The raw `Env.rec` and the group-member representation agree on one finite unrolling, including recursive function/suspension cycles and a closure whose capture refers back to its suspension.

`ValueRep` is relational. It is not assumed to be injective or functional. Different physical addresses may have identical meanings; an empty raw recursive component need not force a unique syntactic descriptor interpretation. The specific address inversions in the connected examples recover a meaning from the world lookup and exact suspension constructor, not from a nonexistent global injectivity theorem.

`StateRep` requires bounded raw memory and justified occupied cells at world entries. Other raw cells may exist. A thunk needs represented effective code/capture only; no body-termination witness is required. A cached value needs a represented pure result and an actual finite evaluation of the immutable body's exact input. Fresh world extension preserves existing meanings, but is not confused with mutable raw-cell extension or arbitrary state validity.

`Creation.PendingGroup` keeps a genuine preclose receipt: new meanings are prospective while raw captures are still unclosed. Actual creation allocates fresh cells, establishes effective target provenance and uses SRec to close them. Old cells and their certificates survive. The process assumes no future result of a new body. `WorldDomain` derives admissibility from the receipt/group member relation and derives allowed cached results from their stored finite witnesses and the separate output-preservation law.

### Certificate construction and execution simulation are not circular

`ActiveHistories` indexes every pending raw memoize occurrence by stack position. It allows the same address at multiple positions; the concrete before/after cyclic configurations satisfy it with duplicate active addresses. Each occurrence records an actual prior pure prefix from its immutable body input to the current control with the inner portion of the pure continuation.

On normal return, `BodyHistory.completed` closes the already executed top body prefix with delivery. `return_memoize` supplies that result to actual raw memoization, constructing the certificate that a later hit may consume. It does not assume a first write or require the current cell to remain a thunk. On a hit, `reuse_cached` extracts a certificate already stored in the input invariant and replays it through the current unmatched inner pattern. It does not recursively assume the theorem for an unproved future body.

`ConfigRep` contains memory/control/frame/history relations, not a simulation field. The private `ExecutionBlock` is a package of previously proved actual local transitions/prefixes, not another evaluator or an axiom. `Ordinary.IsOrdinary` and its complement exhaust the special shapes. All ordinary controls and return protocols were inspected, including primitive failure, pattern mismatch, ordered fallback, raised unwinding and invalid continuations.

`RecursiveStep` consumes the actual positive `3 * bindings.length + 2` raw creation/closing prefix and one pure step. Stable `ConfigRep` is asserted at its boundary, not falsely at intermediate raw creation controls. The strict interior no-body-event law accounts for those intermediate states. The active outer-force creation client exercises preservation of an older history while allocating a new recursive thunk.

`finite_correspondence` uses strong induction on the remaining **raw** evaluation count. Its recursive call strips a positive actual raw prefix. Pure cache expansion is supplied by an existing certificate, so a longer pure replay does not threaten that induction. All result constructors remain represented, including raised packets, matching outcomes and diagnostic faults.

`body_entry_correspondence` instead inducts on the index of an actual observed raw prefix. It needs no finite enclosing execution. Ordinary/one-step cases advance the actual history; the multi-step recursive interval is skipped using its proved absence of a body event. The result is a represented admitted pure configuration at the actual raw body event, not an assumed alignment for an arbitrarily selected pure run.

### The source self-reentry implication is genuine and universal in finite outcomes

An old occurrence history followed by the next actual pure force step gives a strictly positive recurrence at the same immutable body/effective environment. Continuation decomposition handles every outcome, including a body fault and a normal body whose caller faults. From a hypothetical finite plugged evaluation it extracts an isolated finite evaluation with the needed count inequality. Deterministic count uniqueness contradicts the positive recurrence. No type-safety assumption removes the fault cases.

The raw active-force theorem obtains a contradiction by finite correspondence. `body_event_iff` recovers the exact inspected address and current thunk from the unchanged raw event. Prefix stripping then transports the contradiction to the original source start. `finite_body_entry_not_active` derives finite-run nonreentry afterward; nonreentry is never an invariant premise used to prove itself.

The cyclic source client discharges initial state/environment/domain and primitive laws from empty memory, supplies the independently reduced actual 29-transition prefix and next body0 event, and identifies the old memoize occurrence at index3. It calls `source_reentry_not_terminates`, which constructs the histories through the general bridge. Its universal search-none theorem is a consequence for every fuel, not a conclusion inferred from exhausting finitely many budgets. Although that source uses Empty primitives, the independent nonempty scalar/identity clients make the primitive laws substantive.

### Cache applications close the intended missing connections

The finite repeated-force source retains raw21/pure23 counts and constructs its final represented cache through the general finite correspondence. The admitted expected-function-fault source uses the same theorem and retains its five-step fault result.

The literal returned-suspension source has raw15/pure15 executions. Inversion of the actual returned address relation recovers the original empty capture and world meaning from the theorem's existential output. Later reuse consumes that recovered state/meaning and obtains the stored two-step body certificate, raw hit1/pure replay3, and complete later raw3/pure5 matching runs with unchanged raw memory. Its caller binding is distinct from its original body capture.

The recursive-closure application reuses `returningClosure` exactly. It first recovers address0's meaning from actual raw5/pure1 recursive creation. It strips those prefixes and applies finite correspondence to the actual residual raw48 execution. Immutable extension preserves the recovered meaning; cached lookup supplies the actual successful body witness and closure representation. Inversion of that representation recovers the captured self-address relation. The source executions remain raw53/pure51, with the concrete raw one-allocation/one-body/one-write/one-hit trace.

The later false application reaches the captured suspension after an actual 18-step prefix. It invokes `reuse_cached` under the actual four-frame continuation and combines hit1/replay3 with the independently checked 17-step suffix, obtaining raw36/pure38 and the exact same raw final memory. This is a hit after body completion, not active body reentry. No final world, cache certificate or acyclic-capture assumption is postulated. **PREP-10019-01 is addressed at the static implementation/client level**, subject to the acceptance blocker and any correction candidate review.

### Persistence and count limits remain substantive

`ValuePersistence.HasValue` asserts existence of some value payload at an exact address. Bounded allocation cannot replace that occupied cell; SRec preserves the value constructor; assignment and memoization write values. The actual one-step, finite-run and observation laws therefore establish constructor persistence. The finite-run use of `ConfigBounded` supplies future allocation freshness, not purity, typing or active-address uniqueness.

The assignment client proves an actual 7-to8 payload change, then obtains the later hit from the public prefix theorem. The inherited effectful reentrant client retains two cache writes; the new theorem only excludes future body entry after a value already exists. The raised-body retry client explicitly proves its particular memory is still a thunk and does not apply `HasValue` to an uncached cell.

These are distinct from pure semantic cache correctness and from event multiplicity. **PREP-10019-02 remains an explicit scope boundary:** the candidate has no universal at-most-one cache-write trace theorem, and none is required as a substitute for its stated certificate reuse and constructor-persistence claims. Concrete one-write counts remain concrete. Equal pure meanings at two new addresses do not imply alias sharing, equal memory, equal event traces, equal raw/pure costs or host cost bounds. Finding DOC-001 concerns prose that blurs one exception boundary, not a missing universal write-count requirement.

## Inherited integration and existing interfaces

The full integration diff and every changed source/client were inspected, with relevant unchanged definitions. Those include raw Syntax/Machine/Rules/Store, the Progress finite evaluation/termination/search/uniqueness interface, Prefix observations and store/SRec operations. The new source-specific pure interpretation reuses the existing Progress, Resources and Durability machinery. It does not replace the generic evaluator or infer stronger equal-count transport from relational values.

Inherited `Relocation` transports actual raw transitions, memory, faults/events and finite executions both ways under explicit primitive equivariance and the private-hole address injection. `ForceObservation` separately supplies bounded initial memory, fixed existing cell contents and a fixed capture. Its normal/raised force-delay results preserve the explicit additional12/10 transitions and omit only the private cell through the stated relation. The reference-allocation/mutation clients and dangling-capture fault discriminator exercise those hypotheses. The contract does not claim equal ordered force/direct traces or an equivalence of faults, exhausted budgets or divergence.

The four FRP changes are direct imports only. Their existing mathematical bodies are unchanged and the newly explicit dependencies correspond to existing uses (natural-number monotonicity, finite-set operations, Archimedean real reasoning and Nat size). `SquareApplications.lean` includes all new connected client modules. That integration is statically present but has not yet passed its own full gate. The complete file inventory is appended below, tied to the manifest rather than excluding inherited files because they belong to another ticket.

## Focused evidence inspected and its limits

I inspected command records, source/configuration hashes and matching compiler logs, including the five principal terminal records below. Their recorded relevant inputs match this candidate; the record flags say inputs stayed unchanged during each focused run. Commands use the pinned offline Nix environment and `LEAN_NUM_THREADS=1`, followed by `lake build` for the named example target. These are development targets, not `./check.sh --candidate HEAD`.

| Record stem under `session/validation` | Target | Exit/jobs | Recorded input count |
| --- | --- | --- | --- |
| `suspension-pure-execution-r1` | `Examples.SuspensionPureExecution` | 0 / 764 | 39 |
| `suspension-pure-no-reentry-r1` | `Examples.SuspensionPureNoReentry` | 0 / 768 | 43 |
| `suspension-pure-cached-program-r1` | `Examples.SuspensionPureCachedProgram` | 0 / 764 | 41 |
| `suspension-pure-cached-closure-r1` | `Examples.SuspensionPureCachedClosure` | 0 / 768 | 45 |
| `suspension-value-persistence-r3` | `Examples.SuspensionValuePersistence` | 0 / 748 | 23 |

Exact evidence identities:

| Record stem | JSON SHA-256 | Log SHA-256 |
| --- | --- | --- |
| `suspension-pure-execution-r1` | `c9b894c89023b68df7ee7c6234d79121afb76ba4309a448beafab9a4d9e069ed` | `2f6172f9da5c1ecf3546684711fff2ea732eddb28118a5cb104814975e5b05c1` |
| `suspension-pure-no-reentry-r1` | `510a892dbb09765f63636d6eeed589f2ed865501c7f7afee37ed3cb3385f008a` | `b7574f55b30139ef8f76ffaa30533616c2a5ea41d22956ac56a99cd818443bca` |
| `suspension-pure-cached-program-r1` | `53986990f29de549dc73722ab449b6c704873606f203deb75a271e6f06587f50` | `d31728d2068daba9199199e570103acb0ca188b37e650ec3c91c84dfe1146529` |
| `suspension-pure-cached-closure-r1` | `bf8ae8c36481edd3cc447ed0b2fb806f9fc021c8ee207426a10150b7734af912` | `619f6dbb616697a340d51d32d303f056225df7189adcd83d3187bf423515b659` |
| `suspension-value-persistence-r3` | `f472c2a8715e135f359791b70cf8006553ac394c9ceb8d5ac91069327148e8f3` | `885b27abd63f6f59bdde8f84d115c4d2b61cc739c590c0cdc79c059311439707` |

I also checked current-input focused evidence for the machine, representation, recurrence, domain, history/simulation, forcing, domain-state, world-domain, ordinary core/client, recursive step, reentry, raw decomposition, BodyEvent, raw recursive-stack extension and force observations. Representative additional exact matches include BodyEvent r2 (744 jobs), Decomposition r2 (745), raw-recursive-stack r1 (785) and ForceObservation r2 (751). The current Compatibility r2 record/log is in `active-validation`, not the older r1 copy in `session/validation`: JSON SHA `9f59a68e14cbd029cfc68cd541ece27f2cee43d1f5cc830fb4f370463757feb2`, log SHA `7f22bda5bf323d95b78ee77cd088ebc9c0bc741c4109796071eed5269c9f9fe9`; its26 inputs match and its target passed751 jobs.

Older evidence was not silently promoted. Pure Values r1-retry and Compatibility r1 failed on older bytes. Creation r4 and Memory r4 passed their then-current inputs but some imported/example bytes subsequently changed; later matching closure checks cover the current dependencies. Raw Recursive r3 has an older Recursive hash, while raw-recursive-stack r1 matches the current extension. Relocation r6 failed overall on its then-current example despite core progress; ForceObservation r2 is the later matching successful client closure. An unchanged-input flag on an old or failed record is not a current success.

The exact full integration candidate still has no verification record. These checks do not establish the exhaustive declaration/axiom audit, public-entrypoint success, absence of all undeclared validation inputs or immediate final verification. No optional re-testing or compiler run was initiated by this reviewer.

## Prior findings and retained disposition

| Prior item | Independent round1 disposition |
| --- | --- |
| PREP-10019-01 — missing connected cached recursive closure | Addressed statically by the actual creation-to-residual-run-to-cache-to-later-hit client and matching focused evidence; acceptance remains subject to VAL-001. |
| PREP-10019-02 — successful-write multiplicity boundary | Retained explicitly; no general write-count theorem is asserted or inferred. No new count requirement is imposed. |
| Earlier incomplete method/model/integration snapshots | Historical preparation, not acceptance or present proof absence. The current formal source and terminal evidence were inspected directly. DOC-002 corrects only the current foundation record's stale present-tense claim. |

## Complete reviewed integration-file inventory

All paths below are relative to the frozen `validation-purity` checkout identified above. The manifest supplies exact individual SHA-256 values; this review independently matched all58.

- `Applications/FRP/Demand.lean`
- `Applications/FRP/Finite.lean`
- `Applications/Suspensions/BodyEvent.lean`
- `Applications/Suspensions/Decomposition.lean`
- `Applications/Suspensions/ForceObservation.lean`
- `Applications/Suspensions/Pure/Compatibility.lean`
- `Applications/Suspensions/Pure/Continuation.lean`
- `Applications/Suspensions/Pure/Creation.lean`
- `Applications/Suspensions/Pure/Domain.lean`
- `Applications/Suspensions/Pure/DomainState.lean`
- `Applications/Suspensions/Pure/Execution.lean`
- `Applications/Suspensions/Pure/Forcing.lean`
- `Applications/Suspensions/Pure/History.lean`
- `Applications/Suspensions/Pure/Machine.lean`
- `Applications/Suspensions/Pure/Memory.lean`
- `Applications/Suspensions/Pure/NoReentry.lean`
- `Applications/Suspensions/Pure/Ordinary.lean`
- `Applications/Suspensions/Pure/Recurrence.lean`
- `Applications/Suspensions/Pure/RecursiveStep.lean`
- `Applications/Suspensions/Pure/Reentry.lean`
- `Applications/Suspensions/Pure/Representation.lean`
- `Applications/Suspensions/Pure/Simulation.lean`
- `Applications/Suspensions/Pure/Syntax.lean`
- `Applications/Suspensions/Pure/Value.lean`
- `Applications/Suspensions/Pure/WorldDomain.lean`
- `Applications/Suspensions/Recursive.lean`
- `Applications/Suspensions/Relocation.lean`
- `Applications/Suspensions/ValuePersistence.lean`
- `Examples/FRP.lean`
- `Examples/IndefiniteService.lean`
- `Examples/SuspensionBodyEvent.lean`
- `Examples/SuspensionDecomposition.lean`
- `Examples/SuspensionForceObservation.lean`
- `Examples/SuspensionPureCachedClosure.lean`
- `Examples/SuspensionPureCachedProgram.lean`
- `Examples/SuspensionPureCompatibility.lean`
- `Examples/SuspensionPureCreation.lean`
- `Examples/SuspensionPureDomain.lean`
- `Examples/SuspensionPureDomainState.lean`
- `Examples/SuspensionPureExecution.lean`
- `Examples/SuspensionPureForcing.lean`
- `Examples/SuspensionPureHistory.lean`
- `Examples/SuspensionPureMachine.lean`
- `Examples/SuspensionPureMemory.lean`
- `Examples/SuspensionPureNoReentry.lean`
- `Examples/SuspensionPureOrdinary.lean`
- `Examples/SuspensionPureRecurrence.lean`
- `Examples/SuspensionPureRecursiveStep.lean`
- `Examples/SuspensionPureReentry.lean`
- `Examples/SuspensionPureRepresentation.lean`
- `Examples/SuspensionPureSimulation.lean`
- `Examples/SuspensionPureValues.lean`
- `Examples/SuspensionPureWorldDomain.lean`
- `Examples/SuspensionRelocation.lean`
- `Examples/SuspensionValuePersistence.lean`
- `SquareApplications.lean`
- `docs/research/pfds-pure-suspensions.md`
- `docs/research/pfds-suspensions.md`

Review saved at 2026-11-02T22:57:13.217857+00:00.

## Return to coordinator

Candidate `ea8afa12706d30cdc69ece1a172d5f21a3ea1809`; ticket base `a3feaff319ad5fad912fb8bdc113f33fea4e2a60`; complete integration base `b422800fb5b6dc1253823057c0ea71644274d77c`.

**Spec outcome: Blocked, with findings present.** Static source findings:2 documentation findings (worst Medium); formal implementation findings:0; separate validation blockers:1. Carry all three stable IDs to the next round. I remain available for the correction candidate and exact-gate continuation in this same review loop.
