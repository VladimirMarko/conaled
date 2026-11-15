# Pure recursive forcing — independent Standards review, round 1

## Outcome and immutable scope

**Outcome: Blocked.** This candidate has one unresolved medium documentation defect, one unresolved blocking acceptance-evidence finding, and one low evidence-preservation finding fixed during this review. No Lean theorem or implementation defect was established by the independent static review. That assessment is not a successful build, exhaustive axiom audit, or acceptance.

Reviewer: /root/pure_suspension_review/standards, the Standards axis of the existing local10019 review loop. The Spec report was not consulted. Author preparation was read as a set of claims to inspect, not as independent acceptance. No compiler was run and no source, build, configuration, dependencies, Git state, or refs were changed by this reviewer. The only reviewer-authored artifact is this report.

| Identity | Exact value |
| --- | --- |
| Frozen candidate | ea8afa12706d30cdc69ece1a172d5f21a3ea1809 |
| Checkout | /workspace/scratch/ca9a61d0bf30/validation-purity |
| Incorporated ticket base | a3feaff319ad5fad912fb8bdc113f33fea4e2a60 |
| Ticket scope | 49 files, 6 commits |
| Original full integration base | b422800fb5b6dc1253823057c0ea71644274d77c |
| Full integration scope | 58 files, 10 commits, no exclusions |
| Candidate manifest | session/validation/pure-suspension-candidate-r1.json |
| Manifest SHA256 | 32df55521cb1c88e900398a069e3697a43b40ce556a34ec6b5477d3a14a879c5 |

Both supplied bases were independently checked as ancestors, with the expected merge bases. Actual nonempty Git diff file sets and commit sets were compared with the manifest. Every recorded changed-file SHA256 matched the candidate. The ticket's six commits are 6f2290f2ab916468d499e5de388ed7be7408dc96, 86b394f5537cd9a61ac9b9708b5fef8face6d047, 41895aaff989c81cfe1ed23243e773be308d8711, a0ceaca91d86107d2365e82c50a92e1147ef46e8, 501a95463f455b52ea839eb8bbcf6ab9379862e4, and ea8afa12706d30cdc69ece1a172d5f21a3ea1809. The exact authoritative commit lists are in the manifest; the full integration also includes the four foundation commits listed there.

The complete requirements were read, with independently matched fingerprints:

| Requirement | SHA256 |
| --- | --- |
| session/requirements/REQUEST.md | b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499 |
| session/requirements/REQUEST-union-v2.md | 3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c |
| session/requirements/pure-recursive-forcing.md | 57ddefb472b9393a3fe890f880ad4eb94893f5aa6bd8be912da2d7dfa4f4ec55 |

This is the first Standards acceptance review of this candidate. A separately prepared later candidate does not alter round 1's identity or findings.

## Findings and required dispositions

### PURE-STD-DOC-001 — Medium — unresolved

**The public implementation record overstates the effect of exceptional suspension completion.**

Evidence: candidate docs/research/pfds-pure-suspensions.md, lines 132–134, in the unrestricted ValuePersistence discussion, says that a body that raises leaves its thunk uncached and supports another identical execution. Lines 85–91 also describe exceptional exit as leaving the thunk uncached without stating the needed local qualification.

The preserved raw semantics does not establish that universal claim. Applications/Suspensions/Machine.lean, raised_skips_memoize at line 384, preserves the memory already reached by the exceptional return and pops the current memoize frame without that frame's own successful cache write. Applications/Suspensions/Pure/Forcing.lean, raise_memoize at line 131, has the corresponding precise local contract. Neither law reverts inner effects or establishes that the address still contains its original thunk.

There is an existing independently inspected counterexample in Examples/SuspensionMachine.lean: outer_exception_preserves_inner at line 189 and outer_exception_then_hit at line 201. An outer body raises after an inner successful force has cached address 1; the cached value remains, and a later force hits that cache. The examples retain two body entries and one write, followed by a hit in the handled case. Examples/SuspensionValuePersistence.lean, Exceptions.raised_body_can_repeat at line 132, proves the narrower specific six-step execution whose thunk actually remains unchanged. Its result does not generalize to every raising body.

Applicable standards: docs/agents/architectural-quality.md requires preserving semantic distinctions and checking claims against actual interfaces; the example-driven-development statement-review guidance requires comparing explanations, hypotheses, and conclusions with independently understood intended behavior. The local10019 requirements and dispatch explicitly preserve outer-exception/inner-cache behavior.

Required remedy: explain that an exceptional memoize frame performs no own successful cache write and retains the memory reached by the body, including inner effects. Attribute repeatable identical execution to the particular unchanged-thunk exception client. Scope the earlier local-correspondence explanation accordingly. This finding requires a documentation correction and review of its exact new candidate; it does not require changing the Lean transition or adding a replacement theorem.

Round 1 disposition: unresolved in ea8afa. A correction prepared in another immutable candidate is not silently incorporated into this report.

### PURE-STD-VAL-001 — Blocking — unresolved

**The exact candidate has no completed full acceptance gate or final verification.**

Evidence: no own terminal successful stock ./check.sh --candidate HEAD execution, complete exhaustive audit, or matching .lake/verification.json is supplied for ea8afa; the record is absent in validation-purity. There is consequently no immediate successful ./check.sh --verify-candidate HEAD evidence for this candidate. Focused builds recorded below establish individual development checks only.

Applicable standards: AGENTS.md's build/audit requirement, the README acceptance modes, ADR 0010, and the review-loop requirement to bind acceptance to the actual stable candidate. Static source comparison, a different candidate's check, successful selected targets, or both review axes cannot replace the gate.

Required remedy: the source owner must complete the stock full candidate check and exhaustive audit on the candidate actually proposed for acceptance, preserve its terminal evidence and matching verification record, and perform immediate final verification before acceptance. Reviewers must inspect that exact evidence and any intervening changes. No optional broadened tests are requested here.

Round 1 disposition: Blocked, regardless of the separate documentation finding. The prerequisite 901 check and the separate 10014/Chapter 2 gates do not supply this candidate's evidence or acceptance.

### PURE-STD-EVID-001 — Low — fixed with independent review evidence

**The successful Compatibility r2 focused evidence was initially absent from the checkpointable session evidence.**

During review, session/validation retained the failed Compatibility r1 pair, while the successful r2 JSON and log existed only in active-validation. The failed r1 is not success evidence. This made the claimed successful client result incomplete in the review/checkpoint evidence set.

The owner copied the original r2 pair into session/validation without changing the originals, failed r1, or candidate source. This reviewer independently compared the copies byte-for-byte and checked their identities:

| Preserved file | Bytes | SHA256 |
| --- | ---: | --- |
| session/validation/suspension-pure-compatibility-r2.json | 9454 | 9f59a68e14cbd029cfc68cd541ece27f2cee43d1f5cc830fb4f370463757feb2 |
| session/validation/suspension-pure-compatibility-r2.log | 3134 | 7f22bda5bf323d95b78ee77cd088ebc9c0bc741c4109796071eed5269c9f9fe9 |

The terminal r2 result is exit 0, 751 jobs. All 26 recorded before/start/after input hashes match the frozen candidate. This closes the evidence-preservation defect at the review level. It does not supply the missing complete candidate gate or assert that this reviewer uploaded a checkpoint.

## Review basis and source boundary

The review applied AGENTS.md, the code-review skill and its heuristics, example-driven-development including worked statement review, architectural-quality.md, domain.md, GLOSSARY.md, language-direction.md, the ADR index, ADRs 0001, 0002, 0006 and 0010, README build/audit guidance, review-loop.md, and the preservation-contract inventory. The dispatch, existing coordinator record, complete saved requirements, and relevant preparation reports were also read. Repository standards take precedence over style heuristics.

Primary-source inspection used the supplied local book and thesis, not an unseen paraphrase. The book's printed pages 31–33 supply the delay/force/cache notation and behavior; thesis Appendix A printed pages 133–136 supply the dynamic rules, recursive groups, and printed-page-135 self-force remark. The thesis page image was inspected as well as extracted text. The original unrestricted model, including effectful reentry, is deliberately retained. The task is a pure-domain theorem and supporting explicit cache facts within the book/thesis union, not full acceptance of Chapter 4 or Appendix A.

Source identities were independently hashed:

| Source | SHA256 |
| --- | --- |
| research-pfds/source-assets/okasaki-book-2003.pdf, 232 pages | b9dbf4f6ade4c24da438fd5415fc3abdd3af0aa8459d7e41e4a27de844c7ad41 |
| research-pfds/source-assets/okasaki-thesis-1996.pdf, 162 pages | f4b92ed7ea425f6f1019f20a4ef40df505327fbc5f1346ed6b7a2e28ab56d072 |

No full source text is incorporated into this report. The explicit source boundary excludes a new blackhole transition, assumed nonreentry, an assumed termination witness for every active body, acyclicity, source type safety, converse adequacy, and global complexity claims.

## Independent standards and statement assessment

### Operations, domains, representation, and creation

The purity predicate is over the existing Core expressions and patterns. It excludes mutable-reference operations, reference patterns, and generative exception names while retaining finite data, functions, recursive functions/suspensions, ordered matching, fixed exceptions, and diagnostic faults. Permitted recursive RHS shapes and distinct names are separate hereditary restrictions, not smuggled typing or termination assumptions. Fault clients demonstrate that the admitted domain need not be type safe.

Pure/Value.lean's finite mutually defined values and group descriptors retain original RHSs and an earlier outer environment, without containing newly created group members. Unrolling reconstructs members and effective captures in the raw binding order. Pure/Representation.lean reuses Durability.Heap and Extends for an immutable address-to-meaning world; ValueRep is not claimed injective or functional, and equal meanings at different addresses do not identify storage. Recursive captures remain representable after their suspension cell is cached.

Pure/Creation.lean obtains a prospective world from actual creation receipts. PendingGroup records captures before the actual SRec close. The closing argument supplies the represented expanded captures and preserves old occupied cells. Distinct names ensure allocated delayed members remain effective close targets; the checked duplicate-name counterexample explains this premise. No future body evaluation is assumed to allocate a thunk or close a group.

Primitive operations are parameters rather than specification-defined implementations. Pure/Compatibility.lean separately states representation compatibility over every world and represented input. Pure/Domain.lean separately requires preservation of hereditary allowed code in outputs. Identity/scalar adapters and fault cases are usable positive instantiations. Address comparison supplies the negative distinction between raw equivariance and representation compatibility; an effect-bearing returned closure distinguishes compatible representation from hereditary output preservation. This is necessary separation of obligations, not redundant assumptions.

### Certificates and actual execution histories

Pure/Memory.lean's unforced CellRep requires represented code/captures but no termination witness. A cached CellRep requires an actual finite pure-body evaluation. Its uniqueness result concerns the pure evaluation/value/count; it does not make all represented raw payloads equal. StateRep bounds and justifies the world's represented cells while allowing other raw cells.

Pure/History.lean records an actually executed pure prefix for each pending raw memoize-frame occurrence. Duplicate active addresses are permitted. Histories are advanced, pushed, popped, and completed from past execution. ConfigRep relates actual memory, control, frames, and these histories; it has no field assuming future termination, nonreentry, or the simulation to be proved.

Pure/Forcing.lean's delay law allocates without evaluating a body, including a known recurring body. Thunk entry may reenter an already active address. return_memoize constructs the cached certificate from the completed past history and performs the write before inner matching resumes. reuse_cached consumes an existing certificate and replays it through the remaining caller pattern/frames. raise_memoize preserves reached memory and omits this frame's own write. This last precise law is sound; the public prose overstatement is isolated in PURE-STD-DOC-001.

### Noncircular finite and body-entry correspondence

Pure/Ordinary.lean covers stable ordinary raw transitions. Its five special shape classes are handled by actual delay, recursive entry, force/cache, and normal/raised memoize laws. Pure/RecursiveStep.lean uses the existing raw recursive-creation prefix of 3 × bindings.length + 2 transitions and one auxiliary step. Recursive.lean proves that no body event occurs strictly inside that macro prefix; ConfigRep is not falsely asserted for every intermediate creation state.

Pure/Execution.lean, finite_correspondence at line 155, inducts on the remaining actual raw transition count. Ordinary/special single steps decrease it by one; recursive creation consumes a proved positive prefix. Cache-hit expansion uses an already stored finite certificate, rather than recursively assuming completion of the current active body. The final answer and raw state remain represented, including raised and diagnostic outcomes.

The separate body_entry_correspondence at line 186 inducts over the index of an actually observed raw prefix. It does not assume the enclosing run terminates. The absence-of-body-events law handles intermediate recursive-creation states, and the local correspondence constructs the related pure configuration at the observed event. These two inductions establish different required properties and are not circular uses of the eventual no-reentry result.

Pure/Continuation.lean and the raw Decomposition.lean distinguish an isolated body fault from a normally delivered boundary followed by a caller fault. Exact counts are retained for all outcomes. Pure/Recurrence.lean uses a strictly positive actual prefix returning to identical isolated input with extra caller frames. An alleged finite run would contain a strictly smaller isolated finite run, contradicting deterministic evaluation-count uniqueness. The zero-prefix literal example makes the positive-prefix premise meaningful.

Pure/Reentry.lean obtains such a recurrence from the actual pending occurrence and current same-address force. BodyEvent.lean identifies the inspected raw address directly from the unchanged transition. Pure/NoReentry.lean combines those results with finite correspondence: finite_body_entry_not_active derives absence of an active entry for finite runs; source_reentry_not_terminates starts from allowed represented memory/environment/code with empty histories. Nonreentry, active-body termination, acyclicity, and source typing are not hypotheses replacing the required conclusion.

### Connected applications and the preparation findings

Examples/SuspensionPureNoReentry.lean begins from the actual mutual source program and empty raw memory. Its independent 29-transition prefix reaches the second force of address 0 with the older memoize frame at index 3. The general theorem excludes every finite outcome; failed search for every fuel is derived afterward, not inferred from bounded enumeration. The recurrence clients separately connect the finite descriptor to the actual pure source entry and repeated body input.

The finite-correspondence clients include repeat forcing with raw 21/pure 23 transitions and an admitted expected-function fault at five transitions. Examples/SuspensionPureCachedProgram.lean starts with the actual literal source, obtains raw/pure 15-step executions, derives final StateRep from correspondence, and recovers the stored meaning and original empty capture by result inversion. Its later force consumes that recovered certificate, with raw 3 versus pure 5 transitions.

**PREP-10019-01: implemented, independently verified at static/focused-evidence level.** Examples/SuspensionPureCachedClosure.lean reuses the existing returningClosure expression verbatim. Actual recursive creation, raw 5/pure 1, recovers the meaning of address 0. Correspondence for the residual raw 48/pure 50 run constructs final cache representation; cached_lookup_allowed obtains the actual body certificate and represented closure capture. The full source is raw 53/pure 51 and returns 7. A later application to false reaches its captured self-address after 18 transitions. reuse_cached consumes the recovered certificate under four caller frames, with raw hit 1/pure replay 3 and a 17-step suffix, yielding raw 36/pure 38 and identical retained raw memory. The final cache invariant is not supplied by a manual StateRep.memoize assumption. This closes the concrete missing-application concern, while full acceptance remains blocked.

**PREP-10019-02: retained scope boundary.** Applications/Suspensions/ValuePersistence.lean preserves the existential value-cell constructor, not an immutable payload or a global successful-write bound. Fresh allocation uses boundedness; arbitrary executions/observations use the existing configuration-bounded invariant. A later suspended match hits the current payload and cannot enter a body at that address. The assignment client actually changes 7 to 8. Existing effectful reentry still has two writes, and the specific repeated exception client retains an unchanged thunk. The cached-closure client's one-body/one-write/one-hit counts are concrete. No general per-address at-most-one-write theorem is established or required as a substitute for these contracts. Separate subsequent work on such a bound is outside this review.

### Existing interfaces, generality, and architectural heuristics

The work reuses Progress.Machine/Evaluates/search, resource event-list adapters, Durability heaps/extensions, raw continuation discipline, and relational observations. The pure interpreter is an explicit auxiliary semantics, not a replacement for the raw source machine or an asserted implementation of the desired theorem. Its local transition counts are not equated with raw counts or host running time.

The retained Relocation/ForceObservation work fixes existing addresses and consistently relocates future allocation, under explicit bounds, capture restrictions, and primitive equivariance. Its normal/raised finite observations and counts do not imply literal equality of arbitrary heaps, arbitrary fault correspondence, or divergence equivalence. The dangling-capture counterexample makes its fixed-capture restriction substantive.

Case analysis in the raw/pure step, domain, and representation proofs serves distinct obligations over the actual syntax and transition. No concrete repeated implementation with divergent behavior was found that warrants a new generic framework. The private ExecutionBlock packages facts proved by cases; it does not assume the semantic theorem as a field. Explicit world, primitive, and history premises are exercised by connected clients rather than being unused speculative machinery. Arbitrary caller-tail treatment follows ADR 0006's discipline without pretending the untyped raw machine has intrinsically well-typed stacks.

The four FRP changes are direct imports supplying definitions/instances actually used: Order.SuccPred.Nat, Data.Set.Finite.Lattice, Algebra.Order.Archimedean.Real.Basic, and Data.Nat.Size. Their provider chains and call sites were inspected. They do not change proofs or introduce a broad replacement foundation import.

## Validation evidence inspected and its limits

The stock toolchain, dependency manifest, Lake/Nix configuration, check.sh, scripts, ProofAudit.lean, and original raw Syntax/Store/Machine/Rules are unchanged against the full integration base. A full integration diff whitespace check passed. Text inspection found no introduced admission, axiom, unsafe/native proof shortcut, raised proof budget, or linter suppression. Comments containing words such as “axiom” or “admit” are not declarations. This source inspection does not establish the transitive axiom property that the missing exhaustive audit must establish.

The public SquareApplications entrypoint and local import traversal were checked; all changed Lean files are reachable. That read-only traversal is supporting inspection, not a replacement for the stock source guard or audit. The predecessor development tree 501a954 differs from this candidate only by the four direct FRP imports.

The following terminal focused results were inspected with their commands, matching logs, and input identities. Recorded before/start/after or input/queued-input hash fields were normalized according to each record's actual schema. The listed input counts match the current frozen bytes; none of these results is the complete candidate gate.

| Focused record under session/validation | Jobs | Matching recorded inputs |
| --- | ---: | ---: |
| suspension-decomposition-r2 | 745 | 17 |
| suspension-pure-representation-r3 | 630 | 13 |
| suspension-pure-compatibility-r2 | 751 | 26 |
| suspension-pure-machine-r4 | 741 | 19 |
| suspension-pure-recurrence-r3 | 744 | 21 |
| suspension-pure-domain-r2 | 753 | 28 |
| suspension-pure-history-r1, targeting Simulation | 756 | 31 |
| suspension-pure-forcing-r2 | 758 | 31 |
| suspension-pure-domain-state-r4 | 758 | 33 |
| suspension-pure-world-domain-r1 | 760 | 35 |
| suspension-pure-ordinary-client-r2 | 760 | 37 |
| suspension-pure-recursive-step-r1 | 761 | 36 |
| suspension-pure-execution-r1 | 764 | 39 |
| suspension-pure-reentry-r1 | 758 | 33 |
| suspension-pure-no-reentry-r1 | 768 | 43 |
| suspension-pure-cached-program-r1 | 764 | 41 |
| suspension-pure-cached-closure-r1 | 768 | 45 |
| suspension-body-event-r2 | 744 | 19 |
| suspension-value-persistence-r3 | 748 | 23 |
| suspension-raw-recursive-stack-r1 | 785 | 31 |
| suspension-force-observation-r2 | 751 | 16 |

Earlier failures and later source qualifications are retained:

- Compatibility r1 failed overall despite building its core; r2 supplies the corrected terminal client evidence and is now preserved as described in PURE-STD-EVID-001.
- PureCreation core r4 succeeded, but Recursive.lean and the creation client changed later. Current raw-recursive-stack-r1 covers those current bytes; the earlier record is not silently treated as current.
- PureMemory r4 succeeded before later Recurrence/client changes; the current History/Simulation build covers the resulting current chain.
- RawRecursive r3 predates a later change; current raw-recursive-stack-r1 supplies the matching evidence.
- Relocation r6 failed overall despite core success, and ForceObservation r1 failed. ForceObservation r2 covers the corrected current relocation and observation chain.
- The original PureValues retry failed. In the later combined PureMachine r3 batch, the first Examples.SuspensionPureValues subrun has its own terminal exit 0, 505 jobs, and current Syntax/Value/client bytes; the second PureMachine subrun failed. The whole batch is not green. The machine client was corrected and has its separate r4 terminal success.
- The NoReentry terminal JSON and log survived a tool-session loss and record actual completion. That is different from the separate prerequisite 901 interruption, whose preserved runtime-interruption-20261102-2240.json and import-footprint-r3-focused-interruption-r1.json have no successful terminal target result. The latter's unchanged inputs establish no source mutation, not a successful build.

The later ongoing prerequisite gate is for a different candidate. No inference about its eventual success, this candidate's full gate, or 10014/Chapter 2 acceptance is made.

## Complete file coverage and relevant unchanged interfaces

All 58 changed files in the original integration scope were read independently, including full source/client bodies and documentation, not only diff headers:

| Directory/prefix | Files inspected |
| --- | --- |
| Applications/Suspensions/Pure/ | Compatibility.lean, Continuation.lean, Creation.lean, Domain.lean, DomainState.lean, Execution.lean, Forcing.lean, History.lean, Machine.lean, Memory.lean, NoReentry.lean, Ordinary.lean, Recurrence.lean, RecursiveStep.lean, Reentry.lean, Representation.lean, Simulation.lean, Syntax.lean, Value.lean, WorldDomain.lean |
| Applications/Suspensions/ | BodyEvent.lean, Decomposition.lean, ForceObservation.lean, Recursive.lean, Relocation.lean, ValuePersistence.lean |
| Examples/ | SuspensionPureCachedClosure.lean, SuspensionPureCachedProgram.lean, SuspensionPureCompatibility.lean, SuspensionPureCreation.lean, SuspensionPureDomain.lean, SuspensionPureDomainState.lean, SuspensionPureExecution.lean, SuspensionPureForcing.lean, SuspensionPureHistory.lean, SuspensionPureMachine.lean, SuspensionPureMemory.lean, SuspensionPureNoReentry.lean, SuspensionPureOrdinary.lean, SuspensionPureRecurrence.lean, SuspensionPureRecursiveStep.lean, SuspensionPureReentry.lean, SuspensionPureRepresentation.lean, SuspensionPureSimulation.lean, SuspensionPureValues.lean, SuspensionPureWorldDomain.lean |
| Examples/, other suspension clients | SuspensionBodyEvent.lean, SuspensionDecomposition.lean, SuspensionForceObservation.lean, SuspensionRelocation.lean, SuspensionValuePersistence.lean |
| FRP/import changes | Applications/FRP/Demand.lean, Applications/FRP/Finite.lean, Examples/FRP.lean, Examples/IndefiniteService.lean |
| Public entrypoint | SquareApplications.lean |
| Documentation | docs/research/pfds-pure-suspensions.md, docs/research/pfds-suspensions.md |

Relevant unchanged interfaces inspected include raw suspension Syntax, Store, Machine, Continuation, Invariant, Prefix, AddressRange and Renaming; Progress/Evaluation; Durability/Storage heap, extension and update contracts; the existing SuspensionMachine effectful reentry, outer-exception, creation and repeated-exception clients; and the Mathlib providers for the four direct imports. These definitions were used to assess premises and conclusions independently of preparation summaries.

## Acceptance handoff

Retain PURE-STD-DOC-001 unresolved for this immutable round, PURE-STD-VAL-001 blocking, PURE-STD-EVID-001 fixed with the exact preserved evidence, PREP-10019-01's implemented application disposition, and PREP-10019-02's explicit write-count boundary. The next review of a corrected candidate must retain both original bases, the complete integration scope, and every finding disposition. A documentation correction does not cure the missing exact gate.

No acceptance of local10019, local10014, Chapter 2, whole Chapter 4, or Appendix A is granted by this report. The independent Standards reviewer remains available in this same loop to inspect a concrete correction and the actual matching full-gate/final-verification evidence.
