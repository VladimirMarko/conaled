# Local10020 finite pure cache-write counts — Standards review r1

Reviewer: `/root/cache_count_review/standards`  
Review date: 2026-11-03 UTC  
Axis: **Standards only**  
Outcome: **Blocked**  
Unresolved static findings: **0**  
Unresolved required-validation findings: **1**, `COUNT-STD-VAL-001` (**High**, acceptance blocker)

The complete bounded static review is finished. I found no additional violation of the applicable methodology, architecture, public-integration, or connected-example standards. This is not an approval: the exact candidate's own integrated check, exhaustive audit, matching success record, and immediate final verification have not been supplied. Focused success establishes narrower evidence and cannot discharge that requirement.

## 1. Immutable scope and requirements

| Item | Reviewed identity |
| --- | --- |
| Candidate | `3dd930c3e3989f3e5530463f3ac937a629551335` |
| Isolated checkout | `/workspace/scratch/ca9a61d0bf30/validation-cache-counts` |
| Candidate branch | `pfds/cache-counts-review-r1` |
| Bounded task base and merge base | `361f5f3f6bb3de1974510ce355883dac2bf25333` |
| Original full integration base and merge base | `ea8afa12706d30cdc69ece1a172d5f21a3ea1809` |
| Task scope | 13 files, 3 commits |
| Full integration scope | 14 files, 4 commits |
| Exclusions | None |
| Checkout status | Clean when inspected, including the final read-only status check |
| Scope manifest | `session/validation/pure-cache-counts-candidate-r1.json` |

The two bases are ancestors of the candidate. The additional integration commit is the incorporated documentation correction `361f5f3f6bb3de1974510ce355883dac2bf25333`; it is included in this review. The task commits are `78ed1a1501a955a5579a7a098910a5d4bc1361be`, `0ebbf185d084b2cfe0b11501e8c7d4998932c16a`, and the candidate itself. No earlier independent local10020 findings existed to carry forward or dispose of.

I reviewed the complete three-dot differences from both bases, all candidate files in the manifest, and the relevant unchanged definitions and clients needed to interpret the claims. Manifest file sets and SHA256 values matched the candidate. The supplied requirements were read as saved, with these identities:

| Requirement | SHA256 |
| --- | --- |
| `session/requirements/REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `session/requirements/REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `session/requirements/pure-cache-counts.md`, version 1 | `fa5b5c01205aea18cc19aa53047cc7e0d57c0bb225534f0152bc04d7c87e569e` |

The user's local-ticket and durable-checkpoint exception governs tracking. The bounded cross-cutting result does not accept Chapter 2, Chapter 4, Appendix A, or the whole book/thesis union, and it does not retroactively expand local10019's separately frozen review scope.

### Complete file coverage

All five library files were read: `Applications/Suspensions/Pending.lean`, `CacheWrite.lean`, `CacheAccounting.lean`, `TraceObservation.lean`, and `Pure/CacheCounts.lean`.

All five connected clients were read: `Examples/SuspensionPending.lean`, `SuspensionCacheWrite.lean`, `SuspensionCacheAccounting.lean`, `SuspensionTraceObservation.lean`, and `SuspensionPureCacheCounts.lean`.

The remaining full-integration files were read: `SquareApplications.lean`, `docs/research/pfds-cache-counts.md`, `docs/research/pfds-pure-suspensions.md`, and `docs/research/pfds-suspensions.md`. The last file is the additional inherited integration difference and was not excluded.

## 2. Applicable standards and independent procedure

I applied candidate `AGENTS.md`; README environment, build, audit, and proof-boundary guidance; `docs/agents/architectural-quality.md`; `docs/agents/domain.md`; `GLOSSARY.md`; `docs/language-direction.md`; ADRs 0001, 0006, and 0010; the example-driven-development skill and worked-example guidance; and the code-review skill, heuristics, invocation policy, and shared review-loop procedure. Scoped guidance discovery found no additional applicable `AGENTS.md`, `CODING_STANDARDS.md`, or `CONTRIBUTING.md` for these files.

The relevant rules require reuse of existing mathematical and operational interfaces, explicit assumptions, useful structure-preserving observations, public integration, meaningful checked connections, review of formal statements rather than merely elaboration, and complete candidate-bound verification. Heuristics were investigated for actual consequences; repetition of finite control/frame cases was not treated as a defect by pattern count.

I read the complete dispatch and existing local10020 review record. I did not read the Spec axis's report and did not perform a third/coordinator review. No compiler, build, test, cache operation, source edit, dependency edit, Git mutation, or process change was performed. This report is the only written file in this assignment.

## 3. Static assessment and formal statement review

### Actual pending frames and successful writes

`Pending.lean:18–43` extracts the addresses of actual memoize-frame occurrences and proves membership equivalent to the existence of a corresponding concrete frame. It does not erase duplicates. `PendingTransition` at lines 47–51 describes the actual transition as retaining a sublist or pushing the address reported by an actual body event. The public result at lines 170–185 follows the unchanged machine's control/frame cases. The distinctness result at lines 189–200 explicitly requires prior distinctness and freshness for a possible body entry.

This is a useful provenance interface rather than an assumed pure-stack invariant. The raw duplicate-frame client retains an actual reentry that produces `[0, 0]`, so the abstraction does not silently make unrestricted reentry impossible. The positive client uses the public transition/distinctness results on an actual first entry.

`CacheWrite.lean:127–155` characterizes a successful write through the actual value control and top memoize frame. Its statement does not require that the cell still contain a thunk, which matters because the raw machine can overwrite a cached value through an older pending frame. `Settled` at lines 159–160 combines an existing value cell with absence of a pending frame for that address. It deliberately does not assert constant payload.

The preservation theorem at lines 177–196 uses explicit boundedness together with the existing value-persistence and no-body-at-a-value-cell results. An actual write with distinct pending addresses establishes settled status at lines 201–214. Later-prefix results at lines 218–247 reuse the actual observation/step relation; they are not claims about a replacement evaluator. Existing memory/frame boundedness prevents allocation from invalidating the needed freshness reasoning.

The clients exercise first successful force, an older same-address pending overwrite, later cache hits, mutable payload through reference assignment, and an outer exception retaining an inner successful cache. The mutable-payload case keeps the concrete 7-to-8 change and distinguishes a reference write from a cache write. The outer-exception case uses the existing machine execution and retained memory. These cases test precisely the restrictions expressed by the public statements.

### Counting through the existing resource observation

`CacheAccounting.lean:26–29` defines `FreshEntries` over actual unfinished observed prefixes and their next actual body events. This premise is structural provenance; it does not assume the desired cache-write bound. The intervening lemmas transport freshness and pending distinctness through those actual prefixes.

The additive map at lines 75–97 charges occurrences of `cacheWrite address` in the actual `FreeAddMonoid Event` list and proves equality with the existing free-additive-monoid lift. This preserves the existing ordered trace as the source observation and connects counting to reusable resource reweighting. It introduces no alternative operational semantics and does not equate identical source bodies at different addresses.

The zero/successor/finished-suffix laws, monotonicity, and completed-zero propagation at lines 99–167 follow the existing workload observer. Settled states give zero later writes at lines 171–185. The main raw bound at lines 189–213 requires boundedness, initially distinct pending addresses, and `FreshEntries`, and quantifies over every address and every observation budget. The successful-write branch establishes settled status and then uses zero later writes; the other branch transports the invariant. Purity and finite termination are not smuggled into this raw conditional layer.

The accounting client checks an independently specified five-event trace, supplies freshness from actual prefixes, invokes the general bound and pending-distinctness laws, connects the additive charge to its resource lift, and checks completed suffixes and a later hit. Its concrete counts supplement the general laws rather than substitute for their use.

### Pure-source specialization and explicit boundaries

`Pure/CacheCounts.lean:31–44` derives `FreshEntries` from the existing finite nonreentry theorem. It uses actual pending-frame membership to obtain a concrete frame position, then contradicts `finite_body_entry_not_active` at that position. The assumptions retain primitive compatibility, hereditary primitive-output preservation, allowed world/configuration, representation, and an actual finite `Progress.Evaluates` witness. No initial distinctness or absence of repeated writes is assumed as a substitute for this derivation.

At lines 50–68, the source theorem obtains raw memory boundedness from `StateRep`, initial pending distinctness from the empty source-start stack, and freshness from the preceding theorem. Captured environments and source code retain their representation and hereditary domain premises. The conclusion covers all addresses and all observation budgets, including early prefixes and absorbing post-answer suffixes. Lines 71–87 specialize the same result to direct counting in the actual ordered event list.

This finite-completion premise is not a claim that all admitted programs terminate, nor is a finite search bound mistaken for termination. The underlying representation/domain definitions do not contain an assumed write-count or nonreentry property. `CodeAllowed` retains both the effect restriction and recursive-form restriction; `ParametersPreserve` is a separate output law from relational primitive compatibility.

The source clients discharge the general theorem's hypotheses for repeated forcing of a literal, the existing cached returned recursive closure, two independently allocated suspensions with identical code, a handled fixed exception retried, and an unforced delay. They retain exact 21/34/50-step source evaluations and the existing 53-step closure evaluation. The exception and unforced cases use completed-zero propagation to establish zero for arbitrary addresses/budgets where asserted. The cases provide substantive independent outcomes, including separate addresses and body attempts without successful writes.

### Connecting the two trace instruments and preserving the negative case

`TraceObservation.lean:24–81` proves full-answer equality and exact event-list append agreement between the two existing instruments for an actual finite traced evaluation. It retains an arbitrary prior event log; lines 85–90 give the empty-log specialization. The proof follows the existing evaluation relation, transition events, workload successor law, and finished absorption. It adds no evaluator or assumed count equality.

The connected trace client uses a nonempty prior log and cancels only that known prefix when recovering the new observation. It does not claim that an arbitrary prior list was produced by an earlier execution.

`SuspensionPureCacheCounts.lean:240–268` retains the unrestricted effectful counterexample's original statement: address 1 has two successful cache writes in the 300-step observation. It connects the original checked trace through the new bridge, an actual completed prefix at 76 steps, evaluation uniqueness, and finished-suffix absorption. The final correction does not weaken the expected result or raise reduction limits. This preserves an important check against accidentally generalizing the source theorem beyond its domain.

### Dependency interpretation, integration, and documentation

The unchanged dependencies inspected include the relevant transition and measurement definitions in `Applications/Suspensions/Machine.lean`; the complete existing `Observation.lean`; raw `ConfigBounded`, `step_bounded`, `HasValue`, `step_hasValue`, and `hasValue_no_body`; the pure `StateRep`, `ConfigRep.start`, `WorldAllowed`, `ConfigAllowed.start`, hereditary domain/primitive laws, and `finite_body_entry_not_active`; and the existing cached-closure, reentrant-overwrite, and outer-exception executions used by the new clients. This inspection was bounded to interpreting the present full scope, not a new review of all earlier development.

Library results live under `Applications/Suspensions`; their compositions and concrete executions live under `Examples`. `SquareApplications.lean` imports all five new example modules, which import the new library layers. No raw transition, toolchain, dependency pin, audit policy, or build configuration changes in this scope. All ten new Lean files retain `autoImplicit false` and `warningAsError true`. The inspected change introduces no admission, new axiom, native-evaluation shortcut, proof-budget increase, or linter suppression; that static observation does not replace the required exhaustive audit.

The three research documents accurately distinguish focused checking from acceptance, cell-constructor persistence from payload constancy, body attempts from successful writes, exceptional unwinding from discarding reached memory, and finite source evaluation from arbitrary nontermination. They keep the local10019 boundary and chapter acceptance boundaries visible. The correction to the inherited raw-suspension documentation is in scope and does not overstate predecessor acceptance.

**Static disposition:** no unresolved documented-standard violation or concrete heuristic finding was identified. No speculative refactor or optional additional test is requested.

## 4. Development and focused validation evidence

I read all five author handoffs: `session/research/suspension-pending.md`, `suspension-cache-write.md`, `pure-cache-accounting.md`, `pure-cache-counts-source.md`, and `suspension-trace-observation.md`. They retain the opening missing connections, independently specified expectations, statement reviews, actual attempts, and failures. They were treated as author evidence, not independent approval. Their chronological earlier status entries are explicitly superseded by current status; the record is not silently rewritten to hide unsuccessful attempts.

The terminal focused records/logs are in `session/validation/`, with the stems below. I inspected terminal results and input fingerprints, compared recorded final inputs with the candidate, and checked that the retained evidence matches the original outputs. Each reported successful focus finished with exit code 0 and unchanged queued/start/final inputs. These were named-target builds in the pinned Nix environment, not full candidate acceptance commands.

| Focus | Matching candidate inputs | Coverage established by the record |
| --- | ---: | --- |
| `suspension-pending-r3` | 20 | Pending library and connected client |
| `suspension-cache-write-r2` | 26 | Cache-write library and connected client |
| `suspension-cache-accounting-r3` | 29 | Accounting client and its imported library |
| `suspension-trace-observation-r1` | 26 | Trace bridge and nonempty-prior client |
| `suspension-pure-cache-counts-r3` | 58 | Complete source client and unchanged pure-count dependency |

Exact retained evidence identities:

| Focus | JSON SHA256 | Log SHA256 |
| --- | --- | --- |
| Pending r3 | `fa70cd81af7ce36993895c3fceecf8f0f8c47fcd678451ceb0710f63b86d2b1b` | `1f8ce3b7c369a0b1531cae45a0d0fa5df88279b62e6083a1f4828f03ff2934b5` |
| CacheWrite r2 | `d757b317c8837fa5ef56f30b4956154f9272d075e2d2392974d4e8a67797a6f3` | `18961a456eb4d6a8ca24c8b83011a75b663b848a64fde06a51f51df4abc74f1a` |
| CacheAccounting r3 | `3a487946d56ebd5c603d2c269830fd697e8173e6e9847192d1f10c00f20e374f` | `3f530b71192dd6c01b4ff35f5beec66f29657c7319766e514895319374ea982a` |
| TraceObservation r1 | `6381183ca50ec59499b92d7b75e835a6f1a4e84690ad5e5fde7a26671c5acaf9` | `65aaf8af1caa6fae39d0e5902af8b24d40bfbd8b2ec934b55263ce111b81985e` |
| PureCacheCounts r3 | `b7be6defc6d17bc1e7611afb1c262098ef5ae9122f66b156849d08f699ec74f3` | `8d535b14b3c8d456312bb3e74eb83f53c17a361184d51e6ce0f93ea48a6aeb7d` |

Earlier Pending r1/r2, CacheWrite r1, CacheAccounting r1/r2, and source-client r1/r2 failures remain preserved. Relevant diagnostics and their corrections were examined: branch/simplification obligations, unused tactics/simp arguments, the unavailable list helper, singleton/count normalization, and the negative example's default reduction-depth limit. The source-client correction replaced the failing deep reduction with the actual trace bridge described above. It retained the 300-step/two-write proposition and default proof limits. Earlier failed runs do not count as successful validation.

## 5. Complete unresolved finding

### COUNT-STD-VAL-001 — Exact candidate acceptance evidence is absent

- **Axis:** Standards.
- **Severity:** High; required-evidence blocker.
- **Status:** Unresolved.
- **Category:** Validation, separate from static code/methodology findings.
- **Candidate location:** the complete integrated candidate `3dd930c3e3989f3e5530463f3ac937a629551335` in `/workspace/scratch/ca9a61d0bf30/validation-cache-counts`; its `.lake/verification.json` was absent when inspected.
- **Applicable rules:** `AGENTS.md:30–32`; README build/audit acceptance procedure at lines 145–192 and exhaustive-audit boundary at lines 288–291; ADR 0010's public-import coverage and every-invocation exhaustive audit; `docs/agents/review-loop.md:67–91`; local10020 version 1 acceptance requirements.
- **Evidence:** The five matching successful focused records cover named targets and their recorded inputs. No successful own `./check.sh --candidate HEAD`, exhaustive integrated audit, matching candidate success record, or immediate final `./check.sh --verify-candidate HEAD` is available for this candidate. The manifest explicitly records `acceptance: false`. A predecessor's running or successful gate, ordinary reusable compiled artifacts, and a focused build cannot establish this candidate's approval.
- **Consequence:** Integrated public closure, source policy, complete build, and transitive axiom audit have not been established by the required acceptance evidence. The Standards axis cannot pass, and this review cannot justify acceptance or a chapter-frontier advance.
- **Required remedy:** Root must finish the stock pinned-environment candidate check in this isolated checkout with the stable candidate/configuration/dependency inputs required by README, preserve its successful full output and exhaustive audit, and retain the matching `.lake/verification.json`. Both independent axes must reconcile that exact evidence in this same loop. Root must run `./check.sh --verify-candidate HEAD` immediately before acceptance and confirm the resolved commit is this approved candidate. Any source or relevant input correction requires the prescribed new candidate/full-scope continuation; an approval record from another candidate is insufficient.
- **Code change requested:** None inferred from this evidence gap. The reviewer has not launched or duplicated root's validation work.

## 6. Final disposition and continuation

The static Standards assessment of the entire full-integration scope is complete. There are **0 unresolved static findings** and **1 unresolved required-validation finding**, `COUNT-STD-VAL-001`, with worst severity **High**. The axis outcome is **Blocked**, not Passed. No broader claim of Spec correctness or whole-book/chapter acceptance is made by this Standards report.

Bounded base: `361f5f3f6bb3de1974510ce355883dac2bf25333`. Original integration base: `ea8afa12706d30cdc69ece1a172d5f21a3ea1809`. Candidate: `3dd930c3e3989f3e5530463f3ac937a629551335`.

Retain this report and finding ID for the existing loop's exact-gate continuation or corrections. The same reviewer remains available; no duplicate independent review loop is requested.
