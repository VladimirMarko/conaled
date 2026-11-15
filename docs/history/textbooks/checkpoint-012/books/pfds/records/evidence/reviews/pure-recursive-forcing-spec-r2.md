# Local10019 — independent Spec review, round2

## Outcome

**Blocked: no unresolved static findings; one unresolved acceptance-evidence blocker.** Both round1 documentation findings are fixed in this corrected candidate. The full source and mathematical assessment is retained and reassessed through the independently verified unchanged formal/configuration inputs, not narrowed to a two-file acceptance scope. No formal statement or proof defect was found in that assessment.

| Stable ID | Round1 severity | Round2 disposition |
| --- | --- | --- |
| PURE-SPEC-DOC-001 | Medium | **Fixed with independent review evidence** on this candidate. |
| PURE-SPEC-DOC-002 | Low | **Fixed with independent review evidence** on this candidate. |
| PURE-SPEC-VAL-001 | Acceptance blocker | **Unresolved.** The exact corrected candidate has no own complete build/audit verification record or immediate final verification. |

Reviewer: `/root/pure_suspension_review/spec`, continuing the same independent Spec axis and existing local10019 review loop. I did not read the Standards report or use that axis's conclusions as my review. No compiler/build, source/configuration/dependency, Git/index/ref, process or external tracker changes were made. Only this assigned new report was written.

The round1 report remains unchanged at `/workspace/scratch/ca9a61d0bf30/session/reviews/pure-recursive-forcing-spec-r1.md`, SHA-256 `e6caa2fa06920f00accd1affb34d1cf213e3a22aa2fc8042dca387969a66a888`. It remains an honest Blocked assessment of `ea8afa12706d30cdc69ece1a172d5f21a3ea1809`, including its then-unresolved documentation findings. This report does not retroactively alter that outcome.

## Exact current scope and identity checks

Workspace root: `/workspace/scratch/ca9a61d0bf30`.
Frozen checkout: `/workspace/scratch/ca9a61d0bf30/purity-correction`.

- Current candidate: `361f5f3f6bb3de1974510ce355883dac2bf25333`.
- Previous candidate: `ea8afa12706d30cdc69ece1a172d5f21a3ea1809`.
- Fixed ticket base: `a3feaff319ad5fad912fb8bdc113f33fea4e2a60`.
- Original complete integration base: `b422800fb5b6dc1253823057c0ea71644274d77c`.
- Current ticket scope: **50 changed files / 7 commits**.
- Current full integration scope: **58 changed files / 11 commits**.
- Exclusions: **none**.

I read the complete round2 dispatch and independently checked the current HEAD, clean status, both merge bases, both actual changed-file sets, both ordered commit lists and every current manifest file hash. They all match `session/validation/pure-suspension-candidate-r2.json`, whose SHA-256 is `95179e677edbd6bb1613769487496c753a6b1860da565bd372176fdb26effe17`.

The reviewed comparisons are:

```text
git diff a3feaff319ad5fad912fb8bdc113f33fea4e2a60...361f5f3f6bb3de1974510ce355883dac2bf25333
git diff b422800fb5b6dc1253823057c0ea71644274d77c...361f5f3f6bb3de1974510ce355883dac2bf25333
```

The full tree comparison with round1 contains exactly two changed files:

| File | Current SHA-256 |
| --- | --- |
| `docs/research/pfds-pure-suspensions.md` | `2a7d2e304e5590aa774bc425eb69ce00aec872bfffa9d116e4477c645f106ab4` |
| `docs/research/pfds-suspensions.md` | `1257cfb512545c090beadfde13605db4632fae41f53c4b83a0b5f5345688c113` |

Round1 is an ancestor of the corrected candidate. No Lean definition, theorem, proof, example, import, toolchain, dependency configuration, build/audit script or other tracked input changed. The complete58-file integration inventory in the preserved round1 report therefore still identifies the current reviewed scope, with only the two document hashes replaced. The ticket scope gains the foundation document relative to its fixed incorporated base; that document was already included in the full integration review.

## Requirements and guidance retained

The original full request, union request and bounded version1 requirements remain binding. I rechecked all three fingerprints:

| Requirement under `session/requirements` | SHA-256 |
| --- | --- |
| `REQUEST.md` | `b847f23fcce44837f5b1ead01aae43ac5ed626ffd32aab84055dd664e339e499` |
| `REQUEST-union-v2.md` | `3336bed1154438b3683aeb5a1c63fee44e87aff190f5ff69e34705a780b9d22c` |
| `pure-recursive-forcing.md`, version1 | `57ddefb472b9393a3fe890f880ad4eb94893f5aa6bd8be912da2d7dfa4f4ec55` |

The same frozen AGENTS, architecture/domain/language/ADR guidance, review-loop procedure and example-driven statement-review standards apply. The user's local-ticket and durable-checkpoint exception remains in force. The earlier primary-source inspection, exact source identities and source-boundary assessment recorded in round1 are retained. The requirement has not been weakened to obtain static clearance.

This review does not accept local10014, Chapter2, Chapter4, complete AppendixA or the book/thesis union. The separate local10020 development is outside this candidate and was not reviewed or used as evidence. In particular, it cannot supply an unproved write-count theorem to local10019.

## Finding dispositions and correction evidence

### PURE-SPEC-DOC-001 — fixed

Round1 identified two unqualified statements that an exceptional exit leaves the thunk uncached, including an identical retry assertion inside the unrestricted raw value-persistence discussion.

The corrected `docs/research/pfds-pure-suspensions.md:90` now says the pending frame skips its successful write and retains reached memory. The following text explicitly includes a successful write by an inner evaluation. This matches the unchanged raw `raised_skips_memoize` transition and `Pure.Forcing.raise_memoize`; it no longer implies rollback or an unconditional current-thunk fact.

The corrected text beginning at `docs/research/pfds-pure-suspensions.md:136` names `Exceptions.raised_body_can_repeat` and links its actual example file. The unchanged-thunk and same-result retry statement is expressly limited to that particular checked case. The text then names and links `outer_exception_preserves_inner` and `outer_exception_then_hit`, preserving the unrestricted counterexamples in which the outer body raises but an inner successful cache remains.

I compared the whole correction with those retained laws and applications from the complete round1 source review. The result accurately separates the frame-local no-write guarantee, the particular unchanged-thunk retry, and the general possibility of an already installed inner cache. No formal statement, primitive restriction, expected case or source semantics changed. The adjacent existential-payload, two-write and no-general-write-count boundaries remain explicit. **The finding is resolved on361f5f3.**

### PURE-SPEC-DOC-002 — fixed

Round1 identified the stale current foundation statement that local10019 remained unproved.

The corrected paragraph at `docs/research/pfds-suspensions.md:123` now distinguishes the implemented precise pure-domain theorem and recursive source case from acceptance. It links `pfds-pure-suspensions.md`, describes their focused evidence, and states the correct direction: finite admitted executions derive nonreentry from the proved self-forcing nontermination implication.

At `docs/research/pfds-suspensions.md:127`, local10019 remains explicitly unaccepted pending its exact full build, exhaustive audit, independent reviews and final candidate verification. The paragraph continues to require that accepted scope together with the general extension for complete AppendixA/Chapter4 coverage. This matches the current unchanged NoReentry implementation, connected source client and focused evidence. It neither grants chapter acceptance nor turns historical preparation into approval. **The finding is resolved on361f5f3.**

### PURE-SPEC-VAL-001 — unresolved

The corrected candidate's manifest still says `acceptance: false` and explicitly records that its own full gate/audit/record/final verification has not run. I independently checked that `/workspace/scratch/ca9a61d0bf30/purity-correction/.lake/verification.json` is absent. No successful complete-candidate command, exhaustive declaration/axiom audit or immediate final verification was supplied for361f5f3.

The unchanged Lean bytes justify retention of the earlier static mathematical analysis and matching focused evidence. They do **not** create a completed full integration gate. Missing required validation prevents a Passed outcome under the bounded requirement and `docs/agents/review-loop.md`.

Required continuation remains root-owned:

1. Preserve this exact candidate, or capture and review any further correction without excluding earlier scope/findings.
2. Supply the stock isolated `./check.sh --candidate HEAD` result, applicable complete build and exhaustive audit, complete logs and matching `.lake/verification.json` for the actual candidate.
3. Have both retained axes assess the matching evidence and any changed inputs.
4. Immediately before acceptance, run and preserve `./check.sh --verify-candidate HEAD`, confirming the approved exact commit.

Separate prerequisite901 checks, earlier local10014 reviews, focused build output reuse and copied development records do not discharge this blocker. Local10014/Chapter2 and the wider coverage gates remain separate. No new compiler run or optional broadened test was performed for this review.

## Full-scope mathematical reassessment retained on verified identical inputs

The following conclusions apply to the complete current integration scope through the verified identical formal bytes, with the corrected explanations now aligned. The detailed independently inspected definitions, proof reasoning, primary-source comparison and connected applications remain in the preserved round1 report.

| Reviewed area | Current assessment and explicit limit |
| --- | --- |
| Source and hereditary domain | Original Core syntax remains. Reference expressions/patterns and generative exception names are excluded; fixed exceptions, ordered matching, data, functions, recursive declarations and delays remain. Nested permitted RHSs and distinct recursive binders are explicit. No typing, acyclicity or active-body termination premise is inserted. |
| Primitive interface | Actual-output representation compatibility and hereditary preservation remain separate. The nonempty identity/scalar basis, pointer-equality discriminator and returned-effectful-closure negative case retain their meaning. |
| Finite values and immutable world | Group descriptors retain original RHSs and earlier captures; unrolling recovers members without cyclic Lean values. ValueRep remains nonfunctional/noninjective where appropriate; equal meanings do not identify addresses. |
| Actual creation and cached cells | PendingGroup records actual creation/closing provenance without future body results. Thunks have no termination certificate; cached values have actual successful finite pure-body witnesses. Old cells and meanings are preserved through the proved appropriate relations. |
| Occurrence histories and memoization | Every memoize occurrence has its own actual past prefix; duplicate active addresses are allowed. Normal return constructs its certificate from that past; reuse consumes an existing certificate. Exceptional exit retains reached memory without its own write. |
| Finite and body-entry simulations | The finite proof decreases actual remaining raw count. A cache hit expands an already stored witness. The body-entry bridge uses actual prefix index without a finite enclosing-run premise. Recursive creation uses its positive actual prefix and strict interior no-body law; stable representation is not asserted at unsupported intermediate controls. |
| Self-reentry theorem and source client | A positive same-input pure recurrence excludes all finite outcomes, including faults. Actual body-event identity and finite correspondence transfer the obstruction to raw source execution. The actual29-step empty-source prefix and index3 pending frame instantiate the general theorem; universal search-none follows afterward. |
| Literal and recursive-closure cache clients | Actual source execution supplies the final world/cache/capture evidence. The literal15/15 source and3/5 later observation remain. The recursive closure retains actual5/1 creation,53/51 source,18-step later prefixes, hit1/replay3, common17-step suffix and36/38 later application with unchanged raw memory. |
| Raw value persistence | It preserves the existence of a value-cell constructor, allowing payload changes. The7-to8 assignment, effectful two-write run and explicit fixed-exception retry remain. No universal cache-write count is inferred. |
| Inherited relocation/force observation | Explicit primitive equivariance, fixed existing cells/capture and private-address injection remain. The actual reference/effect and dangling-capture clients retain the finite normal/raised12/10-overhead contract; no fault/divergence/equal-trace equivalence is invented. |
| Complete integration | The four direct FRP imports and public entrypoint remain included and unchanged. Existing client imports are present. Their complete integrated build/audit is still unestablished. |

No additional static finding arises from the corrected whole candidate. The pure auxiliary machine remains a source-specific interpretation using existing Progress/Resources/Durability interfaces. It does not replace the raw effectful semantics, assert simulation as an invariant field, or derive equal memory/resource usage from equality of represented values.

## Matching focused evidence and retained qualifications

The representative successful records were rechecked against the corrected checkout's actual file bytes. All recorded relevant input hashes still match; their JSON/log identities are unchanged from round1:

| Record under `session/validation` | Exit/jobs | Input count | Current input mismatches |
| --- | --- | --- | --- |
| `suspension-pure-execution-r1` | 0 / 764 | 39 | 0 |
| `suspension-pure-no-reentry-r1` | 0 / 768 | 43 | 0 |
| `suspension-pure-cached-program-r1` | 0 / 764 | 41 | 0 |
| `suspension-pure-cached-closure-r1` | 0 / 768 | 45 | 0 |
| `suspension-value-persistence-r3` | 0 / 748 | 23 | 0 |
| `suspension-pure-compatibility-r2` | 0 / 751 | 26 | 0 |

Compatibility r2 is now also preserved in `session/validation`. I independently confirmed that both copied files are byte-for-byte equal to the `active-validation` originals inspected in round1:

- JSON SHA-256: `9f59a68e14cbd029cfc68cd541ece27f2cee43d1f5cc830fb4f370463757feb2`.
- Log SHA-256: `7f22bda5bf323d95b78ee77cd088ebc9c0bc741c4109796071eed5269c9f9fe9`.

This is evidence preservation, not a new run or a retroactive success for failedr1. Round1's precise record/log hashes, scoped success of other module/client targets and earlier-input qualifications remain binding. In particular, older failed Values/Compatibility/BodyEvent rounds are not passing evidence; old Creation/Memory/Recursive records are not silently assumed to match later edits; Relocation r6 failed overall and the later matching ForceObservation closure supplies its distinct focused evidence. Verified current dependency identity permits reuse of matching focused results only to their actual coverage.

The commands remain pinned offline Nix target builds with one Lean thread. They do not establish the exact full stock check, complete public entrypoint, exhaustive audit, or final verification. There is no claim that before/after source hashes alone prove absence of transient or undeclared validation inputs.

## Prior preparation and final disposition

- **PREP-10019-01:** retained as addressed at the static implementation/client and focused-evidence level. The actual recursive closure's world, cache and capture are recovered from execution and consumed by the later hit. Acceptance remains subject to VAL-001.
- **PREP-10019-02:** retained as an explicit scope boundary. The candidate asserts no general at-most-one cache-write theorem. Separate future work is not evidence for such a theorem here.
- Historical preparation remains historical. Neither the correction nor this review turns contributor statement checks into independent acceptance.

**Current Spec outcome: Blocked.** Static review is complete for the full58-file integration candidate, with **0 unresolved static findings, 0 formal implementation findings and1 unresolved validation blocker**. The2 prior documentation findings are fixed with the evidence above. The worst unresolved issue is PURE-SPEC-VAL-001, absence of exact complete-candidate validation.

Candidate `361f5f3f6bb3de1974510ce355883dac2bf25333`; ticket base `a3feaff319ad5fad912fb8bdc113f33fea4e2a60`; complete integration base `b422800fb5b6dc1253823057c0ea71644274d77c`. I remain available for the same-loop exact-gate continuation.
