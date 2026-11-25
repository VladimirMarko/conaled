# Independent Spec review — round 6, recovered C6c

## Outcome and scope

**Spec: Blocked. Source-content review: complete, with zero actionable source findings. Required-validation finding SP-V001 remains unresolved.** This is the original Spec axis in the existing implementation review loop. It is neither a new review nor an additional review axis. The fixed original base has not advanced. The complete cumulative 22-path candidate was assessed; prior reasoning was reused only for the 14 earlier Lean owners whose immutable bytes were independently matched to the previously reviewed round-5 owners.

The new fixed-width predecessor, decoded-certificate dispatch, and independent connected cases satisfy the selected fixed requirements on the supplied source and focused evidence. This assessment does **not** establish whole-library acceptance, receiving acceptance, a qualified FDSA-5-93 row, a complete verifier machine, formal NP membership, or completion of the broader programme. The exact-candidate integrated check has been started separately; no successful completion, matching acceptance receipt, final nonrepairing verification, or final supported post-validation comparison was supplied for this report.

### Immutable review binding

| Item | Identity |
|---|---|
| Original base and merge base | `bc95f503ccbf043136c6699992388f750270e8e6` |
| Candidate C6c | `2b3738c116b1a9a439a8fa38663e2da824a56339` |
| Candidate tree | `49fa40ddd4a5f84a0b743a0b8ca2df6248dbd930` |
| Scope identity | `de55f3aa4b6139fc018fe4f42bc9c69ba1c1f695c183f6ddd375b060c1e73d95` |
| Source/content identity | `35d0e5189e52cbd3c8175b4a235fcb0dbcf30379dd186c199fab82e73dc7bda7` |
| Projection identity | `c464cf403fcc282b52cf366d1f43cf4c6f08abedf07bfb30a1cb0db417007897` |
| Supported capture | `candidate-6c.json`, 9,666,703 bytes, SHA-256 `a94236b9c964f2343ea56f4a7507046d234f045edc5bc27e720324ac65bc2944` |
| Complete requirements | `requirements-6.txt`, 312,060 bytes, SHA-256 `2951b9e12bc0c3cf43d3f5c02c621015086040e80ec000f1fc5752a00274d0bc` |
| Scope manifest | `manifest-6.json`, 1,309 bytes, SHA-256 `fc2d8067b737277096cd8ce7aabe5406917f710c99ee0c7ab238f38e06a3f429` |
| Frozen coordinator input | `review-record.json`, 465,644 bytes, SHA-256 `4f8fc4777e4de44ddf5202e8ee2e3925903cec073bce8c7d4d36778099ff58ea` |

The actual review diff is `git diff bc95f503ccbf043136c6699992388f750270e8e6...2b3738c116b1a9a439a8fa38663e2da824a56339`, one immutable snapshot commit, with 22 changed paths, 11,489 insertions and 164 deletions. The receipt reports `status: ok`, whole mode, the same original base, and the exact scope below. `manifest.entries` is empty and `manifest.exclude` is empty. The receipt's large excluded-path inventory enumerates unchanged paths outside this scope; it is not an exclusion of task content. All 22 scoped immutable body sizes and hashes were independently matched to the metadata and audit inputs.

## Requirements, continuity, and review method

The first 218,148 bytes of `requirements-6.txt` have SHA-256 `76f3a3bb9f00f92a125cc6fbca95e1ad72168ddac188627c70c7c9495635a5ab`, exactly the previous complete requirements-5 input. The full 93,912-byte added suffix was read, including the independently fixed cases and the prospective input-parser paper. All earlier obligations remain active.

The fixed new inputs are the 45,543-byte `FixedWidthFuelMachine.design.md` (SHA-256 `611ab4411e562c2a0db369446692cdff961a05de96390105cbbe714a444963ee`), 24,012-byte `FixedWidthFuelMachineCases.plan.md` (`89f8bde059cd6d4b8c4ec6e05a3002544f3d0d2c436516c718e5c9041d7faa77`), and 23,432-byte `InputParserMachine.future.md` (`5a49fccfb1653a73e317fcf4c0f6dbe5c4c31b42f101f84f1ff5eaa639a300fa`). Their full content is retained in the requirements and, with only the recorded heading-depth normalization, in the maintained research paper. The future parser is explicitly prospective and outside the selected executable increment. Its conditional counts and remaining proof obligations are not treated as implemented or accepted results, and do not create a new acceptance gate for the fuel component.

I applied the repository AGENTS, task-authority, domain, architectural-quality, formal-development, review-loop, code-review, example-driven statement-review and relevant ADR guidance. The three new source bodies were read in full: 866 lines of `FixedWidthMachine.lean`, 584 lines of `FuelDispatchMachine.lean`, and 760 lines of `RotationCertificateFuelMachine.lean`. I inspected the actual immutable diff, related unchanged source predecessor, the pinned TM2 transition semantics and the actual `StateTransition.EvalsToInTime` record/composition semantics. No heavy build, checkout change, source edit, or common-record edit was performed by this axis.

The review examined intended semantics, independent specifications, quantifier order, domains, hidden hypotheses, vacuity, runtime callbacks, actual returned data, failure paths, costs, reached-state claims, and distinguishing connected cases. The actual Audit6 types and printed bodies were read, not merely its command inventory or author summary. Output display abbreviated namespace prefixes only; no binder, hypothesis, conclusion, or definition body was removed for that readback.

The restored workspace provides the full round-5 report pair and the coordinator's complete five-round history. The five historical round objects match the archived checkpoint101 input exactly. Earlier report descriptors are retained in that history and in round 5; this report does not claim that every earlier separate report file was newly materialized or rehashed after the wipe. Historical dispositions remain zero source findings and unresolved SP-V001, with no historical approval transferred to the expanded candidate.

## Source findings and required validation

There are **no SP-001-style source findings**, no requested source changes, and no closed or suppressed source findings. The only finding is the existing required-validation blocker:

### SP-V001 — Exact expanded candidate lacks required integrated validation

- **Severity:** blocking acceptance.
- **Status:** unresolved; carried from round 1 and reassessed for round 6.
- **Location:** complete candidate C6c/tree above, its public entrypoint and exhaustive project acceptance gate.
- **Requirement:** complete saved requirements; repository Build and audit/development guidance; review-loop validation of the actual candidate; required-validation disposition in the code-review workflow.
- **Evidence:** fresh matching normal focused builds passed for the three fuel owners (1,346 jobs) and retained parser/binary/decoder/framing owners (1,349 jobs). Actual selected-closure Audit6 passed, and this axis completed the new semantic readback. The isolated exact-C6c command was started with `./check.sh --candidate 2b3738c116b1a9a439a8fa38663e2da824a56339`; successful completion and its full acceptance evidence have not been supplied. A focused import-closure census is not the exhaustive integrated audit.
- **Consequence:** Spec cannot be marked Passed, the base cannot advance as accepted, and source/receiving/publication acceptance is not established.
- **Remedy:** supply successful exact-candidate isolated integrated validation, the matching receipt and compiler/dependency/environment bindings, final nonrepairing verification, and supported final post-validation comparison. Reassess this same finding on this same axis. If source changes, capture another immutable candidate against the fixed original base and review the changed scope.

A prevalidation live comparison is not introduced as an additional required gate. Capture plus bound before/after focused evidence establishes which source was inspected; the required comparison remains the final supported comparison after validation and final verification.

## Fixed-width predecessor: intended semantics and actual machine

### Independent semantic target and arbitrary words

`Resources.BinaryCounter.FixedWidthMachine.PredSpec` independently describes both possible raw bit-word forms. For every `k` and arbitrary higher tail, a word `false^k ++ true :: tail` returns the positive result with exactly `true^k ++ false :: tail`. For every width `b`, the all-zero word `false^b` returns the zero result with the **same supplied word**, including its width. The empty word is the zero-width case. The relation is not defined as a machine run or as the source predecessor result.

`bitWord_cases`, the structural `predSpec`, `predSpec_spec`, and `predSpec_iff` make the relation total and functional on all raw bit words. The source-connection theorems identify the exact `decFixedRun` result: `some ys` yields the positive handoff with that same `ys`; `none` yields the zero handoff with the original fuel. Width and value consequences follow from the actual returned word. There is no canonical-bit, positive-value, valid-certificate, equal-tree-size, or arbitrary natural-number decoding premise attached to the all-raw core run.

The structural `runSteps` is a proof-side accounting function. It is not called by a machine callback. Its exact cases and comparisons are:

| Entry or raw shape | Actual TM2 transitions to the live exit |
|---|---:|
| Empty scratch, first true after `k` low zeros | `2*k + 2` |
| Empty scratch, all-zero width `b` | `2*b + 2` |
| Arbitrary existing scratch of length `m`, remaining first true after `k` zeros | `2*k + m + 2` |
| Arbitrary existing scratch of length `m`, remaining zero width `b` | `2*b + m + 2` |
| Either restore phase, existing scratch length `m` | `m + 1` |
| Uniform empty-scratch bound | `runSteps fuel ≤ 2*fuel.length + 2` |
| Connection to unchanged source tariff | `runSteps fuel ≤ (decFixedRun fuel).2` |

The generalized borrow input has logical meaning `false^m ++ raw`: existing scratch records low zeros already removed. Its remaining count is `runSteps raw + m`, not the count of a fresh run over the reconstructed logical word. Both the positive and restored-zero outputs account for all existing tokens. The clients with one pending token separate this meaning from an incorrect disposable-scratch interpretation.

### Finite representation and executable callbacks

The core uses two local stack indices (`fuel`, `borrowed`), three owned phases (`borrow`, `restoreTrue`, `restoreFalse`), two result exits, and disjoint sums for arbitrary protected stack indices and caller labels. Fuel has Boolean alphabet; scratch has Unit alphabet; protected stack `k` has its supplied alphabet `Γ k`. Registers are `Option Bool × R`; the local option is overwritten by actual pop results and reset at every jump. Caller register state is preserved.

The executable `block` is a fixed finite statement tree. Borrow pops fuel, branches on the actual optional bit, pushes one Unit token for a false bit or the replacement false bit for the first true, then jumps to the appropriate phase. Restore pops one actual Unit token, writes the appropriate Boolean, and repeats; empty scratch jumps to the appropriate live result label. EOF is detected by the actual optional pop value. No local block halts, calls a recursive list evaluator, reads length or numeric value, invokes a source-code/validity oracle, or receives an unbounded list in a callback.

`program caller` delegates external bodies only after the machine actually reaches and subsequently steps an external label. The disjoint label/stack sums exclude aliasing. `program_eq_of_agrees` permits an arbitrary ambient program whose three owned bodies agree; it places no condition on arbitrary caller bodies. The statement proofs quantify the caller before arbitrary fuel, scratch, registers and protected lists, so there is one fixed program for all those inputs.

Some semantic theorems generalize beyond finite carriers because finiteness is unnecessary for correctness. The finite-machine interpretation uses the explicit Fintype instances for indices, caller labels, caller registers, and every protected alphabet. Concrete Bool/Unit instantiations demonstrate nonvacuous finite control. This is an open timed component, not a new closed whole-verifier FinTM2/NP record. The actual abstract TM2 transition count concerns executions of bounded statement blocks; it does not silently identify source-event work, host memory, or TM1/physical runtime with those transitions.

### Actual runs, first exit, and represented intermediate states

The seven one-step equations describe full actual configurations, including arbitrary old registers, fuel, scratch and protected context. The restore and borrow iterates are proved by composing those transitions. `borrowInTime` constructs actual `StateTransition.EvalsToInTime` data with an `EvalsTo` step count and an actual Option-bind iterate ending at `some` of the exact live exit configuration. `borrowInLinearTime` retains that actual count and supplies the uniform width bound; it is not an assumed polynomial-time field.

`Owned` means precisely one of the three owned phase labels. `phaseSteps` and `remainingSteps` describe the exact remaining rank of arbitrary phase configurations, with rank zero outside the component. `phase_step_data` proves actual progress, rank decrease by one, local-register reset, caller-state preservation, and fuel-plus-scratch cell conservation. These are derived from the machine transitions, not assumed as a simulation oracle.

The generic rank-prefix lemma is instantiated with those proved progress facts. `phase_prefix` covers every `n ≤ phaseSteps phase raw borrowed`, returns an actual present reached configuration, its exact remaining rank, an actual local-step path, and the equivalence `n < duration ↔ Owned reached.l`. The endpoint is therefore the first external handoff; no arbitrary caller transition has occurred. The local register is canonical after any positive number of steps. Caller-independence covers all of these actual prefixes, including the endpoint.

`stackCells` counts the local stacks plus every protected stack over finite `K`. The preservation theorem is over `LocalStep` and its reflexive-transitive closure, where each edge starts inside owned control. Connecting it to `phase_prefix` yields exact cell conservation for every actual component prefix. It does not assert conservation for unrestricted later caller execution or for host-level allocation. This boundary is material and is demonstrated by a real caller that pushes a protected cell after handoff.

`FuelRepresents` independently records the original word through borrow, positive restoration, zero restoration and the live result. In borrow it reconstructs the removed low zeros from scratch length; in restoreTrue it records the original first true and the rebuilt prefix; in restoreFalse it records the original all-zero width. At a result label it requires empty scratch and the independent `PredSpec` relation. It is false at unrelated caller/halt control. Preservation is proved from actual local steps and lifted to every actual bounded borrow prefix. This prevents a correct final arithmetic result from concealing an incorrect intermediate represented word.

## Decoded-certificate dispatch and source connection

`FuelDispatchMachine` adds one protected Fin16 certificate stack and an actual inspection label around the same generic predecessor program. Its program definition reuses `FixedWidthMachine.program` through a caller handler; it does not duplicate the predecessor implementation.

`inspectBlock` performs an actual **peek** of the certificate. It maps only presence into the finite local register. EOF reaches the live `atEnd` exit in one transition and leaves arbitrary fuel, existing scratch, protected data and caller state intact. A nonempty certificate reaches the actual borrow phase in one transition, preserving the entire `tag :: tail` word. It neither consumes or interprets the tag, checks tree equality, parses a move, nor reads fuel on EOF.

`dispatchSpec` is an independent branch description at this decoded-word boundary. Generalized nonempty runs admit arbitrary existing scratch with its represented-low-zero meaning. The source-aligned all-raw `dispatch_run`, timed records and top-level prefix theorem explicitly start with empty scratch. Exact counts are one for EOF, `2*k+3` for a first true after `k` zeros, and `2*b+3` for an all-zero width `b`; the uniform bound is `2*fuel.length+3`. Every raw tag and arbitrary tail is covered. The nonempty count is bounded by source predecessor work plus one, while the source stream has its own further costs.

The returned-data connection is substantive. `checkStreamRun_of_fuel` uses the actual source predecessor hypothesis `(decFixedRun fuel).1 = some ys`. It unfolds the existing stream into the actual parsed move result, applies that move to the **current source tree**, and feeds the exact returned `ys`, actual reached tree, target and actual rest into the recursive stream. Parse/apply failure returns the actual local false branch. The full measured equation includes wrapper entry, actual predecessor work and the actual continuation's work. `dispatch_positive_stream` conjoins that source equation with the machine's live handoff carrying the same `ys`; `dispatch_zero_stream` conjoins actual restored-fuel rejection handoff with source rejection.

These conjunctions do not claim the machine already executes the parser, rotation, equality or recursive stream. The independent cases additionally store source/target tree codes in finite-alphabet protected stacks, so represented trees are data rather than an unbounded tree register. Full compiled continuations and their representation/composition proofs remain open.

The dispatch ownership/rank proof distinguishes inspection from core phases. Actual core steps cannot jump to inspection, which justifies reusing the core rank. `local_progress` is obtained from actual pinned `TM2.stepAux`, with actual configuration decomposition. The local-step frame theorem preserves the complete certificate, all other protected stacks, caller state and exact cell count. `dispatch_prefix` and caller-independence cover all actual top-level prefixes through the first live exit, with the explicit empty-scratch entry condition. No claim about arbitrary caller code after handoff is imported.

## Independent connected cases and distinguishing obligations

All 61 new checked public case declarations were read in source and in their actual elaborated output. The JSON companion enumerates every new checked name, printed body and finite synthesis. The cases connect to production results and actual transitions; they are not a list of disconnected arithmetic identities.

| Case family | Distinguishing behavior and connection |
|---|---|
| First true and arbitrary higher suffix | Full actual output retains the untouched higher word; positive time depends on the low-zero prefix, not total width. |
| Zero widths 0, 1, 2 | Actual exits take 2, 4, 6 transitions and restore exactly `[]`, `[false]`, `[false,false]`. |
| One versus one with high zeros | Equal numeric values yield two-transition positive runs with different retained output widths. Later fresh zero runs take 4 versus 8 transitions. No free caller re-entry is asserted. |
| Two/four and nonpalindromic 20→19 | Actual low-prefix reversal/restoration preserves the nonpalindromic higher suffix and high zero width, excluding a whole-word reverse or normalization implementation. |
| Actual returned source word | The same `ys` has the source width/value property and appears in the live actual machine configuration. |
| Arbitrary pre-existing scratch and restore tails | Both restore phases prepend to arbitrary existing fuel; generalized borrow counts only remaining restoration, and the one-token examples separate zero/positive represented meanings. |
| Stale local register and EOF | Actual pops overwrite stale optional values; empty fuel and empty scratch are not fabricated from old register contents. |
| Intermediate failure/success configurations | Explicit false/false failure restoration and low-zero/first-true success traces expose actual token contents and phase changes, rather than only a final result. |
| Ambient programs and caller independence | Actual execution follows the three/four owned bodies under arbitrary external implementations, through the exact first handoff. |
| Every actual prefix | Clients combine actual run hypotheses, existence from production prefix theorems, remaining-rank ownership equivalence, caller/context preservation and exact workspace. These are not vacuous final-state-only implications. |
| Represented 12→11 state | The actual two-token restore configuration after three steps satisfies the independent representation invariant for the original word. |
| Actual timed caller composition | The generic client consumes genuine timed evidence from the exact returned live configuration using the same step function; the concrete sentinel supplies that evidence. |
| Sentinel caller | Two component steps reach a live positive label; a third actual step pushes a protected cell and creates a present halted configuration; only the fourth step yields outer `none`. Workspace is conserved through handoff and increases by one afterwards. |
| EOF versus nonempty dispatch | Empty fuel plus EOF takes one step; empty fuel plus any raw symbol takes three. Arbitrary high-zero width does not slow EOF. |
| Nonempty certificate untouched | Positive/zero dispatch preserves every tag and arbitrary tail; one pending token still has represented meaning. |
| Width-sensitive later dispatch | First positive handoffs for width-one/width-three representations take three each; later zero entries take five/nine. |
| Source zero rejection | All-zero width `b` gives machine handoff `2*b+3` and actual source false observation `2*b+4`, with arbitrary trees/tag/tail. |
| Reserved tags and missing move delimiter | Every reserved tag 11–15 reaches the positive handoff before parsing; source costs 7 for the reserved head and 9 for the missing delimiter are kept distinct from the three-step handoff. |
| EOF equality boundary | The machine's one-step EOF exit is independent of source/target equality; actual empty-shape source comparisons give true/false at source work 3. |
| Emitted legal rotation | Actual emitted root-right certificate and represented tree-code context reach the parser exit in three machine transitions; the actual source verifier succeeds at work 22. |
| Longer borrow | Arbitrary `k` low zeros and higher tail give `2*k+3` machine steps and source work `3*k+22` for the same real root rotation. |
| Equal initial trees, nonempty certificate | The machine still takes the positive handoff and preserves the certificate; the actual source stream rejects the root rotation at work 18 rather than short-circuiting equality. |
| Eager binary layer | For 24-bit input coding empty shapes with width-one zero fuel, any one-bit certificate fails at source work 48; a fully encoded one-tag certificate fails at 57. The generic case covers every bit and every tag. |
| Decoder-to-gate bind | The explicit reserved-tag client connects actual partial decode `(none,2)`, actual complete decode `(some [11],6)`, the 48/57 binary source observations, and the actual five-step zero-fuel gate reached only by the decoded token word. No unvisited-bit-tail claim is imported. |

The finite concrete control/stack cardinalities are checked (core registers Bool: 6; core labels Unit: 6; core stack indices Unit: 3). All new finite instance syntheses succeeded, including dispatch stack families and Fin16 certificate alphabet. Arbitrary contexts remain arbitrary lists over finite alphabets; no size bound or correctness assumption on their contents is smuggled into these cases.

## Retained cumulative owners and public contracts

The 14 earlier Lean owners are byte-for-byte identical to reviewed C5b and checkpoint101. Their complete prior assessment is retained, and their original Audit5 public output is exactly reproduced inside Audit6. This reuse does not imply that C6c inherits integrated acceptance.

| Retained capability | Spec conclusions retained for identical source |
|---|---|
| Actual tree and complete input parsers | Arbitrary frames and raw tails, successful and failed continuations, actual child/bind reconstruction, raw recognition and malformed/early failures. Tree cost `7*n+3`; raw bound `5*M+2`; complete input cost `7*Ns+7*Nt+3*b+15`, raw bound `20*(M+1)`. Unequal tree-size syntax is allowed and bit width is retained. |
| Actual binary-fuel stream | Equality only at actual EOF; predecessor before parsing on every nonempty step; actual move on current returned tree; same returned fuel and rest; immediate stop on all failures. Raw iff has no validity/canonical-bit/equal-size/positive-fuel premise; work bound covers all raw tails. |
| Independent Yes and attained witness | Common-size shapes and attained minimum distance define the independent language. A witness is chosen to fit both the supplied numeric threshold and `2*n−2`; successful intermediate sizes bound encoding. Word witness bound `2*M²`, including small shapes. |
| Word verifier | Actual input parse first, false before certificate on input failure, direct binding of returned fields; raw acceptance iff, soundness, small completeness, and all-raw work `32*(M+W+1)²`. |
| Four-bit codec and binary verifier | All 16 LSB-first blocks, reserved tags, width and block order, arbitrary successful/failed suffixes, exact pack/unpack/partial costs and raw bound. Input decode→parse→complete certificate decode→stream, no second input parse. Independent BinaryYes, bit witness `≤I²`, raw work `40*(I+C+1)²`, and explicit eager-certificate limitation. |
| Concrete bit decoder | Fixed finite three-stack/three-label execution, independent injective result code, exact all-raw `2*floor(I/4)+2`, actual linear/polytime record, and actual reached-cell bound `I+1`, with arbitrary-state/tail and halt/outer-none cases. |
| Strict pair framing | Independent raw framing/injectivity/failure semantics, actual four-stack/five-label program and cleanup, generalized states/tails, success `2*I+2*C+4`, all-raw bound `≤2*N+2`, actual workspace `N+1`. Same witness carries framing/size/time/space statements; actual returned pair feeds the source verifier. Literal 121/132/66 and appended 122/134/source-false-112 separators remain intact. |

`SquareApplications.lean` contains the three new ordinary imports in addition to all retained public imports. It is exactly unchanged from checkpoint101; relative to C5b the three new imports were inserted before the unchanged final comment. The older entire entrypoint is therefore not literally a file prefix. No executable source was hidden by omitting its public import.

## Recovery, proof repairs, and immutable source continuity

The checkpoint101 source corresponds to the first complete C6b attempt. Its core checks failed; dispatch and cases had not compiled. Those historical outcomes remain recorded. The prospective repair recipe was unexecuted at that freeze and is not retroactively treated as a pass.

I compared the archived checkpoint101 source with immutable C6c. The core repairs address configuration extensionality over protected functions, names, arithmetic normalization, explicit rank/label instantiations, relation-path APIs, and removal of irrelevant section instances. Dispatch repairs similarly make actual configuration decomposition, continuation-pair cases and iterate rewriting explicit. The examples make intended finite carrier premises explicit on the client theorems, disambiguate label parameters, and repair proof applications/simplification. This is not a claim that all surface theorem text is identical: the finite premises and explicit parameters are visible and were independently assessed in their actual elaborated forms. They match the fixed finite-context plan and do not weaken its specified target behavior. The executable statement blocks, raw semantic specifications, literal expectations, exact counts, and intended all-raw production domains are preserved.

The recovery record binds the three reconstructed source hashes to the recorded successful post101 source identities. Fresh normal Lake builds were then actually run in the restored environment. Their successful logs are new observations, not reconstructed historical logs. No manual olean injection or resource cap is recorded. The recovered helper baseline was obtained through supported B/B validation with the same original base and full manifest; I independently compared all 11 immutable baseline fields, including entries/content identity, against the old baseline receipt. Changed local retention refs and observed author-source identity do not advance the review base.

The coordinator input's five historical round objects match the archived checkpoint101 input exactly. This report preserves that history, the historical C6a plan-only snapshot, C6b failed/uncompiled state, old-base failure, and unknown post-wipe C5b integrated outcome. It does not rewrite those histories using current success.

## Actual focused evidence and semantic readback

The fresh fuel-owner normal build completed with actual exit 0 at the exact three source hashes, 1,346 jobs; the fresh retained-owner normal build completed with actual exit 0, 1,349 jobs. Both before/after source mappings were independently matched to immutable C6c. Their complete short logs were read. Replayed/build module-system warnings do not constitute a source proof failure or a new specification finding.

Audit6 actually ran `lake env lean -EhasSorry` under the pinned native profile and completed exit 0 in approximately 6.55 seconds. I independently matched its 22 before/after source bindings, all six configuration bindings, candidate/base/tree, receipt, input-manifest, audit-source and output-log hashes. The configuration files are unchanged from B. The environment record identifies Lean 4.35.0 / commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and the nine pinned clean dependencies, including Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The audit namespace is equal to the immutable repository `ProofAudit` namespace except for the scoped success sentence. Its import boundary is deliberately narrower than the full public entrypoint. The complete Audit5 source is an exact substring of Audit6 at byte offset 179. The old actual contract/type/body output is an exact prefix of the current readback after the census: **483,922 bytes**, SHA-256 `b4dbfdc6a55712fd3682cff25f64d338aed70f98b31f422da9909a0e237ce4a4`. All 40 earlier module census counts are unchanged.

| Audit measure | Actual value |
|---|---:|
| Selected project modules | 43 |
| Kernel-safe declarations, including generated/private logical roots | 2,841 |
| Theorem declarations | 1,902 |
| Unsafe runtime declarations excluded | 0 |
| Three new owners together | 505 safe declarations / 285 theorems |
| All 17 cumulative new owners | 1,558 safe declarations / 1,031 theorems |
| Total public check outputs | 438 |
| Newly added checked outputs | 217: 91 core, 65 dispatch, 61 case declarations |
| Total/new printed definitions | 135 / 78 |
| Total/new finite-instance syntheses | 40 / 27 |

The actual transitive axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`. This is a census of every safe declaration in the imported project closure, not a spot check of theorem names. The new actual readback spans log lines 6728–12981; every line was read, with output-truncation gaps reread before conclusion. Pretty-printed proof elisions and generated matcher wrappers were not mistaken for complete semantic definitions: the actual source bodies, related APIs and pinned semantics were inspected separately.

The readback confirms the material hypotheses and quantifiers: arbitrary caller code; arbitrary finite caller/protected representations where intended; arbitrary raw input and higher tails; generalized scratch meaning; explicit empty-scratch source entry; actual `some` live endpoints; actual `EvalsToInTime` constructors; actual caller composition; rank-bounded first-exit paths; restricted local reachability; and actual returned source fuel/current tree/rest. Finite instances do not introduce unbounded numeric or tree registers. No source-only expected result is presented as an already executed complete verifier machine.

These focused results resolve neither the whole-entrypoint build nor the exhaustive integrated gate. `candidate-6c-metadata.json` and the immutable maintained records describe the historical capture-time state (“prepared, unrun” for Audit6); the later bound result and this semantic inspection supersede that observation for the current review without modifying the frozen source.

## Maintained paper, canonical requirements, and progress records

The current paper retains the entire earlier C5b paper as an exact byte prefix. The archived checkpoint101 paper is also an exact prefix of C6c. The full fixed fuel design, independent case plan and prospective parser plan are retained with the recorded heading normalization; current recovery observations append to their historical context. Earlier source mathematics and fixed expectations were not replaced by a terse recovery summary.

I independently compared the current CTB and coverage objects with B, and with the archived checkpoint101 source for the recovery-only edits:

- All **44 complete `new_tickets` objects**, not only their IDs, are equal to B. The canonical sorted compact-JSON digest of that unchanged array is `9b6c880e1a451c6c4d549c32b19ef224b62903dea2bf71b7bc2772c92801d718`.
- All three canonical requirement owner files are byte-identical to B. Canonical owner declarations, authority, namespaces, source correspondence, authorized scope, PFDS remaining work, literal user override, historical catalogs, IDs and unrelated states are unchanged.
- Sixteen of the 18 local-state objects are wholly unchanged. CTB-78 changes only its current next-action prose; CTB-24 changes the selected current-work/progress descriptions. All protected receiving fields, including progress084/#660, prior R2/#659 and checkpoint074, retain their full objects and scopes.
- All **681** pre-existing numeric/Boolean/null CTB leaves and all **129** such coverage leaves retain their types and values at the same JSON paths. No qualification count or Boolean was promoted. All non-FDSA book objects and FDSA qualification details other than the selected explanatory boundary prose are unchanged.
- Relative to checkpoint101, CTB has only five changed text leaves and coverage only one changed text leaf; container shapes and all nontext data are identical. The three fuel source owners appear explicitly in the author increment and fuel preparation record.
- Chapter 5 remains 92/94 with FDSA-5-92 and FDSA-5-93 open; Chapter 9 remains 61/110 with its retained remaining rows. Historical acceptance remains tied to its original source scope. Current focused progress is not presented as receiving acceptance.

C05-093 is retained as the ledger alias for FDSA-5-93, the page-76 NP-membership/polynomially checkable rotation-distance-witness obligation, not a newly invented printed exercise. Separate mandatory FDSA-5-92 still requires the exact maximum `2*n−6` for `n≥11`. The full VFA/FDSA/PFDS programme, the PFDS book/thesis union and separate ADWH programme remain intact.

The new component does not close the full machine bridge. Actual input/move parsers, rotation and equality execution, repeated streaming, eager binary/framing adapters, represented-state links, quantitative time/workspace composition, output/cleanup and final formal NP correspondence remain open. The future parser paper explicitly preserves its unimplemented status, rollback/representation obligations and conditional bounds. The selected component's completed content review does not qualify that prospective work.

## Validation history and next disposition

The original-base check was actually completed unsuccessfully with outer exit 1 and ten constituent Lean exit-137 failures. The preserved final record does not establish their cause, a proof diagnostic, or a passing receipt. Those sources are unchanged by this cumulative scope. The historical C5b integrated run has no known final outcome or passing receipt after the wipe; it is not described as a currently live command.

The exact C6c integrated command was started in the separate acceptance checkout at 2026-11-21 21:45:32 UTC under the pinned native profile, with private project outputs and the stable dependency cache. Root reported session 13287 running. This axis has not been supplied a matching successful completion, full exhaustive-audit receipt, final verification or final comparison. **SP-V001 therefore stays unresolved and the overall Spec outcome remains Blocked.** No failure cause, ETA or eventual result is inferred.

Root additionally supplied checkpoint102 creation, independent archive/recovery verification and successful save records. The recovery record describes an ordinary fresh public clone plus the 22-file delta reconstructing the exact C6c tree, without a private author commit or earlier packet. I read and identified those records; archive inspection itself was performed by the designated recovery work, not by this Spec axis. Recovery/save evidence remains separate from source acceptance, and this report postdates the frozen packet102 review state.

When matching integrated evidence is supplied, this same Spec axis can reassess SP-V001 without replacing the completed source assessment for unchanged C6c. Any source change requires a new immutable scope assessment in the same loop. No receiving/master publication or person-directed action was performed or authorized by this review.

## Complete immutable file inventory

Each row below was matched against `git show C6c:path`, candidate metadata and the focused audit binding. “Retained” means equal to the previous reviewed C5b body; it does not mean accepted as part of C6c's still-pending integrated gate.

| Path | Bytes | SHA-256 | Round-6 treatment |
|---|---:|---|---|
| `Applications/Resources/BinaryCounter/FixedWidthMachine.lean` | 40,378 | `005720a8f68c8140125a9e22724bdb007d096cc55bb253dc982cd2b6f3a86b76` | New source; full review |
| `Applications/Resources/RotationCertificate/BinaryVerifier.lean` | 12,641 | `1fe9596dbc3fabe75e57583f6283d14eb2f6b19aeac503bdde3c1d56ad6c57bd` | Retained; identity checked |
| `Applications/Resources/RotationCertificate/BitCodec.lean` | 15,284 | `3d4ee905352fd99f544a9ef6cc2e5224bbfbba0d654c0835ccc4a94643d4f72e` | Retained; identity checked |
| `Applications/Resources/RotationCertificate/BitDecoderMachine.lean` | 20,150 | `9a666a7a75a6b70e2eb8efb50973042b9ef71494588f2d31aa3d58e1e225f267` | Retained; identity checked |
| `Applications/Resources/RotationCertificate/BitPairFraming.lean` | 34,844 | `62b4b6cb63c9711a0582798a736f342f5a850325be8deb1962e096d4f028fa49` | Retained; identity checked |
| `Applications/Resources/RotationCertificate/FuelDispatchMachine.lean` | 28,035 | `a233cf25f0557e6bdad5c763e187c18199b2a7fbb1322b62ef2747f7127e665a` | New source; full review |
| `Applications/Resources/RotationCertificate/InputParser.lean` | 12,371 | `071227a01d3ed214a5fae42300a7b36e715a3fda0110e92ff8f71f2196b33e95` | Retained; identity checked |
| `Applications/Resources/RotationCertificate/Streaming.lean` | 16,291 | `5421a2b300c23d05fd25f548ee8d893441534a3124638f62a0c7a78efb9683ed` | Retained; identity checked |
| `Applications/Resources/RotationCertificate/TreeParser.lean` | 11,312 | `be9ac0557d725aa5001631b2400936f354344a4c049f14e69dcdf2a0c7d9c2da` | Retained; identity checked |
| `Applications/Resources/RotationCertificate/Verifier.lean` | 7,117 | `777c78bbd3d9e22cdf9091df7480e753ef9215ce3d3353b61a47ed56f2c2d211` | Retained; identity checked |
| `Applications/Resources/RotationCertificate/Witness.lean` | 4,494 | `9c072519897b4da2f439b57d07aaa39666286064c852c811149af055460b7650` | Retained; identity checked |
| `Examples/RotationCertificateBinary.lean` | 14,837 | `b73a0090e5d19eade84b4bb43b6314d2a3da2b46bba0569f17daf20d5a7c6673` | Retained; identity checked |
| `Examples/RotationCertificateBitDecoderMachine.lean` | 15,665 | `4e1f7f108e107b89d76493795d878be03d333e9ce5fade9d58c0f27be4f520ed` | Retained; identity checked |
| `Examples/RotationCertificateBitPairFraming.lean` | 27,139 | `871160b76b8c7842c7252516f207728e311a145e6219dd4e0582216c2e17a2e1` | Retained; identity checked |
| `Examples/RotationCertificateFuelMachine.lean` | 40,502 | `0e97492fa34beac791117d3e04cc35b450d23cf76ee9c001300f0a12b7fe375b` | New source; full review |
| `Examples/RotationCertificateParsing.lean` | 12,173 | `1283fca9fcde79b2e603b1052a03b28af93e4dc6b0b187d792f1a6eaed86ce96` | Retained; identity checked |
| `Examples/RotationCertificateVerification.lean` | 16,154 | `b1a71b06db5ccf357a45516256d2118690f5d42949c4097d630100f47aa96bc8` | Retained; identity checked |
| `SquareApplications.lean` | 43,460 | `bf57a2fddf29afa6ab93471412e5bf373b8309ba49c40d37517132895acbf561` | Current imports/paper/records reviewed |
| `docs/research/fdsa-rotation-certificate-preparation.md` | 264,302 | `f3074f113007e57985ba616476eb6149f2dd635d225591c2cdb79633fe94699d` | Current imports/paper/records reviewed |
| `docs/textbooks/CTB.json` | 821,776 | `bbb1207bcc0b891a67745c2d46c8c287b702813af78153a3f403bb00bca41f9b` | Current imports/paper/records reviewed |
| `docs/textbooks/coverage.json` | 54,158 | `b9e70e1e89342a819f9aaa4bbfd305f9035d045f48965664790a913afd0308c2` | Current imports/paper/records reviewed |
| `docs/textbooks/inbox/README.md` | 5,187 | `fac7b36b5dea123da9b7e1b916548b3efa8ba0de6a481f7b7bb0f38d2929738f` | Current imports/paper/records reviewed |

## Evidence descriptors

The companion JSON carries the complete command-name inventories, source bindings, preservation results, historical dispositions and machine-readable finding. The principal files are:

| File | Bytes | SHA-256 |
|---|---:|---|
| `candidate-6c.json` | 9,666,703 | `a94236b9c964f2343ea56f4a7507046d234f045edc5bc27e720324ac65bc2944` |
| `candidate-6c-metadata.json` | 8,868 | `b6015fd149c82701eebdcc7094869aaf37f4c62991b1fa1a7af1a702d02c3311` |
| `requirements-6.txt` | 312,060 | `2951b9e12bc0c3cf43d3f5c02c621015086040e80ec000f1fc5752a00274d0bc` |
| `requirements-history-6.json` | 3,778 | `1c1c1794d3612b0be7824b2748bd2b92eddbb38bd3b6e5e92a768d7bd6d9ea0a` |
| `manifest-6.json` | 1,309 | `fc2d8067b737277096cd8ce7aabe5406917f710c99ee0c7ab238f38e06a3f429` |
| `scope-extension-6.json` | 4,139 | `503083f55a498fbf6df95756f29bfa9d7a3cd44fa3381f25e7067d778b236f3a` |
| `baseline-6-retention-recovery.json` | 1,843 | `61c377c82aea5cb30cf48b0fa83e834cb78505badbc32a2585d25d8ac554554c` |
| `baseline-6-recovered.json` | 9,664,530 | `7ba2a151c00b0e3c20951777f1563f850e659aca8f93f18417dd81e42c649f6f` |
| `recovered-fuel-source.json` | 1,117 | `26be0630a38202bc33a19adf73e89cd479796174f8bcb7a490a1f386b7fc216b` |
| `recovered-fuel-build-102-result.json` | 2,002 | `195748db747ad09de7636041d68efb41b21622e2bd465534dfa66794e6991ef8` |
| `recovered-fuel-build-102.log` | 6,470 | `f787b6980593b459ef73a4a6c0e3aa6d875f7513a87a27630368df73f218bdc6` |
| `recovered-prior-owners-build-102-result.json` | 6,441 | `b4863cdcc5987014ef488daed96a04c9e96d48b5c7475170754b9f7e4513fcab` |
| `recovered-prior-owners-build-102.log` | 5,181 | `265e9a4dfe6af844f37b9117651775371987107cc555cee6ccf7a547154c8b22` |
| `environment-recovered-102.json` | 1,470 | `8bd6308b69c8b869509f4a092e56289afa4c92785505a2246f995e1dd034a272` |
| `focused-audit-inputs-6.json` | 55,009 | `c205136e26ea581cd049eecb652cacc8ca4959569552950fc1dce5c03db063fc` |
| `FocusedAudit6.lean` | 58,429 | `655f104f238b7ddcb506fc4ae52ac3dbf40f1d3a46974003cdf31745ff1c1a75` |
| `focused-audit-result-6.json` | 10,399 | `6ca69f98c0498379079a9f8cb4e869e94f673f82573c1fbb9c3f2210cdeabaa2` |
| `focused-audit-6.log` | 952,799 | `046e903eeb73d279950f942d96711b44f8ef88f9a1604d68c9ec494bc79a9282` |
| `acceptance-c6c-check-start.json` | 878 | `6b5f6dbec611be51be0a3d94b3fb359d7f7440d20190ec38501598f9cb41a198` |
| `baseline-check-final-result.json` | 3,752 | `23eac26744ede3f2e22e4c2a0b4682900be76308d8af12937d886dc8049d77b4` |
| `review-record-checkpoint101-input.json` | 403,220 | `a20338671ca23f65317543f05ec323d809a8ed997025664cdbe07655fe0655fe` |
| `review-record.json` | 465,644 | `4f8fc4777e4de44ddf5202e8ee2e3925903cec073bce8c7d4d36778099ff58ea` |
| `spec-review-round5.md` | 43,170 | `9ace15ef585229fd6aab2d351ba840f4f4cb29e8e43499ed8225f4ac17c00fdd` |
| `spec-review-round5.json` | 71,620 | `41ca591bf1741facc1cb08c790bc530e5c891bde6f616c5d672d04c9cf0e3003` |
| `checkpoint-102.json` | 515 | `b43930777ab9fee601a929b64a2f20faa823280d1dac705f7f7970349dee3e84` |
| `checkpoint-102-recovery.json` | 13,216 | `3ae684c0c7122ed1180e5e29d079c167b201cfadc2666aacc47a9a6c7ce7133b` |
| `checkpoint-102-save.json` | 455 | `c350ec0d905e052a44b9ec083e11dd0e9ccd51e57c4f6b0afa76966d5b4c380e` |

Completed by `/root/parser_review/spec` at 2026-11-21T22:05:59.008031+00:00. No source, checkout, coordinator record, or prior report was modified.
