# FDSA-XW01 — independent Spec source preparation

**Current outcome: Blocked pending actual validation.** At the exact original candidate `7c6bc92c276d39e84351324c442869b8ffa6758c`, I found **zero new concrete Spec source findings** in the complete frozen XW01 scope. This is an independent nonauthor source assessment, not final approval: no candidate compilation, actual expanded-type inspection, whole-project check/audit, final two-axis approval or immediate candidate verification is credited here.

## Identity and complete scope

The fixed original base is `a14977b9e316cc484ffad8a470d26b15615956c0`; the candidate is its direct child. The immutable diff has exactly six paths, 837 added lines and no deleted lines. I read every line of every complete candidate file and the entire original diff. The scope is not reduced to the core or to a later delta.

| Complete immutable file | Lines | SHA-256 |
| --- | ---: | --- |
| `Applications/Probability/AccumulatedWork.lean` | 157 | `7731f8a6c5222810ba11a056fc620c68a152dce0024ff3e2544d17fff70a80ba` |
| `Examples/AccumulatedWork.lean` | 299 | `7ef773d2ce87ce1b119838e083ee4a4cff072f5d96f4a8887f8494a80d04c20c` |
| `Examples/AccumulatedWorkBoundary.lean` | 219 | `68ba8fd9571ad860d7f5aabd7093f35c0220ff12ead1e283e903b5bdc90a6927` |
| `SquareApplications.lean` | 253 | `40d97b7972ba8085c076c6482cc99f130f8e92beeea3f5c0b5fc8e040e4727dd` |
| `docs/research/fdsa-accumulated-work.md` | 145 | `191a7c449f936b84c17f3f5d33a935dd4440a199fc7287e576dfd38f4fbaca8e` |
| `docs/research/fdsa-reconstruction-map.md` | 278 | `35c5cf425168b21900c84735020df5b6a6b9ba86c099ad4d2c555821858a7024` |

The entire 160-line frozen `reviews/accumulated-work-requirements.md`, SHA `85c651891cf8c8ee016706bf8baad7711dbd9965eb20ad5c6e96d2ab112728e1`, is controlling. I also read the full ticket, candidate handoff, 264-line draft preflight, 380-line probability API preflight, 578-line probability source preflight and 167-line finite-calculation record. The old author preflight explicitly excluded the Boundary module; **this review includes all 219 Boundary lines and all frozen boundary requirements**. Author reports and calculation aids do not substitute for the source assessment.

The governing AGENTS, implementation, shared review-loop, code-review/heuristics, example-driven-development/worked-example, architecture/domain/glossary/ADR/language and README instructions retain their previously fully assessed identities: all 15 candidate blobs were compared and match exactly. The README's normal-versus-fresh acceptance rules remain in force; a focused build is not a complete candidate check. Source changes alone do not invent a fresh-check trigger. The Lean and dependency pins are unchanged, including Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Mathematical statements and quantifiers

All six core declarations quantify over one arbitrary measurable sample space and the **same measure** `μ`, with nonnegative extended-real stage observations `X : Nat → Ω → ENNReal`. The core does not impose a finite/countable/nonempty sample space, a probability measure, finite measure, independence or an algorithm-specific conditional law. That distinction is substantive: local normalization of the eight-point worked example is not exported as a hidden core premise. All conclusions are actual integral or measure inequalities; none simply assumes the desired expected-work bound.

| Frozen requirement | Public source contract | Independent assessment |
| --- | --- | --- |
| 1. Geometric means | `lintegral_le_geometric`, lines 39–50 | Initial integral at most `N` and every integrated one-step drift at most `q` times the preceding integral imply the time-`t` bound `q^t * N`. Induction and monotone multiplication suffice. No measurability, strict contraction, finiteness or independence premise is introduced. |
| 2. Shifted and total sums | `lintegral_tsum_shift_le`, lines 54–70; `lintegral_tsum_le`, lines 74–81 | AE measurability of each stage justifies interchanging the countable nonnegative sum with the lower integral. Each shifted mean is bounded by the proved geometric bound, then the ENNReal geometric-series identity gives `q^w * N / (1-q)`. Total work is the zero-shift specialization. Infinite values remain meaningful. |
| 3. Finite expected work | `lintegral_tsum_lt_top`, lines 85–94 | `q < 1` makes the denominator nonzero and finite `N` makes the quotient finite. `q = 0` and `N = 0` are retained. Finite expected work is not claimed to prove a finite number of stages. |
| 4. Tail from the actual prefix | `measure_tsum_ge_le`, lines 99–137 | For the chosen natural `w`, the actual prefix sum is AE bounded by `w*N`. Together with strict contraction and positive finite `N`, this yields the non-strict tail mass at threshold `w*N + N/(1-q)` at most `q^w`. The hypothesis concerns that prefix, not an unrelated sequence of expected prefixes. |
| 4, convenient corollary | `measure_tsum_ge_le_of_stage_le`, lines 141–155 | AE bounds `X t ≤ N` for all stages imply the chosen prefix cap by a countable-index AE conjunction and finite-sum comparison. Countability is for natural stages, not for outcomes. The more general single-prefix result remains public. |

The tail proof first proves finiteness of `w*N`, positivity and finiteness of `N/(1-q)`, and AE measurability of the remaining sum. It decomposes the actual total into the finite prefix plus the shifted tail. On the AE prefix-cap set, the large-total event implies a large-tail event by **finite** ENNReal additive cancellation. `measure_mono_ae` transports this event inclusion. Markov's inequality at the positive finite threshold and the shifted-integral bound then cancel that threshold and yield `q^w`. The proof never cancels a possibly infinite prefix and never divides by `q`, so zero drift remains available.

I checked the potentially consequential extended-real cases in the source argument. The unrestricted mean and series bounds deliberately permit `q ≥ 1` and infinity. In ENNReal, zero times infinity is zero, consistently with a zero next-stage integral forced by zero drift. The summability fact used for prefix decomposition is summability in the extended topology and does not assert a finite sum. The finite-integral theorem separately imposes strict contraction. The non-strict tail theorem separately excludes `N = 0`, with a concrete counterexample below.

## Actual measured work and the dependent finite law

I read the complete unchanged local `Measured`, `Workload` and `CallCount` modules. `Measured` stores an actual value and cost; `bind` evaluates the continuation on the produced value and adds costs, `run` sequences those steps, `reweight` keeps the produced value and maps its recorded cost, and `tick` adds one to the actual cost. These contracts support the clients directly; the example does not define a fictitious program whose cost is merely the desired total.

The main example uses the single law `uniformOn univ` on `Fin 8`. Stage zero always charges one, stages one/two/three charge on the nested events `ω<4`, `ω<2`, `ω<1`, and all later stages charge zero. `step` records the active stage in the actual output list and charges one; `program` runs the four stages on the same outcome. The complete output lists, stage charges and measured costs were assessed together.

| Outcomes | Actual output | Actual cost | Probability |
| --- | --- | ---: | ---: |
| `0` | `[3,2,1,0]` | 4 | 1/8 |
| `1` | `[2,1,0]` | 3 | 1/8 |
| `2,3` | `[1,0]` | 2 | 2/8 |
| `4,5,6,7` | `[0]` | 1 | 4/8 |

The exact stage means are `1`, `1/2`, `1/4`, `1/8`, followed by zero. They prove the actual integrated drift with `q=1/2` and initial bound `N=1`. `accumulated_eq_cost` links the infinite observation sum to the measured program cost using finite support; the mean is exactly `15/8`, and the public generic theorem yields the bound `2` and finiteness. This is a genuine use of the generic result after deriving its premises for the actual common law.

The positive-shift case is also connected. At `w=1`, the remaining accumulated work equals the natural measured cost minus its initial one-unit charge; every outcome has that charge, so the displayed subtraction has no accidental underflow. The exact remaining mean is `7/8`, while the generic shifted bound gives `1`. The event of measured cost at least `3` is exactly `ω<2`, with mass `1/4`; the generic non-strict tail bound is `1/2`.

The same-law dependence is explicit: the first two nontrivial stage events have masses `1/2` and `1/4`, their intersection has mass `1/4`, and the product of their masses is `1/8`. The example proves the mismatch. No independent-stage multiplication is used in the generic argument or the calculation.

The affine client preserves its actual output through `reweight (2*·)` and then uses `bind` to add a three-unit charge. Its actual cost is `2*W+3`, exact mean `27/4`, and bound `7`. The bound uses the original generic expected-cost bound plus justified integral scaling/addition under the concrete probability law. The event at threshold `9` is exactly the original event at threshold `3`, so its mass is `1/4` and its bound `1/2`. The affine offset is not silently substituted into the original drift hypotheses.

## Consequential boundaries

| Boundary | Source evidence and mathematical consequence |
| --- | --- |
| Zero drift, positive initial work | `oneStageRun` genuinely composes three ticks through bind, producing value `7` and cost `3`. `singleWork` observes that actual cost at time zero and zero later. The generic mean/finite/tail statements apply with `q=0, N=3`. |
| Zero versus positive tail prefix | The zero-prefix event includes the entire one-point law: equality at the non-strict threshold gives mass `1` and bound `0^0=1`. For every positive natural prefix, the threshold exceeds total work and the tail mass/bound are zero. |
| Zero initial bound | `zeroWork` has expected total zero by the generic mean theorem, but at `N=0, q=1/2, w=1` the non-strict zero-threshold event has mass `1`, not at most `1/2`. This validates the positive-`N` tail restriction without excluding the zero-mean case from other results. |
| Mean drift without a prefix cap | Under the uniform three-point law, `rareWork` is `3` only on outcome zero at time zero, and otherwise zero. Its initial mean is `1`, drift is zero and total mean is `1`; the event of total at least `2` still has mass `1/3`, contradicting the proposed zero tail bound at `q=0, w=1`. |
| Missing cap made explicit | The rare-work prefix-cap failure is derived using the public single-prefix theorem and its known positive tail, so the example identifies the exact missing premise. No prefix bound is assumed in the counterexample calculation. |
| No strict contraction | `constantWork` is constantly one on the one-point law. It has initial mean one and drift ratio one, but both total work and its integral are infinity. The extended bound at denominator `1-1` is valid and vacuous; the finite conclusion is not claimed. |

All values, events and law normalizations above were assessed from the complete source, not accepted from the author calculation record alone. Arithmetic/proof elaboration remains untested by this reviewer and must be established by the real candidate checks.

## Pinned API assessment and source correspondence

The receipt records exact Mathlib blobs and literal line ranges read. I inspected the relevant source contracts for: `lintegral_tsum`, AE measurable countable sums, the ENNReal geometric series and always-extended summability, prefix-plus-shifted-tail decomposition, finite additive cancellation, quotient positivity/finiteness/cancellation, `measure_mono_ae`, `ae_all_iff`, Markov's non-strict threshold bound, the actual uniform measure and its finite-event formula, finite-space lower integrals, and the affine scaling/addition identities. The generated additive prefix and AE-sum contracts were checked through their pinned multiplicative declarations and `to_additive` attributes; this is source inspection, not a claim to have printed their elaborated types. The API checks did not disclose an extra core sample-space or probability hypothesis.

For primary book correspondence I directly read the pinned book text, literal-newline lines 1471–1547, covering the three-way selection dispatch and printed pages 34–35. The PDF identity is `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`; extracted text identity is `7e5c0b4e157d28d303cc6248746aa63e1415445fa79f3556ff95ac1bf6b17333`. The book's high-probability discussion cites Karp (1994), section 2.5. This unit supplies a bounded generic analytic layer toward that discussion; it does not assert that the book already states every present formal theorem.

I read the full retained probability source preflight, including its attributed inspections of the pinned AFP QuickSort source, the newer quickselect recurrence account, and the joinable-treap discussion. Those preserved attributions are not a new full theory/paper read or rebuild by me. The unavailable Karp source remains unavailable; no contents are invented. The newer recurrence account has a different larger-branch cost model and strict-tail conventions, so its result is not silently treated as the exact non-strict measured-work theorem here. None of those external proofs is a Lean dependency of this unit.

The following algorithm obligations remain substantive and deferred: conditional fresh occurrence sampling given selection history, duplicate keys and valid ranks, the appropriate next-size bound and its conditional mean, and a bridge from accumulated stage sizes to the actual scan tariff. A natural-prefix tail parameter does not automatically prove the same claim for arbitrary real prefixes. Both recursive quicksort branches and the distinction between uniform-input and fresh-pivot laws remain separate. Shared priority ranks, overlapping treap operands, conditional cluster/rank bounds and weighted costs do not acquire independence from the analytic theorem. No parallel-span requirement or later chapter activation is added.

The public note and reconstruction-map addition accurately describe an uncompiled analytic draft and these exclusions. Their original historical Chapter 1 status does not supersede the currently accepted Chapter 1 record; status must be reconciled in a future incorporation candidate. The earlier map's Chapter 1 interface sentence is not classified as a new XW01 copy of XP01-DOC-001: this original XW base predates the later budget-interface change.

## Authored surface, findings and remaining gates

The source inventory has **78 public named declarations: 67 theorems and 11 definitions**. Core contributes 6 theorems; Main contributes 29 theorems and 6 definitions; Boundary contributes 32 theorems and 5 definitions. Main additionally has two private named finite-law helpers and one **anonymous** `IsProbabilityMeasure law` instance. There are no anonymous example declarations in these three files. The instance is separately accounted for; its compiler-generated name and elaborated type are not invented. These are source counts, not audited kernel declaration counts or whole-project counts.

Every authored statement and proof body in the original scope was assessed. The complete name/line inventory in the receipt is navigation for the later actual-type inspection, not a substitute for that inspection. **Zero actual XW01 types, zero focused successes and zero full-candidate audit results are credited by this source preparation.** No concrete Spec finding was found; the outcome nevertheless remains **Blocked**.

Completion still requires an exact incorporation candidate with its full original scope preserved, qualified pinned execution, applicable normal/fresh validation, complete closed logs and actual exits, all relevant expanded public statements and generated/private/instance coverage under the project rules, a successful whole-project check and exhaustive permitted-axiom audit, complete independent Standards and Spec final assessments, and immediate matching `--verify-candidate HEAD` before any accepted fast-forward. No source/API inspection relaxes those gates. The live foundation check and its pending 145 types/potential 110 mapping gain no credit from this review; the existing C2 and XP type dispositions are unchanged.

This reviewer performed no compiler, process polling, cache/output, source, ref, pin, ticket, global-control or external-message action. Only this small report and dedicated provenance are written. Existing F, C2 and XP reports remain byte-identical. A separately requested XR primary-source render relocation is packaging work only and does not reopen or alter the XR mathematical assessment.
