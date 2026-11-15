# FDSA-XU04 — independent Spec source preparation

## Current disposition and fixed scope

**Blocked for approval.** This is the independent Spec source preparation for original candidate `11923e9ffd17246b6f22c5594002a1ba0434e43c`, whose sole parent and fixed review base is `a0597381f02eddd074ee96cabaa974f2062285f8`. The whole original six-path scope is retained. No new concrete Spec finding was identified in that complete source assessment. **Zero actual printed types, compiler results, full checks or audits are credited to this candidate.** Source assessment is not approval, and the later Chapter 2 dependency validations do not apply automatically to these older inputs.

Reviewer: `/root/chapter02_spec`, an independent nonauthor. This continues the existing whole-book review loop; it does not activate Chapter 10 or replace any earlier unit's review. Foundation terminal review remains the priority when its actual secured evidence is supplied. The parent released only this new report/provenance write scope after checkpoint 0104; all existing Foundation, Chapter 2, XP01, XR01 and XW01 review records remain byte-identical.

The frozen requirements are `reviews/permutation-expectation-requirements.md`, all 272 lines, SHA-256 `926fddbeb2d20b45842416b90ba96c78dbeaa84064d5d135cf3bb5b2d620624a`. All ticket, start, candidate and three preflight records and both saved calculation files were read completely. The calculation files aid independent expectations; they are not Lean validation evidence. Exact source, control, API and declaration inventories are in `provenance/permutation-expectation-spec-preparation-20261104/source-assessment.json`.

| Original changed path | Complete read | SHA-256 |
|---|---:|---|
| `Applications/Probability/PermutationExpectation.lean` | 273 lines | `a322a016ea767d0a1f294cac5f709c20bc7e41d0e1e4f05d2aa2eb9ebc1c1cf9` |
| `Examples/PermutationExpectation.lean` | 191 lines | `5f89da2fb3dc77e886532708962eccdf7fc93cbdbaaaf0ef5fe486f231f7a037` |
| `Examples/PermutationExpectationBoundary.lean` | 332 lines | `e5547ba32b5f786c221a5f2259282452c17e05b86eacc9808d5d490a5f62b333` |
| `SquareApplications.lean` | 256 lines | `2a537090f1bb7c625897e5206c20ac4753afc6d722733950a667645082c9a71e` |
| `docs/research/fdsa-permutation-expectation.md` | 184 lines | `9a835956f4f914f9a76e50975458b01d90597e09ceebf606ed9349bbb18ecabe` |
| `docs/research/fdsa-reconstruction-map.md` | 332 lines | `bf1f4f5dd009da181a1cfbcf94dc52ebbbdde3a564b24cf000b6c477f049d0d1` |

The exact base-to-candidate diff contains only these six paths, with 1,001 insertions and no deletions. All complete files, including the whole root and reconstruction map, were read; the root/map diff was also read. The new root import reaches the Main examples, which import Boundary and core. Core imports the existing minimum layer and ordinary pinned Mathlib, while Boundary reaches the existing order/tail layers. There is no hidden chapter implementation in this original diff.

## Governing rules and input identities

All 15 applicable governing blobs at this candidate match the previously completely assessed instruction/source identities: `AGENTS.md`, implementation, review-loop, code-review and heuristics, example-driven development and its worked example, architecture/domain/glossary, ADR index/0001/0010, language direction and README. The README's complete earlier read is retained, with the independently reread normal-versus-fresh rules at lines 161–248. A focused build is not a complete candidate check and audit. A fresh check is required only when the actual README trigger applies; losing a workspace does not revoke the recorded accepted Chapter 1 baseline.

The immutable `lean-toolchain` SHA-256 is `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`, `lake-manifest.json` is `dff886ff5836eedead6c53293f8cb6de0653ed9f1e2d63d9bfeb6ed983e8ca4b`, and `lakefile.toml` is `76966dfb4ea744d75d4bbe20ed3a6c576a17145d23f36ba44c4422673c51b04f`. The relevant library source was read at Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. These are source identities, not a runtime or generated-output qualification. A read-only optional lookup found that this candidate has no `lakefile.lean`; its actual configuration is the recorded TOML file. No compiler was invoked by this reviewer.

## Frozen requirement correspondence

| Frozen requirements | Complete source assessment |
|---|---|
| Preparation and baseline, lines 9–49 | Original fixed candidate/base, six paths, old dependency inputs and strict options retained; no transferred compile/type evidence. |
| Actual count and deterministic laws, lines 50–74 | Core `beforeCount`, `beforeCount_empty`, `beforeCount_le`, and the strict-precedence predicate under their stated weak assumptions. |
| Original global-law expectation, lines 75–116 | Both ENNReal and real count integrals, fixed subset outside the sample binder, injective priority map, finite actual sample space, and finite/integrable real conversion. |
| Nonempty ordinal bridge and mean, lines 117–150 | Actual `Finset.min'` order statistic under arbitrary full-rank equivalence; explicit subset nonemptiness; one-based position and its real expectation. |
| Coordinated public calls, lines 151–168 | Main and Boundary use the same public count/rank/mean results, not disconnected numeric claims. |
| Counts and actual positions, lines 169–188 | Three- and four-element means, nonidentity nonmonotone rank assignment, singleton and full-set cases. |
| Numeric minimum versus ordinal position, lines 189–202 | An actual minimum in an infinite priority type, a proved affine bridge to the public count, and a distinct raw-value mean. |
| Empty, tied and adaptive boundaries, lines 203–221 | Empty subset, empty index type, ties without injectivity, and a sample-dependent singleton with constant size. |
| Same relative order, changed global placement, lines 222–244 | One original permutation law and its actual conditional measure; supported full-order argument, actual count expectation, and both singleton-order pushforward laws. |
| Source limits and acceptance, lines 245–272 | Original-law/fixed-subset scope, Chapter 10 representation/work obligations and conditional-history limits preserved; actual types and all final gates remain pending. |

## Core statements, hypotheses and proof connections

`beforeCount` (core lines 43–45) is the `Set.ncard` of the actual strict-precedence set: an index `b` is counted precisely when its sampled priority is strictly less than every selected sampled priority. The definition requires only `LT P`; it does not assume a finite priority target, measurable priority values, an inhabited index type or a global decidable equality. Its extension to an infinite index type follows `Set.ncard`'s documented zero-at-infinity convention, rather than silently asserting finite cardinality. The requested stochastic statements separately require a finite index type.

`beforeCount_empty` (48–50) uses the vacuous predicate and states `Nat.card I`. `beforeCount_le` (54–66) adds `Finite I` and a preorder, proving that the counted set is contained in the selected set's complement: a selected index cannot strictly precede itself. The resulting bound is `Nat.card I - S.card`. Priority injectivity is unnecessary here, and the tied-priority example preserves that distinction.

The private event bridge (68–86) identifies the event for an unselected `b` with the existing minimum event on `insert b S`. The reverse direction uses priority injectivity to turn non-strict minimum comparison into strict comparison against each selected index, excluding equality with `b`. The second private lemma (88–112) converts the actual counted set into a sum of indicators over the complement. It does not replace the observable by a separately defined count with the desired mean.

`lintegral_beforeCount_uniformOn` (116–151) quantifies the fixed priority and fixed `S` before integrating over the original uniform permutation measure. Its public assumptions are `Finite I`, `LinearOrder P`, the permutation sample's measurable space and measurable singletons, plus injectivity of the priority map. The proof creates finite enumerations locally, uses finite-domain measurability, sums the actual event indicators, and applies the minimum-event probability to `insert b S`. Each unselected index contributes `1 / (S.card + 1)`, giving `(Nat.card I - S.card) / (S.card + 1)` in ENNReal. There is no nonempty-subset or nonempty-index assumption in this count theorem, and no independence assumption between the indicators.

`integral_beforeCount_uniformOn` (155–186) has the same mathematical premises and gives the quotient in real arithmetic. The proof supplies `Integrable.of_finite` for the actual count under the finite uniform measure, supplies nonnegativity, converts through the corresponding lintegral, and discharges the finite positive-denominator conditions before applying `toReal`. This avoids treating the totalized real integral of a nonintegrable observable as an expectation. The numerator is the cast of the natural complement size; the final division is not natural-number division.

`beforeCount_rank_eq` (190–221) takes an arbitrary equivalence `rank : I ≃ Fin U`, a fixed selected set and `hS : S.Nonempty`. The right side is the actual value of the minimum of `S.image (rank ∘ π)`. The proof uses the bijection `π.trans rank` to identify the counted set with the preimage of the strict initial interval below that minimum, then uses the interval cardinality. It requires no key-order monotonicity of `rank`, no probability structure and no separately supplied finite enumeration. The nonempty proof belongs to the actual `min'` expression; there is no default element posing as a minimum.

`integral_firstPosition_uniformOn` (225–271) integrates that actual minimum value plus one, cast to the reals, under the original global law. It obtains finite cardinality from the rank equivalence, uses the pointwise bridge, proves integrability and normalizes the constant-one integral, then converts the count formula to `(U + 1) / (S.card + 1)`. The proof explicitly uses `S.card ≤ U` before natural subtraction/casting. The empty-subset count-plus-one expression is handled elsewhere as a sentinel, not as an instance of this nonempty minimum theorem.

The pinned API reads cover the actual `Set.ncard` conventions and finite complement/preimage lemmas, generated additive indicator-sum theorem, `Finset.min'`/`lt_min'_iff`/monotone-image minimum, `Fin.card_Iio`, finite integrability, finite indicator lintegrals, real integral addition/constant multiplication, nonnegative real-to-ENNReal conversion, finite `toReal` equality, conditional AE restriction and uniform-law normalization. Exact partial read ranges, including surrounding namespace/typeclass contexts, are recorded in the receipt. These are source-contract assessments, not printed elaborated types.

## Connected cases and independently assessed values

| Case and actual observable | Assessed result and connection |
|---|---|
| `Fin 3`, selected `{0,1}`, identity rank | Count bound 1, count mean `1/3` in both ENNReal and real form, and actual first-position mean `4/3`, by public results. |
| Same selected set, rank swapping 0 and 2, identity sample | Rank is explicitly not monotone in key order; actual count is 1 and one-based minimum position is 2. The public rank bridge, not a monotonicity assumption, connects them. |
| `Fin 4`, selected `{0,3}` | Actual count mean `2/3` and first-position mean `5/3`, via the same public formulas. |
| Integer priority `100 + 10*j.val` on `Fin 3` | Priority injective into infinite `Int`; actual count mean `1/3`. The actual numeric minimum is proved equal to `100 + 10*beforeCount`, giving real mean `310/3`, which differs from ordinal mean `4/3`. |
| Empty selected set in `Fin 3` | Actual count and count mean 3; count-plus-one sentinel 4. No nonempty minimum is asserted. |
| Empty index type | The permutation sample still has its identity permutation and normalized uniform measure; actual count and mean are 0. No fabricated selected key or rank minimum is introduced. |
| Singleton `{1}` in `Fin 3` | Pointwise actual count equals `(π 1).val`; count mean 1 and first-position mean 2. |
| Full subset in `Fin 3` | Actual count 0 from the deterministic bound; actual first-position mean 1. |
| Constant tied priority in `Fin 2`, proper singleton | Actual count and mean 0 while the injective formula would give `1/2`; the deterministic complement bound still holds. This exposes the expectation theorem's injectivity premise. |
| Adaptive subset `{π.symm 0}` in `Fin 3` | Cardinality is constantly 1, but its sampled minimum rank is always 0, so actual count and mean are 0 instead of the fixed-singleton mean 1. Fixed cardinality cannot replace a fixed subset. |
| Fixed singleton `{1}` after observing global first key 0 | Actual count mean changes from 1 to `3/2`, while its relative-order pushforward remains uniform on the singleton order under both measures. This is a same-environment counterexample to transferring global-placement means. |

The raw numeric minimum is explicitly defined by `Finset.min'` of the sampled priority image (Main lines 146–148). Its affine identity (150–162) uses monotonicity of this particular integer map and the image minimum theorem; that monotonicity is an example-specific bridge, not a new premise of the general count/ordinal results. Its real mean (164–184) uses integrability of the actual finite-domain count and the actual affine identity, so it is not a standalone arithmetic equality disconnected from the algorithmic observable.

### Conditional environment example

Boundary lines 181–332 retain one actual global-order random variable, formed by restricting the inverse-permutation order of `[0,1,2]` to the full index set. `firstZero` is its actual first-event set. The original law gives this event mass `1/3`; `afterZero` is exactly the original measure conditioned on that event, with positivity used to establish its probability instance. The two remaining actual tails `[1,2]` and `[2,1]` each have conditional mass `1/2` from the existing tail theorem.

The private supported-order enumeration and public `global_order_of_first_zero` rule out unsupported full orders. Mapping the global order through the same sampled permutation recovers the fixed positions. This connects the two supported orders to the actual value of the fixed-singleton preceding count, giving the on-event identity `count = 1 + indicator(tail21)`. The AE conditional restriction lemma transports that identity to the actual conditional measure. Explicit integrability, integral congruence, addition and the tail event's real measure yield the actual conditional mean `3/2` (lines 272–300).

Finally, `singletonOrder` is the actual restricted order of the fixed singleton under the same sampled permutation. Its value is `[1]` and its pushforward law is proved under both the original and conditional measures, using the existing order/tail public interfaces. The example therefore exhibits equal relative-order laws with unequal means of a different global-placement observable. It neither introduces an independent resampling nor concludes that a conditional global ranking is again uniformly distributed.

## Primary source correspondence and retained limits

The pinned book text was read at literal-newline lines 5178–5310, including the Chapter 10 notes around printed pages 124–125. Its complete-file SHA-256 is `7e5c0b4e157d28d303cc6248746aa63e1415445fa79f3556ff95ac1bf6b17333`. The precise relevant obligation records were read at `research/chapter10-obligations.md` lines 450–487, covering C10-112–118 and their source limits. Neither range is described here as a fresh read of the entire book or entire chapter inventory.

The book notes attribute the join-based approach and its generalization to balancing schemes, including treaps, and the work bound involving `m log(n/m + 1)`. They do not themselves state every fixed-subset order-statistic identity implemented in this shared unit. The more specific root-rank argument is retained through the fully read pinned source preflight's attributed inspection of the Blelloch source, page 7:25, SHA-256 `c39df24da9ffdd1027777c26a8ef0330d73e8f8b2282c5accb4c090b2b0f3057`, DOI `10.1145/3512769`. No new complete reading or rebuild of that external paper is claimed. It is not a Lean dependency.

The mathematical bridge has the appropriate fixed-before-sampling structure: fix a nonempty `A` and a fixed `B` before drawing one ranking on `A ∪ B`; with `s = |A|` and `|B| ≤ s`, the universe size is at most `2s`, so `(U + 1)/(s + 1) ≤ (2s + 1)/(s + 1) < 2`. Applying this to actual treap roots still requires the canonical representation/root-as-minimum bridge. This source preparation does not discharge that later implementation obligation.

The public note and added map section preserve C10-117's expected-work status, actual join/split recurrence and tariff obligations, correlations from shared keys or overlapping sets, and the need for conditional depth/Jensen arguments before charging adaptive histories. A bound on an expected depth does not factor a correlated weighted expectation. XU04 is not an algorithm cost theorem, an independence theorem, a conditional-global-uniformity theorem, a treap implementation, or a parallel-span result. No later chapter is marked accepted by this source review.

## Exact inherited dependency boundary

The following complete old dependency sources were independently read at this XU04 candidate, together with their complete source diffs to reviewed Chapter 2 development `4b5dbfa07288acc73f25c27838d3fb2f78e77d71`:

| Input | Old XU04 SHA-256 | Read | Difference requiring explicit incorporation/validation accounting |
|---|---|---:|---|
| `Applications/Probability/PermutationMinimum.lean` | `648a2d799ea9905a27992ad4e8653ad21a0457c5301e8c0a026d08d9cd067bbb` | All 197 lines | Later C2 changes three ordinary local definitions from `letI` to `let`; the old bytes remain here. |
| `Applications/Probability/PermutationOrder.lean` | `b427902814c19d269c850c97cb43728034d03df2539c5e357ce7ce715191298f` | All 319 lines | Later C2 clarifies one intended Sublist header explicitly and repairs local instances, scoped assumptions, finite-index binders, composition and conditional simplification. |
| `Applications/Probability/PermutationTail.lean` | `1093b94886936b4cb859a371a863bfcf0b388db90a3bc063018329a399fe6f33` | All 485 lines | Later C2 repairs filter/cons simplification, local definitions and explicit conditional-tail proof steps. |

The old minimum event still describes a minimum on the selected sampled priorities under the original global permutation measure. The order layer's inverse-permutation orientation matches the count interpretation, and its supported order/fiber laws concern the actual restricted order. The tail layer conditions that same original measure on an actual first event, and the mapped remaining-subset result keeps its subset-of-remaining premise. These original mathematical contracts support the intended XU04 argument by source assessment.

None of the three whole input files is byte-identical to its later C2 source. Therefore the later focused passes or actual-type inspections are not credited to this original candidate. The Order header repair is a source-level preservation of the intended sublist proposition; there is no claim that the older unelaborated expression had a verified equivalent elaborated type. These are already known inherited correction inputs, not new mathematical findings against XU04 and not permission to edit source in this review. A future incorporated successor must retain the whole frozen XU04 scope and explicitly account for its corrected inputs and actual validation.

## Complete authored declaration accounting

| Module | Public theorems | Public definitions | Named local instances | Private named theorems | Anonymous local instances | Anonymous examples |
|---|---:|---:|---:|---:|---:|---:|
| Core | 6 | 1 | 0 | 2 | 0 | 0 |
| Main examples | 18 | 11 | 0 | 0 | 2 | 0 |
| Boundary examples | 29 | 14 | 2 | 10 | 8 | 0 |
| Total | 53 | 26 | 2 | 12 | 10 | 0 |

Thus there are **81 explicit public named declarations**, including the two named local probability instances, plus the separately accounted private and anonymous surfaces. The receipt lists every authored name, kind, exact source line and source-header hash. It handles the same-line `@[simp]` attribute on `beforeCount_empty` and distinguishes anonymous local instances from named public declarations. Private names are authored source labels, not guessed private kernel names. This is an authored-source inventory, not an enumeration of generated kernel declarations and not an actual-type inspection.

All 81 public names must be accounted for in the eventual explicit statement-inspection surface, with private/anonymous proofs remaining in source, compilation and full-audit scope. The two named local instances are `Examples.PermutationExpectationBoundary.original_isProbabilityMeasure` and `Examples.PermutationExpectationBoundary.afterZero_isProbabilityMeasure`; their probability claims are part of the conditional-example semantics. No current count is added to C2's 1,763-name disposition or Foundation's still-pending 145-name inspection.

## Findings, remaining gates and actions

**New concrete Spec findings: none in the completed original source scope.** The source and documentation make the critical finite, nonempty, injectivity, fixed-subset and original-law boundaries explicit. Known inherited API corrections remain recorded above without duplicate finding IDs or transferred acceptance evidence. This does not establish that the uncompiled source elaborates: finite `decide` reductions, casts, local instance placement and pinned tactic/API elaboration still require actual compiler evidence.

Approval remains Blocked pending the exact incorporated candidate's qualified compilation and complete actual public-type inspection, applicable full normal/fresh check and exhaustive audit, complete terminal logs and immutable input/verification records, and both independent final review axes. Immediate `./check.sh --verify-candidate HEAD` remains mandatory immediately before any accepted local fast-forward. Full audit proof restrictions and the allowed axiom policy are unchanged. The accepted Chapter 1 state is preserved; no failure or success is inferred from the still-live Foundation execution.

Only this new report and its small dedicated Spec provenance were written. No source, reference, output, pin, cache, ticket, global control, build process or external service was changed or inspected for runtime state. No new render, enumerative experiment, compiler invocation or process poll was performed. Complete report/receipt readback is recorded separately in the current-boundary receipt after the actual bounded reads; source-read credit is retained for all ranges identified above.
