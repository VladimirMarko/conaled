# XW01 independent Standards source preparation — 2026-11-04

## Current disposition

**Blocked — complete original source preparation, with zero actual compiler/type credit.** I independently assessed the entire six-path change from `a14977b9e316cc484ffad8a470d26b15615956c0` to `7c6bc92c276d39e84351324c442869b8ffa6758c`, against the complete frozen FDSA-XW01 requirements. **No concrete mathematical, architecture or source-coverage Standards finding was identified.** Ordinary elaboration issues remain possible: this original candidate is uncompiled, its actual expanded types have not been read, and all full acceptance gates remain open.

The exact Foundation continuation retains priority when root supplies terminal evidence. Earlier Foundation, Chapter 2, XP01 and XR01 reports and the XR provenance remain byte-identical. Their acceptance states and statement counts are unchanged. Historical references to the originally unaccepted Chapter 1 repair describe the original branch; they do not invalidate the later accepted Chapter 1 state or authorize incorporation of this old draft without reconciliation.

## Exact scope and completed reading

The candidate has the fixed base as its sole parent. The complete delta is six paths, 837 added lines; all 1,351 lines / 63,345 bytes of the resulting scoped files were read independently.

| Path | Lines | SHA-256 |
| --- | ---: | --- |
| `Applications/Probability/AccumulatedWork.lean` | 157 | `7731f8a6c5222810ba11a056fc620c68a152dce0024ff3e2544d17fff70a80ba` |
| `Examples/AccumulatedWork.lean` | 299 | `7ef773d2ce87ce1b119838e083ee4a4cff072f5d96f4a8887f8494a80d04c20c` |
| `Examples/AccumulatedWorkBoundary.lean` | 219 | `68ba8fd9571ad860d7f5aabd7093f35c0220ff12ead1e283e903b5bdc90a6927` |
| `SquareApplications.lean` | 253 | `40d97b7972ba8085c076c6482cc99f130f8e92beeea3f5c0b5fc8e040e4727dd` |
| `docs/research/fdsa-accumulated-work.md` | 145 | `191a7c449f936b84c17f3f5d33a935dd4440a199fc7287e576dfd38f4fbaca8e` |
| `docs/research/fdsa-reconstruction-map.md` | 278 | `35c5cf425168b21900c84735020df5b6a6b9ba86c099ad4d2c555821858a7024` |

The core (157 lines), main client (299), boundary client (219), dedicated note (145) and public root (253) were read in full. The full reconstruction map was read in contiguous ranges 1–145 and 146–278. The existing-file diff adds one root import and the sixteen-line accumulated-work map section; the four new files were assessed as complete additions. The main client imports the boundary client, and the public root imports the main client. Thus the entire boundary module, including the noncontracting formal counterexample, is in the intended public check/audit scope.

The frozen requirements are 160 lines / 9,206 bytes, SHA-256 `85c651891cf8c8ee016706bf8baad7711dbd9965eb20ad5c6e96d2ab112728e1`. I read the complete ticket, 122-line candidate handoff, 264-line author draft preflight, 380-line probability API preflight, 578-line coordinated source preflight and 167-line calculation record. The historical author preflight expressly excluded the boundary file; this independent review does not retain that exclusion. An initially truncated aggregate display of that preflight was superseded by complete bounded reads of lines 1–132 and 133–264 before credit was recorded.

The instructions and ten configuration/checker files were compared byte-for-byte with the already-reviewed XR candidate, with no differences. Previously completed applicable AGENTS, implementation/review-loop, code-review, architecture, domain, language, ADR, glossary and example-driven readings therefore remain applicable. The source retains official Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and the same eight additional pins. The Nix waiver does not waive any pin, proof restriction, immutable-check, independent-review or immediate-verification gate.

Exact source/control identities, read ranges, names, authored headers, configuration and API receipts are in this review's dedicated provenance. Author/root/Spec reports are aids; none supplies independent source or actual-type credit.

## Core statements and minimal assumptions

The core supplies six ordinary theorems over one arbitrary `μ : Measure Ω`, with `[MeasurableSpace Ω]` and a universe-polymorphic `Ω`. Observations are `X : Nat → Ω → ℝ≥0∞`. Their nonnegativity is intrinsic. The statements add no probability normalization, finite-measure or sigma-finite premise, no independence or Markov-property premise, and no `Fintype`, `Countable`, `Inhabited` or equality capability on the sample carrier. Countability of the natural time index is distinct from countability of `Ω`.

| Public core theorem | Source statement and argument assessed |
| --- | --- |
| `lintegral_le_geometric` | From the initial actual lower-integral bound and a one-step inequality under that same measure, derive every `E_t ≤ q^t*N` by natural induction. No measurability, strict contraction or finite-value premise is inserted. |
| `lintegral_tsum_shift_le` | Almost-everywhere measurability of each observation permits interchange with the actual shifted countable sum. The preceding public mean bound provides termwise domination; existing ENNReal geometric and scaling laws give `q^w*N/(1-q)`. |
| `lintegral_tsum_le` | The zero-shift specialization is the actual total sum, including zero initial bound and zero drift factor. |
| `lintegral_tsum_lt_top` | Strict contraction makes `1-q` nonzero; finite `N` then makes the integral bound finite. It does not add `N≠0` or `q>0`. |
| `measure_tsum_ge_le` | One supplied AE prefix cap, positive finite `N` and `q<1` imply the mass bound for the actual **non-strict** total-work threshold. All finite/positive cancellation conditions are proved. |
| `measure_tsum_ge_le_of_stage_le` | An AE cap for each stage derives the one-prefix premise by finite summation. The weaker single-prefix contract remains available; the all-times cap is confined to this corollary. |

The drift premise is one-step information about the supplied observations. It neither assumes the target accumulated-work bound nor certifies an algorithm's conditional sampling law. A common joint distribution must be supplied by each later consumer; equal marginal means do not identify that law.

### Extended values and zero boundaries

The code stays in ENNReal throughout the analytic argument. Countable sums, lower integrals, multiplication and division retain infinity; there is no `toReal` conversion or totalized real integral concealing nonintegrability. Mathlib's ENNReal `Summable` result means convergence in the extended topology and does not assert a finite total. The unconditional geometric identity remains valid for `q≥1`; the bound can then be infinite. When `N=0`, the relevant zero/infinity arithmetic is retained rather than divided away.

No proof divides by `q`. Thus `q=0` remains valid, including `q^0=1` and zero positive powers. Finiteness is obtained exactly where `q<1` and `N≠∞` are supplied. Finite accumulated integral is not presented as finite-step termination: a sequence may have vanishing or summable stage work while continuing indefinitely.

### Prefix decomposition and the non-strict tail

Write `P_w` for the actual first `w` observations, `R_w` for the actual shifted sum, `C=w*N`, and `B=N/(1-q)`. The source proves `B>0`, `B≠∞` and `C≠∞` before cancellation. The denominator is nonzero from strict contraction and is finite because it is a subtraction from one. The numerator's nonzero/finite hypotheses give the corresponding threshold properties.

On the full-measure set where `P_w≤C`, the actual infinite-sum decomposition is `P_w+R_w=W`. If `C+B≤W`, then `C+B≤P_w+R_w≤C+R_w`; finite left-addition cancellation yields `B≤R_w`. This establishes the correct event inclusion almost everywhere. The proof then applies the AE form of measure monotonicity, division-form Markov to the AE-measurable remaining sum, the independently derived shifted integral bound, and cancellation of the positive finite `B` to obtain `μ{C+B≤W}≤q^w`.

I checked the inclusion direction, equality at the threshold, the finite cap used in addition cancellation, and both side conditions used in multiplicative/division cancellation. The source does not strengthen the premise to everywhere bounds or require all prefixes. The stage-cap corollary uses countable-time `ae_all_iff` to form one common full-measure set and then sums only the chosen finite prefix.

## Pinned APIs and existing interfaces

The following exact dependency contexts were independently read at the Mathlib pin and matched against immutable blobs: lower-integral countable interchange and affine linearity; ENNReal geometric series, unconditional summability and multiplication of sums; the generated primed natural prefix/tail theorem; generated `AEMeasurable.tsum`; arbitrary-measure Markov; `measure_mono_ae`; uniform-on-universe normalization/cardinality formulas; finite singleton-mass integration; finite addition cancellation, division positivity/finiteness/monotonicity and positive finite multiplicative cancellation. The ledger records only the bounded excerpts actually read, rather than claiming whole-file coverage.

The primed prefix decomposition is generated from the monoid theorem `Multipliable.prod_mul_tprod_nat_mul'`, so its additive specialization applies to ENNReal without an additive group. The unprimed group-valued route is not substituted. The codomain capabilities behind `AEMeasurable.tsum` specialize to ENNReal; they do not impose a Polish or countable structure on `Ω`.

The old `Mathlib.Data.ENNReal` paths are five-line deprecated shims at this pin. A read-only lookup followed those imports to the actual `Mathlib.Basic.ENNReal` definitions before assessing the relevant signatures. This was source discovery, not an observed compiler error. In particular, the NNReal-to-ENNReal division coercion requires a nonzero denominator; source-level numeric proof patterns remain subject to actual elaboration and are not credited as checked by this API reading.

The complete unchanged `Resources.Measured`, `Workload` and `CallCount` modules were read. `bind` feeds the returned value into its continuation and adds actual observations; `run` sequences these transitions; `reweight` changes the observation while retaining the value; `tick` adds exactly one. Bounded unchanged Table/kernel/execution contexts confirm the documentation's existing semantic boundary. The new core does not import finite sampling, kernel construction or resource execution merely to carry its analytic statements.

## Connected measured clients

### One environment, actual execution and independent observations

The main example uses the standard uniform measure on `Fin 8`. Its probability-measure instance is tied to that concrete law. The four stages share the same `ω`; they are not four independent draws. Stage zero always records zero and charges one. Stages one, two and three are active respectively at `ω.val<4`, `<2` and `<1`, prepend their actual indices and charge one; inactive stages preserve the list and contribute zero. The ordinary `Resources.run` executes stages `[0,1,2,3]` in order.

| Environment | Ordered returned value | Actual measured cost |
| --- | --- | ---: |
| 0 | `[3,2,1,0]` | 4 |
| 1 | `[2,1,0]` | 3 |
| 2 or 3 | `[1,0]` | 2 |
| 4–7 | `[0]` | 1 |

I independently checked these values and costs, including the reversed index order caused by prepending. `program_value` and `program_cost` are separate claims. `observation` casts the actual stage charge and becomes zero after stage three. The sum-to-cost bridge first reduces the actual countable sum to its finite support and then identifies the measured run's cost. The desired sum is not assigned as a fabricated observation of an unrelated extensional function.

The stage means are `1,1/2,1/4,1/8`, and the total mean is `(4+3+2+2+1+1+1+1)/8=15/8`. The initial bound and integrated drift are established from those actual finite-law observations. The upper bound two and finite-integral result invoke the generic theorems through the actual sum-to-cost bridge. The two private finite-uniform helpers are included in the full source assessment; their general `Fin n` identities do not assert normalization of `Fin 0`.

After the always-present first stage, residual costs are `3,2,1,1,0,0,0,0`, with mean `7/8`. The natural subtraction by one cannot underflow in this actual program. The source proves the complete shifted-sum equality for every environment, and its upper bound one invokes the positive-shift generic theorem.

The non-strict threshold-three event is exactly environments zero and one, with mass `1/4`; the generic theorem supplies its upper bound `1/2`. The event is nonempty. The first two nonconstant active events have masses `1/2` and `1/4`, intersection mass `1/4`, and marginal product `1/8`. Their explicit mismatch retains the dependent common environment; no independence inference enters the generic bound.

### Actual affine composition

`affineProgram` reweights the completed observation by two, then uses ordinary `bind` for an explicit final charge of three while preserving the returned list. Its actual observation is `2*cost+3`, producing costs `11,9,7,7,5,5,5,5` and mean `27/4`. The upper bound seven follows from lower-integral linearity and the generic-derived bound two, rather than merely weakening the exact enumeration. The probability instance for the concrete law justifies integrating the added constant as three.

The threshold-nine event is proved equal to the original threshold-three event. Both its exact mass `1/4` and its generic upper bound `1/2` transfer through that equality. Condition tests and environment selection remain outside this example's explicit tariff, as disclosed in the source and note; no physical runtime or complete randomized-algorithm claim follows.

## Consequential boundary clients

| Boundary | Complete source assessment |
| --- | --- |
| Zero drift | Actual `bind`/`tick` composition evaluates the initial value four once, passes it into the two-entry body, returns seven and observes three entries. Its observation is three at stage zero and zero later; generic total/finite/tail results admit `q=0`. |
| Zero versus positive shift | At `w=0`, the non-strict work-three event has full mass and the bound is `0^0=1`. For positive `w`, the higher threshold is impossible and the generic zero bound forces zero mass. |
| Zero initial bound | Zero observations supply valid zero initial/drift premises and the generic total integral equals zero with `N=0`. On the same probability space, the zero-threshold non-strict event has mass one, exceeding `(1/2)^1`; the tail's positive-N condition is substantive. |
| Missing prefix | Under uniform `Fin 3`, actual observations are work three at one outcome, zero at the other two, and zero at every later time. Initial mean one and zero drift hold, but threshold-two mass is `1/3>0`. The omitted-prefix tail is false. The source then applies the actual public tail theorem to show that the required AE prefix cap cannot hold. |
| Missing contraction | Constant unit observations under the Unit Dirac law satisfy the initial/one-step shape at `q=1`, yet have infinite accumulated sum and integral. The extended-valued public bound still applies with zero denominator; no finite conclusion is claimed. |

These are mathematical boundaries of the precise statements. The rare-work contradiction retains the actual event, actual uniform mass and original drift law. The formal constant-work counterexample is included through the same public import path as the rest of the unit. None is relegated to unchecked commentary or removed to make a proof easier.

## Complete declaration and instance accounting

| Module | Explicit public names | Public definitions | Public theorems | Private named helpers | Anonymous instances |
| --- | ---: | ---: | ---: | ---: | ---: |
| Analytic core | 6 | 0 | 6 | 0 | 0 |
| Main client | 35 | 6 | 29 | 2 | 1 |
| Boundary client | 37 | 5 | 32 | 0 | 0 |
| Total | **78** | **11** | **67** | **2** | **1** |

The source therefore has 81 authored declarations when both private helpers and the anonymous instance are included. The anonymous instance has authored type `IsProbabilityMeasure law`, for `Examples.AccumulatedWork.law`; it is not silently folded into the 78 explicit names or omitted from the review. Its generated declaration name and actual type have not been established by a compiler run. There are no anonymous `example` commands. Generated equation/recursion/elaboration auxiliaries remain part of the eventual exhaustive audit.

The exact public/private names, source locations and authored headers are preserved in `source-preparation.json`. This is source accounting only: **actual XW expanded types read = zero**. No F/C2/XP/XR count or potential reuse disposition is changed.

## Findings, remaining scope and acceptance boundary

There are **zero concrete Standards source findings** in this preparation. The frozen requirements' non-strict comparator, common-law interpretation, minimal measurability, finite/positive threshold conditions, actual measured clients and all requested consequential boundaries remain intact. No assumptions, observations, expected values, proof restrictions or validation gates were changed.

The documentation accurately keeps conditional uniform pivots/history, source selection scan-volume correspondence and tariff conversion as later algorithm-specific work. Quicksort must account for both recursive branches; this single-sequence drift theorem cannot certify its whole work. Treap shared priorities and conditional weighted charging remain separate. Uniform ranking combinatorics is not retroactively counted as implemented by this unit. The original branch's general reconstruction-map context must be reconciled with later accepted/reviewed mapping changes on incorporation; this source assessment does not overwrite those later fixes or reopen their records.

Actual focused compilation, complete expanded-type review, the applicable whole-candidate integrity check and exhaustive proof audit, both independent final axes, and immediate verification of the exact approved candidate remain mandatory. Source/configuration identity and API reading give no object-authenticity or compiler-result credit. Normal-versus-fresh acceptance rules remain unchanged; this preparation does not demand a new fresh run without an applicable trigger.

No compiler, process, generated output, cache, source or ref action was performed. The central outputs remain retired/unusable and were not consumed or snapshotted. The only writes are this small new report and its own provenance. All protected earlier reports and XR receipts were hash-checked before and after these writes. On completion, this review is held for checkpoint0103; Foundation terminal evidence remains the next priority if supplied.
