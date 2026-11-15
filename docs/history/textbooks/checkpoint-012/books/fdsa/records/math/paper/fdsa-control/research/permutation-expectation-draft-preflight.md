# Preceding-count expectation draft: bounded source assessment

Recorded 2026-11-02 by the retained `tail_examples_preflight` contributor.
**No source-level finding was identified in the inspected XU04 draft.**
This is a bounded statement, proof-route and API assessment within the
existing book implementation loop. It is not a final Standards or Spec
gate, compiler result, axiom audit or acceptance decision.

## Candidate, requirements and inspected identities

Root reported that the stopped source files were committed without further
changes as candidate `11923e9ffd17246b6f22c5594002a1ba0434e43c`, with parent
`a0597381f02eddd074ee96cabaa974f2062285f8`, and that the worktree is clean.
That Git identity is the coordinator's supplied record; this contributor
did not run Git. The checkout is `conaled-permutation-expectation`.

The frozen requirements were read in full:
`../reviews/permutation-expectation-requirements.md`, 14,497 bytes, SHA-256
`926fddbeb2d20b45842416b90ba96c78dbeaa84064d5d135cf3bb5b2d620624a`.
Ordinary SHA-256 file reads established these source identities:

| File relative to the checkout | Bytes | SHA-256 |
|---|---:|---|
| `Applications/Probability/PermutationExpectation.lean` | 12,849 | `a322a016ea767d0a1f294cac5f709c20bc7e41d0e1e4f05d2aa2eb9ebc1c1cf9` |
| `Examples/PermutationExpectation.lean` | 8,255 | `5f89da2fb3dc77e886532708962eccdf7fc93cbdbaaaf0ef5fe486f231f7a037` |
| `Examples/PermutationExpectationBoundary.lean` | 14,682 | `e5547ba32b5f786c221a5f2259282452c17e05b86eacc9808d5d490a5f62b333` |
| `docs/research/fdsa-permutation-expectation.md` | 9,278 | `9a835956f4f914f9a76e50975458b01d90597e09ceebf606ed9349bbb18ecabe` |
| `docs/research/fdsa-reconstruction-map.md` | 20,131 | `bf1f4f5dd009da181a1cfbcf94dc52ebbbdde3a564b24cf000b6c477f049d0d1` |
| `SquareApplications.lean` | 8,431 | `2a537090f1bb7c625897e5206c20ac4753afc6d722733950a667645082c9a71e` |

The three Lean modules and the new expectation document were read in full.
Assessment of the reconstruction map was limited to its new **Shared
preceding-count and ordinal-position means (draft)** section. Assessment of
the public root was limited to the new `Examples.PermutationExpectation`
import. Full-file hashes identify the surrounding inputs without claiming
to review every older declaration or paragraph again.

The current AGENTS file was read. Architectural-quality, example-driven,
domain/glossary and ADR 0001/0010 guidance already read in this continuing
assignment was retained. No additional implementation/review loop was
started. The bounded independent expectations in
`permutation-expectation-calculations.json` were read; the earlier exhaustive
permutation/subset campaign was not rerun.

## Actual count, structural assumptions and fixed global law

`beforeCount` is the required ordinary `Set.ncard` of the strict-before
predicate on the actual key-to-label permutation. It is not defined as an
unrelated indicator sum or as a minimum selected by a default. Its only
structural parameter is `[LT P]`; the definition has no public finiteness,
enumeration, index equality, index order, measurability or inhabitance
assumption. Both its docstring and the source-use document explicitly retain
the standard zero value of `Set.ncard` for infinite sets.

`beforeCount_empty` exposes the vacuous predicate as the whole index type,
giving `Nat.card I` with the same weak assumptions. `beforeCount_le` adds
finite I and a preorder, then proves containment in the complement of S:
a member of S would have to precede itself strictly. The complement-cardinal
calculation is separate from the stronger injective-priority mean. Ties do
not invalidate this structural bound.

The lower-integral theorem retains the exact fixed-S quantifier and the
original uniform measure on all permutations. Its private event lemma is
used only for b outside S. Forward strict comparisons give the minimum
event on `insert b S`; reverse non-strict comparisons become strict because
injectivity of priority and of the permutation rules out equality with a
member of S. The inserted b itself satisfies its required self-comparison
non-strictly. This is the correct bridge to XU01's existing minimum theorem.

The private sum bridge first identifies the actual counted set with the
filtered complement finset and then casts its cardinality into ENNReal.
It connects that cardinality to a finite sum of actual event indicators.
Finite integral linearity and the old minimum law give one reciprocal
`S.card + 1` contribution per outsider. No independence assertion is used.
The complement cardinal yields the intended Nat subtraction before casting.

The successor denominator is nonzero and finite. Empty S and empty I remain
covered: an empty selected set counts all keys, while an empty index type
still has its identity permutation and a normalized global law. The public
mean laws impose no nonempty subset/index premise, public Fintype or
DecidableEq I, or measurable structure on the priority target. Local
classical finite enumeration stays inside the proofs.

## Real integrability and the actual ordinal bridge

`integral_beforeCount_uniformOn` explicitly obtains
`Integrable (fun π => (beforeCount priority S π : ℝ)) μ₀` using the finite
sample and finite measure. It consumes that witness in
`ofReal_integral_eq_lintegral_ofReal`, with a separate nonnegativity witness.
The displayed ENNReal ratio is proved finite before the `toReal` transport.
Thus the real formula does not depend on the totalized value of a
nonintegrable integral.

`beforeCount_rank_eq` uses the actual nonempty image
`S.image (fun a => rank (π a))` and its `min'`. The composed equivalence
`π.trans rank` maps the counted set bijectively to the Fin U initial segment
below that minimum. The resulting `Fin.card_Iio` value is its zero-based
rank. The image minimum is not defined to be beforeCount, and there is no
empty-set default. The statement needs no separate finite-I, measurable or
index-order hypothesis; the supplied equivalence already supplies the
finite population.

`integral_firstPosition_uniformOn` observes that same actual minimum with
Nat addition by one before the real cast. It uses the pointwise bridge,
finite integrability and the normalized global measure. It explicitly
derives S.card≤U before rewriting natural subtraction as real subtraction,
and justifies the positive real successor denominator before cancellation.
There is no zero/one-based shift error or natural-division mean. The
nonempty premise remains attached to the ordinal interpretation.

## Main examples and their public theorem connections

| Case | Connection and assessment |
|---|---|
| Fin3, S={0,1}, identity rank | Both ENNReal and real count means 1/3 use the new mean laws; the actual finite-image first position has mean 4/3 through the ordinal theorem. The actual count also uses the structural bound. |
| Nonidentity rank swapping 0 and 2 | At the identity sample the actual image ranks are {2,1}. The generic bridge gives minimum/count 1 and one-based position 2. Nonmonotonicity in key order is retained. |
| Fin4, S={0,3} | The count mean 2/3 and actual first-position mean 5/3 use the generic laws. No unnecessary full distribution theorem is claimed. |
| Int-valued priority 100+10*j.val | Its injectivity supplies the generic count mean despite the infinite priority target. Monotonicity is used only for the numeric minimum bridge, not added to the general mean assumptions. |
| Actual numeric minimum | `rawMinimum` is defined as the minimum of the numeric image. `Finset.min'_image` and the rank bridge then prove equality with 100+10*beforeCount pointwise. Explicit finite integrability justifies affine integral composition and mean 310/3, which is compared with ordinal mean 4/3. |

The raw-minimum bridge is substantive: the selected finite numeric image is
present in the definition, and the positive affine map's minimum-preserving
property is proved before integration. The independent expectation 310/3
has not been obtained merely by naming an affine expression the minimum.

## Boundary examples and conditional placement

The boundary module keeps all required consequential cases connected:

- Empty S on Fin3 has actual count and mean 3 through the empty/count laws;
  count+1=4 remains a sentinel. Empty I uses the generic count mean to get 0,
  with explicit normalization of its permutation measure and no manufactured
  selected key or minimum.
- A fixed singleton has count mean 1 and actual one-based first-position
  mean 2. The full Fin3 subset has count 0 through the structural bound and
  first-position mean 1 through the ordinal theorem.
- Constant priorities on Fin2 with proper selected subset {0} give an
  identically zero strict-before count and mean. The unchanged structural
  bound is exercised; the formula without injectivity would instead give
  1/2. The proper subset prevents the counterexample from degenerating into
  a full-set zero on both sides.
- The sampled singleton `{π.symm 0}` has cardinality one but actual count
  zero through the pointwise rank bridge. Its mean differs from the fixed
  singleton's mean. The fixed-S mean theorem is not misapplied to this
  sample-dependent argument.

For the conditional-placement example, `globalOrder` is the actual full
inverse-permutation observation, `firstZero` is its first-key-0 event, and
`afterZero` is the original measure conditioned on that event. XU03's head
theorem gives mass 1/3, which is used to establish that `afterZero` is a
probability measure. Both conditional tail masses 1/2 come from XU03's
universal source-fiber result.

The exhaustive on-event list decomposition is obtained from the public
whole-order support theorem and a finite supported-order table. Applying
key-to-label π back to the inverse global order recovers positions. This
determines π(1) as rank 1 in order `[0,1,2]` and rank 2 in `[0,2,1]`.
`singleton_count_eq`, itself a specialization of the new rank bridge,
then supplies the actual count. The source therefore connects the count
to the actual conditional observation with the correct inverse orientation.

The count identity is asserted only on `firstZero` and lifted to
`afterZero`-almost-everywhere equality. The conditional count, constant and
indicator each have explicit finite integrability witnesses. Integration
uses the conditional tail mass to give 3/2. The original mean 1 separately
uses the new global-uniform theorem. This is a real same-sample change of
measure, not a pair of unrelated newly defined draws.

Finally the actual singleton-relative-order function has the same HasLaw
under both measures. The original HasLaw uses XU02's map theorem, and the
conditional HasLaw uses XU03's same-sample projection map with the explicit
containment `{1} ⊆ univ.erase 0`. Hence the claimed counterexample has both
required parts: equal observed relative-order laws and unequal global
placement means. It correctly rejects replacing the new mean's original
global-uniform premise by that restricted-order HasLaw alone.

## Focused pinned API checks

Only concrete uncertainties in the inspected proof routes were checked in
the existing Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`:

- `Data/Set/Card.lean`: the supplied finite upper-set witness matches
  `ncard_le_ncard`; the complement, finset coercion and injective-preimage
  cardinality statements have the directions and premises used by the core.
- `Algebra/BigOperators/Group/Finset/Indicator.lean`: the displayed
  `prod_mulIndicator_eq_prod_filter` generates the additive
  `sum_indicator_eq_sum_filter` with the four explicit arguments used in
  the count-to-sum proof.
- `Data/Finset/Max.lean`: the dual-generated `lt_min'_iff` and
  `min'_image` have the asserted universal-comparison and monotone-image
  meanings. The numeric example supplies the image-nonempty premise expected
  by `min'_image`.
- `MeasureTheory/Integral/Lebesgue/Add.lean`: `lintegral_finsetSum` takes
  the measurable summands supplied from the finite sample space.
- `MeasureTheory/Function/L1Space/Integrable.lean`:
  `Integrable.of_finite` requires finite source, measurable singletons and a
  finite measure. The generic original law provides these, and the changed
  conditional law is explicitly normalized before its uses.
- `MeasureTheory/Integral/Bochner/Basic.lean`, `Basic/ENNReal/Basic.lean`
  and `Basic/ENNReal/Inv.lean`: the integrability/nonnegativity transport,
  finite `toReal` equality, denominator condition for `div_ne_top`, and
  `toReal_div` match the actual proof arguments.
- `MeasureTheory/Integral/Bochner/Set.lean`: `integral_indicator_one`
  returns `μ.real s`; the boundary proof explicitly rewrites this to the
  `toReal` measure value before using the conditional tail mass.

No readily identifiable API mismatch was found. These source signatures do
not establish that imports, implicit-instance inference, casts, proof-term
unification, tactics or all declarations elaborate in the completed build.
No elaborated types or compiled output were inspected.

## Documentation, integration and remaining limits

The document and new reconstruction-map section match the inspected actual
count, strict/non-strict event bridge, integrability, image minimum and
conditional example. They consistently distinguish numeric priority values
from ordinal positions, and fixed subsets from merely fixed cardinalities.
They state the totalized infinite-set cardinality convention and retain
empty/nonempty boundaries. They claim no algorithm acceptance.

The Chapter 10 use is qualified by the still-unproved canonical treap
root/minimum correspondence and the fixed operand-set assumptions. The
elementary below-2 positional consequence is consistent with U≤2s and s>0.
Conditional depth, Jensen, adaptive histories, actual work and C10-117's
correlated weighted charging remain explicitly open. A scalar bound on E[d]
is not used to factor E[dZ].

The public root imports the new main example; that module imports its
boundary module and core. The unconditional core imports XU01 and ordinary
cardinality/integration APIs, while the boundary module supplies the
XU02/XU03 conditional uses. This matches the frozen module separation.
This source inspection is not the project's import-coverage check.

**No XU04-SP finding is opened by this bounded assessment.** No requirement
or independent expected value was changed, and no final review finding is
closed. Only this report was written. No compiler, Git, project hash helper,
active gate, cache, configuration, repository source, tracker or requirements
were changed. No exhaustive calculation or external research campaign was
performed. Focused compilation, the complete guarded candidate build and
exhaustive audit, both independent final review axes and immediate candidate
verification remain outstanding, as do the predecessor acceptance gates.
