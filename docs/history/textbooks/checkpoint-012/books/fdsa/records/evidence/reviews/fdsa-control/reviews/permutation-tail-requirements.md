# Shared conditional remaining-order requirements

Recorded 2026-11-02 before implementation. This is FDSA-XU03, a bounded
cross-cutting unit under the user's explicit exception for shared concerns.
The governing request is `../REQUEST.md`. Chapter 1 remains active; this unit
activates or accepts no chapter. All earlier chapter and shared requirements
remain in force.

## Origin, preparation and baseline

Whole fixed-subset orders from XU02 support one-step pivot conditioning for
the existing Chapter 2 and Chapter 3 obligations. A minimum marginal alone
does not establish a conditional law of the actual remaining list. The
pre-implementation evidence is:

- `../research/permutation-tail-api-preflight.md`, SHA-256
  `4488c46c39a6c3bec7f906079686ae76062b9281f056b3782aea1da4f5feff46`.
- `../research/permutation-tail-source-preflight.md`, SHA-256
  `b81176f85c477674aa73133f567d655038f6d09324adfddb614364dcbd17646e`.
  Its append preserves the original assessment and explains the generic
  observed-law premise, almost-everywhere support and history boundary.
- `../research/permutation-tail-calculations.json`, SHA-256
  `b614ea7eb98b3aaba5c15006a967e1d8da51fc373d5b963c99cdccce6b4632eb`.
  These exact finite calculations are independent expectations, not Lean
  validation.

Use the isolated development worktree `conaled-permutation-tail`, branch
`work/fdsa-permutation-tail`, based on the committed whole-order draft
`4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8`. Record its clean starting state
before source edits. Its dependency chain, including the Chapter 1 repair,
is unvalidated. Share only the unchanged pinned dependency packages; project
build outputs remain separate. Do not change the active old Chapter 1
candidate or its gate, start another compiler while that gate is active, or
alter the toolchain/checker configuration. This unit initially produces an
explicitly uncompiled source draft.

Reuse ordinary functions, lists, finsets, permutations, Mathlib measures,
`ProbabilityTheory.cond`, `Measure.map` and `ProbabilityTheory.HasLaw`.
No new probability carrier, ranking datatype, selector, random executor,
conditional kernel, law record or general probability framework is needed.
Keep operations, observed meaning and probability laws separate. Suggested
modules are `Applications/Probability/PermutationTail.lean`,
`Examples/PermutationTail.lean` and a separate boundary example. Routine
private-helper placement and proof choices may differ from the preflight.

## Observations and deterministic contracts

Use the existing `restrictedOrder positions S π` and `orders positions S`
without changing their inverse-permutation orientation or value meaning.
Define one ordinary event for an arbitrary observation:

`firstEvent (Y : Ω → List I) a := {ω | (Y ω).head? = some a}`.

The event definition needs no decidable equality, measurable structure,
completeness, Nodup, finiteness, order or inhabitedness. Existing finset
filtering retains its own decidable-equality requirement. Use the total
`List.head?` and `List.tail`; introduce no default key or second tail executor.

Establish the exact event identity

`firstEvent Y a ∩ {ω | (Y ω).tail = xs} = {ω | Y ω = a :: xs}`

without distribution or nonempty-list assumptions. Establish cons support:

`a :: xs ∈ orders positions S ↔ xs ∈ orders positions (S.erase a)`

under `positions.Nodup`, `a ∈ positions` and `a ∈ S`; full completeness is
not needed for this deterministic helper. For the actual projection, prove
that on `firstEvent (restrictedOrder positions S) a`, its tail equals
`restrictedOrder positions (S.erase a) π`. This bridge needs Nodup but no
completeness. It is an on-event equality, not a pointwise equality on every
permutation. The previously proved nested-filter law supplies the fixed
remaining-subset value bridge.

## Conditional law under an arbitrary environment

Let `positions` be Nodup and complete (`∀ a, a ∈ positions`), S a fixed
finset, and `a ∈ S`. Write B=`S.erase a` and
`ηS := uniformOn (orders positions S : Set (List I))`.
For arbitrary `{Ω} [MeasurableSpace Ω]`, `{μ : Measure Ω}` and
`{Y : Ω → List I}`, take the existing premise

`hY : HasLaw Y ηS μ`.

Use existing measurable-space and measurable-singleton instances on `List I`.
Completeness supplies finite I and hence countable List I locally. Do not
require finite or discrete Ω, uniformity of μ, a public finite enumeration
of I, a measurable space on I or Option I, an index order, or a nonempty I.
Do not strengthen the `AEMeasurable` field of HasLaw to globally measurable Y.
Source normalization follows from the normalized finite nonempty output
law; no independent probability-measure assumption is necessary.

Prove these three contracts, with the proposed explicit argument order
`positions hnd hcomplete S a ha hY`:

1. `head_mass_of_hasLaw`: `μ (firstEvent Y a) = (S.card : ℝ≥0∞)⁻¹`.
   Membership ensures a positive finite conditioning-event mass.
2. `hasLaw_tail_cond_first`: the actual `fun ω => (Y ω).tail` has law
   `uniformOn (orders positions B)` under `μ[|firstEvent Y a]`.
3. `hasLaw_filter_tail_cond_first`, with subsequent arguments `T hT`,
   where `hT : T ⊆ B`: the actual
   `fun ω => (Y ω).tail.filter (fun b => decide (b ∈ T))`
   has law `uniformOn (orders positions T)` under that same conditioned
   measure. T is fixed outside the environment sample; it may depend on the
   already fixed revealed a and fixed input data.

These are conclusions from the unconditioned whole-order law, not premises
assuming the desired conditional conclusion. Keep Ω, μ and Y inferred from
hY. A private ordinary conditional-map transport helper is sufficient:
`(μ[|Y ⁻¹' H]).map Y = (μ.map Y)[|H]` for AEMeasurable Y and measurable H.
Existing restriction/map/scalar laws prove it, including null events;
absolute continuity preserves a.e. measurability. Existing HasLaw composition
then transports the canonical tail and filter laws. An equivalent sound
proof is acceptable without adding a new interface.

Under a generic HasLaw premise, support and Nodup hold almost everywhere.
Do not infer pointwise support of Y, or literal emptiness of an outsider
event that is only known to have measure zero. Null conditioning is zero,
not a normalized conditional probability law. Successive applications may
retain nested conditioning explicitly. Invoking the existing intersection
identity for successive conditioning requires its measurable-event premises.

## Actual global-permutation specializations

Retain `μ0 := uniformOn (Set.univ : Set (Equiv.Perm I))` and
`O := restrictedOrder positions S`. Use XU02 to establish its actual
observed law, rather than introduce an independently sampled tail.

Under Nodup, completeness and `a ∈ S`, expose the head-event mass and the
universal conditional source-fiber formula, for every xs:

`(μ0[|firstEvent O a]) {π | (O π).tail = xs}
  = if xs ∈ orders positions (S.erase a)
    then (Nat.factorial (S.erase a).card : ℝ≥0∞)⁻¹ else 0`.

These scalar event statements require only measurable-space and
measurable-singleton instances on the permutation sample space. A local
discrete List I instance may be chosen in their proofs; it is not a public
hypothesis. Also expose the corresponding `Measure.map` equality with the
caller's List I measurable/singleton structure, and the conditional law of
the actual `restrictedOrder positions T` for fixed `T ⊆ S.erase a` through
the on-event bridge. Preserve the original complete positions in every
whole-order invocation; a partial tail cannot enumerate all of I.

Record the exact measure identity
`μ0[|firstEvent O a] = uniformOn (firstEvent O a)` using ordinary conditioning
of the finite counting measure. This identity does not need positive-event
membership or Nodup; its finite-source/completeness and measurable-event
requirements should remain separate. It is particular to the original
uniform environment and must not be asserted for arbitrary μ.

The direct proof may sum the old full-output fibers `O π = a :: xs` to
obtain head mass and then condition. Normalize using
`(S.erase a).card + 1 = S.card` and factorial successor. All reciprocal
arithmetic is ENNReal with justified finite/nonzero denominators, including
the singleton case with zero-sized remainder. Repeating global relabeling,
exposing old private machinery, or adding a stabilizer/action framework is
unnecessary. Avoid aliases for every equivalent measure-expression form.

## Connected cases and boundary expectations

Develop these cases alongside the general results and connect them through
the public statements. Ordinary finite reductions may establish concrete
membership/counting premises, but not replace the new generic connections.

Use Fin4, original positions `[0,1,2,3]`, S=`{0,2,3}` and a=0. Retain head
mass 1/3, and the two different actual tails `[2,3]` and `[3,2]`, each of
conditional mass 1/2. Exercise both the public source-fiber formula and the
mapped/HasLaw meaning. Retain an unsupported output with conditional mass
zero. Use the conditional-uniform-environment identity in a concrete
specialization. Exercise the fixed remaining-subset theorem through the
actual filtered tail and its on-event projection bridge; an empty or
singleton proper remaining subset is sufficient alongside the full pair.

For successive reuse let ν be the original law conditioned on first0.
The actual tail Y has uniform order law on `{2,3}` under ν. Instantiate the
generic head-mass theorem again to get next-head-2 probability 1/2, then
instantiate the generic conditional-tail theorem again to obtain the sole
remaining list `[3]` with mass one. Keep the same complete positions and
the actual nested conditional measure. Establish
`ν (firstEvent O 0) = 1` whereas `μ0 (firstEvent O 0) = 1/3`, so the full
environment law has changed. This is a two-step use, not a complete
algorithm-history theorem.

Retain these consequential boundaries:

- First in S differs from first globally. The key-to-label swap of 0 and 1
  has inverse global key list `[1,0,2,3]` and selected list `[0,2,3]`.
  Check this actual pointwise witness rather than identifying the two events.
- S=`{2}`, a=2 has the sole conditional tail `[]` with mass one through the
  new result. Empty S has `head? = none` with mass one under the global law;
  its some-a event is empty and conditioning it is the zero measure. An
  outsider a is likewise a zero-event conditional measure. Include an empty
  index universe without introducing a distinguished key. Do not normalize
  these null events into the nonempty uniform target measure.
- On Fin3, S=`{0,1}`, condition on selected head0 and observe T=`{1,2}`.
  T excludes 0 but is not contained in S.erase0. Its conditional orders
  `[1,2]` and `[2,1]` have masses 1/3 and 2/3. This refutes replacing the
  containment premise by merely excluding the exposed key. The observation
  is the actual original T projection under the same conditioned sample.

## Source limits and acceptance

For C02-024 this supplies a specified-pivot remaining-order law and separate
filtered branch marginals. It does not prove the AFP joint partition law,
sorting recursion, random-input/fresh-choice correspondence or source costs.
For C03-059–077, occurrences remain distinct even with equal payload values;
revealing a value may merge occurrence events. A later history proof must
establish its initial law, identify actual program updates, justify fixed
retained sets and containment, and account for every revealed event. The
selection value/rank/termination, fresh-choice coupling, drift and tail-cost
theorems remain queued. No independence or arbitrary adaptive-subset law is
claimed, and no treap charging or expected-position obligation is discharged.

Review quantifiers, optional-head meaning, actual tail identity, a.e. versus
pointwise support, conditioning positivity, singleton/empty boundaries,
factorial normalization, output measurability, reuse of complete positions,
fixed-subset containment and connections to the actual new public laws.
Use only the allowed project axioms and pinned environment. No admission,
new axiom, unsafe/partial definition or proof-checking bypass is permitted.

Integrate the examples through the public root and document source use and
remaining boundaries. Capture an immutable candidate with these requirements
outside its diff. Focused compilation, applicable full guarded candidate
build and exhaustive audit, both independent final axes and immediate final
candidate verification remain mandatory. Preserve unresolved findings.
Neither a preflight, source draft nor recovery checkpoint supplies acceptance
credit. Integration depends on the repaired Chapter 1 and preceding shared
base acceptance as well as this unit's own matching gates.
