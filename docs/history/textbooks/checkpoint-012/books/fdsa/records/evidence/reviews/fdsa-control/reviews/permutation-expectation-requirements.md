# Shared preceding-count and ordinal-position requirements

Recorded 2026-11-02 before implementation. This is FDSA-XU04, a bounded
cross-cutting unit under the user's exception for shared concerns. The
governing request is `../REQUEST.md`; Chapter 1 remains active and no
chapter is accepted or activated by this unit. Earlier requirements and
source inventories remain unchanged.

## Preparation and baseline

The previously queued fixed-subset expectation is the next finite
observation connection after XU01's minimum law. It supports a later
shared-priority treap estimate without claiming that algorithm's expected
work or conditional charging proof. Inputs frozen before implementation:

- `../research/permutation-expectation-api-preflight.md`, SHA-256
  `5b5bf7b620513cdb0939fd14b25564076258e6a64293849b26fac2b50df03686`.
- `../research/permutation-expectation-source-preflight.md`, SHA-256
  `b6f0245a6b4b0e585a58b6bba2d7303c79ead487675dce16230d0f4906a97a5e`.
  Its append preserves the first assessment and clarifies conditional
  placement and the priority assumptions.
- `../research/finite-ranking-calculations.json`, SHA-256
  `36f853f68d0f0713581aea33e7c91187a003f99bb7386ff5ba509e52964c1949`.
  Reuse its existing exhaustive checks and selected expectations; do not
  rerun that campaign merely because a new unit is starting.
- `../research/permutation-expectation-calculations.json`, SHA-256
  `37c25e61646617234caab34968e7c50f6abedcb4b42164eea802f9e7a89997f8`.
  This adds only bounded arithmetic and specified pointwise cases for the
  conditional-placement, nonidentity-rank, raw-minimum and tie boundaries.

Use isolated worktree `conaled-permutation-expectation`, branch
`work/fdsa-permutation-expectation`, starting at the committed conditional-tail
draft `a0597381f02eddd074ee96cabaa974f2062285f8`. Record its clean starting
state before source edits. Its predecessor drafts, including the Chapter 1
repair, remain unvalidated. Share only the unchanged pinned dependency
packages, with separate project outputs. Do not alter the active old
Chapter 1 candidate/gate, start another compiler while that gate runs, or
change toolchain/checker configuration. The initial result is an explicitly
uncompiled source draft.

Use ordinary finsets, sets/cardinality, permutations, existing Mathlib
measures/integrals and XU01's minimum-event theorem. Suggested core:
`Applications/Probability/PermutationExpectation.lean`. Use connected main
and boundary example modules and concise source-use documentation. No new
ranking type, selector record, probability carrier, sampling executor,
expectation wrapper or general integration framework is justified. Only
the conditional example needs XU02/XU03; the unconditional core can depend
on XU01 and the directly used ordinary cardinality/integration APIs.

## Actual count and deterministic laws

For an index type I, target P with a strict relation, fixed `priority : I → P`,
fixed `S : Finset I` and key-to-label permutation π, define one observation:

`beforeCount priority S π :=
  Set.ncard {b : I | ∀ a ∈ S, priority (π b) < priority (π a)}`.

This ordinary noncomputable Nat-valued operation needs only `[LT P]`.
It needs no finite enumeration, decidable equality, measurable structure,
index order or inhabitance. Its finite-population meaning is used under
`[Finite I]`; retain the standard fact that Set.ncard is zero on infinite
sets, rather than claiming this Nat value counts an infinite set.

Expose `beforeCount_empty priority π = Nat.card I` with only the operation's
assumptions. Expose the sharp pointwise bound

`beforeCount priority S π ≤ Nat.card I - S.card`

under `[Finite I] [Preorder P]`, without injectivity or probability premises.
No member of S can satisfy its own strict self-comparison, so the counted
set is contained in S's complement. Keep this semantic bound separate from
the stronger probability hypotheses. Do not add a public Fintype or
DecidableEq I merely to choose a proof enumeration.

## Expected actual count under the original global law

Under `[Finite I] [LinearOrder P]`, injective priority, and existing
measurable-space/measurable-singleton instances on `Equiv.Perm I`, use the
actual existing `μ0 := uniformOn (Set.univ : Set (Equiv.Perm I))`.
Prove, for every fixed S including empty S:

`(∫⁻ π, (beforeCount priority S π : ℝ≥0∞) ∂μ0)
  = ((Nat.card I - S.card : ℕ) : ℝ≥0∞) / ((S.card + 1 : ℕ) : ℝ≥0∞)`

and

`(∫ π, (beforeCount priority S π : ℝ) ∂μ0)
  = ((Nat.card I - S.card : ℕ) : ℝ) / ((S.card + 1 : ℕ) : ℝ)`.

The numerator subtracts in Nat before casting, with S.card≤Nat.card I
justified when changing to real subtraction. The denominator is a positive
finite successor. Division is in ENNReal/Real, never Nat. The index type
may be empty; its permutation type still contains the identity and the
global law remains normalized. The priority target may be infinite and
requires neither a measurable space nor a measurable priority function.
No public key order, Fintype, DecidableEq, Nonempty I or nonempty S belongs
on these expectation results.

The actual count must be connected pointwise to the finite outsider-indicator
sum. For b∉S, prove that the strict-before event is exactly XU01's
`minimumEvent priority (insert b S) b`. The converse uses injectivity to
rule out a tie with each member of S; membership in S instead makes the
strict-before event impossible. Apply the existing minimum theorem to get
1/(S.card+1) for each outsider, then finite integral linearity and the
complement cardinal. Do not replace the count with an unrelated defined
sum or add an independence premise. The helper event equivalence and sum
mechanics may remain private.

For the real law, justify genuine integrability using the existing finite
sample/finite measure APIs (for example `Integrable.of_finite`), and the
finiteness of the displayed ENNReal answer. Existing `integral_toReal` or
`ofReal_integral_eq_lintegral_ofReal` can transport the mean. Do not use
the totalized value of a nonintegrable real integral as an expectation.
No redundant public integrability wrapper is needed; keep the actual
integrability argument visible in the proof/use.

## Nonempty ordinal bridge and its mean

Supply `rank : I ≃ Fin U` and `hS : S.Nonempty`. The actual assigned-rank
image is `S.image (fun a => rank (π a))`, with nonemptiness from hS.
Expose the pointwise bridge

`beforeCount rank S π =
  ((S.image (fun a => rank (π a))).min'
    (hS.image (fun a => rank (π a)))).val`.

This is equality with the actual finite-image minimum on its proved
nonempty domain. It is not the definition of beforeCount or a default
chosen at an empty set. The composed equivalence maps the strict-before
set onto the initial segment of Fin U below that minimum; existing
cardinality and `Fin.card_Iio` results suffice. Rank itself supplies local
finiteness, so this bridge needs no separate public `[Finite I]` and no
measurable-space hypothesis.

Under the same ordinary permutation sample measurability, prove the real
mean of the actual one-based image-minimum position:

`(∫ π,
  ((((S.image (fun a => rank (π a))).min'
    (hS.image (fun a => rank (π a)))).val + 1 : ℕ) : ℝ) ∂μ0)
  = ((U + 1 : ℕ) : ℝ) / ((S.card + 1 : ℕ) : ℝ)`.

Use the pointwise bridge, genuine finite integrability, the count mean and
normalization. Derive S.card≤U and justify subtraction/cancellation before
the final real algebra. There is no assumed relationship between rank and
the keys' search order. The nonempty premise remains on this ordinal
interpretation; at empty S, count+1 is only a sentinel beyond the universe.
Arbitrary numeric priorities with gaps or translations do not have this
raw minimum-value expectation.

## Coordinated public calls

Use namespace `Applications.Probability.PermutationExpectation` and these
explicit argument orders, with types/universes/instances and U inferred:

- `beforeCount priority S π`.
- `beforeCount_empty priority π`.
- `beforeCount_le priority S π`.
- `lintegral_beforeCount_uniformOn priority hinj S`.
- `integral_beforeCount_uniformOn priority hinj S`.
- `beforeCount_rank_eq rank S hS π`.
- `integral_firstPosition_uniformOn rank S hS`.

The rank bridge is zero-based; congruence under Nat addition by one gives
the corresponding pointwise one-based equality without another alias.
Private helpers and equivalent sound proof choices are routine decisions.
Retain these actual semantics and the minimal structural assumptions.

## Connected cases and independent expectations

Develop the theory and its uses together. Concrete cardinality/arithmetic
calculations must be connected to the new public theorems rather than
independently reproving only their expected values.

### Counts and actual positions

Use Fin3, identity rank and S={0,1}. Connect the count mean 1/3 through both
the ENNReal and real laws, and the actual one-based position mean 4/3
through the ordinal theorem. Exercise the deterministic count bound on
the actual observation. Retain a nonidentity rank equivalence: swapping
labels 0 and 2, with the identity sample and the same S, gives actual
minimum rank 1, beforeCount 1 and one-based position 2. Use the generic
rank bridge for this pointwise connection.

Include the saved Fin4/S={0,3} specialization with count mean 2/3 and
one-based position mean 5/3 through the generic results. A full distribution
theorem is not required by these mean specializations.

### Numeric minimum versus ordinal position

For Fin3/S={0,1}, use the injective Int-valued priority `j ↦ 100 + 10*j.val`.
Its count mean is still 1/3 through the generic theorem with an infinite
priority target. Define the raw observation as the **actual minimum of
S's finite image** under this numeric assignment. Prove that the positive
affine map preserves the minimum and connect it to the rank bridge, giving
raw minimum `100 + 10*beforeCount` pointwise (with the intended casts).
Only then derive the real mean of the raw minimum as 310/3 by justified
integral composition. Compare with ordinal mean 4/3. Merely naming the
affine expression the minimum is not the required value bridge. No general
numeric-priority expectation theorem or extra gappy-priority example is
required.

### Empty, tied and sample-dependent subset boundaries

- Empty S on Fin3 has actual count and mean 3 through the new empty/count
  laws; count+1=4 is a sentinel. Include I=Empty with mean count 0 through
  the generic law and no manufactured key or nonempty minimum.
- A singleton on Fin3 has mean count 1 and actual one-based position mean
  2; this may reuse S={1} in the conditional example below. A full Fin3
  subset has actual count 0 and first-position mean 1. Exercise the bound
  or generic means as appropriate.
- Constant priorities on Fin2 with S={0} have actual strict-before count
  and mean 0, whereas the expression without the required injectivity
  would give 1/2. This proper subset is essential: a full subset would
  conceal the failure. The deterministic bound still applies without
  injectivity.
- On Fin3 let Sπ={π.symm 0}, chosen after sampling under identity rank.
  Its cardinality is always one, but its actual beforeCount is always 0,
  so its mean is 0 rather than the fixed-singleton mean 1. Retain this
  small counterexample to replacing a fixed S by fixed cardinality.

### Same relative-order law, different global-placement mean

Use Fin3 and the actual full-universe order
`O := restrictedOrder [0,1,2] Finset.univ`. Let E be its first-key-0 event
and ν=`μ0[|E]`. For the fixed count subset S={1}, show:

- μ0(E)=1/3 and the actual conditional tails [1,2] and [2,1] have mass
  1/2 through XU03's head/tail results. Use one tail mass plus the proved
  exhaustive on-event value decomposition if that gives a smaller proof.
- The actual count is respectively 1 or 2. Connect its pointwise value on
  E to the new rank bridge; equivalently use `1 +` the indicator of tail
  [2,1]. Lift the on-event identity to ν-a.e. equality and integrate using
  genuine finite-sample integrability and the proved probability measure.
- Its mean under ν is 3/2, while the new global-law mean under μ0 is 1.
- The actual singleton-relative-order observation has the same existing
  HasLaw under both measures. Establish this through XU02's actual map
  and XU03's conditional same-sample projection map with T={1}.

This bounded counterexample distinguishes placement from the order within
S. A restricted-order HasLaw alone cannot replace the global-uniform
premise of the new mean. Keep the original sample and conditioned measure;
introduce no independent draw or generic conditional expectation framework.

## Source limits and acceptance

The fixed-set positional estimate supports one part of the Chapter 10
shared-priority treap argument after its canonical root/minimum bridge.
For operand sets A,B with |B|≤|A|=s>0 and universe A∪B, the formula entails
the expected one-based root position is below 2. It does not supply actual
treap work, conditional depth, Jensen's hypotheses, adaptive histories,
rank-cluster continuation or the correlated weighted-charging argument.
C10-117 remains open. A bound on E[d] does not factor E[dZ]. Overlapping
operands remain coupled by one global ranking. No quicksort/selection
algorithm correspondence or cost bound follows from the scalar mean.

Review the actual counted set, strict/non-strict equivalence, insert
membership, fixed-S quantifier order, finite versus totalized cardinality,
empty-index normalization, actual integrability, Nat subtraction/casts,
nonempty rank minimum, zero/one-based distinction and conditional-placement
counterexample. Keep the global law and all actual observations explicit.
Use only allowed project axioms and the pinned environment; no admission,
new axiom, unsafe/partial definition or proof-checking bypass is permitted.

Integrate examples through the public root and document source boundaries.
Capture an immutable candidate with these requirements outside its diff.
Focused compilation, the applicable full guarded candidate build/exhaustive
audit, both independent final axes and immediate candidate verification
remain mandatory. Preserve all findings and matching input identities.
No preflight, uncompiled draft or durability checkpoint closes a formal
acceptance gate. Integration also depends on acceptance of the repaired
Chapter 1 and preceding shared base.
