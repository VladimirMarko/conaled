# Uniform input mean: source-author repair 2

## Role, boundary, and actual evidence

This is a bounded source-author correction in the existing Chapter 2 loop, not
an independent Chapter 2 review. My separate independent foundation Standards
continuation remains held with outcome **Blocked**. I did not author or modify
foundation F. The completed foundation addendum is separate from this record.

The author worktree began clean at
`aa89aeccf7e06cd046b4f3c5c430631d4ea73b5b`, on
`work/fdsa-ch02-uniform-input`. It retains the complete original uniform-input
scope from `9d5dcd2cfbd6fc5df572234a85bf4957d0c32a21` over prepared prefix
`204dba90967f11a2dfe186316bc85a29acbcc576`, including all repair-1 corrections.
The coordinator reports the old core bytes as identical to central candidate
`5398db774ed5ca9938d0562e379d757323e7a355`. I verified the author file against its
recorded SHA-256 before editing; I did not inspect or mutate central outputs.

The complete emitted diagnostic block was read: **2,136 bytes, 37 lines, two
error headers**, SHA-256
`427fcc34e2ba86f0958ab30c91a1d526f19fbe977b18275f672a4aee2bab1d2d`.
Its capture records a fixed 34,903-byte prefix of the still-growing focused-7
log, SHA-256
`5297eb78c9f17c50c31a65802fe47ac8f267def6a167eab47d9a116752409659`.
The snapshot supplies actual diagnostics, **not an aggregate terminal result**.
No execution session was polled. No compiler, Lake, build, cache, or candidate
output command was run by this author.

`diagnostics.txt` and `diagnostic-capture.json` are exact local copies. Complete
pre-edit core and examples are saved as `before-core.lean` and
`before-examples.lean`. `source.diff` preserves the complete proposed change.

## U-ELAB-025: conditional integral linearity

### Actual failure and correction

At the original core location 298:6, `rw [integral_add ...]` failed to match the
integral of the actual pointwise child-cost sum. The generated rewrite pattern
retained unresolved child-set metavariables inside function addition. The goal
already contained the exact left-child observation, exact right-child
observation, and exact real-valued source toll under the same conditional
measure.

The correction supplies the functions explicitly:

```lean
f := fun π => observedCost positions lt (leftChild lt S a) π +
  observedCost positions lt (rightChild lt S a) π
g := fun _ => ((4 * (S.card - 1) + 3 : Nat) : ℝ)
```

Both calls to `integrable_observedCost_cond` now name the actual child sets.
Their `Integrable.add` proof is used for precisely the displayed pointwise
sum. The second integral split likewise names those same sets. This does not
change the measure, an observation, the source tariff, or any public definition.

I read the exact pinned `MeasureTheory.integral_add` and `integral_add'`
definitions in `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`, and the
`Integrable.add` definition in
`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`. The former accepts
explicit functions and integrability proofs; the latter returns integrability
of their pointwise function sum. Both source-file identities and the pinned
Mathlib commit are recorded in `author-start.json`. There is no invented API or
new integrability assumption.

### Complete affected statement assessment

The unchanged written theorem is:

```lean
theorem conditional_mean (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (lt : I → I → Bool)
    (S : Finset I) (a : I) (ha : a ∈ S) :
    (∫ π, observedCost positions lt S π ∂
      (uniformOn (Set.univ : Set (Equiv.Perm I)))[|
        firstEvent (restrictedOrder positions S) a]) =
      meanBy positions lt (leftChild lt S a) +
        meanBy positions lt (rightChild lt S a) +
          ((4 * (S.card - 1) + 3 : Nat) : ℝ)
```

The unchanged section context requires decidable equality on labels and the
measurable-space/singleton instances for their permutations. It does not impose
a label order, default label, global finite-type parameter, ordered comparator,
distinct keys, or payload equality. The complete finite environment is supplied
by the existing `positions` hypotheses. The selected head membership guarantees
a nonempty selected set and a positive finite event mass; no division through a
zero event is introduced.

The observation remains the real cast of the existing measured two-filter
quicksort exercise-cost coordinate on the actual restricted order. The same
sampled permutation supplies the revealed head and both recursive filtered
tails. The proof first uses the actual event equation almost everywhere,
then conditional integrability and integral linearity, then each child's
already-proved conditional marginal equality. Linearity does not require
independence, and no independence premise or joint-law assertion appears.

The toll remains `4 * (S.card - 1) + 3`, with subtraction in `Nat` before the
cast. The child expectations include the empty-input source cost of 1. This is
an exact exercise-cost statement; it neither charges payload lookup nor claims
the same exact formula for append-inclusive literal work.

I reread the relevant actual-event, integrability, positive-event,
`child_integral_cond`, head-partition, `first_integral`, and
`meanBy_recurrence` source connections. Those sources and their assumptions are
unchanged. The full corrected `conditional_mean` proof was read back in bounded
untruncated output. The explicit functions remove the observed matching
ambiguity without changing the requested mathematics. Corrected elaboration is
still pending the coordinator's compiler run.

## U-ELAB-026: arithmetic proof sequencing

### Actual failure and correction

At the original core location 578:31, the unused-tactic linter rejected the
all-goals operator in `field_simp [hnR] <;> ring`. The correction retains both
tactics as ordinary sequential steps:

```lean
field_simp [hnR]
ring
```

No linter setting or validation gate was relaxed. There is no new branch,
arithmetic lemma, additional hypothesis, or altered expression.

### Complete affected statement assessment

The unchanged written theorem is:

```lean
theorem meanBy_eq_closedForm (positions : List I) (hnd : positions.Nodup)
    (hcomplete : ∀ b, b ∈ positions) (key : I → κ)
    (S : Finset I) (hinj : Set.InjOn key (S : Set I)) :
    meanBy positions (fun x y => decide (key x < key y)) S =
      QuickSortMean.closedForm S.card
```

The unchanged section context adds a linear order on the independently
universe-polymorphic key type; it still does not order labels or demand global
injectivity of their key function. `hinj` is restricted to the selected set and
is inherited by each actual child. The outside-key-collision example remains
usable. No default element or payload equality instance is introduced.

The full corrected proof was read back. It still performs strong induction on
selected-set cardinality inside the fixed label environment. The empty case
uses the actual empty expectation and numerical zero-cardinality formula. In
the positive case, the previously proved actual integral recurrence supplies
both child expectations; the strictly smaller child-cardinality facts and
inherited local injectivity justify the induction calls. The key-rank sum law
then converts those actual child cardinalities to the finite numerical sum.

Only the final positive-cardinality arithmetic step changes tactic sequencing.
`hnR` still justifies denominator clearing; the preceding cast argument still
proves the source natural-number toll equals `4 * (n : ℝ) - 1` when `n > 0`.
The numerical closed-expression recurrence is applied only after deriving this
equation from the execution. No execution recurrence is assumed, and there is
no fictitious global-size process inside one fixed finite environment.

The actual input wrapper, occurrence-preserving transport, distinct-key
requirement, arbitrary-payload theorem, and Nat-indexed family Big-O bridge are
unchanged. Their source connections were reread along with the unchanged
append-inclusive inequality bridge. There is no new exact harmonic formula for
the literal cost. Corrected elaboration remains pending.

## Retained consequential cases and scope

I reread the entire unchanged 352-line examples file in two bounded outputs.
Its bytes, all 57 declarations, and all independent expected conclusions remain
unchanged. In particular:

| Connected case | Retained expectation and purpose |
| --- | --- |
| Empty labels, arbitrary empty input, arbitrary singleton | Actual source costs 1, 1, and 5; no invented zero base tariff. |
| Arbitrary comparator on two inputs | Either orientation costs 13, connected to actual execution. |
| Three selected labels in a larger environment | Actual conditional costs 25, 21, 25; each head mass 1/3; extreme union mass 2/3. |
| `three_mean_from_heads` | Uses the corrected `conditional_mean` and the actual partition recurrence with the independently calculated event costs, giving 71/3. |
| `three_mean_from_closedForm` | Uses the corrected `meanBy_eq_closedForm` separately and also gives 71/3. |
| Deliberate outside key collision | Refutes global key injectivity while preserving injectivity on the selected subset. |
| Empty child at either extreme | Actual filtered input is empty and its conditional expectation is 1. |
| Arbitrary payload occurrence and tagged-three cases | Preserve permutation/length and give 71/3 without payload equality or ordering assumptions. |
| Distinct tagged records with equal sort keys | Actual quadratic family `2*n^2 + 2*n + 1`; at three inputs, 25 differs from 71/3. |
| Tagged range of arbitrary payloads | Genuine growing length-n family, exact numerical mean, and proved Big-O. |
| Scalar and literal bounds | Constants 32 and 64 respectively, with the required `n ≥ 2` premises. |
| Zero/one logarithmic boundaries | Refute an all-length multiple-of-`n*log₂(n)` bound when the positive source cost remains. |

The original complete five-stage scope and 125-declaration author assessment
remain in force. All 68 core and 57 example declaration headers and order were
matched against the prior inventory. All definitions, local instances, section
variables, `omit` scopes, imports, options, and example bytes are unchanged.
The static comparison removes only the bodies of `conditional_mean` and
`meanBy_eq_closedForm`, then establishes exact equality of the entire remaining
core text. This is source identity evidence, not a substitute for kernel
checking or actual elaborated-type inspection.

The full prior 125-claim source assessment is retained for unchanged content.
An initial oversized display of an old inventory object was truncated; it is
not represented as a new complete raw inventory reading. The complete 125-name
summary, affected theorem bodies, relevant source dependencies/consumers, full
two-error diagnostic block, complete diff, and all example lines were read in
bounded untruncated outputs. `source-inventory.json` preserves every unchanged
written header and records the two changed proof bodies explicitly.

## Disposition and handoff

No new mathematical source or statement finding arose. U-ELAB-025 and
U-ELAB-026 have proposed source corrections with complete affected author
assessment; their actual compiler resolution is pending. The historical
U-ELAB-001 through U-ELAB-024 records and all first-repair changes remain intact.
No earlier failed or partial run is relabeled successful.

`git diff --check` completed with actual exit 0. The only source diff is in
`Applications/Resources/UniformQuickSortMean.lean`; the examples are
byte-identical. No mathematical test, compiler, build, audit, final type
inspection, or independent C2 review was run in this author worktree. All
required immutable-candidate validation, complete elaborated-type assessment,
both independent review axes, and immediate acceptance verification remain
outstanding.

The local scoped commit and its exact identities are recorded separately in
the receipt. Root should integrate only this one-file successor while
preserving newer central dependencies, then validate the actual immutable
integrated candidate. This author returns to HOLD after the handoff.
