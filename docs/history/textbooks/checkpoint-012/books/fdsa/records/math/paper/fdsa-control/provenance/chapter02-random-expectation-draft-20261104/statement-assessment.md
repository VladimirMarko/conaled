# Random quicksort means: complete source and per-claim assessment

Date: 2026-11-04. Exact draft candidate:
`7b1851cee7fe580a4fe235740b0c07e4ddd8fc58`, parent
`0ec9954479b081664bd4504c90fb66fba5fd22c8`.
**Source assessment only: these new files have not been compiled, audited,
or subjected to elaborated-type readback or either independent review axis.**
No acceptance or obligation closure is claimed.

## Identity, scope and readback

Root reviewed the complete bounded expectation plan with zero design findings
and released exactly the two new files. The old author branch was clean at
`bb4fb243bb7b16ae8bef921fec479a86f2b01c90`; ancestry was verified before the
exact fast-forward to `0ec9954479b081664bd4504c90fb66fba5fd22c8`.
The start record preserves that actual operation, output, final clean state,
and unchanged initial random sources, deterministic dependency and pins.

The commit adds only `Applications/Resources/RandomQuickSortMean.lean`
(334 lines, 16,480 bytes) and `Examples/RandomQuickSortMean.lean`
(118 lines, 5,733 bytes). Every line and proof body of both final files was
read back. There are 22 public resource declarations, 10 public examples,
and 15 private proof helpers. The complete source inventory is adjacent.
The held worktree is clean, and it has no `.lake` directory.

Source hashes:

- Resource: `41d81697ef917d32f6946b05b7381882838e67e8f4be9408a1b218633cea04d2`.
- Examples: `a00248d8ecb10c425c1376e39ceccd77b6a1c468b952ef838f0494624bc26670`.
- Complete saved diff: 23,105 bytes, SHA-256
  `4159b746c268bba22a59bc3df447d850eac8f3e7ca7d90db117bb63be6d65100`.

Git's staged whitespace check closed exit 0. This is not a Lean check.
Both files retain `autoImplicit false` and `warningAsError true`. Source
inspection found no prohibited placeholder, axiom, unsafe/native proof
escape, suppressed linter, or changed execution profile. No builder, cache
operation, external mutation, or acceptance integration was performed here.

## Public resource contracts: all 22 declarations

All general statements use arbitrary `α : Type u`, `lt : α → α → Bool`,
and the actual input `xs`. No payload equality, inhabitation, finite carrier,
countability, measurable space, order, distinctness, supplied sampler,
independence or numerical mean-recurrence premise is introduced. The two
all-false mean formulas state their input-local comparison hypothesis
explicitly. The following are source statements awaiting elaboration.

| Public name(s) | Contract assessed |
| --- | --- |
| `exerciseMean`, `literalMean` | Ordinary real integrals of the existing actual Nat cost projections under their `PMF.toMeasure`; no separate probability law or cost recursion. |
| `exerciseLaw_lintegral_le` | Actual lower expectation bounded by the finite cast of `2*n^2+2*n+1`, with n the actual list length. |
| `literalLaw_lintegral_le` | Actual lower expectation bounded by the cast of `(5*n^2+9*n+2)/2`, with the division performed in Nat first. |
| `exerciseLaw_lintegral_ne_top`, `literalLaw_lintegral_ne_top` | Explicit finite lower-integral conclusions derived from those actual support bounds. |
| `exerciseLaw_integrable`, `literalLaw_integrable` | Genuine `Integrable (fun k : Nat => (k : Real))` under each actual projected measure. They use finite lower integrals and measurable Nat observations. |
| `exerciseMean_eq_toReal_lintegral`, `literalMean_eq_toReal_lintegral` | Actual real means identified with lower-integral `toReal`; preceding independent integrability contracts prevent treating this identity alone as finiteness evidence. |
| `exerciseMean_nonneg`, `literalMean_nonneg` | Nonnegative real means of nonnegative Nat observations. |
| `exerciseMean_le`, `literalMean_le` | The actual real means inherit the finite natural bounds, including the literal bound's natural floor division. |
| `exerciseMean_nil`, `literalMean_nil` | Both actual empty-input means are 1; no empty pivot average is formed. |
| `exerciseMean_singleton`, `literalMean_singleton` | Actual singleton means are 5 and 8 for every payload and Boolean comparator. |
| `exerciseMean_cons` | The actual nonempty mean is the uniform average of the means of its actual indexed-removal/filter children, plus `4*tail.length+3`. Index, selected pivot, remainder and both child filters remain explicit in the statement. No size-only recurrence is assumed. |
| `literalMean_comparison` | `exerciseMean ≤ literalMean ≤ 2*exerciseMean`, transported through weighted observations of the same actual run. |
| `exerciseMean_of_all_false`, `literalMean_of_all_false` | Under `∀ a ∈ xs, ∀ b ∈ xs, lt a b = false`, actual means are the real casts of `2*n^2+2*n+1` and `2*n^2+5*n+1`. |

## Private proof chain and consequential checks

The private weighted bind lemma expands `PMF.bind_apply`, commutes the
nonnegative sums, and factors the weights using the exact pinned ENNReal
sum APIs. The pure/map/add/constant specializations do not request a measure
on arbitrary payload values. Weighted support monotonicity explicitly treats
zero-weight results separately. The Nat lower-integral identity uses the
existing countable-integral/singleton-measure APIs.

The lower-expectation bound follows from the actual public support bound,
not from termination alone or an invented finite carrier. It is established
before the real integrability contracts. The generic `integral_nat_eq`
identity is valid even for an arbitrary Nat PMF with infinite expectation;
its source comment explicitly warns that the identity alone is insufficient.
For the actual cost laws, the separate finite lower bounds and `Integrable`
proofs are present and do not depend on the later mean recurrence.

The private two-child calculation integrates two supplied PMFs and the pure
returned cost expression. Its actual application uses `exerciseLaw_cons`,
which is already derived from the original measured run. The selected pivot
is a valid occurrence index; `List.length_eraseIdx_add_one` is applied with
an explicit actual-list result type to identify the remainder length.
The real equation supplies finite child means, finite sums and finite weights
before `ENNReal.toReal_add` and `toReal_sum`. No real sum interchange relies
on an absent integrability argument, and no priority or conditional-uniform
input hypothesis is added.

The append-inclusive comparison first rewrites both lower means as weighted
observations over `run lt xs`. Supported observations use the checked
`literalCost_comparison`; unsupported observations have zero weight.
Only after this common-run comparison are the finite lower inequalities
transported to Real. This preserves the actual coupling and avoids comparing
integrals under two unrelated marginal measures.

The all-false formulas map the existing actual joint cost law by the first
projection and by the sum of both coordinates. They therefore retain tagged
duplicate behavior even when output ordering changes. Their polynomial
algebra does not stand in for an execution correspondence.

Production imports stay within the actual resource module and the inspected
lower/real-integral and ENNReal arithmetic APIs. `PMF.Integrals` is imported
only by the new examples, where its finite-integral theorem is actually used.
No XW/XU draft, new generic mean record, stochastic table, or replacement
executor is imported. Ordinary `let` bindings are used; there is no `letI`
compatibility workaround or disabled linter.

## Public example contracts: all 10 declarations

| Public example | Fixed expectation and actual-law connection |
| --- | --- |
| `empty_uninhabited_means` | Both means 1 for `Empty` payloads and an empty input. |
| `singleton_means` | Means 5 and 8 for arbitrary-universe payloads and arbitrary comparator. |
| `two_key_exercise_mean` | Actual `[0,1]` exercise mean 13, using the checked pure exercise law. |
| `two_key_literal_mean` | Actual `[0,1]` total costs 19/20 with masses 1/2 each, derived by projecting the checked two-run law; actual mean 39/2. |
| `three_key_exercise_mean` | Integrates the checked actual three-key 21/25 law, with weights 1/3 and 2/3; actual mean 71/3. |
| `constant_key_payload_means` | Arbitrary tag lists with key 7 retain both exact quadratic mean formulas, without instances on the tag type. |
| `two_equal_key_tag_means` | Distinct Boolean tags sharing key 7 have actual means 13 and 19. |
| `all_equal_three_means` | The checked actual pure three-equal-key run gives means 25 and 34. |
| `arbitrary_payload_integrable` | Clients both real integrability contracts at arbitrary payload universes. |
| `arbitrary_payload_mean_comparison` | Clients the actual two-mean comparison without a coupling premise. |

The sole private example helper transports an actual PMF map from `Fin n`
to Nat through `PMF.toMeasure_map` and `integral_map`, then applies the existing
`PMF.integral_eq_sum` on the finite **index** carrier. It never applies that
finite-carrier theorem directly to Nat. The inspected pinned theorem
signatures and measure-map direction were used explicitly.

These expected constants were fixed in the reviewed plan before the new proof
scripts were written. The original cost-law examples remain unchanged. The
new three-key mean does not assert an unproved exact literal mean or a general
harmonic law from numerical agreement.

## Outcome and remaining gates

No concrete mathematical contract mismatch was found during this complete
author source assessment. Proof elaboration and linter outcomes remain
unknown until root's exclusive central check; no successful compiler result
for this new source is claimed. Exact elaborated types, including all
universes and inferred assumptions, still need readback after a pass.

The distinct-key occurrence/rank bijection, inherited key distinctness,
actual size recurrence, connected harmonic formula, logarithmic/Big-O bounds,
separate uniform-input first-pivot mean, and selection/removal work remain
mandatory later work. The actual observations still exclude random-bit and
physical runtime claims. All frozen Chapter 2 requirements and 112 obligations
remain unchanged.

The accepted Chapter 1 state is preserved. This child has not accepted the
foundation candidate or Chapter 2. Full immutable-candidate validation and
audit, independent Standards and Spec reviews, and immediate candidate
verification before local acceptance remain required. After saving this
record and handoff, the author holds all writes for checkpoint 0089 and
root's subsequent compiler coordination. No new slice is started.
