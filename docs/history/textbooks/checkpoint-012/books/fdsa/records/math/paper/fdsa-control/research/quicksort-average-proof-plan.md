# Quicksort average and randomized bounds — source scope and proof plan

Prepared 2026-11-02. **Read-only mathematical preparation, not a Lean proof or
chapter acceptance.** This note closes a coverage ambiguity in C02-024. It
keeps the two mathematical assertions in §2.3 as obligations without importing
the entire bodies of the cited papers or inventing an unrestricted cost claim.

## Source and actual scope

The pinned July27,2026 book, §2.3 on printed pp.16–17, explicitly states an
average `O(n lg n)` bound for first-pivot quicksort and an expected bound of the
same order when the pivot is randomized. It also says that their analysis is
outside the book's exposition. That describes where the authors supply the
proof, not permission to mark the stated mathematics checked in this project's
whole-book reconstruction. The introduction makes the same expository boundary;
Exercise2.4 later supplies a separate deterministic worst-case obligation.

The existing C02-024 inventory/reuse rows originally classified both average
claims as an expository exclusion. Root has asked their owners to correct that
classification. Preserve distinct requirements for (1) average input order and
(2) randomized pivot selection. Neither follows just from Exercise2.4's uniform
quadratic upper bound.

Primary source identities:

- Book URL: <https://fdsa-book.net/functional_data_structures_algorithms.pdf>,
  SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
- `Sorting.thy` at Isabelle commit
  `f86f290225eebcc52c1ae7dba2e098f405f51c21`, SHA-256
  `dfa60eae99cd6fa31e4fdd45f488282f913619a204061960e43ddceba4cadfca`.
  Its literal source body is left quicksort, singleton pivot, right quicksort,
  with two append occurrences. Exact append observations must retain the
  parsed association; value associativity is not a cost proof.
- Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and current conaled
  Chapter1 candidate `1aabd512284fe86254278ac631eda061d311050b`.

## Precise distribution and key assumptions

A faithful standard reading of the first average claim is a uniform ordering
of `n` distinct, totally ordered keys. One finite sample space is
`Equiv.Perm (Fin n)`; the input list enumerates that permutation. A general
`Nodup` list can later be related by its order-preserving rank representation.
This does not require a distribution on arbitrary payload values, and payload
records can retain a key map with distinct keys.

For the second claim, fix an input with distinct keys and choose a uniformly
random **occurrence** as pivot at every nonempty subproblem. Removing that
occurrence leaves exactly `n-1` elements. Either give the actual finite random
execution, or prove a distribution correspondence with a finite uniform random
priority ordering. Merely replacing the execution by an invented recurrence is
insufficient. A one-time shuffle and recursive random pivots need a checked
law-equivalence if one is used to certify the other.

The hypotheses matter. For the displayed two-way algorithm, all equal keys
always go to the right partition. Randomizing their order or choosing any
occurrence as pivot does not balance that input. The constant-list family has
the same quadratic Exercise2.4 count as an extremal sorted input. Consequently,
no uniform claim over arbitrary duplicate-bearing multisets follows from this
model. Preserve this family as a checked domain counterexample; do not silently
change the source algorithm to its separate three-way exercise variant.

## Exercise2.4 metric and exact mean

Let `T` be the exercise's actual recurrence: empty cost1; each nonempty call
pays the two recursive costs, two full filter traversals with unit callback
cost, and one function-entry charge. Append is deliberately uncharged.
For `n>0`, a pivot of rank `k` therefore gives

```
T = T_left + T_right + 4*n - 1
length left = k
length right = n-1-k.
```

The nonempty expression may be written without natural subtraction as
`4*(n-1)+3`; use a field/cast only after its domain has been established.
Under either distribution above, pivot rank is uniform on `0,...,n-1`, and
conditional recursive relative orders have the corresponding uniform law.
Linearity of expectation then gives the rational recurrence

```
A_0 = 1
A_n = (2/n) * sum_{k=0}^{n-1} A_k + 4*n - 1  (n>0).
```

For the fixed-first-pivot input average, the missing combinatorial step is
substantial and explicit: conditioned on a pivot rank and fixed relative orders
of the two sides, the original tail has the corresponding binomial number of
interleavings. The marginal laws of both sublists are uniform. Do not assume
independence where linearity suffices; do prove the marginal correspondence.

Subtracting the equations for successive sizes yields

```
n*A_n = (n+1)*A_(n-1) + 8*n - 5.
```

At `n=1`, verify this directly from the nonempty/base equations instead of
using a nonexistent positive-size averaging equation at zero. Dividing by
`n*(n+1)` and telescoping gives

```
A_n = 8*(n+1)*harmonic n - 12*n + 1.
```

This is a **derived target for the exercise metric**, not a formula printed by
the book and not yet a Lean theorem. It includes `n=0` using `harmonic 0=0`.
It should be proved only after the measured algorithm/distribution recurrence
is established, so it cannot be mistaken for an unconnected numerical sequence.

## Independent small calculations

### Exact bridge to the comparison metric

There is a useful pointwise target, before taking any expectation. Define `Q`
using the same pivot choices and partitions as the book algorithm, with empty
cost0 and nonempty cost `Q_left + Q_right + (n-1)`. The partition lengths sum
to `n-1`, so induction on the actual execution gives

```
T xs = 4 * Q xs + 4 * xs.length + 1.
```

This identity is valid for any input when both observations use the **same**
partition/pivot execution, including repeated keys. It uses the source's two
filter charges and empty-call charge. It does not assert that the algorithm
literally executes only `Q` comparisons or that arbitrary comparison counters
have this observation. The identical relation can be proved for every supported
random execution, then transported through the common distribution.

The classical mean `2*(n+1)*H_n-4*n` for `Q` therefore yields exactly
`8*(n+1)*H_n-12*n+1` for `T`. This gives a second proof route and a check on the
direct recurrence algebra. A proof of the mean for an unrelated numerical
sequence remains insufficient.

### Pinned AFP proof reference and semantic boundary

The public AFP entry *The number of comparisons in QuickSort* by Manuel Eberl
(entry date March15,2017) supplies a suitable existing proof reference. Its
dated source archive is
<https://isa-afp.org/release/afp-Quick_Sort_Cost-2026-10-26.tar.gz>, SHA-256
`cda7ed0a00991dcf8a5adff2d9909d6e761b2d8fb9501425ed8b93dbf462f457`.
Exact theory hashes and retrieval metadata are recorded in
`../provenance/afp-quicksort-cost-source.json`; reading copies are outside the
checkpoint payload. No Isabelle assertion is imported as a Lean axiom.

Inspected correspondence points:

- `Randomised_Quick_Sort.rquicksort` chooses a uniform valid occurrence index,
  removes it, partitions the rest, and records `n-1` plus recursive costs.
  `snd_rquicksort` connects that execution to the length-indexed cost law under
  `linorder_on`, set containment and distinctness hypotheses.
- `expectation_rqs_cost` connects the distribution to its mean recurrence;
  `rqs_cost_exp_eq` proves the harmonic formula and
  `rqs_cost_exp_asymp_equiv` proves the asymptotic comparison bound.
- `Quick_Sort_Average_Case.qs_cost_average_conv_rqs_cost` proves a **distribution**
  identity for a uniform permutation of a finite ordered set. Its proof uses
  uniform head selection, random partition interleavings and the rank bijection.
  `expectation_qs_cost` then transfers the expectation.

The AFP sorter places `y ≤ pivot` on the left and its complement on the right;
the book uses `y < pivot` on the left. After removing the pivot, distinctness
makes these partitions equal for the average-case domain. That equality and
the measured execution bridge must be proved explicitly. The value sorter
and the pointwise identity above do not by themselves justify forgetting this
domain difference. The AFP file also contains a separate three-way variant;
its repeated-key bound is not evidence for the displayed two-way sorter.

`quicksort-average-calculations.json` enumerates all permutations for `n≤7`
using exact rational arithmetic, the literal filter partition, and the supplied
exercise tariff. It is independent calculation evidence, not kernel checking.
The means are:

| n | Number of permutations | Mean T | Maximum T |
|---|---:|---:|---:|
|0|1|1|1|
|1|1|5|5|
|2|2|13|13|
|3|6|71/3|25|
|4|24|109/3|41|
|5|120|253/5|61|
|6|720|331/5|85|
|7|5040|2903/35|113|

Every enumerated mean matches the derived harmonic target. The independently
computed maxima and constant-list counts are `2*n*n+2*n+1`. Retain a small
connected mean case, e.g. size3, and a repeated-key case alongside the eventual
universal proofs.

## Harmonic bounds and asymptotics: exact reuse

Inspected pinned declarations:

- `Mathlib.NumberTheory.Harmonic.Defs`: `harmonic : Nat → Rat`,
  `harmonic_zero`, `harmonic_succ`. No new harmonic-number implementation.
- `Mathlib.NumberTheory.Harmonic.Bounds`: `log_add_one_le_harmonic` and
  `harmonic_le_one_add_log`, with casts to Real in their conclusions. The
  upper theorem also handles zero according to Lean's total real logarithm,
  but an `n log n` asymptotic estimate should use an eventual positive domain.
- `Mathlib.Data.Fintype.Perm`: `Fintype.card_perm`; in particular the finite
  permutation sample space has cardinality `n!`.

After the exact mean is connected, `harmonic n ≤ 1+log n` immediately yields
an explicit upper bound such as `A_n ≤ 16*n*(1+log n)` for `n≥1`.
For `n≥2`, positivity of `log 2` and monotonicity of log give an
`n*log n` bound with a fixed positive constant, for example
`16*(1+1/log 2)`. Use natural logarithm first and a standard change-of-base
bridge for the book's `lg`; do not confuse real log with `Nat.clog`, whose
rounding was useful for deterministic merge heights.

The eventual theorem may be packaged with Mathlib's asymptotics API after an
explicit eventually-valid inequality is proved. No logarithm theorem or
probability backend needs to be rebuilt for this result.

## Appends and the source's whole-call interpretation

The exercise count is not the full call count of the literal displayed
`left @ [pivot] @ right` expression. Preserve that limitation explicitly.
There is nevertheless a simple useful **bound** bridge: if the left partition
has length `k≤n-1`, the two append counts are at most `2*n+1` for either
association. This is at most `4*n-1` for `n≥1`, which is already the exercise's
nonrecursive tariff. With the same empty cost, induction can therefore prove
full append-inclusive count `≤2*T` when all other primitives use that same
call-count convention. For the actual parsed association, prove the concrete
recurrence first; the common bound does not assert equal counts for the two
associations.

Uniform random pivot selection/removal is another operation. Any claim about
an implementation of that choice must add its own work, e.g. a linear list
traversal after an abstract uniform index. Such an extra linear toll preserves
the asymptotic argument after an explicit comparison bound, but its work is
not included in the exact harmonic formula above. No unqualified Lean wall-time
or random-bit complexity claim follows from these abstract observations.

## Probability architecture and API traps

The repository already provides `Applications.Probability.Table` with exact
rational nonnegative entries and row sums1. `Table.comp`, `deterministic`,
`kernel`, `lintegral_kernel`, and `kernel_comp` connect finite stochastic tables
to Mathlib kernels. Those are useful if a finite bounded execution/result
representation is chosen. `ProbabilityProgress.Execution` instead resolves a
whole run in one random environment and retains its joint law; no new random
environment framework is needed.

Mathlib supplies `PMF.ofFintype`, `PMF.ofFinset`, `PMF.bind` and
`PMF.bindOnSupport` if a distribution on the measured recursive result is more
convenient. A uniform positive finite type can be constructed with
`PMF.ofFintype` and the explicit normalized-weight sum proof.

Do **not** use a remembered `PMF.uniformOfFintype` API without inspection. At
this pin it is a deprecated alias (dated2026-10-04) for
`MeasureTheory.Measure.uniformOfFinset`, which returns a Measure and takes a
Finset argument. The current `Measure.uniformOfFinset` is also available,
with `uniformOfFinset_apply_singleton` and `uniformOfFinset_apply`. Choose the
actual construction needed rather than relying on the old namespace spelling.

This note does not choose a new public general abstraction. The finite-average
statement needs only the uniform finite sample space and the existing measured
cost. The random-pivot statement should reuse one of the existing semantic
routes with checked execution correspondence and explicit termination/domain.

### Additional exact finite-sampling APIs

Further bounded inspection at the same Mathlib pin found useful pieces, but
no ready-made uniform random-partition theorem in the inspected probability,
list, finite-set and combinatorics directories. This is a bounded search result,
not a claim of absence from every dependency.

| Pinned module/declaration | Useful fact and boundary |
|---|---|
| `Mathlib.Data.List.Permutation`, `length_permutations`, `mem_permutations`, `nodup_permutations` | The actual `List.permutations` enumeration has length `n!`, lists exactly permutations, and has no repetition when the original list is `Nodup`. It can express a rational finite average without requiring `Fintype` on all payload values. |
| Same module, `permutations_perm_permutations'`, `Perm.permutations` | The efficient enumeration agrees up to list permutation with insertion enumeration; changing the initial listing preserves the multiset of generated permutations. This transports finite sums, not arbitrary order-sensitive folds. |
| `Mathlib.GroupTheory.Perm.Fin`, `Equiv.Perm.decomposeFin` | An actual equivalence `Perm (Fin (n+1)) ≃ Fin (n+1) × Perm (Fin n)`. Its inverse sends0 to the chosen pivot and sends a successor index through `swap 0 pivot`. That remaining-key encoding is not generally order-preserving. |
| Same module, `Equiv.Perm.decomposeFin'`, `decomposeFin'_symm`, `decomposeFin'Symm_zero`, `decomposeFin'Symm_succ` | The alternative inverse sends a successor index through `pivot.succAbove`, preserving the remaining-key order. **Its current signature starts at `n+2`**, so size0/1 are separate base cases. The equivalence is noncomputable, suitable for a counting proof, not an executable shuffle claim. |
| `Mathlib.Logic.Equiv.Basic`, `Perm.extendDomain`, `extendDomain_apply_image`, `extendDomain_apply_not_subtype` | A permutation of a subtype can be extended while fixing its complement. This can build equal-cardinality bijections between fibers of relative-order observations, fixing the pivot and all keys outside one partition. |
| `Mathlib.Algebra.BigOperators.Group.Finset.Defs`, `Fintype.sum_equiv`, `Equiv.sum_comp` | Reindex finite sums through the actual sample-space equivalence. Neither theorem supplies a probability distribution or a source-execution correspondence by itself. |
| `Mathlib.Probability.ProbabilityMassFunction.Constructions`, `PMF.map_ofFintype` | Push-forward weights are explicit sums over fibers. It requires finite source **and finite target types**; use an appropriate finite subtype or finite observation space instead of imposing finiteness on arbitrary payload lists. |
| `Mathlib.Probability.ProbabilityMassFunction.Integrals`, `PMF.integral_eq_sum` | For a finite sample type with a measurable space and measurable singletons, the expectation is the finite sum of `toReal` weights times observations. `integral_eq_tsum` handles general sample types only with its explicit integrability premise. |

The average-input proof needs only the conditional **marginal** uniform laws
of the two filtered sublists. A possible alternative to explicit binomial
interleaving counts is a fiber bijection: extend a permutation of one partition
to all keys while fixing its complement, act on the original permutation, and
show the required relative-order observation is transported. Then all fibers
over that partition's orderings have equal cardinality. Prove surjectivity and
nonzero finite normalization, including empty partitions; equal fiber sizes
alone are not the full argument.

The randomized-pivot expected bound can instead be proved directly by induction
on input length: its uniformly chosen occurrence has uniform rank on a list of
distinct keys; recursive expectations depend only on the two resulting lengths.
This does not require proving equality of the **entire** randomized and
average-input cost distributions if the book obligation is only their means.
If a common full distribution theorem is implemented because it simplifies the
proof, it requires the stronger joint partition law; do not infer it from the
two marginal expectation identities.

## Acceptance obligations retained

1. Implement and verify the source two-way sorter and its exact supplied cost.
2. Prove the conditional uniform-pivot/recursive-subproblem law, not only the
   algebraic recurrence solution.
3. Connect the harmonic identity, logarithmic bound and named distribution to
   the actual cost observation.
4. Supply the random-pivot execution model and its own correspondence.
5. Retain duplicates and append/pivot-selection work qualifications.
6. Run ordinary connected-case, candidate validation, proof-audit and both
   independent review gates within Chapter2. This preparation accepts none.
