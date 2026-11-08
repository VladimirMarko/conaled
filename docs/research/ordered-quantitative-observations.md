# Ordered approximation and compositional numerical error

For [#299](https://github.com/VladimirMarko/conaled/issues/299), retain relational
containment as the enclosure contract and investigate a small sensitivity-aware
error certificate alongside it. Interval abstract interpretation supplies an
applicable ordered account. A direct quantitative sum/tensor presentation does
not admit the numerical operations below with their specified metric. This is a
bounded paper comparison, not a new numerical backend or a migration decision.

The subsequent [checked composition implementation](numerical-error-composition.md)
formalizes the bounded proposal across the affine client and the existing
rational disk-motion execution. Claims labeled paper derivations below describe
this report's original scope.

## Client and observations fixed before adaptation

The independent client is a two-stage real scalar pipeline:

```text
f(x) = 2x + 1
g(y) = 3y - 2
h(x) = g(f(x)) = 6x + 1
```

Execution order is observable: reversing the stages gives a different function. A client author provides
approximate implementations `fhat`, `ghat`, nonnegative uniform error bounds
`df`, `dg`, and an input pair with `|xhat - x| ≤ e`. Their obligations are
`|fhat(z) - f(z)| ≤ df` and `|ghat(z) - g(z)| ≤ dg` for every real `z`.
These are specifications of hypothetical implementations; no floating-point
algorithm is assumed.

Observe the exact output `h(x)`, the selected approximate intermediate
`yhat = fhat(xhat)`, final value `zhat = ghat(yhat)`, and a certified output
interval. The required error certificate must compose for arbitrary
nonnegative `e`, `df`, `dg`. A fixed discriminator uses `e = 0`, `df = 1/10`,
`dg = 1/5`. An interval analysis also takes the input range `[-1,1]` and must
produce a sound range after both stages.

These observations have different comparisons. Exact outputs use real equality;
error uses absolute distance; interval precision uses inclusion, with a smaller
interval more precise. A wide enclosure is not a large error in a selected
approximate value. The selected values remain part of the client even when two
implementations have the same bound. No quotient by equal certificates is
allowed. There are no probabilistic observations in this task.

The freeze was recorded outside the repository before adapting either route.
Prior exposure included the local enclosure/resource contracts and the previous
source assessments. The fixture was chosen from numerical composition, rather
than from the constructors of a local compiler. Both routes below answer that
same fixture, including its failure tests.

## Source results and exact applicability

**Source result, Bacci, Mardare, Panangaden and Plotkin.** Inspected
[arXiv:2212.11784v4](https://arxiv.org/html/2212.11784v4), §§2–3, 5 and 6,
including the proofs around Theorems 27–28 and 54–55. Signatures are disjoint
and finitary. Models use extended metrics and operations nonexpansive for the
maximum metric on finite powers. Basic theories admit axioms with finite
variable-distance premises. Continuous theories admit schemata whose conclusion
bounds range above a continuous function of the premise bounds; they are basic.

| Result | Hypotheses and conclusion |
| --- | --- |
| Theorem 27 | Basic `U,V`: `T(U+V) ≅ T(U)+T(V)` in `Met`. |
| Theorem 28 | Continuous `U,V`: completed free monads satisfy the corresponding coproduct equation in `CMet`. |
| Theorem 54 | Basic `U,V`: `T(U⊗V)` is the tensor of their free monads in `Met`. |
| Theorem 55 | Continuous `U,V`: the completed analogue holds in `CMet`. |

Sum combines axioms without cross-operation equations. Tensor additionally
requires zero-distance interchange between every pair of operations from the
two signatures. The free-algebra and bialgebra arguments establish the required
adjoints; these statements do not assert existence of tensors for arbitrary
monads. `Met`'s monoidal sum metric differs from its categorical maximum product
metric. These hypotheses replace the earlier introductory-only assessment in
[the discovery record](external-discovery-280/extension-initial.md).

**Source result, Cousot and Cousot.** Inspected the authoritative local
[1977 scan, Appendix 12, printed pp. 251–252](../references/cousot-1977/source.pdf#page=15),
visually checking H1–H3, L2 and T1–T2 against the
[transcription](../references/cousot-1977/appendix-12.md).
For complete lattices `C,A`, monotone endomaps `F,F#`, and monotone
`α : C → A`, `γ : A → C`, H2 requires `α ∘ γ = id` and `c ≤ γ(α(c))`.
H3 requires local simulation, equivalently `α(F(c)) ≤ F#(α(c))` or
`F(γ(a)) ≤ γ(F#(a))`. L2 proves their equivalence under the preceding assumptions.
T1 and T2 give greatest- and least-fixed-point bounds; in particular
`lfp F ≤ γ(lfp F#)` and `α(lfp F) ≤ lfp F#`. Equality is not a conclusion.
Continuity appears separately in H4/L4 for the Kleene-chain construction.
The finite pipeline below needs only local simulation and monotonicity, not a
fixed-point theorem or a widening. See the existing
[source inspection](cousot-1977-source-inspection.md) for the broader account.

The author-hosted PDF timed out during this investigation. The checked-in scan
was available and supplied the primary evidence; its SHA-256 is
`5d2956eed13b2d40f6e15c2087fb870c3dea54a332fe46ee07cea608ca417238`.
Only these two primary-source investigations were deepened. Source access
failure is not evidence against a mathematical route.

## Error composition and a rejecting example

**Paper derivation.** The frozen exact stages have Lipschitz constants `2` and
`3`. Triangle inequalities give

```text
|yhat - f(x)| ≤ df + 2e
|zhat - g(f(x))| ≤ dg + 3|yhat - f(x)|
                  ≤ 6e + 3df + dg.
```

The selected intermediate value is the witness connecting the two estimates.
A stage with sensitivity `L` and local error `d` acts on input error by
`e ↦ L*e + d`. Composing first `(L1,d1)`, then `(L2,d2)`, produces
`(L2*L1, L2*d1 + d2)`. Nonnegative coefficients make this transformer monotone;
function composition supplies associativity and `(1,0)` supplies the identity.
For three stages, either association gives constant term
`L3*L2*d1 + L3*d2 + d3`. This derives the certificate law without assuming
commutativity or additive accumulation of bare errors.

Choose the admissible implementations `fhat(z)=f(z)+1/10` and
`ghat(z)=g(z)+1/5`, with `xhat=x`. The final discrepancy is exactly
`3/10+1/5 = 1/2`. An additive writer of errors would report `3/10`, which is
false. If `xhat=x+1/100`, the bound is attained at `14/25`.
These rational calculations are reproducible with exact fraction arithmetic;
they are not new checked Lean theorems.

The same fixture rejects three further assumptions:

- **Nonexpansiveness:** `|f(1)-f(0)|=2 > 1`. A usual-metric scalar model of the
  proposed quantitative operations fails before any sum theorem can apply.
- **Tensor interchange:** `g(f(x))=6x+1`, but `f(g(x))=6x-3`. Identifying these
  at distance zero changes the specified denotation. Even solving the metric
  mismatch would not validate this tensor presentation.
- **Symmetric precision:** `[0,0] ⊆ [-1,1]`, but the reverse inclusion fails.
  A symmetric distance with zero exactly when one interval includes the other
  cannot express this comparison. Real-value error remains symmetric; interval
  precision does not inherit that symmetry.

A rescaled metric between different stage types could make particular maps
nonexpansive, but its units and rescaling proofs would become new author
obligations. A discrete metric would lose the requested numerical bound.
Neither silently preserves this client's specified absolute-distance contract.
These failures reject this direct presentation, not all quantitative semantics.

## Relational and ordered interpretations of the same pipeline

**Paper derivation, relational route.** At each stage relate an approximate and
exact scalar by `R_e(xhat,x) := |xhat-x| ≤ e`. The first implementation maps
`R_e` to `R_(2e+df)`; the second maps that relation to
`R_(3(2e+df)+dg)`. This requires indexed relations or explicit bound parameters,
not one unchanging relation chosen by erasing `e`. Compose using the actual
intermediate `yhat`. Relational simulation gives the bound on every admitted
input pair; it does not reconstruct inputs or implementations from a bound.

For enclosures use `Contains(I,x)`. An exact stage maps an input enclosure to
its interval image. An approximate stage maps it to that image expanded on both
sides by its local error. If `xhat ∈ [-1,1]`, the first approximate output lies
in `[-11/10,31/10]`, and the final one lies in `[-11/2,15/2]`.
The exact range for inputs in `[-1,1]` is `[-5,7]`. These are separate range
claims; when the real and approximate inputs differ, their admissible ranges
must be related explicitly or expanded by `e` first.

**Paper derivation, abstract-interpretation route.** Let `C = Set ℝ`, ordered
by inclusion. Let `A` consist of all closed real intervals, including empty,
unbounded and the whole line, again ordered by inclusion. Define `γ` as the
underlying set and `α` as the smallest closed interval containing a set.
Intersections give meets; the closed interval hull of a union gives joins.
Thus both domains are complete lattices. The maps are monotone,
`α(γ(I))=I`, and `S ⊆ γ(α(S))`.

For a scalar function `k`, let `K(S)` be its direct image and define
`K#(I)=α(K(γ(I)))`. Then `K(γ(I)) ⊆ γ(K#(I))` by extensivity. For the selected
positive affine stages this interval image is exact. A certified approximate
stage can use the monotone overapproximation
`K#_d(I)=α({k(x)+u | x ∈ γ(I), |u| ≤ d})`. The uniform error obligation proves
`khat(γ(I)) ⊆ γ(K#_d(I))`. Monotonicity composes these inclusions and yields
exactly the enclosures calculated above. Thus this is an applicable instance
of the source's local simulation conditions, not an analogy based on terminology.

This account is broader than finite rational endpoint records. Such records
alone have neither all these joins nor a top interval, so they do not satisfy
the complete-lattice hypotheses merely because containment composes. No claim
here applies the source's fixed-point results to the local finite record type.
The fixture itself needs no unbounded endpoints or recursive analysis.

**Reflection limits.** Soundness points from a concrete result to membership in
an abstract result. Membership does not imply attainability for the selected
implementation. For `fhat=f+1/10`, the symmetric error enclosure contains points
that this implementation never produces. Also `{−1,1}` and `[-1,1]` have the
same closed interval hull, so equality of abstractions does not reflect equality
of concrete sets. The insertion does reflect order between abstract intervals
through `γ`; that narrower fact does not supply concrete reflection.
An analysis can be sound while too imprecise for a requested tolerance. If a
client requires exact dependence preservation under cancellation, this interval
route must itself be rejected or refined.

## Existing checked evidence and author costs

The inspected local revision is
`36e102788d74268710bfd94e4f29b147bafbb885`. The following are **existing Lean
claims**, read at that revision, not formalizations added by this report.

| Existing evidence | Reuse and boundary |
| --- | --- |
| [Interval arithmetic](../../Applications/Intervals/Arithmetic.lean), `add_contains`, `neg_contains`, `mul_contains`, `compile_contains` | Rational containment and relational composition already work. `interval_cancellation_is_wider` exhibits `[-2,2]` for interval cancellation although exact cancellation is zero. |
| [Measured resources](../../Applications/Resources/Measured.lean), `bind_assoc`, `bind_erases`, `reweight_bind`, `reweight_bound` | Cost composition, value erasure, additive reweighting and monotone bound transport are separate contracts. `same_value_different_cost` prevents reflecting cost from value erasure. These claims do not certify numerical error addition. |
| [Numerical execution](../../Applications/Orbifold/NumericalExecution.lean), `run_correct`, `run_append`, `run_error` | Exact endpoint correspondence, execution concatenation and an explicit changing error calculation are retained. This does not prove a floating-roundoff theorem for the new scalar fixture. |

The rational affine enclosure specialization can reuse the existing arithmetic
primitives and `compile_contains`; its independent real interpretation needs
an explicit rational-to-real bridge. A bound-indexed scalar relation is a
proposed specialization, not an existing compiler theorem. One can carry each
bound in the representation state or make it an explicit theorem parameter;
this report does not choose a universal compiler representation.

The relation-based interpretation agrees with
[ADR 0007](../adr/0007-incremental-and-enclosure.md). Its author supplies the
exact primitive, interval operation and containment proof. A numerical error
extension additionally needs a domain, sensitivity and uniform local error
proof, plus evidence that each intermediate remains in the next stage's domain
if the bounds are not global. Bounds are semantic inputs, not coefficients a
compiler may infer without justification. The independent exact denotation,
chosen approximation, stage index and error witness must remain visible in
specializations.

Abstract interpretation adds an abstraction/concretization pair and order laws;
complete lattices become obligations only when invoking the relevant global
theorems. A quantitative presentation would additionally require an admissible
metric algebra and, for tensor, cross-operation interchange. The frozen client
fails those last requirements. These are mathematical obligation counts, not
measured author-time results. No author usability trial was run.

## Decision and owned residual work

**Adopt** the separation of exact equality, ordered enclosure and numerical
error for this client. **Retain** the current containment interface and existing
resource semantics. **Investigate** a small error-certificate specialization;
**reject** bare additive error accumulation and the direct usual-metric
sum/tensor presentation tested here. **Defer** a general quantitative effect
library and recursive interval analyzer until an independent consumer requires
their stronger hypotheses.

The bounded proposal is a lemma for composition of a chosen approximate map
with a chosen exact `LipschitzWith` map and a uniform error bound, returning the
explicit new bound. Reuse Mathlib's metric/Lipschitz and order interfaces rather
than add a parallel hierarchy. Validate identity, composition, this affine
specialization and the failed additive bound with example-driven development
before choosing any shared API. The current report does not assert that a
particular Mathlib declaration already packages the entire lemma.

| Proposed owner | Residual and acceptance condition |
| --- | --- |
| [#174](https://github.com/VladimirMarko/conaled/issues/174) | Consider the bounded error lemma and interval specialization; preserve chosen values and containment, and check the amplified-error failure case. No new backend is required. |
| [#193](https://github.com/VladimirMarko/conaled/issues/193) | Keep resource cost and error-transformer composition distinct. Any reuse must prove the coefficient action, identity and associativity rather than reuse scalar addition by name. |
| [#36](https://github.com/VladimirMarko/conaled/issues/36) | Own a future abstract-domain/fixed-point bridge if needed; provide complete domains and simulation hypotheses before importing global soundness conclusions. |
| [#235](https://github.com/VladimirMarko/conaled/issues/235) | Decide whether a second consumer warrants a shared bound-indexed interface; retain the existing enclosure and endpoint witnesses in any retrofit. |

These are ownership proposals, not new tracker assignments. The experiment
leaves integration and general formalization unproved. It changes no Lean code,
compiler frontend, universal syntax, kernel assumptions or numerical runtime.
Documentation validation checks links, arithmetic examples and whitespace;
independent Standards and Spec review remains part of the enclosing workflow.
