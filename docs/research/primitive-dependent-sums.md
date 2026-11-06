# Primitive dependent sums and the stronger eta contract

This records the bounded comparison for [#327](https://github.com/VladimirMarko/conaled/issues/327)
and the separation test in [#331](https://github.com/VladimirMarko/conaled/issues/331).
Keep the existing strong Sigma interface and expose the primitive alternative.
The alternative admits models excluded by the strong inverse law, while the
strong interface derives eliminator uniqueness and preservation from fewer
primitive operations. No existing provider or client is migrated.

## Contract and equality boundaries

[PrimitiveSigma.Capability](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/Capability.lean)
requires formation, packing over the base, primitive dependent split and beta.
For `A` over `Γ` and `B` over `Γ.A`, packing maps `Γ.A.B` to `Γ.Σ(A,B)`.
For **every admitted family** `C` over `Γ.Σ(A,B)` and section `d` of `C[pack]`
over `Γ.A.B`, split returns a section of `C`. Beta identifies its pullback along
packing with the chosen branch. There is no unpacking operation, repacking
law, section uniqueness or reflection assumption in the builder fields.

The three relevant equalities have different roles:

| Equality | Meaning here |
|---|---|
| Source judgmental equality | A derivation of an equation in the specified guarded theory. |
| Semantic host equality | Lean equality of the actual interpreted operations or substitutions. Source equations are sound for this equality. |
| Object identity | A section of the model's identity family. It need not reflect to host equality. |

HEq in the semantic interface aligns sections across the stated dependent
types. It is host equality with heterogeneous indices, not a replacement for
object identity. The original strong capability supplies a comprehension
isomorphism, including both host inverse equations. The new capability does
not identify that isomorphism with an object identity witness.

[Stability](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/Stability.lean)
adds formation and packing naturality, then a separate substitution law for
the **chosen** primitive split. The reindexed branch is cast using packing
naturality and the structural substitution equations. Its type is precisely
`(C[sumMap])[pack']`. Split naturality cannot be obtained by invoking the old
strong uniqueness theorem. Identity and sequential sum maps retain their
explicit family comparisons.

## Derived projections and propositional eta

The first projection eliminates into `A[weaken]`. The second eliminates into
`B[firstMap]`, where `firstMap` pairs the base projection and the first
projection. The proof `firstMap_pack` aligns this second motive with the old
second family. This is the dependent type adjustment required for the second
projection's beta law; no untyped component equality is substituted for it.

Pairing the projections constructs `unpack`. Comprehension extensionality and
the two derived projection beta laws prove `unpack ∘ pack = id`. They also
prove that repacking is over the base and is the identity after precomposition
with packing. These results do not prove `pack ∘ unpack = id`.

For propositional eta, form the identity family between the repacked generic
sum element and the generic sum element. Over packing, the derived beta laws
align these elements, so reflexivity supplies a branch. Primitive split gives
`eta`, with its beta theorem. This construction uses modeled identity,
reflexivity and identity substitution, and does not use J. The capability
already lives over a structural model with those operations; the full source
interpreter additionally retains contextual J from its prior model.

## Complete separating interpretation

[ConstantFamilies](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/ConstantFamilies.lean)
uses types as contexts, functions as substitutions and sections, and **constant
families only**. Identity families are always the unit type. Context extension
is an ordinary product. The primitive sum of `A` and `B` is `(A × B) × Bool`.
Packing inserts `false`. Split evaluates the branch at the stored context and
two components, ignoring the flag.

This supplies split for every family and branch admitted by this model,
including branches that vary with the context and both components. It is not
merely a projection-beta structure. The restriction to constant families is
essential: a family distinguishing the extra point is not admitted. The model
has no universe of all dependent families, and this counterexample must not
be described as such a model.

[ConstantContextual](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/ConstantContextual.lean)
constructs contextual J for every finite tail. Its recursive map retains all
tail entries while replacing the endpoint and identity witness by the root.
The checked left-inverse and commuting-square equations prove J beta and
substitution. [ConstantStable](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/ConstantStable.lean)
supplies formation, packing and primitive split stability for every base map.
Thus the example satisfies the whole selected weak contract, including its
inherited contextual Id/J fragment and substitution laws.

Repacking resets a true flag to false, so its substitution is unequal to the
identity. The derived object-identity eta term still exists. A Boolean section
that reads the flag also separates split eta: restricting it to packing and
then splitting produces the constant-false section, rather than the original
section. [Separation](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/Separation.lean)
uses soundness to prove this source split-eta rule is not derivable from its
well-typed premises, both before and after the substitution-rule extension.
This is an explicit counterinterpretation, not a failed simplification.

## Strong specialization and source comparison

`ofStrong` keeps the strong provider's formation, packing and exact chosen
split. Its derived unpack equals the original unpack. `Stable.ofStrong` and
`Map.ofStrong` obtain the additional laws from the existing strong proofs;
callers supply no new laws. The native provider exercises a nonconstant
second family and motive, `Fin(n + 1)`, alongside the constant-family
countermodel.

[Comparison](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/Comparison.lean)
proves that primitive source split and the old source split have the same
selected denotation at their typed motive/branch boundary. Every weak source
derivation is sound in each specialized strong provider. This is not a claim
of raw-expression equivalence: the new operation takes and validates a motive
argument, whereas old split is substitution along unpack. Malformed raw
arguments need not have the same behavior. No universal conservativity or
weak-to-strong model expansion theorem is claimed.

[DerivedEliminationLaws](../../SquareKit/Internal/DependentJudgments/Sigma/DerivedEliminationLaws.lean)
checks split eta in the **first** strong Sigma theory. Substitution composition,
packing-after-unpacking eta and substitution identity suffice. The later
closure theory merely exposes this derived rule. At model level split eta was
already derived; this work does not introduce another strong builder axiom.

## Maps, extensions and retained data

[Maps](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/Maps.lean)
separates formation/packing preservation from preservation of the chosen
primitive split. The latter is a map field for the weak contract. Identity and
composition preserve it, including motive and branch comparisons. For strong
providers the old map's split theorem discharges that field. No requirement to
preserve all raw totalization failures is hidden in this semantic map contract.

[Theory](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/Theory.lean)
extends the contextual source language and supplies its sound interpreter.
[Reindexing](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/Reindexing.lean)
adds the selected formation, constructor, branch-type and split substitution
rules without changing expressions. Raw source substitution of derivations
remains available separately from these object-context substitution laws.

[Recovery](../../SquareKit/Internal/DependentJudgments/PrimitiveSigma/Recovery.lean)
uses the existing dependent memo client. It retains the selected certificate
section, transported certificate, value and dependent action, with exact
denotation equalities. The certificate derivation and selected data survive
both constructor admission and the later substitution-law extension. Reduct
recovers the prior interpreter, including its selected contextual J. These
are conditional extensions for supplied providers, not an assertion that
every old model admits a new sum capability.

## Builder work and remaining boundaries

| Obligation | Strong provider | Primitive provider |
|---|---|---|
| Sum representation | Formation, pack, unpack | Formation, pack, split |
| Computation | Both inverse equations, over-base equation | Split beta, over-base equation |
| Projections | Supplied unpack components | Derived by split |
| Dependent split typing | Derived from host repacking eta | Part of primitive split's dependent type |
| Split uniqueness | Derived | Fails in the checked model |
| Split substitution | Derived from formation/pack stability | Required explicitly |
| Map preservation of split | Derived from formation/pack preservation | Required explicitly |
| Propositional repacking | Available | Derived from Id/reflexivity and split |

The weaker interface removes the isomorphism requirement but adds obligations
for the chosen eliminator and its preservation. It is not uniformly less work
for a provider. Existing native strong callers retain their current facade;
no wrapper migration is counted as a reduction in caller work. The new weak
provider is the concrete reason to retain the alternative.

The [finitary type-theory study](finitary-type-theories.md) records the literature
and distinguishes typed rule boundaries, arbitrary raw assumptions and
translations between independently specified calculi. This comparison settles
the selected sum contract, not #326's ordinary-calculus correspondence, #325's
non-strict dependent comparisons, or #321/#322 higher-model adoption. It adds
no host axioms, universes, higher model, or universal framework. The scoped
recommendation is to retain both interfaces and their explicit specialization.

## Statement review and checked cases

The projection proofs retain the actual second family and its cast; eta's
conclusion is a modeled identity section. The separating theorem negates host
repacking equality and separately rules out a precise source split-eta rule.
All model-side eliminator and stability statements quantify over every admitted
motive and branch. The constant-family restriction is visible in the model,
and the native specialization exercises genuine varying families.

[PrimitiveDependentSums](../../Examples/PrimitiveDependentSums.lean) checks
selected `Fin` recovery, exact strong unpack recovery, sequential model maps,
two noncommuting substitutions and their family comparison, component retention
at an extra point, object eta and the source obstruction. Generic memo recovery
checks selected data rather than merely inhabitation. Full repository acceptance
and independent review remain recorded with the issue's candidate evidence.
