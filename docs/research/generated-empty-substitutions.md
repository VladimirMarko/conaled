# Generated substitutions into empty

The answer depends on which primitive arrows are admitted. For the structural
grammar specified below, every arrow into empty is source-equal to the canonical
iterated projection. If the grammar also admits typed substitution hypotheses,
there is a satisfied hypothesis giving an arrow into empty which is not
source-equal to identity. These statements use the same guarded source equality.

This resolves the bounded question in
[#330](https://github.com/VladimirMarko/conaled/issues/330) and supplies an explicit
boundary for [#326](https://github.com/VladimirMarko/conaled/issues/326). It does
not prove uniqueness for every derivation of the engine's `Sub` predicate.

## Objects, arrows and equality

[`GeneratedSubstitutions.lean`](../../SquareKit/Internal/DependentJudgments/GeneratedSubstitutions.lean)
uses the existing `GeneratedContext`: empty followed by finitely many typed
extensions. Each family can depend on the entire preceding context. Objects
retain their context expressions and extension presentations. Object expressions
are not quotiented by arbitrary raw context equations.

`GeneratedArrow P Ω` fixes both object presentations and an arrow expression.
It has these constructors:

- Identity at a generated context.
- Composition of two generated arrows with the same intervening presentation.
- Weakening from a typed extension to its prefix.
- Pairing a generated arrow with a term having the required substituted type.
- Conversion of an arrow expression along a source equality, keeping its domain
  and codomain fixed.
- A primitive arrow with both a source `Sub` derivation and permission from P.

Every constructor has a source typing derivation, established by
`GeneratedArrow.typing`. Pairing retains the dependent term judgment. Neither
schematic substitution of raw variables nor arbitrary proof of the `Sub`
predicate is silently counted as structural generation.

`closedArrows` grants no primitive-arrow permissions. It still permits type and
term declarations, and the terms paired into a context can use the full source
theory. The uniqueness theorem is valid for arbitrary Ω: restricting its
declarations to a conventional well-formed type/term signature is not needed
for this implication. Such a restriction remains relevant to a correspondence
with an independent calculus. An arrow hypothesis in Ω is insufficient to make
that arrow structurally generated under this policy.

`hypothesisArrows Ω` additionally permits each substitution judgment explicitly
listed in Ω. This changes the generated arrows, not the source rules or their
equality. The example below compares these policies using the same Ω.

For either policy, `GeneratedCategory` takes the quotient of generated arrow
representatives by **existence of a source equality derivation** at the fixed
boundaries. Reflexivity, symmetry and transitivity make this a setoid;
congruence makes composition well defined; the guarded identity and associativity
rules establish the category laws. Different proofs of the same arrow expression
are identified. No claim is made that proof witnesses of equality are themselves
equal.

## Closed generation gives uniqueness

Write `eΓ` for the existing canonical projection from generated context Γ to
empty. `GeneratedArrow.empty_natural` constructs a source derivation of

```text
eΓ ∘ σ = eΔ
```

for every closed generated `σ : Δ → Γ`. Its induction uses identity and
associativity for the identity/composition cases. Weakening is the definition
of the canonical projection at an extension. Pairing uses the existing
weakening-after-pairing equation. Equality conversion uses congruence and
transitivity. The primitive case is impossible under `closedArrows`.

At Γ = empty, `eΓ` is identity, so `empty_unique` gives `σ = eΔ` as a source
derivation. The canonical projection itself belongs to this same grammar by
`toEmpty`. Consequently `GeneratedCategory.emptyUnique` constructs a `Unique`
instance for each hom-set into the empty object: existence and uniqueness in
the source-equality quotient are both established.

No terminality axiom was added to the semantic model interface or the source
theory. This proof does not use interpretation in the Boolean model to infer
a source equality.

## A primitive hypothesis separates two generated arrows

[`Examples.GeneratedEmptySubstitutions`](../../Examples/GeneratedEmptySubstitutions.lean)
defines the single assumption `Sub empty empty s`. Under `hypothesisArrows`,
the hypothesis rule and the permission constructor make s a generated arrow.
Identity is another generated arrow with the same boundaries.

The existing full `ReachableLoops.model` interprets every context as Unit and
every family and section as Unit. Substitutions are Bool, identity and weakening
are false, composition is Boolean or, and pairing retains its substitution
argument. Assign s the value true. The new `satisfied` theorem checks the actual
source assumption in this interpretation. The old ambient example alone did
not establish this source-generated counterexample.

If a source equality `s = id(empty)` existed under this assumption, soundness
would give `true = false`. `Hypothesis.not_equal` rules out that derivation;
`distinct_classes` then distinguishes the two arrows in the generated category's
source-equality quotient. `not_terminal` refutes subsingleton endomorphisms of
its empty object.

The assumption list also satisfies `TypedAssumptions`. There are no equality
assumptions whose operands need definedness witnesses. Thus that existing
condition cannot imply empty-context uniqueness. It is not defective in its
intended model-map use; it is insufficient for this stronger claim.

Finally `not_closed` proves that this very s is not in the closed generated
grammar. The two results therefore do not contradict one another, and the
primitive-arrow counterexample is not misapplied to closed generation.

## Cases, validation and scope

The examples include a declared type over empty followed by a term of its
identity-substituted type. `termType` derives that type from the preceding
declaration, and `satisfied` checks a concrete assignment. Pairing this term
and then forgetting it exercises the source uniqueness theorem. A further
extension uses an identity family whose endpoints are the preceding generic
variable; the canonical projection inhabits the generated-arrow grammar for
that dependent tail. The general uniqueness result covers every arrow of that
grammar into empty, including composition and equality conversion.

Statement review distinguishes the policy parameter from Ω, fixed object
presentations from equality of contexts, and source derivability from equality
in one interpretation. The counterexample supplies typed derivations and a
satisfying model assignment, so its hypotheses are not vacuous. The category
quotient uses source equations only between admitted arrows. The closed
uniqueness theorem is a derivation-producing construction, stronger than merely
checking that all examples evaluate alike.

The library and examples are imported by the public entrypoint for the normal
build and exhaustive proof audit. Exact candidate validation and independent
review evidence are retained by the orchestration.

For #326, a proposed conventional-to-guarded translation must establish that
its substitutions land in this grammar, or explicitly extend the grammar and
recheck the theorem. Derived path/telescope operations are not new primitive
constructors here; using their structural expansions requires the applicable
source equations. Nor has this task proved that every guarded `Sub` derivation
with only type/term assumptions has such an expansion. That broader completeness
claim belongs to source adequacy. Arbitrary primitive substitution assumptions
require either a different correspondence or additional explicitly justified
laws. The generic engine remains available under both policies.
