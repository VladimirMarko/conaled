# Checked nominal dependent telescope

[#369](https://github.com/VladimirMarko/conaled/issues/369) implements the binding
fixture and maintenance change from the
[#365 report](architecture-scaling-study/binding-probability-controls.md).
[NominalTelescope](../../SquareKit/Internal/NominalTelescope.lean) constructs a
finite-permutation quotient, interprets its named annotations, and compares it
with intrinsic contextual families. The
[checked cases](../../Examples/NominalTelescope.lean) retain `(7,1)` through two
base substitutions and `(7,1,1)` after adding the dependent tail. Both capture
mutations and both selected-value resets fail the stated contract.

## Independent contract and admitted fragment

For free natural expressions `N,Z`, the contract is

```text
a : Fin(N+1)
b : Fin(|a|+1)
result : Fin(Z+|a|+1), with selected value |b|
```

The maintenance extension adds `r : Fin(|b|+1)` and returns
`(Z+|a|, b', r)` in `Σ k, Σ b' : Fin(k+1), Fin(|b'|+1)`. The inclusion
`b'` has underlying value `|b|`; it never chooses an arbitrary inhabitant.
The typing proof uses `|b| < |a|+1` and nonnegativity of `Z`.

This is a fixed telescope schema, parameterized by arbitrary finite expressions
built from free natural atoms, literals and addition. It admits the selected
second argument as its body, and the selected third argument as the extension.
It does not admit arbitrary bound bodies, shadowing, nested lambda syntax,
weak comprehension models or a complete nominal dependent language. These
restrictions are explicit in the constructors. In particular, the alpha class
at fixed `N,Z` has only one element because only bound spelling varies there.
The full `Program` also retains `N,Z`, so distinct free-expression syntax is
not identified by this quotient.

The contextual presentation records `N,Z` and uses the intrinsic dependent
families `First`, `Second`, `Third` and `Result`. It has no bound atom fields.
`liftFirst`, `liftSecond` and `liftThird` construct the typed base change;
`observe_substitute` and `tail_substitute` preserve the selected values.
This is a contextual Type-family realization of the report's contract, not a
new de Bruijn parser or an assertion that the existing source calculus already
admits arbitrary dependent functions.

## Finite permutations, freshness and alpha abstraction

Atoms are natural numbers. `FinitePerm` contains a bijection and a proof that it
fixes every atom above some finite bound. Identity, inverse, composition and
transpositions have constructed instances. An expression's `bound` describes
a finite initial segment containing its free atoms. The support used here may
be larger than the least support; the development makes no least-support claim.

For `k = max N.bound Z.bound`, a `Frame k` contains a finite permutation fixing
every atom below `k`. Its bound names are the images of `k,k+1,k+2`.
`Frame.fresh` proves that they avoid the free support, and
`Frame.name_injective` proves they are distinct. The identity permutation gives
a representative for every `N,Z`; no freshness premise is left to an axiom.

`Frame.Alpha` is the orbit relation under finite permutations fixing this
support. Its definition mentions neither contextual families nor evaluation.
`Frame.alpha` constructs the orbit witness `g ∘ f⁻¹` between frames. The
annotated telescope is generated from the frame, so `annotations_action`
checks that the action moves its dependent annotations and selected body
along with the binder names. This is a simultaneous abstraction of this fixed
ordered telescope. It is not a construction of the general FM-set universe
or of an arbitrary nested abstraction functor.

The source inspiration is Gabbay and Pitts,
[*A New Approach to Abstract Syntax with Variable Binding* (2002),
Lemma 5.1 and Corollary 5.2](https://www.cl.cam.ac.uk/~amp12/papers/newaas/newaas-jv.pdf).
Their fresh-transposition account explains why spelling can be hidden, while
freshness constrains what operations descend. Our finite orbit construction
is a bounded implementation of that idea. The paper's general abstraction
and iteration theorems are not imported as axioms, and its results are not
being claimed as dependent typing theorems.

`Frame.env` extends a free valuation at the actual named atoms.
`annotations_eval` proves that the six named expressions evaluate to the
specified first, second and third bounds, result index, selected body and
selected tail. `nominal` and `nominalTail` then construct finite values using
the derived bounds. `comparison` and `tail_comparison` retain those values;
alpha invariance follows from these proved evaluations. Quotient elimination
in `abstractObserve` uses that invariance proof.

## Substitution and equality boundaries

`Expr.subst` recursively substitutes free expressions. `substitute` constructs
a fresh canonical frame after substitution and rebuilds all annotations from
the substituted `N,Z`. This is sufficient because the admitted body schema is
fixed. It is not an implementation of substitution for arbitrary named syntax.
The new finite support is computed from exactly the expressions in use; the
substitution function need not have finite range.

`substitute_id` and `substitute_comp` derive the alpha-class laws from expression
substitution and the constructed orbit witness. `substitute_preserves` connects
that operation on classes to typed lifting beneath both binders.
`two_substitutions` and `tail_two_substitutions` compose the typed lifting and
named interpretation results. The numerical examples use these public results,
then reduce the independent arithmetic expectation from #365.

`toContextual` and `fromContextual` are inverse on the admitted schema, by
`contextual_roundtrip` and `nominal_roundtrip`. `comparison_reflects` states the
precise equality reflection: syntactic equality of the free `N,Z` expressions
corresponds to equality of nominal programs modulo bound spelling. Numerical
interpretation can identify more expressions, such as adding zero, and is not
claimed to reflect this syntactic equality. Selected observation equality is
equality of dependent finite values, with proof irrelevance for their bounds.

The two source substitutions use colliding spellings deliberately. The first
maps free `z` to `a+2`; the second maps that free `a` to `b+3` while doubling
the other free parameter. Frames preserve the old second spelling after the
first step and freshen it after the second. At the reported values, the correct
index is 7. `first_capture` evaluates the unfreshened expression and obtains
4 rather than 3; `second_capture` obtains 8 rather than 7. These are mutations
of named evaluation that omit the required fresh frame, not accepted programs
with mysteriously wrong denotations.

`no_bound_name_observer` rules out every function on alpha classes that returns
the first binder's representative atom. Its witness swaps a canonical binder
with a fresh atom, leaving the free support fixed. `resetting_second_fails`
and `resetting_third_fails` separately reject replacing the selected finite
value by zero. Merely preserving the result's inhabitedness would miss both.

## Maintenance and native clients

Adding the dependent tail requires a named third annotation using the second
atom, a selected tail expression, its typing proof in `nominalTail`, and the
stronger observation type. The generic finite-permutation action and free
expression substitution are reused. `tail_alpha_invariant`,
`tail_two_substitutions` and `tail_retains` discharge the new comparison,
substitution and old-observation obligations. The contextual implementation
extends the intrinsic family with `Third` and retains the exact selected `r`.
It needs no name support argument, but still needs the dependent type alignment.

The existing interfaces remain unchanged. At baseline
`6176f4c195b133bfcc5faca2d5bc63b474c6884d`, inspection of
[FiniteTail](../../SquareKit/Internal/DependentJudgments/FiniteTail.lean) confirms
that its `reindex` traverses declarations under successively lifted contextual
substitutions. [DependentFunctions](../../SquareKit/Internal/DependentFunctions.lean)
provides `Sub.lift_comp`, `depSub_comp` and `funcSub_comp` for its own bounded
nameless fragment. Those are useful reusable mechanics, but neither is the
nominal capture-avoidance proof above. This implementation does not migrate
those clients or route the alternative through an incumbent adapter.
Mathlib's permutation and finite-value operations are reused at pinned revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).

The checked comparison establishes this fragment's mathematical feasibility.
It reports neither executable compiler adequacy nor measured author
productivity. Source size and proof length do not measure either. The next
obligation under #289 is an independently specified body extension that changes
the selected dependency, together with a local abstraction/concretion and
substitution proof that survives it. That would test the limits of rebuilding a
fixed schema. General nominal syntax and weak-model coherence remain separate
work, coordinated with #235 and #290. #107 remains paused, #108's held-out
theorem remains unselected, and #260 remains inactive.

The bounded successor [#382](https://github.com/VladimirMarko/conaled/issues/382)
now checks a generated arithmetic body language, including a body-only free
atom collision and a selected sum of bound inputs. Its
[varying-body report](nominal-varying-bodies.md) records the local substitution
laws and remaining nested-binder and typing obligations. It preserves this
fixed-schema interface and its third-tail client.
