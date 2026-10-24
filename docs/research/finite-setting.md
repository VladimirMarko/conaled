# Parameterized finite presentations in Set families

Implementation of [#120](https://github.com/VladimirMarko/conaled/issues/120),
following the [reviewed contract](composable-setting-contracts.md). The experimental
public interface is [FiniteSetting](../../SquareKit/Internal/FiniteSetting.lean),
with [checked examples](../../Examples/FiniteSetting.lean).

## Source, models and denotation

`Formula`, `Sequent` and `axioms` represent the finite geometric scheme
`top ⊢ p ∨ q`, `p ∧ q ⊢ bottom`, `p ⊢ parameter`. `Presentation X` supplies
its predicate parameter. Every `X : Type u` and `r : X → Prop` is admissible.
The fixed three sequents are shared source data, rather than a field callers
must rebuild. The syntax has no excluded-middle connective or axiom and no
requirement that r be decidable. This bounded scheme is separate from the
existing regular-fragment syntax, which does not provide these connectives.

`Formula.eval` interprets syntax in predicates. `Satisfies` interprets all
three source sequents at every parameter. `satisfies_iff` identifies exactly
coverage, disjointness and containment in r. `Model` stores P, Q and this
satisfaction evidence. It does not store an externally chosen category.

The denotation `Fiber T x` is `PLift (T.parameter x) ⊕ Unit`; `PLift` places
a proposition's proof type in `Type`. Thus the left summand has one element
when r holds and no elements otherwise, and the right has one element always.
`Section T` is a dependent function choosing one fibre element at each x.
`modelSectionEquiv` proves the correspondence in both directions, including
the inverse laws. Equality of models is equality of both predicates, with
proof irrelevance for satisfaction evidence. This is Set semantics.

`Model.toSection` uses classical host reasoning to decide P at each point.
Coverage then identifies Q when P fails. This noncomputable definition is
necessary for this implementation's conversion from propositional coverage
to a function valued in a sum; neither `DecidablePred r` nor decidability of P
is an argument of the interface. `Section.toModel` obtains its predicates
from the summand tags and needs no classical selection. Host reasoning does
not add excluded middle to the represented source theory or establish this
construction for arbitrary internal topoi.

## Substitution and the generic partition

`Presentation.subst`, `Model.subst` and `Section.subst` substitute an arbitrary
function `σ : Y → X`. The source generator and sequent data stay fixed; the
parameter becomes `r ∘ σ`. `Formula.eval_subst` proves the interpretation
law for every formula, and `Model.subst` uses it to preserve satisfaction.
Both directions of the correspondence commute with substitution. All three
substitutions satisfy identity and composition laws, across independently
chosen context universes.

`Total T` is the dependent sum of the fibres, with first projection to X.
`genericSection` chooses the second projection; `genericModel` is its partition
by summands. Substitution along a section's `graph` recovers that section and
its model. `genericModel_model_recovery` recovers any model through its
corresponding section. `totalMap` maps a substituted total family into the
original one, commutes with projection, and satisfies identity and composition.
`genericSection_subst` and `genericModel_subst` identify the generic data after
this substitution. These public comparisons are the intended input for #121;
clients need not reconstruct satisfaction proofs.

## Statement review and checked cases

The intended first case was a two-point context with r true only at 0: a model
selecting P={0}, Q={1} must correspond to a section selecting left at 0 and
right at 1. Bool represents these points as false and true. The independently
specified `varyingSection` supplies that expected result. The missing connection
was an equivalence between predicate partitions and dependent sections; the
core interface supplies it, and `varying_correspondence` proves equality through
`modelSectionEquiv` and its inverse law. Initial elaboration of the case exposed
that equality of the predicates needs propositional extensionality rather than
definitional equality. The expectation and model stayed unchanged.

The next cases exercise the consequences and boundaries of that connection:

- `zero_two_choices` and `one_only_right` check the varying fibre itself.
- `true_left` and `true_right` give both choices when r=true;
  `false_section_unique` uses the equivalence to show every model gives the
  everywhere-right section when r=false. These include inhabited contexts,
  so existence is not inferred from an impossible model premise.
- `substitute_not` applies correspondence naturality to exchange the fibres.
  `varying_generic_recovery` uses the generic recovery theorem to recover the
  independently specified predicate model.
- `rejects_uncovered`, `rejects_overlap` and `rejects_forbidden_left` use
  `satisfies_iff` to refute interpretations violating each sequent separately.

Review of the formal statements checks that `Satisfies` quantifies over all
three sequents and every x, with implication in the stated direction. The
partition theorem assumes neither inhabited X nor r; the right summand ensures
models exist even for r=false. The equivalence quantifies over every model and
section, and both inverse laws compare the original objects, rather than only
their tags. Fibre proofs are irrelevant, as required for these Set subobjects.
The substitution theorems use arbitrary functions and include both directions
of the equivalence. Total maps retain the base projection and the generic
partition. The concrete rejection cases confirm that coverage, disjointness
and containment have not been silently dropped. Helper extensionality and
evaluation lemmas are exercised by these constructions and cases.

## Remaining classifier obligations

This implementation supplies the finite presentation and its Set-family
model/section correspondence. It does not construct E/A, geometric morphisms,
a slice-topos classifier universal property, arbitrary internal-site semantics,
or change of ambient topos. These require categorical universal properties
and coherence beyond equality of dependent Set functions. It also does not
extend the regular proof language with geometric derivation rules. The
mixed-square experiment #121 must build its pullback comparison using these
interfaces; the general geometric-morphism pseudopullback remains separate.
