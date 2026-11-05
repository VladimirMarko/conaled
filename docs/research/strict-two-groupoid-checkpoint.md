# Strict two-groupoid construction checkpoint

These are construction checkpoints for [#322](https://github.com/VladimirMarko/conaled/issues/322).
The dependent higher adoption gate remains closed. The
[frozen test](dependent-higher-identity.md) and its memo are unchanged.

`SquareKit.Internal.PathTransport.TwoGroupoidPath` constructs the concrete
total-space discriminator. `Base` reuses the existing Mathlib bicategory
double delooping at `Multiplicative ℤ`. The path fiber is the one-object
integer groupoid. `fiberAction m` is a natural transformation of its identity
functor, preserving zero and addition.

The total space has one object, integer arrows, and cells retaining an integer
base component with boundary `a = b + m`. `Cell.fiber_boundary` connects this
equation to composition with the actual fiber transformation. The hom-category
is a groupoid, the total bicategory is strict, and integer negation gives
strict inverses for its arrows. Whiskering retains the base component.
All bicategory laws, including interchange, are proved. Parallel cells in
this particular total space are unique because their base component must be
`a - b`; this does not identify the distinct second identities in the base.
The integer hom-groupoid instance is scoped to avoid assigning that category
structure to ordinary integer clients globally.

`coherentContraction` is a Mathlib strong transformation from the identity
endofunctor to the constant-zero endofunctor. Its naturality comparison has
base component `a`. The unit, composition and 2-cell naturality pastings are
equalities of actual cells. The comparison is invertible, so its reverse
orientation is available without claiming strict naturality. A strict
contraction with any component `c` would require `c = a + c` for every integer
`a`. `no_strict_contraction` refutes this using `a = 1`.

This checkpoint constructs the concrete total bicategory directly. It has not
yet constructed a general higher-family interface or a Grothendieck operation
whose specialization produces that bicategory. The fiber action and boundary
connection constrain that next construction; they do not replace it.

## General hom-categories and reindexing

`TwoGroupoidHom` now constructs the hom-category for extension endpoints from
an arbitrary category `C`, strict bicategory `B`, evaluation functor `E : C ⥤ B`,
and target object `b`. Objects are pairs `(c,f)` with `f : E(c) → b`.
An arrow consists of `α : c → d` and a genuine fiber 2-cell
`ρ : f ⇒ E(α) · g`. In its intended application, `C` is a base hom-category,
so these objects and arrows are the total context's 1-cells and 2-cells.

The construction restricts bicategorical Yoneda along `E` and uses Mathlib's
contravariant Grothendieck construction. That construction can be reused for
each hom-category even though its locally discrete base prevents directly
using it as the whole higher context extension. Reindexing along any functor
`D ⥤ C` preserves the fiber cell, and its identity and composition laws are
proved as equalities of functors. When `C` is groupoidal and every hom-category
of `B` is groupoidal, the total hom-category is groupoidal. The inverse is
constructed from the inverse base cell, strict base cancellation and the
whiskered inverse fiber cell; both inverse equations are proved.

`StrictTwoTransformation.Trans` supplies the next family-action component:
a strict natural transformation between strict higher functors, with its
arrow equation and fiber 2-cell naturality. Its conversion to a Mathlib strong
transformation derives the unit and composition coherences. These are
structural transformation laws, not assumed elimination laws. The integer
action gives a concrete inhabitant with its component preserved by conversion.

`Examples.TwoGroupoidHom` connects the integer-boundary cells to the general
construction by mutually inverse encoding and decoding. A separate example
uses `B²ℤ` as the fiber and a discrete base. Its integer-one fiber 2-cell is
distinguished from zero, rejecting a general locally discrete fiber shortcut.
The reindexing and inverse cases consume the generic construction's theorems.
No third cell data is introduced at this layer; equalities establish the
ordinary hom-category laws. This is not yet a proof that all dependent type
constructors preserve the finite-dimensional restriction.

## Statement review and retained cases

Every new cell operation preserves its stated boundary. Equality of cells
uses uniqueness after retaining the base component, rather than erasing it.
`Cell.base_eq` quantifies over every cell and derives the forced difference
from its boundary. `comparison` supplies such a cell for every pair of
integers, preventing a vacuous uniqueness argument. No assumptions about
contextual J or general family closure occur in these proofs.

The four named results in `Examples.TwoGroupoidPath` check the oriented
calculation `3 = -2 + 5`, the integer-one component of the actual strong
transformation, rejection of base-component erasure, and failure of the
strict shortcut for an arbitrary contraction component. They consume the
public comparison, component and rejection results.

The strict-contraction failure is mathematical. Initial Lean failures while
constructing the checkpoint concerned alias reduction for integer arithmetic,
category instance inference and explicitly typing categorical composition;
they did not show a failure of finite-dimensional closure. Those errors were
resolved without changing the independently chosen boundary or contraction.

For the general layer, statement review checked the direction of the
contravariant Grothendieck boundary and inverse pasting, arbitrary functor
quantification in reindexing, and both input hypotheses of groupoid closure.
The generic layer does not assume locally discrete fibers. Its positive
integer fiber case witnesses that distinction. Encoding and decoding recover
the complete concrete cells, including their base components; equality of
decoded labels alone is not used as a claim of a general extension equivalence.

## Remaining construction

1. Specify the general small strict 2-groupoids and higher family collection,
   reusing Mathlib bicategories and strict functors where appropriate. Families
   must retain transformation action on base 2-cells; sections need their own
   coherent 2-cell data. Construct reindexing and Grothendieck extension,
   then connect this concrete example to that operation. The hom-category,
   its strict reindexing and vertical inverses are constructed. What remains
   is the admitted higher-family collection with its horizontal action laws,
   horizontal composition of these hom-categories, coherent sections and
   substitution of the complete extension. The cell correspondence above
   does not supply those missing constructions.
2. Prove closure of the proposed dimension restriction under extension,
   reindexing, Sigma and open identity. Construct reflexivity and contraction
   in general. Do not replace non-discrete fiber 2-cells by host equality.
   Preserve a counterexample if the chosen restriction fails.
3. Construct J for every admitted motive and finite dependent tail. Prove
   section coherence, reflexive computation and substitution. If Pi is used,
   construct its closure too. Transporting objects alone does not meet this
   obligation.
4. Interpret the specified judgments and retained generic argument, including
   both substitutions of the dependent pair and transported `apd` source.
   Construct the endpoint conjugation and integer observer in that same
   interpretation. Retain nonconstant transport and lower-truncated clients.

[Warren's primary source](https://mawarren.net/papers/crmp1295.pdf), especially
the transformation definitions, Grothendieck cell boundaries, elimination
naturality cells and Theorem 7.1, supplies the construction reference. Its
omega-dimensional soundness result is not a proved finite restriction here.
The separate #321 cubical programme is unchanged.

## Validation boundary

The focused Lake builds check both construction layers and their retained examples.
The repository audit implementation, with its entrypoint replaced by that
focused import, checks all declarations in their project import closure.
This is development evidence. Full candidate acceptance, the integrated
exhaustive audit and independent Standards/Spec review remain pending before
integration or any issue-completion claim. No new axioms or audit exceptions
are introduced.
