# Changing families in path contractions and finite dependent tails

This continues the [shared family-map experiment](family-map-contextual-elimination.md)
for [#433]. The first checkpoint, `81c4784`, compared changing motives over fixed
tails or a supplied contraction square. This continuation constructs the root
square from base/family data, propagates it through changing dependent tails,
and uses the resulting square in elimination. It implements neither an arrow
model nor a derivation-indexed interpretation.

## Mathematical interface

For categories `Γ, Δ`, a base functor `K : Δ ⥤ Γ`, groupoid-valued families `A`
and `B`, and a natural transformation

    α : B ⟶ K ⋙ A,

choose sections `x` of `A` and `y` of `B` with the explicit point-preservation
equation

    y.familyImage α = x.reindex K.

This is equality of sections, including their action on arrows. It is not
merely an objectwise equality or an unspecified natural isomorphism. The result
requires no invertibility, fullness or faithfulness of `α` or `K`. Both base
categories have `IsGroupoid` instances for the path contraction.

`PathComparison.baseFamilySquare` constructs the actual coherent square between
the two normalized path contractions. Its path functor sends the endpoint and
chosen identity arrow through the family transformation and base functor. It
does not discard the chosen arrow by replacing every path with reflexivity.
The forward equation, inverse equation and counit coherence are all proved.

`Section.familyImage` is a component presentation used to make this path map
explicit. `familyImage_eq` proves it equals the prior `Section.mapFamily`, and
`familyImage_lift` gives the same mapped section functor. This introduces no
alternative section semantics.

## Construction and equality

`FamilyMapPath` first constructs the family-induced map over one base. Its
arrow proof uses naturality of the family transformation and the endpoint
conjugation in `directIdentity`. `familyMap_arrow` proves preservation of the
actual path-contraction arrow. That equation establishes counit coherence; the
square is not obtained from the endpoints alone.

`FamilyMapSquares` composes coherent squares and combines the same-base family
square with the existing substitution square. The explicit section equation
above supplies the endpoint relabeling. This gives the general base/family
square without assuming that elimination commutes.

For a dependent extension, `familyLiftSquare` proves compatibility of the two
Grothendieck contractions under a changing family. Its inverse equation follows
from naturality at the original inverse counit; its counit equation retains the
fiber arrow and equality transports. `liftChangingSquare` combines this result
with the existing pullback lift. The two dependent families are independently
specified and related by a natural transformation; one need not be definitionally
the pullback of the other.

All three fields of `EquivalenceSquare.Square` are established with the existing
strict equations and explicit equality transports. The final elimination
comparison is strict equality of functors, including arrows, through the
previously checked `eliminate_familyMap`. No natural isomorphism is silently
promoted to equality.

## Arbitrary finite changing tails

`ChangingTail` is a finite sequence of paired dependent declarations. At each
step it contains a target family, an independently specified source family, and
a natural transformation over the preceding context comparison. The new context
comparison is the induced Grothendieck functor. Thus the next declaration can
depend on the entire preceding extension, including earlier family variables.
No fixed tail length, constant-family premise or empty-tail restriction appears
in the construction.

The sequence projects to two existing categorical `ContextualElimination.Telescope`
values. `ChangingTail.propagate` constructs a branch functor and the coherent
square between their existing reindexed contractions by structural recursion.
It does not take the final square as an assumption.

`PathComparison.eliminateChangingTail` starts from the general base/family data,
constructs the root square, propagates it through the finite changing tail, and
passes that proof to `eliminate_familyMap`. Its remaining section hypothesis is
the ordinary mapped-branch equation. It does not assume the conclusion that
elimination commutes. Motives at the final contexts may also change under an
arbitrary natural transformation.

These tails are categorical telescopes. This experiment does not construct
comparisons for every generated `Typed` derivation, nor package them into a new
`Typed.Model`. Connecting a chosen source-comparison implementation to the
categorical data remains work for either route.

## Checked cases and statement review

`Examples.ChangingFamilyTails` reuses the noninvertible projection
`Discrete Bool × C4 → C4`. The first experiment proved that it is not full and
not injective on objects. The new cases check:

- the actual path-map image of each chosen C4 loop is exactly the same label,
  and distinct labels remain distinct;
- the general base/family theorem constructs its root square, with an explicit
  point-preservation equation;
- two successive noninvertible changing declarations, with the second family
  over the first extended context;
- construction of the final contraction square from that root;
- an elimination application with explicit inhabited branches and a proved
  mapped-branch equation, consuming the constructed square.

The concrete declarations in the two-step fixture are constant families. The
universal construction separately quantifies over arbitrary families at each
successive context, and its definition recurses over the complete finite
sequence. Constant examples are not used to infer that generality.

Statement review checked the induction domain, endpoint equation, arrow action,
contraction coherence, independently changing tail families, and absence of an
invertibility premise. The final test's branches are constructed explicitly;
the branch compatibility obligation is discharged from the constructed square.
The terminal motive in that test checks the complete comparison connection; it
does not replace the universal theorem for arbitrary motives.

## Architectural boundary and remaining work

The interface uses categories, functors, natural transformations, sections and
the existing normalized contractions. `ChangingTail` records mathematical
comparison data for finite dependent extensions; it is neither new source syntax
nor a model of comparison judgments. An arrow-model implementation and a
derivation-indexed implementation can both construct these inputs and consume
the results without changing this interface or each other's implementation.
No exclusive choice between them is made here.

The proved endpoint contract is strict equality of the mapped sections. A
point comparison supplied only as a natural isomorphism would need a further
explicit comparison construction; this report does not claim that extension.
Likewise the theorem uses strict functor-valued families and natural
transformations already present in the groupoid model, not pseudofunctor-valued
families.

For #433, parameter restriction must still be connected to the generated source
contexts, families, substitutions and sections using one of the two routes.
Generated smooth descent closure remains unproved. The retained source proof,
its existing smooth consumers and prior milestones are unchanged. No full
smooth-model completion or author-productivity conclusion follows from this
experiment.

Focused checks and selected-root axiom inspections are recorded in the external
handoff. The parent workflow owns fresh acceptance validation, exhaustive audit,
public coverage and independent review. No source rules, trust assumptions,
heartbeat limits or toolchain settings were added.

[#433]: https://github.com/VladimirMarko/conaled/issues/433
