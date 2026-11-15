# Assembly partial maps and program-index lifting

[#385](https://github.com/VladimirMarko/conaled/issues/385) constructs the P1
partial-map classifier on the assembly category from
[the P0 prerequisite](internal-sdt-prerequisites.md). It supplies a domain
boundary for #386's monad and slice comparisons. It does not construct an
effective topos, internal completeness, or the selected solver of #371.

## Source and admitted domains

Van Oosten and Simpson, [*Axioms and (counter)examples in synthetic domain
theory*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf),
Definition 3.1 and §3, published pp.265–266, specify assemblies, tracked maps,
and inherited-realizer subassemblies saturated by a recursively enumerable
support. Their program-index lift uses diagonal evaluation. The present
construction proves the corresponding classification and presentation
comparison in Lean, without importing the paper's internal-logic axioms.

An assembly has a carrier in `Type u` and a nonempty set of natural-number
realizers for each element. Every admitted arrow must have a partial-recursive
tracker terminating on every realizer of every input. Arrow equality is
extensional equality of the underlying total functions, independent of the
tracker. These P0 definitions remain unchanged.

For a predicate `P` on an assembly `A`, `Admissible A P` means there is one
partial-recursive function `φ` such that, whenever `n` realizes `x`, `φ n`
terminates exactly when `P x` holds. `admissible_iff_support` proves the
equivalent all-realizers and some-realizer descriptions. No condition is
imposed on unused natural numbers. The domain object retains *all* realizers
of each included element; replacing it by an arbitrary monomorphism is outside
this theorem.

## Constructed interfaces

[AssemblySubobject](../../SquareKit/AssemblySubobject.lean) constructs carrier
restrictions, their monic inclusions, and pullbacks of inclusions with tracked
mediators and uniqueness. It also constructs general pullbacks using paired
realizers and the equality of the two images.
[AssemblyLimits](../../SquareKit/AssemblyLimits.lean) exposes these universal
properties as Mathlib `PullbackCone`/`IsLimit` data and supplies `Mono` for the
inclusions and `HasPullbacks` for the category.

[AssemblyPartialMap](../../SquareKit/AssemblyPartialMap.lean) keeps the
specified domain, its admissibility proof, and the actual tracked map from
that subassembly separate. Classification generates a program that first
waits for the domain semidecision and then runs the supplied map tracker.
The generating function terminates without testing whether the emitted
program terminates. The underlying optional value is defined classically;
its computational admission follows from this separate tracker proof.

[AssemblyLiftClassifier](../../SquareKit/AssemblyLiftClassifier.lean) recovers
an admissible domain from any arrow into `programLift` and constructs the
tracked map on that domain. `partialMapEquiv` proves both round trips,
including exact selected values and the domain. The original partial-map
span and the recovered span both have proved pullback universal properties
against `programLiftUnit`. Reindexing along any admitted input map commutes
with classification. Postcomposition along an admitted result map commutes
with the lift's map operation.

[AssemblyDiagonalLift](../../SquareKit/AssemblyDiagonalLift.lean) independently
specifies realizers by evaluation at their own program index. Both comparison
arrows retain the optional value and use computable code transformations
fixing the original input before changing the index. Their composites are
identity arrows; they commute with lifted maps and units. Equality here does
not identify program indices or their running times. The diagonal map action
is transported through this proved equivalence.

## Checked cases and exclusions

[AssemblyPartialMaps](../../Examples/AssemblyPartialMaps.lean) exercises total
and empty domains and the domain of programs halting at zero. The halting
client returns the original input index, preserving selected data rather than
only reporting definedness. It has both a terminating and a divergent input.
Mathlib's halting theorem proves that this admitted domain has no computable
decision predicate. Its reindexing law applies to arbitrary computable changes
of natural-number parameter.

A Boolean assembly in which every number realizes both values has a proper
inherited-realizer subobject that is not admissible. No classified arrow can
have precisely that domain. A separate control rejects an external map that
sends its two Boolean values to different coded natural numbers. Thus neither
an arbitrary subobject nor an arbitrary externally specified partial function
is silently admitted. Presentation comparison retains bottom and the exact
selected number, and the classifier equivalence recovers the original halting
partial map.

## Boundary for P2 and later work

P2 can use constructed pullbacks, admissible inverse images, the classifier
bijection and its source/result compatibility. [P2 / #386 now constructs](assembly-lifting-monad.md)
tracked lift multiplication, the monad laws, and its stated slice comparisons.
Those are derived constructions, not fields assumed here. [P3 now supplies iteration and conditional selection](internal-cut-iteration.md).
P4–P5 still owe concrete completeness and uniform varying-family constructions
before the selected-solution comparison.
The category is still assemblies, not a constructed effective topos. No
source theorem about all internal propositions transfers merely from the
classifier proved here. Native external partial-computation clients remain
unchanged.
