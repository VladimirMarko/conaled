# Tracked assembly lifting and change of base

[#386](https://github.com/VladimirMarko/conaled/issues/386) constructs P2 of the
[internal SDT prerequisites](internal-sdt-prerequisites.md). The ordinary lift
and the lift in each assembly slice are now Mathlib monads. Change of base
preserves the slice lift, its unit and its multiplication. These constructions
use the [P1 partial-map classifier](assembly-partial-map-classifier.md); they
assume neither a certificate state object nor an algebra on that future object.

## Source and equality boundary

Van Oosten and Simpson describe lifting by partial singletons, with singleton
unit and union multiplication, in Definition 1.2 and the following discussion,
pp.237–238 of [*Axioms and (counter)examples in synthetic domain theory*](https://www.pure.ed.ac.uk/ws/portalfiles/portal/12306183/1_s2.0_S0168007200000142_main.pdf).
Their assembly presentation and program-index lifting appear in §3,
pp.265–266. The implementation constructs the corresponding operations for
our assembly category. It does not import the paper's internal topos reasoning
as an axiom. The slice comparison below is derived from our classifier and
pullbacks; it is not a transcription of a slice theorem from the paper.

Carriers have type `Type u`, realizers are natural numbers, and each arrow
must have a partial-recursive tracker on every realizer of every input.
Arrow equality compares carrier functions. It does not identify program
indices or assert equal runtime. Host `Option` case analysis alone does not
supply an assembly arrow. The proofs below explicitly supply tracking or
compose previously tracked arrows.

## Multiplication and slices

[AssemblyLiftMonad](../../SquareKit/AssemblyLiftMonad.lean) constructs
`programLiftMul`, with carrier function `Option.join`. Its tracker generates
a program which first runs the outer program and then runs the returned
inner program. This handles both outer divergence and an outer program that
returns a divergent inner program. The checked laws are both unit laws,
associativity, and naturality. `programLiftMonad` packages them using Mathlib.

For a tracked family `p : A → B`,
[AssemblySliceLift](../../SquareKit/AssemblySliceLift.lean) defines the slice
lift as the inherited-realizer subassembly

```
{ (b,t) : B × L A | ∀ x, t = some x → p x = b }.
```

The base is retained even at bottom. `sliceClassify` classifies an admissible
partial map whose defined values lie over a specified total base map. Its
graph, uniqueness and recovery theorems follow from P1. A nowhere-defined
partial map constructs `sliceBottom`, without requiring the target family
to have an inhabited fiber. [AssemblySliceMonad](../../SquareKit/AssemblySliceMonad.lean)
constructs multiplication by flattening the selected lifted value while
retaining the base. `sliceLiftMonad` proves the monad laws in `Over B`.

## Change of base and standard interfaces

For every tracked `f : C → B`,
[AssemblySliceComparison](../../SquareKit/AssemblySliceComparison.lean)
constructs an isomorphism from the pullback of the slice lift of `p` to the
slice lift of the pulled-back family. The forward arrow first recovers an
admissible partial map on the pullback using P1, then classifies it. Its graph
retains the actual `C` coordinate and selected `A` value. The inverse forgets
the redundant coordinate inside a defined value. Both inverse equations and
both base-preservation equations are proved.

[AssemblySliceReindex](../../SquareKit/AssemblySliceReindex.lean) provides the
computed pullback functor, identity comparison, and composite comparison.
[AssemblySliceCoherence](../../SquareKit/AssemblySliceCoherence.lean) proves
identity and composite coherence, naturality for every tracked arrow over
the base, and compatibility with unit and multiplication. The explicit
coherence equations use the inverse comparison arrows; the comparisons are
isomorphisms, so these determine forward coherence. `baseChangeNatIso`
packages naturality in the standard category of slice objects.

[AssemblySlicePullback](../../SquareKit/AssemblySlicePullback.lean) connects
this computed presentation to Mathlib's chosen pullback and `Over.pullback`
by a natural isomorphism. Thus the computed pullbacks remain accessible
without requiring clients to adopt a separate slice-category interface.

## Checked cases and remaining obligations

[AssemblyLifting](../../Examples/AssemblyLifting.lean) exercises selected 17,
outer bottom, inner bottom, and an actual nested constant-program realizer.
Two successor base changes retain base 3 and selected data `(5,17)` in the
appropriate fiber. The general composite coherence theorem specializes to
these two nonidentity changes. Another case classifies the undecidable
halting domain from P1, preserving its selected input index.

A negative control distinguishes slice lifting from pulling ordinary `L p`
back along `B → L B`. That ordinary pullback excludes bottom: its equation
requires `some b = L p t`. Our slice lift instead has a tracked bottom over
every base, including the checked base 3. These constructions therefore
cannot be substituted for each other.

P3 still owes iteration objects and their universal properties; the later
completeness and selected-client obligations remain open. This work provides
no effective topos, universe classifier, fixed-point selector, certificate
state algebra, or countdown adequacy theorem. The external ordered-domain
clients retain their contracts. The examples measure mathematical coverage,
not authoring productivity.
