# Rational kernels and exact tables

`RationalKernel` lets an author begin with a native finite Markov kernel and
rational singleton masses. `RationalKernel.table` reconstructs exact rational
entries. Finite additivity and the Markov law supply row normalization; callers
do not supply a reconstruction theorem or a second normalized table.

The existing `FiniteKernelEquality` API already reflects whole-kernel equality
into exact table equality. This addition supplies the other direction for
native kernels with rational masses. `tableKernelEquiv` gives both round trips.
Its objects are tables and full kernels with proof-valued properties, not
supports or chosen random-bit implementations. It does not recover a sampler,
random seed, operational path or cost from a distribution.

Tables already serve as arrows between finite spaces. The new view retains
kernel composition and identity, proves exact table recovery of composition,
and derives identity/associativity from the native kernel laws. Coordinate
changes use native kernel `comap` and `map`; their identity and composition
laws and reconstructed entries are proved. This is a homwise equivalence of
presentations with those operations, not a claim about arbitrary infinite or
irrational kernels.

The Bernoulli client begins with Mathlib's probability measure. The author
supplies a rational parameter in the unit interval and rational singleton-mass
facts. No hand-written row-normalization proof is needed. It then changes
coordinates through Bool, ULift Bool and a swapped Bool presentation, recovering
the exact one-third entry. The direct Metropolis–Hastings table client remains
under its original hypotheses and recovers unchanged. One-third and two-thirds
coins have the same positive support and different entries, preventing a
support-only replacement of the mass-bearing interface.

The generic setup pays for finite singleton reconstruction and its transport
once. Compared with authoring a table, the native route trades a row-sum proof
for rationality proofs; it is useful when the kernel and probability law already
exist. It is not automatically shorter for a small hand-written transition
matrix. Reconstruction uses choice and is noncomputable; existing executable
tables and sampling implementations remain available. There is no measured
productivity or runtime claim.

The initial search found existing parser witness transport and existing kernel
equality reflection. Both were retained rather than wrapped again. The selected
addition completes the remaining finite rational reconstruction direction.
#635 owns this construction, #634 the wider search, and #636 reassessment.
The richer higher-order QBS and native sampler obligations in #494–#497 remain
separate, as do the suppression experiments #546/#548.
