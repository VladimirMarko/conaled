# A fibrant cubical universe without univalence

[#650](https://github.com/VladimirMarko/conaled/issues/650) supplies a bounded
control in the existing De Morgan cubical setting. The universe has two
disconnected Boolean codes, both decoding to the unit family. Its code family
and universal decoder have lawful uniform fillers. Nevertheless, its actual
native path-to-equivalence map is not a homotopy equivalence.

The construction is in
[TaggedUnitUniverse](../../SquareKit/Internal/Cubical/TaggedUnitUniverse.lean),
with checked consumers in
[NonUnivalentUniverse](../../Examples/NonUnivalentUniverse.lean).
All contexts and fibers are `Type 0`-valued. The code context is the dependent
total of the constant Boolean family over the terminal cubical context.
The decoder is the constant `PUnit` family over that code context. A code in
an arbitrary context Γ is a natural Boolean section; it need not be globally
constant. The example evaluates the generic code at both Boolean values.

## Filling and substitution

`constantFilling` specializes the existing discrete dependent filler.
`codes_fibrant` and `decoder_fibrant` prove both cap/boundary equations and
uniformity for arbitrary contexts, substitutions, cofibrations and open boxes.
These are the repository's native `Filling.Lawful` contracts, not an assumed
fibrancy flag or a filler only for closed points.

`decoded a` is substitution of the universal decoder along the actual code
map. `decodedFilling a` reindexes its selected filler.
`decoded_reindex` and `decodedFilling_reindex` are strict equalities for
arbitrary substitutions; repeated substitution follows by applying them twice.
The examples retain the generic code, its two closed selections, and the
chosen decoder's open-box equations.

## The counterexample concerns native paths and equivalences

The false and true codes have isomorphic decoded families: `sameFiber` is
the identity isomorphism of the unit family. `HomotopyEquivalence.ofIso`
constructs the native contractible-fiber witness, and `equivalentFibers`
packages it as a section of the internal equivalence family, retaining the
chosen contractions as well as the function.

`no_path` proves that the native cubical path family between these codes has
no section. It uses `constantFamily_path_endpoints` and evaluates the resulting
endpoint equation at the zero-dimensional point. This is stronger than
observing that the two Lean Boolean values are unequal. Same-tag reflexivity
provides a positive path control.

`pathEquivalence` pulls the decoder's filler back along a native code path
and applies `IntervalTransport.map` and `IntervalTransport.equivalence`.
`pathToEquiv` internalizes that construction at the generic path, with target
`EquivalenceFamilies.equiv`. It is the transport construction for this
universe, not an arbitrary function out of an empty closed path space.

`not_univalent` rules out a native `HomotopyEquivalence` of that internal map
at the two closed tags. If such a witness existed, its homotopy-fiber center
over `equivalentFibers` would supply a path between false and true, contradicting
`no_path`. The external transport function is also proved nonsurjective.
No univalence assumption appears in these proofs.

## Classification still recovers the decoder

`classifierRecovery` uses the shared `PresheafFamily` representable decoder
and evaluation construction on the actual universal decoding family. The
examples check its evaluation hypothesis and recovery inverse equation.
Classification recovers a family up to an explicit isomorphism; it does not
assert that equivalent decoded families determine a path between arbitrary
codes of a separately chosen universe. Here it correctly recovers the unit
decoder while the discrete tags remain disconnected.

## Represented fragment and omitted closure

This universe represents only the constant unit family through its code
maps, with duplicate names. It has primitive unit sections, substitution and
lawful filling. It does not classify all fibrant families, or even its own
Boolean code family. No code operations or laws for general dependent sums,
products, identity types, recursive types, a universe hierarchy, or Glue are
provided. Ambient constructors continue to exist; closure of this chosen
universe under them is not asserted. In particular this is not a model of
full Glue-closed syntax from which univalence follows.

The ambient library still has the separate univalent small-family universes:
`Presheaf.SmallUniverse.NativeUnivalence.univalence` in
[NativeUnivalence](../../SquareKit/Internal/Cubical/NativeUnivalence.lean) and
`Cartesian.SmallUniverse.NativeUnivalence.univalence` in
[CartesianUnivalenceCompletion](../../SquareKit/Internal/Cubical/CartesianUnivalenceCompletion.lean).
Their constructions and clients are unchanged. Univalence belongs to a
chosen universe and decoder, not just to the cube category. A non-univalent
universe and a different univalent universe can therefore coexist here.

This control justifies no broader non-univalent model project by itself.
Keep the classification and recovery programme independent of univalence;
require it only for consumers whose contracts identify equivalences with
universe paths.
