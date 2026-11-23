# Cartesian constructors over larger contexts

[Issue #605](https://github.com/VladimirMarko/conaled/issues/605) supplies Sigma,
Pi, and Path codes in `smallFamilyCodes.{u}` over arbitrary
`Context.{u+1}` bases. The target universe remains fixed. Context values and
native family values are lifted explicitly; no resizing assumption is used.
This is the Cartesian admission dependency identified in the
[#625 design assessment](sip625-design/decision.md).

## Public interface

Import `SquareKit.Internal.Cubical.CartesianLargeFamilySubstitution` and open
`SquareKit.Cubical.Cartesian.SmallUniverse`. `LargeConstructors.sigma` and `.pi`
accept a code `a` and a dependent code over `total (liftedDecode a)`.
`LargeConstructors.path` accepts an interval-indexed code and endpoint terms.
Each returns a `Result C` containing a small code, a decoding isomorphism to
`C`, a selected filler on its decoder, and its lawfulness proof.

For a new family, use `SmallPresentation.Data C` to supply small representatives
of its fibers, then `LargeConstructors.construct` with a lawful native filler.
Clients do not assemble represented charts. `Data.pi` proves function smallness
by injecting native Pi elements into restriction-indexed values; it does not
assume the larger base is small. `Data.path` uses the endpoint subtype of that
function family. These constructions reuse the original model's proof strategy
with Cartesian cube maps and variable-source boxes.

`LowerFilling` lowers a filler on a raised family. It raises the variable cap as
well as the tube face. The classifier constructs codes on represented charts
and proves a native decoder isomorphism. The chart declarations moved from
`CartesianUnivalence` into `CartesianUniverseComposition`, retaining their
existing qualified names so admission does not import univalence.

## Exact comparisons and boundaries

`construct_filling` recovers the entire supplied operation after transport
through the decoder isomorphism. `Result.reindex` restricts a result and retains
its chosen filler. `sigmaSubstitution`, `piSubstitution`, and `pathSubstitution`
compare that restriction with independently rebuilt constructors on substituted
inputs. Each accompanying `_filling` theorem preserves the complete selected
operation, including every base context, face, variable cap and box. These are
family isomorphisms and filler equalities after transport, not equalities of
classified codes. `sigmaSubstitution_comp` identifies the composite comparison.

The returned filler is defined by transporting the constructor's supplied
filler. [Canonical decoder recovery](canonical-decoder-filling-recovery.md),
completed in [#607](https://github.com/VladimirMarko/conaled/issues/607),
identifies it with `NativeDecode.filling` of the classified code and derives
canonical constructor-operation substitution. Named Pi/Path identity and
composite comparison laws were supplied by
[#606](https://github.com/VladimirMarko/conaled/issues/606).
The [native constructor transport API](cartesian-constructor-transport.md)
supplies dependent pair/function algorithms along actual Cartesian universe
paths and derives their selected comparison bodies. The total structure
identity theorem remains in #625.

## Checked cases and statement review

`Examples.CartesianLargeFamilyConstructors` uses a context containing both a
generic small code and a natural parameter. It admits an indexed finite family
through the public interface and constructs Sigma/Pi for fibers of size `n+1`.
Its decoder comparisons prove that fibers at zero and one are not isomorphic.
The generic constructor cases impose no discrete presentation on their inputs.

Successor and doubling are proved nonidentity. At parameter two their composite
(doubling first) gives five; the indexed fiber then has six elements. The cases
instantiate all three constructor comparisons at both substitutions and their
composite, preserve whole fillers, and exercise Sigma comparison composition.
The empty Sigma decoder has no elements, while the empty-domain Pi has a unique
section. A decoded path from zero to one is rejected through the constant
family observation; a reflexive decoded path has a section.

Statement review checks the fixed target universe in `Result`, the absence of
base-smallness hypotheses, and the restriction indices in the Pi smallness
injection. The lowering proof quantifies over arbitrary variable caps and
subobjects. Substitution equalities compare whole `Filling` records rather than
only endpoints or selected evaluations. The concrete cases connect their
conclusions to the new decoder and substitution APIs. No new axioms or proof
audit exceptions are introduced.
