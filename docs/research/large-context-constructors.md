# Small-universe constructors over larger contexts

Issue #529 extends fixed-small-universe constructor admission to arbitrary
`Ξ : Context.{u+1}`. The original `sigmaCode`, `piCode`, and `pathCode` and their
raised-small-context clients remain available. The added Myers finite-label
chart-family consumer is tracked separately in
[#565](https://github.com/VladimirMarko/conaled/issues/565), at the owner's request;
that separation does not change #529's requirements.

## Construction and universes

`LargeFamilyClassification.lean` starts from a native family on the larger
context, an explicit `Type u` representative of each fiber, and an equivalence
to that native fiber. It constructs restriction maps by conjugation. Pullback to
small represented charts produces small families with selected lawful fillers.
The code map is assembled on those charts, using `SmallUniverse.chart` and its
restriction law. Its native decoder comparison includes the explicit `ULift`
and both inverse maps.

`LargeFamilyConstructors.lean` supplies these presentations for Σ, Π, and Path.
For Π, `functionValues_injective` restricts a Kripke function to cube morphisms
and small arguments. Every generalized restriction is recovered using its
category-of-elements equation. Thus the function space is small even when the
context is not. `Shrink` chooses a representative only after that injection has
proved smallness. Path fibers are subtypes of the represented function space.
No smallness of all types at the larger level is assumed.

The constructor providers are the existing `sigmaFilling`, `piFilling`, and
`pathFilling` used by `SmallFamilyConstructors`. Their law and substitution proofs
are reused. Input fillers are exactly `NativeDecode.filling` from `UniverseDecode`.
The new `LargeConstructors.Result` returns a code, its native decoder isomorphism,
and a lawful selected filler obtained by transporting the constructor's native
filler through that isomorphism. `construct_filling` recovers that entire native
operation by equality after transporting back.

There are two named selected operations on the output decoder: this returned
constructor filler and `NativeDecode.filling` of the output code. The present
interface does not assert that they are equal. The transport formulas compare
the universal decoder's operation with the constructor algorithm by a native
path, using #528's `NativeTransportComposition.sectionComparison`.

## Statement correspondence

| Public result | Mathematical statement | Contract |
| --- | --- | --- |
| `SmallPresentation.Data.code` | A small fiber presentation with a lawful native filler yields an actual code map on the original context. | Constructed natural transformation |
| `nativeIso` | Decoding that code recovers the presented native family. | Family isomorphism |
| `LargeConstructors.sigma`, `pi`, `path` | Admitted code inputs and typed Path endpoints yield constructor codes and their decoder/filler packages. | Constructed data; no output supplied as a premise |
| `sigmaSubstitution`, `piSubstitution`, `pathSubstitution` | Restricting a constructor is isomorphic to independently rebuilding it from restricted inputs. | Family isomorphism, not code equality |
| The three `Substitution_filling` theorems | Those comparisons preserve the entire returned selected filling operation. | Equality of filling records after isomorphism transport |
| `inputLine_zero`, `inputLine_one` | The actual code line of the supplied native universe path has its stated code endpoints. | Code equality |
| `Result.codePath_transport` | Transport along the constructed constructor code path is the actual universal decoder transport. | Equality of semantic maps |
| `pairAlongPath` | Universal transport of a decoded dependent pair agrees with filling its first component and then its second along that exact first section. | Native path with inverse decoder maps at both endpoints |
| `functionAlongPath` | Universal transport of a decoded dependent function agrees with the selected backwards-argument/dependent-result algorithm. | Native path with inverse decoder maps at both endpoints |

The function algorithm retains `FunctionComposition.comp`, the De Morgan scaling
used to extend composition to a whole filler, and its added initial face. It does
not replace the selected operation with a pointwise function or claim a strict
regularity law. `functionSection_selected` identifies the whole section with the
existing selected Π filler; its initial-value theorem retains the supplied
function. The pair formula likewise retains the whole dependent first filler,
the dependent display map into the second family, and its selected second filler.

Endpoint restrictions can also be compared with constructors independently
rebuilt at either endpoint using the corresponding substitution isomorphism.
The native comparisons do not imply host equality of arbitrary native paths or
source judgmental conversion.

## Checked clients and statement review

`Examples/CubicalLargeConstructors.lean` uses a context containing a natural
parameter and a generic universe code. Σ and Π are applied directly to that
code parameter. A separate dependent family reuses the existing `Fin(n+1)`
construction, where `n` is the actual decoded natural argument; its fibers at
0 and 1 are proved inequivalent by cardinality.

Successor and doubling substitutions are proved nonidentity. Each constructor
has a comparison with independent reconstruction after each substitution and
their composite. A base-count family separately makes the change observable:
at count 2, the two substitutions and their composite give fibers equivalent to
`Fin 4`, `Fin 5`, and `Fin 6`. The dependent-pair and dependent-function consumers
supply actual initial terms to the transport formulas. Their supplied path is
reflexive; the generic APIs quantify over arbitrary supplied universe paths.
The pre-existing whole-package successor ua client remains imported as a
nontrivial-path regression.

Empty-domain controls reject an inhabitant of the decoded empty sum and construct
the unique decoded function from an empty domain. An incompatible-endpoint control
maps the actual decoded Path through the natural observation and derives the
contradiction `0 = 1`; a reflexive endpoint case constructs a section. The
full-equivalence classifier beta law from `UnivalenceLawParameters` is exercised
on an actual substitution decoder isomorphism, retaining the selected contraction
record. `NaturalUnivalenceLaws` remains the owner of the chosen ua comparisons.

Statement review distinguishes the small fiber universe from the context
universe, checks all dependent display domains, and treats `Result.decoding`
as an output of the constructors. The smallness proof uses an injection with
proved injectivity, not an assumed representative for an arbitrary large type.
The negative cases concern the actual returned code and decoder maps.

## Source and acceptance boundary

The intake base is `8e68f4434e3b1dd367c2f6d14fbda057765a5e52`, current master at
intake. No cubical module or cubical example changed after the external handoff's
reviewed `08dbb2a71c8c9236ef2a1283e66f17b5622c3b9e`. The supplied
[checkpoint 129](../history/orbifold/agda-checkpoints/checkpoint-129/README.md)
is preserved with hashes and an archive-integrity inspection. Its checking
receipts remain external evidence; no Agda replay is claimed here.

This is native cubical semantic constructor admission. It does not admit ordinary
Agda Id/J, interpret the Myers Dedekind sheaf families, establish source judgmental
conversion, construct a smooth/cohesive model, or give cumulative universes,
resizing, or arbitrary HIT closure. A proposition-valued client needs its own
hypotheses. #422 retains unchanged-source admission and conversion obligations.

Completion requires the exact-candidate integrated build and exhaustive axiom
audit, followed by independent Standards and Spec review. Development elaboration
alone is not acceptance evidence.
