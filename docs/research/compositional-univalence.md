# Compositional univalence

Issue #528 makes the constructed cubical universe usable for chains of genuine
homotopy equivalences. It supplies native comparisons for identity, inversion
and composition, actual dependent transport laws, and a two-dimensional
comparison of the two bracketings of three representation changes.

## Operations and witnesses

`HomotopyEquivalenceComposition.lean` constructs an equivalence for the actual
composite `f ≫ g`. It extends partial fibers first through the contraction for
`g`, then through the contraction for `f`, and adjusts the resulting path with a
relative filler. Thus it uses general contractible fibers, including their
chosen data. It does not require an isomorphism presentation.

`DependentTransportComposition.lean` proves that transport along the existing
selected native concatenation agrees by a native path with sequential
transport. A lifted dependent square supplies the witness. The same section
comparison gives constant-path transport and both reversal laws without
assuming strict regularity of a chosen filler. Substitution preserves the
selected comparison bodies, including the chosen concatenation filler.

`CompositionalUnivalence.lean` applies these results to the actual universal
family. The orientations are:

| Comparison | From | To |
| --- | --- | --- |
| identity | `ua(id)` | reflexive universe path |
| inverse | `ua(selected inverse)` | reversed `ua(f)` |
| composition | `ua(f ≫ g)` | selected concatenation of `ua(f)` and `ua(g)` |
| dependent concatenation | transport along the concatenation | sequential transport |
| triple | left-associated concatenation of three ua paths | right-associated concatenation |

The selected inverse is transport along the reversed ua path. Both inverse
homotopies relate that exact selected map to the original arbitrary map. Its
complete equivalence witness comes from the accepted path-to-equivalence
construction. This establishes inversion for maps admitted by this universe;
it does not provide a separate family-level adjointification construction for
an arbitrary quasiinverse.

## Natural choices

The raw comparison construction passes through the accepted univalence
inverse laws. Their implementation does not expose all chosen-data
substitution equations. `NaturalUnivalenceLaws.lean` therefore chooses each
public identity, inverse and binary composition comparison once over a
parameter context, then specializes it to the supplied inputs.

`UnivalenceLawParameters.lean` classifies the codes and the complete internal
equivalence records. Its beta laws recover both the maps and their contraction
data. Its composition laws say that classifying after substitution is the same
as substituting the classifier. Consequently the public comparison bodies
commute exactly with recomputation after substitution. The comparison uses
the entire two-dimensional code-valued square; `comparisonSquare_injective`
shows that this retains the whole native two-path for fixed endpoints. The
canonical inner path-family reindexing is explicit. Endpoint lemmas connect
those bodies to the actual ua, selected inverse and existing concatenation.
This is a bounded construction for these operations at the existing universe
level; it does not establish broader universe closure or resizing.

## Three changes and its dimensional boundary

Both bracketings of three ua paths are compared to the ua of one genuine
triple composite equivalence. Reversing the first comparison and concatenating
the second produces `tripleComparison`, a native two-path. `tripleSquare`
exposes its body with the two bracketings on the bottom and top and the source
and target codes on the sides.

This proves one explicit two-dimensional coherence diagram. It does not prove
that independently selected two-paths are equal, a pentagon law, or an
unrestricted higher-coherence theorem. The two bracket paths commute with
substitution. Ordinary restriction of the triple two-path is available;
recomputation naturality of this additional selected two-path is not proved.
The public identity, inverse and binary composition comparisons have the
stronger exact recomputation laws described above.

## Consumers and limits

`Examples/CompositionalUnivalence.lean` uses actual concatenated universal
transport for Boolean negation twice and integer successor followed by
predecessor. It also applies the laws to the existing genuinely varying finite
family, using identity equivalences on its varying `Fin (n + 1)` fibers.
Discrete observations extract equalities of the observed values;
native path witnesses are not silently converted into host equality.

For three successive integer successors, the left and right bracketings use
the shared triple transport lemmas. The client need not construct the
intermediate fiber contractions, adjust the selected concatenation endpoint
casts, or build a map homotopy at each bracket. Those boundaries are handled
once by the reusable transport and univalence comparisons. Direct native
transport clients remain available.

A Boolean transposition path is distinguished from reflexivity through actual
transport observations: the two native path terms are unequal as host values.
This does not compute the fundamental group or rule out a native two-path
between them. The existing cubical path-conversion example also
supplies a native path whose selected endpoints are distinct as host values.
These controls separate native equality, discrete observation equality and
host equality. No source conversion rule or executable cost theorem follows
from these constructions.

Potential later work is a general family-level inverse construction and
higher coherence when a concrete consumer needs it. Neither is required to
use the operations and scoped diagram delivered here.
