# Alternatives and generality assessment

Retain the presented-discrete construction and the finite-groupoid nerve as useful bounded targets. Do not identify the nerve comparison with completion of the retained-square comparison in #574's restricted universe. The smallest promising stronger experiment is to derive a relative comparison for the exact finite-endpoint square using native univalence and discreteness of equivalence families. This avoids requiring a classifier for every Cartesian fibrant family. Its realization and coherence obligations remain open.

## Evidence and scope

This is an independent initial alternatives report. I received the shared brief and frozen proposal/addendum, inspected no other lens reports, and had no prior involvement in their preparation. I inspected source using `git show` at `4c81050dd2844c39bcfc551426f1e1cdbe3bcac1`; concurrent #599 edits were excluded. No repository edits, tracker writes, Lean builds, kernel checks, or computational experiments were performed. Arguments below are paper derivations supported by inspected declarations, not new checked theorems.

Input SHA-256:

- `proposal.md`: `86bb2558a0ed55255ce17a14e57a7aed18e2e0f9310030d5ce7312fedbdfc76b`
- `transport-addendum.md`: `07923de8cf70b059ff665864de8505be6775613cd2160ea230f2b58aae2fe0a5`
- `challenge-brief.md`: `f962444ec1f6c85652979a4572ebe3ff6ffee0e145e53c5123f6b082e5244f67`

Guidance consulted: architectural quality, domain guidance and glossary, ADR 0002, language direction and adoption criteria, EDD counterexample/scope checks, design-challenge, README environment/build policy, and prose guidance. External evidence is the primary [Cartesian cubical manuscript](https://www.cs.cmu.edu/~rwh/papers/uniform/uniform.pdf), especially its abstract and introduction on diagonal cofibrations and non-discrete univalent universes. That model is evidence that constant-code failure is not a general impossibility; it does not supply the proposed cross-category comparison. All specific nerve and alternative constructions here are direct arguments.

## What the alternatives buy

| Route | Useful capability | Remaining selected-square obligation |
| --- | --- | --- |
| Presented-discrete families | Unique filling of every admitted target box, including unlifted boxes; specialized package comparison | No nonconstant code paths in a constant classifier, so cannot express the selected ua square there |
| Finite groupoid nerve with tuple decoder | All-box code filling, discrete decoded families, native permutation paths, and a bounded ua | Equality after Q compares entire nerve cubes but provides no comparison with the retained RU square |
| Finite-endpoint native relative comparison | Potentially compares the actual retained square with a specified realization of independent recomputation | Must construct the realization, boundary alignments and relative three-path with substitution laws |
| General Cartesian classifier and bridge | Broad ua/classification beyond vertex local systems | Substantial additional classification and cross-model coherence, unnecessary to settle this one finite example |

The strongest evidence for keeping the nerve is that its target operations can be specified without source-lift premises. The arrow formula constructs the target cube as an actual functor; it is not merely a list of compatible endpoint observations. It also retains Boolean negation and the order of the two Fin3 swaps. A constant-code replacement would lose a required distinction which this construction preserves.

The presented-discrete route should be the first implementation target for the actual Fin3/Phase package. Its uniqueness argument applies to all lawful fillers of that family, so it can compare independently chosen operations without importing a source choice. Finite cardinality is unnecessary here: the dependency-bearing package can use the proposed presentation by a general small set. Do not force that package into the finite-code universe simply because its carrier is finite. Propositions and function fields require their actual dependent construction and the specialized Pi inverse.

## All-box and transport checks

I found no paper-level obstruction to the nerve filler formula. At a base vertex v, the source graph uses `(v,r_v)`; hence its arrow between v and w is obtained with both conjugating arrows identities even when `r_v != r_w`. This addresses variable source terms, not only fixed endpoint Kan operations.

Tube agreement needs an argument at every cube mapping into the tube. All vertices of such a cube belong to the tube, so every object is the prescribed tube object. Tube functoriality and source-graph agreement identify every prescribed arrow with the conjugation formula. Because nerve elements are functors on vertex groupoids, this proves equality of those entire restrictions. It does not assert that vertex membership implies membership of the original generic cube.

A useful regression fixture is `phi = (x=0) OR (x=1)` on a one-cube: both vertices satisfy phi while its generic Cartesian variable does not. The filler can nevertheless extend the two tube lines because its unconstrained cross-vertex arrows are supplied by B. Use this fixture together with the diagonal `x=y`, the varying source `r=x`, endpoint substitutions and variable duplication. A test that checks only phi's truth at generic cubes would miss the actual construction.

The transport addendum supplies meaningful evidence for Q's coherence. `DependentTransportComposition.lean:373–405` constructs a square lift and compares the actual upper transport with the prescribed right endpoint; lines 407–436 prove reindexing of the lift/top body. The proposed square has left v, bottom v→a, right a→w and top v→w. At t=1 the coordinate conditional interpolates a to w; at t=0 both entries equal v. The algebra uses the absorption factor `(p OR q)` and does not require excluded middle for interval expressions. Applying discreteness only at the resulting endpoint is sufficient for equality of transport functions. Pullback casts and the pathToMap identification remain proof obligations, but the addendum makes this a bounded derivation rather than an assumed coherence field.

## Q changes the observation contract

The distinction is exact:

1. #574 retains a source code-valued square as a whole cube of RU, with an inverse body comparison.
2. Q observes vertex codes and transport bijections. Its output is a whole functor `V_2 → FinSetIso`.
3. Equality of this functor with native target recomputation follows from equality of compatible boundary data because this particular target's two-cubes are boundary-determined.
4. No supplied construction identifies that equality with a relative comparison between the original RU square and an RU realization of recomputation.

Thus Q is not merely a numerical observation, but it is a different observation contract. Any source squares having the same vertex codes and transport bijections are identified by Q, regardless of their other code-valued interior data. I have not constructed two distinct such source squares, so this is a statement of Q's observational scope, not a proved counterexample to injectivity in the selected fragment. Conversely, absence of a counterexample does not prove recovery or the required relative comparison.

A native relative comparison can suffice under #600; literal injectivity or equality of independent chosen fillers need not be imposed. Nevertheless, the candidate must name the common family in which that comparison lives and exhibit its boundary conditions. Equality in N(G) alone cannot inhabit a path type in RU. Treat the current Q equation as a separate, useful theorem and leave the stronger selected-square item open. Do not silently close it by redefining the target observation to be Q.

Keeping the pair `(restricted source body, Q body)` also fails to finish the task automatically: independently filling such pairs would require a source-component filler and compatibility for arbitrary target boxes. Merely storing the retained witness beside independent recomputation supplies neither.

## A smaller stronger route worth testing

There is a concrete alternative between Q-only equality and a classifier for all target families. For finite constant endpoint codes a,c, attempt the following bounded derivation:

1. Show the entire source equivalence family between their decoders is discrete, including equivalence records, not only the underlying maps.
2. Use `NativeUnivalence.univalence` (`NativeUnivalence.lean:22`) to transfer that discreteness to the appropriate truncation statement for `paths a c`. This is already an equivalence of the actual path-to-equivalence map. `leftInverseAt` at line 47 explicitly compares arbitrary native paths with their ua reconstruction; the alternative need not assume every path was originally produced by ua.
3. Derive that two specified comparisons between the same p and q admit a native path relative to p and q. Evaluated as universe bodies, this is the required relative three-dimensional witness, not just an unbased homotopy.
4. Apply it to the actual `swapComposition` and a specified source realization of the independently recomputed finite target square. Use the same frozen composite and concatenation boundaries, or supply explicit boundary alignment comparisons and the corresponding coherence before forming the relative path.
5. Restrict that chosen witness to C and prove its substitution/composition laws.

This is a proposed derivation, not a theorem checked in this review. In particular, a homotopy equivalence with a discrete family gives a homotopical truncation claim, not strict equality of all original path bodies. It must produce the required native witnesses with endpoints intact. The existing `NativeUniverseSquares.comparisonSquare_injective` concerns recovery from an actual full body and cannot replace this derivation.

The missing realization is substantive but bounded: realize the target finite bijection paths by the existing ua, realize the selected composition comparison with explicit boundary identifications, and compare it to the frozen square. First test this on the actual Fin3 square and arbitrary base substitution. A natural classifier map on all N(G) cubes would be stronger and useful, but should not be demanded before determining whether this bounded realization suffices. Nor should this alternative be rejected because the map is absent today. The comparison depends on constructing it, not on the age of an interface.

For a complete general N(G)→RU bridge, the tuple decoder suggests the data to classify, but a C-presheaf family cannot simply be passed to the existing D-based source universe. Extending its vertex-local-system construction to D and supplying the relevant source filling/classification data is one possible route. The challenge then becomes coherent realization rather than an all-foundation bridge. No claim that this has been constructed is warranted.

## Corrections and discriminating tests

Publish the all-box constructions and Q comparison with explicit separate scopes. Label endpoint-Kan versus variable-source/diagonal-Kan, and keep the general package outside the finite-code classification claim. Preserve #599's faithful recovery independently of Q.

The decisive next test is to write the type of the relative three-path for the exact retained `comparisonSquare swapComposition` and an independently recomputed target square with a specified realization. If only `Q S = S_target` can be typed, the stronger item remains open. If finite-endpoint univalence supplies this relative witness with four fixed side faces and both chosen square faces, the bounded route may discharge the selected requirement without a general classifier.

Check Q on reversal and on a noncanonical substituted dimension path before claiming its general naturality; check all-box target filling on the endpoint-union and diagonal fixtures above. Finally, test the comparison on all five package fields at generalized arguments and on both inverse recipes independently. Boolean and Fin3 numerical controls remain necessary separation checks but cannot decide whether the selected square interior was retained.
