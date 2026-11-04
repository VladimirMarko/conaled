# Indexed constructor and observer laws

Issue [#271](https://github.com/VladimirMarko/conaled/issues/271) extends the
compositional contract to families over a fixed index type. The checked result
covers finite indexed constructor terms, index-changing observations, and
substitution by compatible compound terms. It includes vectors and an exact
parser/trie interpretation. [#274](https://github.com/VladimirMarko/conaled/issues/274)
adds depth restriction and recovers all native composite parser operations.

## Contract and evidence

[IndexedCompositional](../../SquareKit/IndexedCompositional.lean) assigns each
constructor an output index and finitely many child indices. A behavior at
index `i` returns `Output i` and accepts `Request i`; a request chooses the
successor index `next i request`. A transition template contains slots for
original children and requested successors, each at its actual index.

`Rule.layer_natural` proves that templates commute with maps of families.
`Rule.Compatible` separately requires output agreement and transition
agreement with a native interpretation. `Rule.fold_morphism` lifts those local
obligations to all finite terms. `bind_morphism`, `join_morphism`, and
`map_morphism` cover compatible substitution, flattening, and leaf maps.
`Behavior.observe_morphism` preserves finite typed observation paths.
Naturality alone does not establish meaning preservation.

[The vector application](../../Examples/IndexedCompositional.lean) interprets
terms as actual `Fin n → Nat` vectors. Cons changes the index from `n` to
`n+1`; tail reverses that change. Nil has no tail request. Doubling observes
a successor and rebuilds a constructor around it. Checked coordinate
observations distinguish 7, 11 and 22, including nested terms and substitution
of a leaf by its full cons expansion. A deliberately wrong cons rule adds one
to the head: its naturality still holds, but compatibility would imply `7 = 8`.
This supplies a failed semantic obligation independent of typing.

[The parser interpretation](../../Applications/Languages/IndexedCompositional.lean)
uses indices `(P,n)`, with `P : List α → Type` and finite depth `n`. An output
is `Decision (P [])`; a letter advances to `(derivative P a,n-1)`. At depth
zero there are no requests. The native interpretations are the existing
`Parser P` and `WitnessTrie P n`, with union, witness transport, intersection,
scaling, concatenation and star. A `cut` constructor restricts depth without
consuming a letter. Both local compatibility proofs feed the shared fold theorem.
`recovered` equates native trie lookup with native parsing for every admitted
word and every finite constructor term with parser leaves. `recovered_trie`
also admits selected trie leaves whose choices differ from the standard parser.

[Checked parser compositions](../../Examples/IndexedParserComposition.lean)
combine union with a sum-swapping witness isomorphism. A nonempty-word parser
example uses `recovered`. Two depth-zero trie leaves choose different nullable
star witnesses: zero empty factors versus one empty factor. After the same
compound construction and transport, `recovered_trie` preserves their exact,
distinct `Decision` results, although their Boolean tests agree. This is a
use of actual star witnesses; the standard parser does not select both witnesses.
The extended examples additionally use nullable star, concatenation, scalar
evidence, intersection and transport in one compound expression.

[The ordinary bridge](../../SquareKit/IndexedCompositionalOrdinary.lean) embeds
#268's terms and retained/successor slots into the singleton-index instance.
It proves bind, fold, output and transition recovery, translates the original
compatibility hypotheses, and derives the original fold morphism through the
indexed theorem. Its mixed fixture retains one child and advances another,
with different current-letter successor results. Existing direct APIs remain
available; callers need not encode ordinary programs to use them.

## Scope, equality, and author costs

Indices are fixed and terms are intrinsically sorted. Substitution must preserve
the index of each leaf. Constructor transition templates must produce exactly
the requested successor index; heterogeneous equality is not silently erased.
In the parser application an explicit word-indexed `Iso` transports selected
witnesses using the native `Decision.map`. General changes of index base,
dependent binders, state-dependent successor indices, quotient equality, and
coinductive productivity are outside this contract.

A new signature author supplies child indices, outputs, request-index changes,
and typed transition templates, then proves two native compatibility equations.
The shared induction replaces a per-interpretation whole-term proof. The vector
client still supplies coordinate observation lemmas; the parser client supplies
word reading and native lookup/parse recovery. Those application obligations
are not removed by the framework. Finite arity avoids a general indexed
polynomial interface at the cost of excluding infinitely branching constructors.

The source-table transposition work supplies alternate presentations of
constructor/observer rows. It does not imply substitution or compositional
semantic preservation. This contract supplies those laws once local equations
hold. Conversely, it does not replace the direct row interfaces.

Full bounded trie concatenation and star retain operands whose available depth
must decrease even when no letter is consumed from that operand. Original-child
slots retain their original index, and successor slots consume a request. A
depth restriction constructor supplies that missing operation. `cut(P,n)` takes
a child at `(P,n+1)` and returns `(P,n)`. Its output is unchanged; each successor
cuts the corresponding child successor. The parser interpretation is identity,
while the trie interpretation is native `truncate`.

The concat template transports a union of the nullable-scaled right derivative
and concatenation of the left derivative with the cut original right operand.
The star template preserves `derivativeStarIso` in its native orientation,
including the list of non-consuming parses, and selects the empty list exactly
as the native parser does. Its recursive star receives the cut original operand.
No restriction on operand nullability is introduced.

`WitnessTrie.ext_lookup` derives whole-trie equality from exact bounded decisions.
`recovered_tree` consequently recovers the full native interpretation of every
finite term through `recovered`. `recovered_concat` and `recovered_star` recover
the direct `unfold_concat` and `unfold_star` equalities without using those
whole-operation theorems as compatibility hypotheses. `truncate_self` and
`truncate_comp` prove restriction coherence; `fold_cut_twice` connects repeated
signature restriction to that native coherence theorem.

The checked cases include a nullable operand, depth zero, a nonempty word at
the depth boundary, and repeated cuts. A positive-depth trie deliberately
selects one empty star factor. Cutting preserves that choice. Resetting it to
the standard empty list violates the exact output compatibility equation,
although the Boolean tests agree. This diagnoses lost witness information
rather than a type error.

The extension adds no shared-framework definitions or new whole-term induction.
Authors still write explicit typed templates and disambiguate child slots in
Lean; the nested concat/star templates expose this cost. Native callers keep
their existing operations. Independent author trials and the equation-view
bridge remain under #235 and the Construction and observation follow-ups.
There is no performance, sharing, infinite productivity or operational adequacy
claim: depth restriction supplies a semantic operation, not a caching policy.

## Primary-source comparison

Turi and Plotkin's [*Towards a Mathematical Operational Semantics*](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf),
section 3 and equation (8), permits multi-sorted power categories. It motivates
moving the ordinary construction to families and retaining the distinction
between syntax, behavior, and compatibility. The Lean proof above is a direct
bounded construction; this note does not claim a formalization of their full
bialgebraic semantics.

Gambino and Kock's [*Polynomial Functors and Polynomial Monads*](https://arxiv.org/pdf/0906.4931),
v2 introduction equation (2) and section 1.1, describes indexed polynomial
functors through families and slices. Section 4 adds hypotheses for free monads;
sections 4.6–4.8 distinguish change-of-base properties and warn that the relevant
left adjoint is not fibred in general. This supports treating fixed families
and arbitrary fibred transport as different design commitments.

Gambino and Hyland's [*Wellfounded Trees and Dependent Polynomial Functors*](https://www.irif.fr/~mellies/mpri/mpri-ens/articles/gambino-hyland-polynomial-functors.pdf),
section 5.1, theorem 14 in that manuscript, works with locally cartesian closed
categories and W-types. Those assumptions support a broader dependent account;
they do not supply the native parser equations proved here. The selected
finite-family interface answers the present vector and witness-sensitive
obligations. Generalizing it requires another application that needs the
additional dependent structure and states its preservation laws.

The [equation-view bridge](equation-composition-bridge.md) generates these vector
rules and a union/scalar parser fragment from binding-free equation cells.
It proves row/column presentation independence separately from semantic
compatibility and identifies a child-inspection cell that cannot factor through
immediate outputs.
