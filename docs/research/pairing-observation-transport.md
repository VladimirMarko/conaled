# Pairing and observation transport

Assessment for [#269](https://github.com/VladimirMarko/conaled/issues/269),
2026-11-04, in Construction and observation. Repository evidence was inspected
at `50cdd4b3cf78e04c245f0d90a3d252ed91aaa2a6`.

**Recommendation:** reuse exact squares and explicit dependent comparisons.
A Chu morphism gives a useful contract for moving representations forward and
queries backward. The parser and vector cases below fit bounded instances,
but do not justify adopting a universal Chu framework. Keeping a common result
object is possible for one language's dependent decisions; changing the
language or forgetting witnesses exposes additional obligations.

This is a research assessment. The displayed constructions and calculations
are handwritten mathematical examples, not new Lean definitions or checked
claims. Links identify existing checked statements used to test the proposed
interpretation. No new formal or runtime guarantee is introduced.

## Source definitions and assumptions

Barr's [*The Chu Construction*](https://www.math.mcgill.ca/barr/ftp/pdffiles/chucon.pdf),
§§2–4, develops closed self-dual structure through modules; its non-symmetric
construction uses a biclosed monoidal base and graded duals. The module
constructions in §3 use equalizers and coequalizers. Its §5 cofree results add
local presentability and a specified class of functors. None is a theorem that
our finite parser syntax represents all possible observations.

For the pairing and morphism definition, Barr's
[*The Separated Extensional Chu Category*](https://www.math.mcgill.ca/barr/papers/chuse.pdf),
§1.1, is more direct: the base is symmetric monoidal closed, objects carry a
pairing into a chosen object, and arrows have opposite variance in the two
components. Component exchange gives contravariant equivalence. Pullbacks
supply the further closed monoidal construction. Section 1.2 defines separated
and extensional objects using a factorization system; these properties are
additional conditions, not assumptions in the basic morphism definition.

The remainder specializes to sets/types and functions with a fixed result
object `R`. It uses neither linear-logic interpretation, tensor rules, cofree
coalgebras nor a change to Lean's ambient logic. Calling the two components
representations and observations is our application of that definition.

## The compatibility calculation

Take `e : X × Y → R` and `e' : X' × Y' → R`. A candidate translation has

```text
f : X → X'                 representation transport
g : Y' → Y                query transport
e'(f(x), y') = e(x, g(y')) for every x and y'.
```

The query map must depend only on the target query. A query translation needing
the particular source state is outside this format. Also, only queries in the
image of `g` are compared; the equation does not assert that the target sees
every distinction available in `Y`.

For a second compatible pair `f' : X' → X''`, `g' : Y'' → Y'`, the composite is
`(f' ∘ f, g ∘ g')`. Its obligation follows by this typed calculation:

```text
e''(f'(f(x)), y'') = e'(f(x), g'(y'')) = e(x, g(g'(y''))).
```

Identity maps satisfy the equation, and associativity follows from function
composition. No injectivity or inverse of `f` or `g` is required.

This fits [Squares](../../Squares.lean) by currying the pairings:

```text
A := Rep X  (Y  → R) (fun x y  => e(x,y))
B := Rep X' (Y' → R) (fun x y' => e'(x,y'))
impl := f
spec := fun profile y' => profile (g(y')).
```

`Square.commutes`, pointwise, is the desired equation; `Squares.compose`
composes the profiles by successive precomposition. This is a paper adapter
into an existing interface, not a newly implemented adapter. A Lean realization
must also choose compatible universes or insert explicit lifts; the existing
`Rep` places its two carriers in one universe. Conversely, an
arbitrary square between these representations need not come from a query
map: its `spec` may combine observations or change results. Identifying which
profile maps arise from precomposition is extra structure.

[HomVariance.map](../../SquareKit/Variance.lean) already implements
pre/postcomposition, with `ident`, `comp` and `interpret` laws. It supplies the
variance calculation, but does not supply `f`, `g`, their interaction equation,
or admissibility of an observation. `Designated` and `PreservedBy` keep such
selection obligations separate. [Relational.RelSquare](../../SquareKit/Relations.lean)
uses two forward maps and one-way relation preservation. A Chu equation has a
backward query map and exact agreement. Replacing the latter by implication or
an arbitrary relation changes the contract; the names are not interchangeable.

## A dependent parser pairing without witness erasure

Fix alphabet `α`, its decidable equality, a type-valued language `P`, and a
finite depth `n`. Consider the following paper instance:

```text
X  = Parser P
Y  = List α
X' = WitnessTrie P n
Y' = { w : List α // w.length ≤ n }
R  = Σ w : List α, Decision (P w)

f(p)       = WitnessTrie.unfold p n
g(w,h)     = w
e(p,w)     = ⟨w, p.parse w⟩
e'(t,(w,h)) = ⟨w, t.lookup w h⟩.
```

Here `R` is one fixed type despite its dependent second component. Both sides
of compatibility have the *same word tag*. The checked
[`WitnessTrie.lookup_unfold`](../../Applications/Languages/WitnessTrie.lean)
provides equality of their exact decisions. Sigma packaging therefore retains
the chosen successful witness or refutation and the word determining its type.
It does not select a common untyped payload or enumerate all parses. Decoding a
package at a specified word requires its tag equality and the corresponding
transport; in this instance the tags already agree definitionally.

Truncation gives a second stage: for `k ≤ n`, map `WitnessTrie P n` to
`WitnessTrie P k` and transport bounded queries by inclusion. Use the same
`R`, tagging by the word alone, rather than including the depth proof in the
result tag. The checked `lookup_truncate` equation provides the next
compatibility obligation; `truncate_unfold` identifies the composite state map
with unfolding directly to `k`. Thus the proposed pairing composition recovers
an existing composite client without strengthening its observation bound.
This loses access to longer queries, not information within an admitted result.

A discriminating case is already checked in
[`LanguageCoalgebraExamples.Parses`](../../Examples/LanguageCoalgebra.lean).
For `Star epsilon []`, `noneEmpty` and `oneEmpty` correspond under
`nullableStarIso` to the empty list and a singleton list of empty parses.
`first` and `second` are depth-zero tries choosing those different witnesses.
Their lookup decisions differ although their Boolean tests agree. The tagged
pairing preserves this distinction because both tags are `[]` and their payloads
remain unequal. Using `Bool` as `R` would fail this test. In particular, no map
from the shared Boolean result can reconstruct both selected decisions.
[`ParserBridge.recognizers_agree`](../../Applications/Languages/ParserBridge.lean)
establishes the separate Boolean bridge; it does not justify that reconstruction.

### Where packaging stops solving the problem

The instance fixes `P`. If a language is transported to `Q` by
`i_w : P w ≃ Q w`, exact decisions live in different fibers. A common total
result type tagging the language, word and decision can retain the data, but
literal equality now requires equality of language tags. An isomorphism
`P w ≃ Q w` is not that equality. Tagging by a representation rather than its
semantic index would be even more restrictive: translating the representation
would change the tag despite preserving its observations.

One can instead use the existing `Decision.map` in
[Parser](../../Applications/Languages/Parser.lean) with the chosen isomorphism
and compare after that map, or formulate a relation between the two result families. Those are
explicitly different contracts from equality into an unchanged `R`. A result
conversion `h : R → R'` leads to

```text
e'(f(x), y') = h(e(x, g(y'))).
```

For witness erasure, `h` is not invertible. For semantic isomorphisms, its
chosen forward/backward maps and their laws matter. Taking a large disjoint
union does not prove either contract automatically. The existing
[`DependentSquares`](../../Dependent.lean) split family model and transport
certificates retain dependent typing; [ADR 0002](../adr/0002-relations-and-synchronization.md)
already rejects using relations to conceal an ill-typed dependent substitution.
[ADR 0004](../adr/0004-convolution-and-languages.md) requires the witness boundary.
These are the interfaces and constraints to recover in a later comparison.

## Independent indexed vector case

The existing [vector transposition examples](../../Examples/EquationTranspose.lean)
use `Fin n → Nat`, with `nil`, `cons`, `repeat`, indexed lookup and size.
Their `Prim.cons` interpretation is `Fin.cases`; checked examples recover head
`7`, tail `11`, the size of a repeated vector, and impossibility of empty lookup.
These definitions supply an independent test of query variance.

For each `n`, consider this paper pairing for the actual `cons` operation:

```text
X  = Nat × (Fin n → Nat)       Y  = Unit ⊕ Fin n
X' = Fin (n+1) → Nat          Y' = Fin (n+1)
R  = Nat
f(a,v) = Fin.cases a v
g(0) = inl ();                g(i+1) = inr i
e((a,v),inl ()) = a;          e((a,v),inr i) = v i
e'(v',j) = v' j.
```

Compatibility has two cases, evaluating respectively to `a` and `v i` by the
existing interpretation of `cons`. With `n=1`, `a=7`, `v=fun _ => 11`, they
recover the checked expected answers above. At `n=0`, the source tail has no
query and the target has just the head query. There is no fabricated `Fin 0`
value or index erasure. The construction changes vector length while keeping
an ordinary fixed result type; that does not solve the dependent-output part
of [#271](https://github.com/VladimirMarko/conaled/issues/271).

Restriction also has a cost: a source query family containing only the head
cannot support this `cons` map with *all* target lookups. For `n=1`, fix head
`7` and vary the tail between `11` and `12`. The sole source observation stays
`7` while the target tail answer changes. No state-independent `g` into that
singleton query set satisfies the equation. Enlarging the source query family
is a semantic obligation, not bookkeeping solved by naming a duality.

## Four different reversal and recovery claims

| Claim | What would establish it | Evidence here |
|---|---|---|
| Reverse program organization | Inverse syntax maps and interpretation preservation | Checked `transpose`/`untranspose` in [EquationTranspose](../../SquareKit/EquationTranspose.lean); restricted typed cells. |
| Embed representations into profiles | Injectivity of `x ↦ (y ↦ e(x,y))` | Requires observations separating representations. The Boolean parser counterexample fails it. |
| Identify observationally equal representations | An explicitly chosen equivalence and a factorization through its quotient | Relative to the chosen observations; richer queries need a new descent check, owned by #267. |
| Dual equivalence | Contravariant functors and inverse laws on the specified categories | Chu component exchange has this structure. It does not identify `X` with `Y`, nor syntax with every function `Y → R`. |

In Set, the separated/extensional conditions of Barr §1.2 specialize to
injectivity of the two profile maps. For surjectivity of the representation
profile map, every permitted profile must have a representing value. These are
distinct requirements. A paper counterexample using the existing `repeat`
interpretation is `X=Nat`, `Y=Fin 2`, `e(a,i)=a`: representations are separated,
but the profile returning `7` at zero and `11` at one is not represented.
Restricting the behavior space to constant profiles can repair surjectivity;
it changes the proposed target rather than proving all behaviors representable.

Component exchange sends `(X,Y,e)` to `(Y,X,fun(y,x) => e(x,y))` and a map
`(f,g)` to `(g,f)` in the reverse direction. Applying it twice returns the
same pairing data. This explains categorical duality, with no requirement that
an individual space be isomorphic to its dual. An equivalence between a selected
syntax category and a behavior category would still need its own interpretation,
reconstruction, morphism action and inverse laws. Neither the program-view
involution nor the bounded observation maps provide them.

## Fit, author obligations and remaining ownership

| Candidate route | Benefit for these tasks | Cost or mismatch | Recommendation |
|---|---|---|---|
| Direct parser/trie laws | Exact dependent decisions and bounds are already exposed | Separate unfolding/truncation statements | Preserve as public specializations. |
| Curried exact squares | Reuses composition and permits redundant representations | Must retain which profile maps arise from query maps; sigma constructors and tag transports for dependent outputs | Reuse for a bounded adapter if a caller needs it. |
| Hom variance and designated maps | Existing precomposition laws and explicit admissibility | Does not derive compatibility or decide which observers descend | Reuse #257; coordinate the descent obligation with #267. |
| Relational/dependent contracts | Can express changed fibers and noninvertible result maps | Exact equality, implication and witness transport must remain distinguishable | Compare against native dependent certificates before adding an interface. |
| Full Chu structure | Gives coherent component reversal and potential closed structure | Extra ambient structure; fixed-result and query-independence constraints; no observed need for its tensor/internal hom in these clients | Decline adoption for this slice. |

The concrete author tasks were: expose parser unfolding and subsequent depth
restriction through one composition rule; express vector construction by query
translation; retain the nullable-star distinction; and explain a language-index
change. Direct proofs require the existing lookup laws and dependent types.
The pairing route adds query carriers, backward maps, result packaging and
profile decoders. The benefit is a single compositional statement of interaction;
the added burden is preserving fibers and the precomposition restriction.
This is an interface analysis, not an independent author trial or a measured
productivity claim. No Lean limitation has been established by it.

No new formal follow-up is warranted solely to package the equations above:
the two positive clients already have checked laws, while a universal package
would add structure unused by them. [#235](https://github.com/VladimirMarko/conaled/issues/235)
owns reconsideration if another client needs reusable query-transport
composition, particularly with changed result fibers. Such a proposal must
recover `lookup_unfold` followed by `lookup_truncate`, the indexed vector case,
and the nullable-star failure case, while exposing result transport and query
admissibility. This is a condition for a future spec, not an implementation
assignment created by this assessment.

[#267](https://github.com/VladimirMarko/conaled/issues/267) retains quotient and
observer-extension laws; [#262](https://github.com/VladimirMarko/conaled/issues/262)
retains semantic-type admissibility; #271 retains indexed composition. The
[#268 result](compositional-constructor-observer-laws.md) proves local-to-composite
compatibility under its own template law. A Chu-map equation for a whole
translation does not derive that induction or substitution theorem from local
constructor clauses. This assessment neither duplicates nor replaces those
scope owners.

The source reading covers the cited Chu definitions and their ambient
assumptions. It does not settle enriched or fibred Chu variants, Dialectica
constructions, or alternative internal-language foundations. Those remain
external comparisons under #235; the present decision is limited to the two
clients and their discriminating cases, not a ranking of all duality theories.
