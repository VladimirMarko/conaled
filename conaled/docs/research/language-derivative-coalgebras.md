# Language derivatives as finite-word behavior

Experiment for [#255](https://github.com/VladimirMarko/conaled/issues/255),
2026-10-30. Finite-word behavior is a final output/transition coalgebra.
Weighted operations and indexed parse tries recover the existing semantics,
including exact selected witnesses. This does not yet transpose source
programs; [#256](https://github.com/VladimirMarko/conaled/issues/256) owns that
separate question.

## The generic semantic contract

[WordCoalgebra](../../SquareKit/WordCoalgebra.lean) defines
`B A O X = O × (A → X)` and `Behavior A O = List A → O`, with arbitrary alphabet,
output and state universes. `run_morphism` proves that running a state preserves
its output and transitions. `unique` proves that any map preserving those two
observations equals `run`, by induction on finite words. No semiring,
decidability, finite-state or injective representation assumption is needed.
The direct semantic-law package is `Morphism c final meaning`; `correct`
recovers its all-word observation theorem.

`zip` combines independent state machines through an arbitrary binary output
function, and `mapOutput` adds a unary output function. Their run theorems
establish pointwise behavior. A finite `Trie A O n` stores observations through
depth `n`; `lookup_unfold` and `truncate_unfold` prove observation and restriction
compatibility. Words beyond a finite snapshot's depth return `none`.

[LanguageCoalgebra](../../Applications/Languages/Coalgebra.lean) embeds the old
Boolean `Machine` without changing its state, nullable observation or next
function. `Boolean.run_eq` is exact run equality; `recognizes` recovers the
existing correctness theorem under its original assumptions. Boolean union
uses generic `zip` with `or`; intersection agrees with the old product machine.
The old machine/parser modules and their public contracts remain available.

## Direct equations and abstract GSOS

Elliott's [§§4.2–4.3, Figures 5–9](https://conal.net/papers/language-derivatives/paper.pdf)
organizes the same clauses differently: symbolic representations make language
operations constructors, while automatic representations make nullable and
derivative observations available directly. This does not identify every
symbolic term with every trie. The original right operand of concatenation
must remain available. Figure 8's termination override is repaired by Figure
9's size-indexed trie, with derivatives at smaller sizes and parsing at infinite
size. Our natural-number snapshots prove bounded observation contracts; they
do not implement that infinite-sized representation.

Turi–Plotkin's [§3 equation (8), §5 Theorem 5.1 and Definition
5.2](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf) use the
abstract rule shape `Σ(X × B X) → B(T X)`, natural in `X`, where `T` is the free
term monad for the signature. `X × B X` supplies both operands and their
one-step observations. Structural recursion computes a term's observation
while retaining its subterms. Flattening rule-produced terms uses the monad
multiplication. Naturality is an additional hypothesis for their lifting
result; a correct handler on one carrier is not automatically such a natural
transformation. Their later categorical duality is also distinct from
Elliott's rearrangement of source definitions.

The local bounded construction uses the binding-free signature of leaf states,
addition, left scaling and concatenation. `Term.bind` substitutes leaf terms;
its leaf, identity and associativity laws are proved without a semiring
assumption. The observation/derivative handlers recurse over the old term,
constructing successor terms without recursively evaluating those new terms.
The rules for concatenation are:

```text
output(p · q) = output(p) * output(q)
nextₐ(p · q) = scale(output(p), nextₐ(q)) + nextₐ(p) · q
```

`Weighted.output_sound` and `next_sound` prove that these handlers preserve
`Convolution.Series` semantics, given only the seed coalgebra's semantic
morphism. `interpretation` packages those equations, and the generic finality
result supplies `run_correct`. Coefficients require `Semiring R`; multiplication
need not commute. The second summand retains `q`, and scaling multiplies its
coefficient on the left. This reuses `Convolution.derivative_mul`, whose
finite-split semantics is already established.

We have not implemented a generic signature functor, natural transformation or
monad lifting for arbitrary signatures. The free terms and their handlers are
specific to this demonstrated algebra, while finality and snapshot observation
are shared. Extending an arbitrary equation table still requires total
handlers and proofs of its actual semantic equations. Nothing here establishes
unbounded productivity for an arbitrary recursive operation specification.

## Indexed automatic parsing

[WitnessTrie](../../Applications/Languages/WitnessTrie.lean) stores a
`Decision (P [])` at its root and, at positive depth, children indexed by
`derivative P a`. Bounded lookup returns `Decision (P word)`: an actual selected
witness or a refutation. `lookup_unfold` proves equality with the symbolic
parser's entire decision, not only its Boolean test. `lookup_truncate` retains
the same decision when restricting a snapshot, and `truncate_unfold` commutes
restriction with symbolic unfolding.

Direct trie operations implement union, intersection, scalar evidence,
concatenation, star and transport through existing witness isomorphisms.
Concatenation uses `nullableConcatIso` and `derivativeConcatIso`; star uses
`derivativeStarIso`, whose index retains lists of empty parses. Recursion
strictly decreases the trie depth. The unchanged operand is truncated to that
smaller depth instead of being discarded or recursed on at unchanged depth.
The `unfold_union`, `unfold_intersection`, `unfold_scale`, `unfold_transport`,
`unfold_concat` and `unfold_star` theorems prove exact agreement with symbolic
construction. Combined with lookup, they establish selected-decision agreement
at every finite word admitted by the depth bound.

An arbitrary trie may store a different valid selection from the parser's.
The checked nullable-star example takes an epsilon witness `e`: the
`nullableStarIso` images of `[]` and `[e]` are distinct witnesses for the empty
word. Two depth-zero tries return those respective witnesses unchanged.
Their Boolean tests are equal. The symbolic star parser selects the empty
list; its agreement theorem does not claim it selects or enumerates all parses.
This distinguishes selected-witness equality, inhabitation agreement and
information lost by Boolean erasure.

## Extension and checked specializations

The weighted signature is extended with pointwise multiplication, distinct
from convolution. All old constructors accept extended operands, so the new
operation can also occur beneath old concatenations. `Extended.old` embeds the
old syntax. `old_output`, `old_next` and `old_meaning` recover its equations;
`old_morphism` and `old_recovered` recover its old machine and all-word behavior.
`extended_correct` proves the new mixed terms' semantics. Adding this operation
requires its output and derivative proofs; the generic finality theorem and
the old client assumptions do not change.

[Checked cases](../../Examples/LanguageCoalgebra.lean) include a natural-number
counter, uniqueness for arbitrary competing interpretations, arbitrary-depth
truncation, and noncommuting matrix coefficients. For two chosen matrix units,
the `(0,0)` entry of the forward product is `1`, while the reverse product's
entry is `0`; the one-character convolution coefficient is `2`. Thus the
specialization can detect reversed coefficient order. Universal examples also
connect weighted run correctness to bounded lookup and exercise a new
pointwise operation beneath an old concatenation. The witness examples retain
the distinct nullable-star selections and specialize the all-word concat/star
agreement theorems.

## What remains setting-specific

| Construction | Assumptions and remaining limits |
| --- | --- |
| Final behavior and pointwise operations | Arbitrary output types and finite words. This Type-level theorem is not a final-coalgebra construction in every ambient category. |
| Weighted concatenation | Existing finite list decompositions and a semiring; noncommutative order is retained. Arbitrary monoids may need different decomposition/summation hypotheses. |
| Proof-relevant parsing | Chosen sums, products, lists, decision procedures and proved witness isomorphisms. Selected decisions are not a quotient by inhabitation. |
| Snapshots | Bounded depth, root observation included. No shared evaluation, finite-state minimization or global memory/time bound is established. |
| Star | Witness star retains arbitrary finite lists of empty parses. Weighted star and infinite summation remain separate, with no invented coefficient convergence law. |
| Extensions | Proven operation equations and syntax embeddings for this signature. Source-code transposition, generic GSOS naturality and unrestricted productivity remain outside this result. |

The [extension assessment](language-extension-metatheory.md) and
[#262](https://github.com/VladimirMarko/conaled/issues/262) retain the broader
question of admissible semantic-type extensions. This experiment supplies an
operation-extension example with explicit local obligations; it does not
replace that question with a fixed universal syntax or semantic algebra.
