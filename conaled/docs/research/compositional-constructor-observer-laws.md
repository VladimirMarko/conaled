# Compositional constructor–observer laws

Bounded implementation and source assessment for
[#268](https://github.com/VladimirMarko/conaled/issues/268).
The implementation recovers weighted language operations from local constructor
rules, with explicit laws for renaming and substitution. This extends the
[finite-word coalgebra experiment](language-derivative-coalgebras.md);
[source transposition](constructor-destructor-transposition.md) addresses a
different question about program organization.

## Source theorem and assumptions

Turi and Plotkin's [Towards a Mathematical Operational
Semantics](https://homepages.inf.ed.ac.uk/gdp/publications/Math_Op_Sem.pdf),
§3, equation (8), PDF page 5, gives abstract GSOS rules the natural-transformation
shape `ρ : Σ(Id × B) ⇒ BT`. Here Σ is a signature functor freely generating
syntax monad T, and B describes one-step behavior on a cartesian category.
Theorem 5.1 (§5, PDF page 7) supplies structural recursion with retained terms.
Proposition 5.1 and Definition 5.2 use naturality to obtain a monad lifting to
B-coalgebras. Its unit and multiplication must be coalgebra morphisms.
The handler at existing terms is `Bμ ∘ ρT`, where μ flattens nested syntax.

The later distributive law in §7.1, PDF page 9, has type `TD ⇒ DT` for a
comonad D and must satisfy unit, multiplication, counit and comultiplication
laws. This requires additional structure. The bounded Type-level experiment
below does not assert that full categorical construction or its general
adequacy consequences. A well-typed handler at one carrier does not establish
naturality or substitution compatibility.

## One constructor layer and arbitrary terms

For the local weighted application, fix alphabet A and coefficients R. Write
`B X = R × (A → X)`. Mapping `f : X → Y` through B keeps the output and maps
each successor by f. The state type varies; A and R remain fixed.
A signature layer Σ contains one addition, scaling or concatenation node with
its operands. T contains finite trees of those nodes and leaf states.

These types describe different interfaces:

```text
ρ_X : Σ(X × B X) → B(T X)     one constructor layer
L_X : T(X × B X) → B(T X)     arbitrary finite term
```

The first gives a rule access to each operand together with its one-step
behavior. The second must recurse through all constructor layers. Calling
L a one-layer GSOS rule would conceal the recursion and its proof obligations.
In the notation below, `η` inserts a leaf, `μ` flattens nested terms, `π₁`
selects the original state, and `⟨f,g⟩` pairs two maps with a common domain.

An explanatory construction of L interprets an annotated leaf `(x,b)` as
`Bη(b)`. At a constructor it recursively observes each child and pairs this
observation with that child's original term, obtained by `Tπ₁`. Applying
`ρ` at carrier `T X` produces nested terms; `Bμ` flattens them. The recursion
is over the input tree, not over newly produced successors.

For a seed coalgebra `c : X → B X`, the induced term coalgebra is

```text
lift(c) = L_X ∘ T⟨id,c⟩ : T X → B(T X).
```

## The restricted rule format

The [shared implementation](../../SquareKit/CompositionalCoalgebra.lean) uses
an operation type `Op`, a finite arity `arity op`,
and freely generated terms. For an operation of arity n, the output rule
combines an n-tuple of outputs. Its successor rule is a term with variables
in `Fin n ⊕ Fin n`: the left summand names original operands, and the right
summand names their successors at the currently observed letter. The chosen
template may depend on that letter and on operand outputs.

Instantiating these template variables defines a one-layer rule of the shape
ρ above. It cannot inspect the identity of a state: output values and letters
are fixed parameters, while state occurrences enter only through syntactic
variables. This restriction permits a proof of renaming naturality by the
term substitution laws. It admits the retained right operand of convolution
and both successors of pointwise multiplication.

This is a subformat of abstract GSOS. Its template cannot refer to an
operand's successor at another letter, inspect several successive transitions,
or branch on equality of states. No completeness claim for all natural
transformations is intended. Finite arity bounds each constructor's operands;
it does not require finitely many operations or bound program depth.

## Laws that make substitution compatible

The following equations explain the mathematical comparison. No explicit
global L object or abstract distributive-law object is defined in the Lean
implementation. Its `lift` recurses directly over terms, and its morphism
theorems establish the corresponding concrete compatibility contracts.
Naturality of the local rule is

```text
B(T f) ∘ ρ_X = ρ_Y ∘ Σ(f × B f).
```

For the global map L, the corresponding law replaces Σ by T. Unit and
multiplication compatibility are separate requirements:

```text
L_X ∘ η_(X×BX) = Bη_X ∘ π₂
L_X ∘ μ_(X×BX) = Bμ_X ∘ L_(TX) ∘ T⟨Tπ₁,L_X⟩.
```

In the second equation both sides start at `T(T(X × B X))`. The pair supplied
to the outer L contains the retained inner term and its computed behavior.
These equations explain why bare naturality of an arbitrary global function
L is insufficient: it does not state what happens to leaves or nested syntax.
When L is generated from suitable local rules, the construction should prove
these equations rather than require every application to establish them again.

A directly usable consequence has a simpler interface. Suppose
`f : X → T Y` preserves output and transitions from c to `lift(d)`. Then
`bind_morphism` proves that substitution `bind f : T X → T Y` preserves
output and transitions from
`lift(c)` to `lift(d)`. Specializing f recovers the unit, syntax flattening,
and the action on seed coalgebra morphisms. The existing
[finite-word finality theorem](../../SquareKit/WordCoalgebra.lean) then turns
that morphism into equality of every word observation.

A semantic interpretation into an algebra of behaviors still needs local
compatibility evidence for that algebra. An arbitrary assignment of meanings
to constructor names does not follow from the syntax or the monad laws.
For weighted languages, the existing convolution derivative equation is that
evidence for concatenation.

## Weighted rules and the retained operand

[The existing weighted implementation](../../Applications/Languages/Coalgebra.lean)
has addition, left scaling and concatenation over a semiring R. Its
concatenation equations are

```text
out(p · q) = out(p) * out(q)
nextₐ(p · q) = scale(out(p), nextₐ(q)) + nextₐ(p) · q.
```

The last q is the original right operand. Replacing it by its derivative
changes the operation. Supplying only `B X` discards this operand; supplying
`X × B X` retains it explicitly. Left scaling and multiplication order must
remain unchanged because R need not be commutative.

Pointwise multiplication provides the extension case:

```text
out(pointwise(p,q)) = out(p) * out(q)
nextₐ(pointwise(p,q)) = pointwise(nextₐ(p), nextₐ(q)).
```

The output rule agrees with concatenation, but the successor rule differs.
The existing extended syntax lets the new operation occur under old
constructors. The new specialization recovers that mixed use and the old
syntax embedding through the shared constructor-law proof. No infinite
summation or weighted-star operation is part of this signature.

## Implemented theorem map

[CompositionalCoalgebra](../../SquareKit/CompositionalCoalgebra.lean) separates
free syntax, syntactic rules and semantic compatibility. It requires no
semiring or algebraic laws on the output type O.

| Interface or theorem | Contract |
| --- | --- |
| `Term.bind_leaf`, `bind_assoc` | Identity and associativity of leaf substitution; substitution into an individual leaf is definitional. |
| `Term.fold_bind`, `fold_node` | Interpretation commutes with substitution; folding into syntax recovers substitution. |
| `Rule.layer_natural` | Mapping both original states and successors commutes with the one-layer rule. |
| `Rule.Compatible` | Output and successor equations for each constructor, quantified over semantic operands. No premise quantifies over composite syntax. |
| `Rule.fold_morphism` | A compatible algebra and a seed coalgebra morphism extend to a morphism for every finite term. |
| `Rule.compatible_lift`, `bind_morphism` | The syntax algebra satisfies its own rules; a behavior-preserving compound substitution preserves every composite term's behavior. |
| `Rule.leaf_morphism`, `join_morphism`, `map_morphism` | Leaf insertion, flattening and mapping seed morphisms preserve output and transitions. |
| `Rule.run_fold`, `run_transport` | The morphism contracts imply equality of all finite-word observations. |

[The weighted specialization](../../Applications/Languages/Compositional.lean)
uses `Semiring R`, with no commutativity premise. `compatible` proves the local
constructor equations, reusing `Convolution.derivative_mul` for concatenation.
`interpretation` applies `fold_morphism`; `correct` then uses the existing
finite-word finality theorem.

`embed_output`, `embed_next` and `embed_meaning` identify the old weighted
syntax with its generic encoding. The `embedExtended_*` counterparts do the
same for the extended syntax. `recovered` and `recoveredExtended` obtain the
old all-word correctness statements from the new generic proof under the
original seed-morphism premise. `old_in_extended` retains the old meanings
when pointwise multiplication is available. These embeddings preserve the
existing direct constructors and client interface.

## Examples that distinguish the obligations

[Checked examples](../../Examples/CompositionalCoalgebra.lean) exercise three
different uses of the interface. The weighted cases retain noncommuting matrix
coefficients: the one-letter expression has entry `(0,0)` equal to 2, while
reversing the chosen coefficient product gives entry 0. Another case places
pointwise multiplication beneath concatenation, so the new constructor must
compose with old ones.

`Substitution.twice_morphism` replaces a constant-output-2 leaf machine by two
added constant-output-1 leaves. `bind_morphism` preserves this replacement in
every compound context; a concatenation context evaluates to 8 at one letter.
A separate example specializes `join_morphism` to nested syntax.

`RejectedRule.bad` replaces concatenation's retained right operand with its
successor. It still satisfies `layer_natural`, as every rule in this format
does. `incompatible` proves that it cannot satisfy the weighted semantic
contract: on a single-letter series concatenated with the empty-word series,
the required successor equation would imply `1 = 0`. Naturality therefore
does not certify a rule's intended meaning. Semantic compatibility is an
additional, observable obligation.

`IndexedVectors` supplies an independent family `Vec n = Fin (n+1) → Nat`.
Its observer returns the first coordinate and reverses the vector on each
transition. Pointwise doubling commutes with that observation. `composite`
extends the local doubling proof to all finite terms, retaining n as a
parameter. A twice-doubled two-coordinate vector produces 12, 28, 12 at
observation lengths zero, one and two. Every term remains in one fixed fiber;
this example does not establish operations or transitions that change indices.

## Author effort and reuse

The earlier [direct weighted development](../../Applications/Languages/Coalgebra.lean)
proves `output_sound` and `next_sound` by induction over each syntax, then
repeats that pattern for `Extended`. The new application author supplies
operation arities, output equations, successor templates and a `Compatible`
proof. `fold_morphism` handles composite induction once; the same theorem
serves the weighted extension and the vector family. Existing convolution
lemmas still supply the mathematical content of the concatenation proof.

The generic format introduces its own work: authors name operand positions
with `Fin`, distinguish original and successor variables with `Sum`, and use
embedding lemmas to recover the direct interfaces. These are visible encoding
costs, not evidence that the final language interface is settled. The examples
compare proof structure; they are not a timed user study or a measured claim
about author productivity.

[#256](https://github.com/VladimirMarko/conaled/issues/256) checks indexed cell
syntax, binder scope and transposition of program organization. It does not
automatically turn those cells into `Rule` templates or supply a `Compatible`
proof. Conversely this result's finitary unindexed syntax does not replace
that indexed syntax or its exact-witness parser contract.

## Indexed parser boundary

[Witness tries](../../Applications/Languages/WitnessTrie.lean) observe
`Decision (P word)`, whose result type depends on the language and word.
A single fixed output type R and an ordinary endofunctor on Type do not
express that contract directly. Packaging indices and witnesses into a common
sum would require separate evidence that interpretation and transport recover
the original fibers and exact selected decisions. Erasing them to Booleans
would discard the contract already proved for the parser.

Consequently the weighted specialization and fixed-fiber vector example do
not establish an indexed GSOS construction for the proof-relevant parser.
[#271](https://github.com/VladimirMarko/conaled/issues/271), under the shared
language workstream, owns that gap. Such a construction must choose
its indexed setting, substitution and transport laws, and its notion of
semantic equality explicitly. The same boundary applies to arbitrary binders,
dependent type formation, effects, recursion and productivity. The finite
syntax construction provides no runtime sharing or resource guarantee.
