# Frozen inputs for the proof-requirement comparison

This is the pre-adaptation fixture for [#286](https://github.com/VladimirMarko/conaled/issues/286).
It deliberately calibrates nonrecursive arguments. These are constructed paper
examples, not extracted Lean terms or measurements of an author's work.

## Source logic and proof boundary

Use many-sorted intuitionistic natural deduction with equality (reflexivity,
symmetry, transitivity and congruence/substitution), implication, conjunction,
disjunction, falsity and universal quantification. Proof terms use lambda
abstraction/application, equality constructors and disjunction case analysis.
A separate data judgment admits dependent pairs `(y,p) : Σ y:A. R(y)` and
projections, with their beta equations. Existential propositions are separate
and do not carry a publicly observable selected witness. The concrete source
extends this logic with natural numbers, addition, zero, and excluded middle
`em : ∀ Q:Prop. Q ∨ ¬Q`. Quantification over Q is schematic if the object logic
is first order. No universe polymorphism or native Lean elimination is assumed.

Named source lemmas are opaque proof leaves:

```text
raN : ∀ a b c:ℕ. (a+b)+c = a+(b+c)
ruN : ∀ a:ℕ. a+0 = a
```

Their usual arithmetic proofs may use induction. This boundary is intentional:
reuse will require interpretations of these lemmas, not claim to abstract their
inductive implementations. `em` is ambient but unused by the first two proofs.

## Statements and exact artifacts

Equality statement E: `∀ x y z:ℕ. (x+y)+(z+0) = x+(y+z)`.
At fixed x,y,z, freeze the proof

```text
e0 := cong (λt. (x+y)+t) (ruN z)
e1 := raN x y z
e  := trans e0 e1
Eproof := λx y z. e
```

Witness statement W: `∀ x:ℕ. Σ y:ℕ. y = x+0`, with selected witness x.
Freeze `Wproof := λx. (x, sym (ruN x))`. Its first projection computes to x;
its existential shadow is `∀ x. ∃ y. y=x+0`.

Second proof of the same E, with an actual stronger-principle occurrence:

```text
Estrong := λx y z. case (em Q) of
  inl q => trans (cong (λt. (x+y)+t) (ruN z)) (raN x y z)
  inr n => trans (cong (λt. (x+y)+t) (ruN z)) (raN x y z)
```

Q is a fresh closed proposition parameter; neither branch uses q or n.
Compare unsimplified dependency extraction and an explicitly justified rewrite
of this proof. Do not conflate a dependency with necessity of the statement.

## Intended interpretations and observations

The two target instances are fixed before either route is adapted:

| Assignment | L | B |
|---|---|---|
| Carrier | finite lists of natural numbers | booleans |
| Binary operation | concatenation `++` | exclusive or `xor` |
| Distinguished element | empty list `[]` | `false` |
| Equality | full list equality | boolean equality |
| W witness observation | exact selected list x | exact selected boolean x |

The shared target logic is the intuitionistic base; arbitrary Q is not supplied
with a decision procedure. Target arithmetic/list/boolean law proofs are model
obligations, distinct from the transported client proof. Successful witness
transport must keep the first projection, not merely the existential shadow.

Negative controls: interpret the same carrier/operation slots as natural numbers,
truncated subtraction and zero, testing the extracted associativity obligation;
and erase a witness to the truth of its existential shadow. The latter must not
count as data transport. Use x=`[0]` and x=`[1]` for distinct list observations.

## Fixed questions and prior evidence

Record sufficient requirements and replay each transformed proof; compare a
manual operation/law interface and a small presented theory with total views
on these same artifacts. Record all declarations/axioms, typing/binding order,
missing obligations, equality and witness observations, and argument-author
versus model-builder work. Do not measure author time or infer a weakest theory.

Use the completed [recursive investigation](../recursive-argument-transport.md)
and [implementation](../recursive-fusion-implementation.md) as the boundary
case beyond this calibration, the [FIFO study](../abstract-fifo-client.md) for
operation versus observation preservation, and the
[author-trial protocol](../../../experiments/toolkit-authoring/protocol.md)
for any later usability trial. Do not redo those completed investigations.
