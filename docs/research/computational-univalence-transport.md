# Computational univalence and representation transport

Research for [#393](https://github.com/VladimirMarko/conaled/issues/393).
Inspected local revision: `78540f8f30ed8cb1afa7dc799a96dac65fec1458`.
This report proposes contracts; it adds no Lean theorem or evaluation result.

Use equivalence-based ordinary transport now where it meets the consumer's
specification. Constructing a universe path becomes necessary when the unchanged
consumer quantifies over types and reasons through that path. The recommended
continuation follows the retained circle cover through universe construction,
source interpretation and its integer observation. The Boolean test below is a
diagnostic within that work, not a substitute for that consumer.

## What computational univalence would promise

The selected semantic reference is [CCHM, arXiv:1611.02108v1,
§§6–8](https://arxiv.org/html/1611.02108v1): Glue supplies universe composition
and univalence. For executable source behavior use the separately specified
[Agda 2.8.0.2 cubical rules](https://agda.readthedocs.io/en/v2.8.0.2/language/cubical.html#glue-types).
Its `uaβ e x` is a path proved using `transportRefl`; it is not a general
judgmental equation for arbitrary open `e` and `x`.

For comparison, take intensional dependent type theory with Bool, a universe,
identity elimination and an opaque univalence constant, with only its original
beta rules as evaluator. Transport along `ua notEquiv` is well typed but has no
new reduction rule. A propositional computation law can follow from univalence;
it does not extend this evaluator. This is a specified comparison calculus,
not a claim that every axiomatic presentation chooses the same rules.

Proposed diagnostic, with the forward orientation of `notEquiv` fixed:

```text
b = transport (ua notEquiv) true : Bool
```

| Observation | Obligation and current status |
|---|---|
| Typing | Interpret Bool, equivalence, universe path and transport. Not supplied by the local universe-free model. |
| Denotation | Show the interpreted transport sends true to false. Requires the chosen universe/Glue construction. |
| Identity witness | Interpret `uaβ`, retaining its path endpoints. Separate from host Lean equality. |
| Evaluation | Give a named source or target step relation and derive `b ⇓ false`. No such result is claimed here. |
| Cost | Count named steps or target operations, including residual transport; a semantic equality contains no bound. |

Even if this closed case normalizes in the selected external checker, that does
not establish conversion of the open general law or adequacy of a Lean emitter.

## Structured client and reuse

Let `e : A ≃ B`, and let a state package contain `initial : A`,
`step : A → A`, and an invariant with a preservation proof. Its explicit
representation change is `e initial` and `e ∘ step ∘ e⁻¹`, with the invariant
pulled back through `e⁻¹`. The candidate theorem compares transport of this
entire dependent package along `ua e` with that explicit package, component by
component, including the proof-bearing field. It must not replace the dependent
package comparison with equality of carrier cardinalities.

The [finite universe](../../SquareKit/FiniteUniverse.lean) already has
`Enumeration.naturality`, `family_transport`, and sum/product naturality and
composition theorems. These are useful concrete equivalence clients.
`Code` has bijections as morphisms; these are not host equality proofs or an
internal cubical universe. The [filler transport](../../SquareKit/Internal/Cubical/FillingTransport.lean)
operation transfers filling across a family isomorphism. It likewise does not
construct a path in a universe. Neither interface should acquire a mandatory
univalence requirement merely to preserve these existing uses.

The substantive retained consumer is
[`Monodromy.agda`](../../experiments/dependent-higher-identity/Monodromy.agda).
Its integer cover uses the successor equivalence as a type path, and its
nested transports distinguish the observations 3 and 2 after loop erasure.
That existing source statement crosses the missing universe, circle,
path-to-inductive-identity and computation boundaries. A state package above
is a compiler-facing companion, not an already implemented source translation.

## Recommendation and rejection conditions

Follow the [universe/Glue construction graph](cubical-universe-glue-milestone.md)
and [HIT consumer plan](computational-higher-inductive-consumers.md), then prove
that the interpretation of the unchanged cover transport agrees with its
explicit integer action. Record source conversion preservation separately from
operational simulation. Compare a native ordinary Lean equivalence proof against
the interpreted route, including admission and repair work, before claiming
lower author effort. The [cross-theory assessment](cubical-judgment-compatibility.md)
explains why changing cubical theory is a real alternative with translation costs.

Reject a claimed completion if it adds an opaque host univalence axiom, proves
only that two booleans have the same denotation, silently erases the cover loop,
or imports the source theorem as an assumption. Deliberately reversing the
equivalence must change the integer action; the Boolean involution alone would
miss that bug. Retain the 3-versus-2 observation to detect witness erasure.
Cost analysis belongs to #406/#200 and must name an evaluator; no efficiency
conclusion follows from the proposed package comparison.

Evidence is source inspection and the repository's existing checked artifacts,
not a fresh Agda or Lean run. The CCHM version, Agda release and pinned experiment
library are fixed here; the latter is Cubical v0.9 commit
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`.
