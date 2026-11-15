# Exact parser equations in constructor contexts

[#276](https://github.com/VladimirMarko/conaled/issues/276) implements transport
fusion and identity-transport elimination in
[ExactRewrites](../../Applications/Languages/ExactRewrites.lean). These equations
remove redundant representation conversions from symbolic parser derivatives.
They preserve the selected decision at every word, rather than only recognition.
No execution-time improvement is claimed; #283 owns the representation and cost
experiment.

## Contract and contextual closure

The starting interface is #274's `IndexedCompositional.signature`: union,
transport, depth restriction, scale, intersection, concatenation and star.
Its indices are `(P,n)`, with `P : List α → Type` specified independently of the
parser. An observation at `w`, where `w.length ≤ n`, returns `Decision (P w)`.
The result includes the chosen witness. Equality of refutations uses Lean's
proof irrelevance; equality of successful results retains all witness data.

For isomorphisms `e w : P w ≅ Q w` and `f w : Q w ≅ R w`, the equation is

```text
transport f (transport e p) = transport (fun w => (e w).trans (f w)) p
```

Here `=` denotes equality of parse decisions after interpretation, not equality
of parser syntax. Both sides have index `(R,n)`. The composite maps a witness
through `e` first and `f` second; its inverse has the reverse order. Identity
transport similarly preserves decisions at index `(P,n)`.
`WitnessTrie.transport_trans` and `transport_refl` prove the corresponding
whole-trie equations. `Parser.parse_transport_trans` and `parse_transport_refl`
recover the direct parser API for every finite input, without a fixed bound.

`contextual_exact` accepts an arbitrary typed term of holes and two fillings.
Its sole equation premise is exact agreement of each filling on words within
that hole's depth. Holes may repeat, be absent, or occur at different indices.
`Term.bind` replaces them beneath any finite combination of the seven supported
constructors. The conclusion preserves native parser decisions at every allowed
root word. `contextual_tree` recovers equality of the native interpreted tries.
Constants can be encoded as holes with identical fillings, so selective local
replacement does not require rewriting every leaf.

The proof uses `recovered`, which was proved through the shared
`Rule.fold_morphism`, to turn the local observation premise into equality of
finite tries via `ext_lookup`. The existing `Term.fold_bind` then propagates
that equality through the context. It does not assume the desired contextual
conclusion or reprove each constructor's derivative compatibility. A richer
signature would need its own compatible interpretation and recovery theorem.

`TransportPair` packages a site's two isomorphisms and parser;
`contextual_transport_trans` discharges the general local premise from fusion.
The author supplies the transports, their inverse proofs, and a typed context.
No quotient, categorical instances, or new AST is required of direct parser
clients. Context authors still manipulate `Term`, finite arities and indices;
this bounded author interface is not evidence of general usability. #279 owns
independent author trials.

## Checked cases and rejected equation

[ExactParserRewrites](../../Examples/ExactParserRewrites.lean) first toggles a
Boolean witness and exchanges product fields. The independently expected result
is `yes (unit,false)`, recovered through the public contextual fusion theorem
on a nonempty input. A second case places fusion beneath star, concatenation,
and depth restriction, and checks both native parser equality and whole-trie
equality. The star operand is nullable. These are applications of the universal
result, not a replacement for arbitrary-context closure.

The negative case reuses #267's compiled `epsilon + epsilon` parser and swapped
sum isomorphism from
[ObservationExtension](../../Examples/ObservationExtension.lean). Recognition
agrees on every word, but the empty-word decisions are explicitly
`yes (inl evidence)` and `yes (inr evidence)`. Thus commuting alternatives and
transporting the result back does not preserve the selected witness.
`selected_incompatible` supplies the failed observer-extension obligation for
`SquareKit.ObservationExtension.Compatible recognition selected`. The existing
`selected_no_factor` rules out descending that selected observer to the Boolean
recognition quotient. Our local equation premise corresponds to `agreement`
with exact word-indexed decisions and the selected bounded word family; it
cannot be replaced by the weaker Boolean relation.

## Comparison with the quotient-law criterion

Bonsangue, Hansen, Kurz and Rot's *Presenting Distributive Laws* (2015),
Theorem 4.3, equates preservation of the chosen equations by a distributive law
with existence of a unique induced law on the quotient monad. Preservation
compares one-step behavior after quotienting successor terms. Proposition 4.10
extends the result to copointed functors. Example 4.9 warns that an equation
valid in final behavior need not be preserved by the chosen law and equation
presentation. [Primary source, §§4.1–4.2](https://arxiv.org/pdf/1503.02447)

For our transport equations, the concrete obligations are identifiable:

| Obligation | Local evidence |
| --- | --- |
| Equal immediate outputs | `Decision.map_refl` and `Decision.map_trans`, including successful witness maps and refutations |
| Matching successor equations | Derivation restricts `e` and `f` to `a :: w`; the same identity/fusion schema applies at the derivative language and smaller depth |
| Retained operands | Existing `Slot.ret` and the compatible concat/star rules retain operands, with explicit depth restriction |
| Replacement under contexts | `contextual_exact`, using `fold_bind` and the shared recovery theorem |

This is a concrete semantic proof in indexed families. It is not a Lean
instantiation of Theorem 4.3: no quotient monad, presentation-generated
congruence, or categorical distributive law over that quotient is constructed.
A proposal to identify syntax modulo these equations would additionally need
that presentation and its one-step equation-preservation proof, including the
retained component of the copointed behavior. The current finite-trie equality
proof solves the requested replacement problem without that infrastructure.
Boolean union commutativity fails already at the exact output obligation.

The decision is to retain the morphism/fold route for these rewrites. No missing
obligation in this client requires a quotient construction. #235 remains the
owner if a future quotient-based client exposes such a need. The proven scope
includes arbitrary finite supported contexts, exact selected witnesses and
nullable-star operands. It excludes optimizer termination, canonical forms,
recognition-only rewrite suites, resource bounds, and arbitrary full abstraction.
