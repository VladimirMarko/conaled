# A primitive extension that retains FIFO client contracts

[#259](https://github.com/VladimirMarko/conaled/issues/259) extends the existing
FIFO source signature with rotation. Old terms retain their compiled meanings
and observations under the same simulation assumptions. A contrasting primitive
that reveals private queue layout has no compatible semantic interpretation.
The code uses the existing compiler's naturality and logical-relation theorems.

## Scope of the extension

[STLCSignature](../../SquareKit/STLCSignature.lean) changes the primitive family
while keeping `Ty`, contexts, binding and term constructors fixed. `map` relabels
primitives, `restrict` restricts a model, and `compile_map` proves that these
commute with interpretation. `map_id` and `map_comp` retain identity and
composition. `compile_target` and `eval_map` recover the ordinary target and
function specializations through the existing model bridge.

`Add P Q` adds a second primitive family. `preserves_extend` takes the existing
structural preservation package and one square for each added operation. It
requires no new structural law when those operations remain unchanged. Semantic
equivalence is still the caller's `HomEquiv`; ordinary equalities are used only
for the specific restriction and concrete target equations that justify them.

This experiment selects #210's FIFO representation-independent client rather
than extending every correspondence fragment. The existing
[Curry–Howard bridge](../../SquareKit/CurryHoward.lean) concerns its own
restricted proof grammar and admissibility; it is not a conservativity theorem
for signature extension. #211's cost contracts are also separate: preserving
queue contents and head observations establishes no new cost bound.

## The new operation and the old client

[FIFOExtension](../../Applications/Sequences/FIFOExtension.lean) defines
`rotate ops q` using only `head`, `tail` and `snoc`. Empty input is unchanged;
otherwise the first element moves to the back. `rotate_related` follows from
any `Simulation`, using equality of head observations to choose the same branch
and then the existing tail and enqueue laws. It does not require a functional,
injective or decidable representation relation.

The extended `primitives` package combines the old operation evidence with
`rotate_related`. `old_target` recovers the original target by restriction;
`old_compile` applies generic signature preservation. `old_observe` then reuses
`Syntax.observe_program`, with exactly its original `Simulation` and related-input
premises. The ordinary client and original modules are unchanged.

The new source client binds the rotated queue and passes it to the old command
word. `observe` applies `STLCRelations.compile_preserves`; it does not reproduce
the term induction. `representation_independent` compares two representations
through their common sequence. `interpretation_preserves` specializes
`preserves_extend`, and `composed_interpretation` uses naturality for the existing
inclusion into relational squares followed by semantic projection. The latter
route already composes its map laws in `STLCRelations.interpretation_laws`.

[LanguageExtension](../../Examples/LanguageExtension.lean) checks:

- The unchanged old client still returns `some 2` through the enlarged target.
- Rotating `[1,2,3]`, then deleting, returns head `some 3`, in both list and
  symmetric-list representations. The expected intermediate sequence is
  `[2,3,1]`, then `[3,1]`.
- Rotation of an empty queue still gives `none` at the observation boundary.
- Two valid private layouts of `[1,2,3]` retain equal extended-client observations.
- Primitive relabeling composes with identity on arbitrary old terms.

These examples use the general preservation results. They are checked
specializations, not independent computations substituted for those results.

## An incompatible primitive

`revealFront` returns the left unit tag if the private front list has length one,
and the right unit tag otherwise. Its source type is
`base → sum unit unit`, so the existing relation requires matching observable
tags. The established `leftLayout` and `rightLayout` both represent `[1,2,3]`,
but their front lists have lengths one and two.

`no_reveal_interpretation` proves that no function from abstract sequences to
these tags can satisfy the relation for all represented inputs.
`no_reveal_primitives` states the consequence at the actual
`STLCRelations.Primitives` interface: no evidence package can install
`revealFront` as that primitive's implementation, regardless of its proposed
semantic meaning. This is a contradiction from concrete related inputs, not a
failed tactic search. The positive extended compiler and all old clients remain
valid. A target supporting this observation would need different observations,
a richer abstract state, or a restriction on admissible representations.

## Guarantees that remain separate

| Property | Result in this experiment |
| --- | --- |
| Old source terms and old proofs | `map` embeds primitives via `Sum.inl`; old client theorems are recovered by `old_compile` and `old_observe`. No old declaration is replaced. |
| Model restriction and old meaning | `compile_map` and `old_target` give exact interpretation/restriction equations. |
| Equational conservativity | Not claimed. No new source equality judgment is defined; preservation does not imply reflection of derivability. |
| New type constructors or axioms | Not implemented. They would change the obligations and could invalidate existing metatheorems. |
| Normalization and canonicity | No theorem about either is added. An opaque natural-number constant without a computation rule would be a closed non-numeral normal form in a calculus with numeral canonicity; that separate paper example does not imply non-normalization. |
| Inference completeness | Not claimed. The existing typed AST supplies its type before this transformation. #147's bounded elaboration contract is unchanged. |
| Witnesses and coherence | Function relations quantify over related inputs; sum tags remain observable. No inverse representation map, witness erasure or arbitrary coherence principle is assumed. |

The [metatheory comparison](language-extension-metatheory.md) supplies the broader
literature context. Its primitive example uses parity; the present experiment
uses the existing FIFO client to test recovery of a previously checked
representation-independence theorem.

## Author obligations and remaining work

The operation author supplies `rotate` and its local relation proof. The target
package adds a case for that evidence; the unchanged compiler induction is
reused. The concrete client supplies its command word and initial-state relation,
then applies `observe`. Existing ordinary clients still use their original API.
No parser, new kernel axiom or global type lattice is required.

There is still internal bookkeeping: a primitive sum, relabeling old terms,
model/target restriction and a sum case split connecting the generic preservation
package to the concrete interpreter. Those steps are visible in this bounded
implementation. Familiar notation could hide them, but no independent author
trial or surface-language improvement is claimed here.

At present a missing preservation proof appears as a Lean field obligation for
`Primitives.correct`. `no_reveal_primitives` explains this failure mathematically;
it does not install a custom diagnostic or a general decision procedure for
incompatible extensions. Source development also encountered dependent-record
rewrite restrictions; using the existing definitional specialization avoided
casts and stronger mathematical assumptions.

No existing interface needed a retrofit. [#235](https://github.com/VladimirMarko/conaled/issues/235)
retains the broader work: dependent signature extensions need typed substitution
and comparison coherence; cost, identity and witness contracts need their own
extension tests; improved surfaces should remove routine bookkeeping while
keeping failed obligations identifiable. This experiment establishes one
successful reusable contract and one rejected extension, not universal language
extensibility.
