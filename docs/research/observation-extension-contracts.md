# Observation-sensitive extension contracts

[#267](https://github.com/VladimirMarko/conaled/issues/267) separates adding
representations under an existing contract from adding observations that refine
that contract. [ObservationExtension](../../SquareKit/ObservationExtension.lean)
proves restriction, compatibility and quotient descent for exact observations.
The [checked applications](../../Examples/ObservationExtension.lean) retain
selected parser witnesses and reuse #259's FIFO client proofs.

## Existing contracts and the selected interface

The implementation audit found different useful contracts already in place:

| Existing interface | Reused meaning and boundary |
| --- | --- |
| `Parser.parse`, `Decision.test_correct`, `ParserBridge.recognizers_agree` | A decision carries an actual witness or its refutation. Boolean recognition forgets the chosen witness. The bridge compares independently constructed recognizers after that forgetting. |
| `Simulation`, `Simulation.representation_independent` | A relation connects valid queue representations to abstract sequences. Client observations agree for inputs related to the same abstract state; the relation need not be a function. |
| `FIFOExtension.observe`, `old_observe` | Rotation is admitted by its local simulation proof. The public compiler contract reuses the old syntax proof and logical-relation theorem. |
| `STLCSignature.preserves_extend`, `ClosedMap.transportLaws` | Operation compatibility and the stated congruence/reflection assumptions govern interpretation and law transport. Observer extension does not supply those assumptions automatically. |
| `RelationTransport.requirement`, `HomQuotient` | Universal partial correctness and categorical quotient operations remain separate. This task uses Lean's `Setoid`, `Quotient.lift` and `Quotient.sound` for value observations, without recreating categorical law transport. |

The bounded shared interface fixes a representation type `X`, observer indices
`I`, result family `R : I → Type`, and `observe : (i : I) → X → R i`.
`agreement observe family` identifies `x` and `y` exactly when every selected
observer returns equal results. Equality is in the same fibre `R i`. No result
is cast between different indices, and no heterogeneous equality or transport
is silently inferred. The parser specialization uses `Decision (P w)` at word
index `w`, retaining that dependent result in full.

`restrict` proves that agreement for a larger selected family implies agreement
for a smaller one. `extend old observe` conjoins an old setoid relation with
equality of one new observation. `extend_restrict` always holds; `extend_iff`
needs `Compatible old observe`, namely constancy on every old equivalence class.
An arbitrary result relation need not be an equivalence, so this module does
not turn every relation in the inventory into a quotient. The existing FIFO
simulation stays intact; its example forms a setoid only on valid states with
equal decoded lists. An observer that compares results by a nontrivial setoid,
or at changing indices with explicit transport, needs a corresponding adapter.
These remain scoped architectural questions under #235, with index-changing
observations under #271. No current consumer was weakened to fit this interface.

`compatible_of_factor` is a sufficient author rule: give an old-compatible
meaning map, a semantic observer, and a commuting equation. `descend` then
constructs the observer on the old quotient; `descend_mk` recovers its value on
a representative. `no_factor` proves impossibility from one related pair with
different observed values. It rules out every total quotient function,
including noncomputable functions, rather than only a particular implementation.

## Parser witnesses distinguish the old identification

`Parsing.left` is the existing compiled parser for `epsilon + epsilon`.
On the empty word its decision is `yes (inl evidence)`. `Parsing.right` uses the
existing `Parser.transport` with the involution swapping the two alternatives.
Its result is `yes (inr evidence)` at precisely the same language and word index.
Both are well-typed parsers for the same witness language; neither is an invented
Boolean surrogate for a parser.

The old family observes Boolean recognition at every word. `old_agreement`
reuses `Parser.parse_correct` to prove that all parsers at this language index
agree under that family. `old_bridge` retains the public `recognizers_agree`
proof relating the original parser to the regex implementation. The richer
`selected` observer returns the actual `Decision (P [])`. `selected_different`
checks the distinct results, `selected_incompatible` names the failed
compatibility premise, and `selected_no_factor` applies the shared obstruction
theorem. `refined_recognition` recovers the old observation from the richer
contract. `witnessAgreement` and `restrict_words` also exercise family restriction
with word-dependent result types, rather than Boolean outputs.

This uses two selected parses of an ambiguous expression, not an enumeration of
all parses. The old correctness and bridge theorems quantify over arbitrary
words and already support nullable stars. A nullable star can have unboundedly
many empty-parse lists; nothing here assumes a finite enumeration of those
lists or changes the parser's selected witness. An observation-sensitive
contract must say which witness is selected, not infer its identity from
recognition success.

## Admitting a FIFO observer and retaining the old proof

`FIFO.State` is the subtype of valid symmetric-list layouts. `contents` observes
the decoded list; `old` is equality of that observation. The representations
`([1], [3,2])` and `([1,2], [3])` both denote `[1,2,3]`.

The new observer `rotated cs` runs #259's compiled rotating client and observes
its head. `rotated_square` is an application of the unchanged public
`Extension.observe` theorem using the subtype invariant and decoder equation.
`rotated_compatible` applies the shared factorization rule. `admitted` proves
that adding this observer leaves the old relation unchanged. The worked case
rotates `[1,2,3]` to `[2,3,1]`, then deletes to `[3,1]`, so its head is `some 3`.
`rotated_value` derives that result through `rotated_square`; `admitted_pair`
checks that the two layouts satisfy the extended contract.

`old_client` restricts the extended contract and applies the original
`Simulation.representation_independent` proof for any command word. No old
proof or module was edited. The theorem retains exactly the original valid-state
and common-list assumptions. `old_client_pair` connects it to the concrete
layouts, and the quotient example checks `descend_mk` on an admitted observer.

The incompatible observer reuses #259's `revealFront`, which emits opposite
sum tags when the private front length is one versus two. `reveal_incompatible`
and `reveal_no_factor` identify the failed premise and rule out descent to this
old quotient. #259's `no_reveal_primitives` already exposes the same obstruction
at the compiler's `Primitives.correct` field; that proof is not duplicated.
The old client remains valid because it never assumed private layout was
observable. It also remains applicable to inputs related by the refined contract,
by restriction, without any compatibility premise for `reveal`. What fails is
retaining the old identification while claiming that `reveal` is invariant on
all old-related states: that requires `Compatible old reveal`, which the checked
pair refutes.

## Extension kinds and author obligations

| Change | Required evidence |
| --- | --- |
| Another representation under the same contract | Supply the original representation invariant and operation simulation. Old clients keep their existing premises. |
| Constructor or primitive extension | Supply interpretations and compatibility for the new operations, retaining old meanings. #259 supplies this for rotation; syntax/restriction equations are separate from observer refinement. |
| Observer extension | Prove constancy on the old relation for an unchanged quotient, or explicitly refine the relation. The parser and layout counterexamples reject constancy. |
| Semantic type extension | Supply the chosen type admissibility and structural/coherence laws. #262 owns this experiment; no completed semantic-admissibility artifact exists at this task's base `50cdd4b3`. This work neither recreates its DRFCaml inventory nor extends the type grammar. |
| Additional axioms | State the new assumptions and justify the intended model. An axiom does not derive normalization, consistency, or compatibility with richer observations. No new axiom is introduced here. |

For the admitted FIFO observer, the author supplies a semantic function and a
commuting square. The existing simulation theorem discharges that square,
and the shared proof handles quotient descent and relation restriction. The
incompatible cases require only the existing pair and unequal results to explain
why the same obligation cannot be filled. Lean's missing `Compatible` or
`Primitives.correct` proof is the diagnostic boundary; this work provides
mathematical counterexamples, not an automatic diagnostic procedure.

The direct FIFO route remains shorter when only one client equality is needed.
The new layer earns its additional setoid/subtype packaging when the author asks
whether observations can descend or whether an extension changes identification.
During implementation, explicit implicit binders were needed when passing the
compatibility proof as a lambda, and `LanguageWitnesses.Language` needed
qualification against the Boolean language alias. These were elaboration/name
resolution costs, not failed mathematical premises. This is one agent's
implementation record, not an independent usability trial.

## Separate metatheorem obligations

Observation preservation gives none of the following for free:

- Syntactic conservativity needs an embedding and, for derivability claims,
  reflection of old judgments. Retaining semantic observations alone does not
  reflect syntax or source equality.
- Normalization needs a reduction relation and termination argument for the
  extended calculus. Total Lean observation functions are not that argument.
- Inference needs a stated constraint/elaboration algorithm with soundness and
  completeness or an explicit bounded contract. Intrinsic indices supply types;
  they do not infer them.
- Operational adequacy needs a comparison between execution behavior and the
  independent meaning, including failure or divergence where present.
- Resource claims need a cost model, workload and bound. Equal sequence contents
  or equal parse decisions do not bound allocation, runtime or retained storage.

#235 owns comparison with other preservation families and any future adapters;
#36/#200 own broader language interpretation and metatheory. The existing
[extension experiment](language-extension-experiment.md),
[transposition account](constructor-destructor-transposition.md), and
[Construction and observation agenda](duality-language-directions.md) retain
their separate scopes.
