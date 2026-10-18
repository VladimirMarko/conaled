# Shared transition machinery after demand delivery

This assessment starts from `2c5d83e`, the demand-delivery implementation for
[#30](https://github.com/VladimirMarko/conaled/issues/30). It asks which repeated
proof obligations justify shared machinery, and whether they expose a missing
Felix construction under [#8](https://github.com/VladimirMarko/conaled/issues/8).
The implementation now reuses Mathlib's closure of consecutive transitions
and keeps the executable recursions local. A new indexed execution interface
would remove short inductions but introduce adapters for path-specific honesty
and a second execution vocabulary. Fairness and request ownership should
remain application definitions.

## Concrete callers and limits

The repeated execution shape is a state at step zero followed by an update
depending on the step index. `Trace.sourcePrefix` supplies the next message;
`Demand.request` supplies the current source state and action. The latter is
time dependent even after fixing its action stream because its transition
reads `Trace.run`. Both are total executable recursions. A shared execution
function can preserve their zero/successor equations without changing the
source schedule or when responses are emitted.
[Sources: Trace](../../Applications/FRP/Trace.lean),
[Demand](../../Applications/FRP/Demand.lean).

| Candidate | Existing uses | Benefit and cost |
|---|---|---|
| Indexed execution with invariant preservation | `prefix_valid`, `prefix_sound`, `done_persists` | Shares induction across source and request states. It should accept an index-dependent invariant: source honesty is assumed at the actual prefix, not at every possible state. Encoding a clock in the state is unnecessary API overhead. |
| Indexed relational execution | Source validity/completion and request completion persistence | A relation between implementation and semantic states can specialize to a unary invariant using a constant semantic state. Existing `RelRep` and `RelSquare` supply the contract and composition; a new simulation record would duplicate them. Actual specializations must demonstrate that their adapter obligations stay readable. |
| Reflexive/transitive refinement along a trace | `prefix_refines`, used by `run_persists` and `interleavings_agree` | Mathlib already closes adjacent edges. Use its theorem rather than create another refinement hierarchy. |
| Pending-or-emitted and processing fairness | `pending_or_emitted`, `eventual_response` | These currently have one request automaton caller. Generalizing would require choices about emission identity, cancellation, duplicate registration, and fairness that the existing experiment does not settle. |
| Schedule-independent observation | `interleavings_agree`, then `registration_order_agrees` | The latter already reuses the former. A generic scheduler would add an interface without supplying a second independent proof. |

`done_persists` is another concrete use of consecutive-transition closure: the
sequence of propositions `request n = done` is monotone under implication.
`monotone_nat_of_le_succ` specializes the same Mathlib relation theorem to that
order. The benefit is a common existing proof interface for source refinement,
request completion, and the already implemented `count_mono`. This is a small
reuse improvement, not a reduction in the mathematical difficulty of these
proofs. The implemented adapters require only the existing refinement laws and the
existing one-step completion law. [Sources: `done_persists`](../../Applications/FRP/Demand.lean),
[`count_mono`](../../Applications/FRP/Trace.lean),
[Mathlib monotonicity](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Monotone/Basic.lean#L525-L530).

These are opportunities at different levels. A second theorem calling the same
FRP helper is evidence of useful application reuse; it does not by itself
justify another library abstraction. In particular, `run` deliberately factors
execution through consumed source-prefix counts. Replacing it with a generic
global state machine would lose the direct reason that equal consumed prefixes
produce equal states. [Source: `run`, `run_eq`](../../Applications/FRP/Trace.lean).

The source safety contract also constrains a relational extraction.
`process_sound` requires validity, an old completion, and honesty for the
accepted window. `traceRep` assumes honesty only along the initial state's
actual source prefixes. A square claiming that every message preserves the
completion relation on every raw state would require an additional honesty premise that the current callers
do not provide. An indexed relation or an explicit path-specific premise can
retain the current theorem. Reject an adapter that silently replaces source
honesty with an unconditional assumption.
[Sources: `process_sound`, `prefix_sound`, `traceRep`](../../Applications/FRP/Trace.lean).

## Mathlib constructions

The inspected Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in
[SOURCES.md](../SOURCES.md).

`Nat.rel_of_forall_rel_succ_of_le` accepts a relation with reflexivity and
transitivity, a sequence, a proof for each consecutive pair, and an index
inequality. This is exactly the closure needed by `prefix_refines` after
providing instances from `Refines.refl` and `Refines.trans`. Its restricted
variant also handles steps after a chosen starting index. No partial-order or
antisymmetry assumption is necessary.
[Mathlib source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/Monotone/Basic.lean#L509-L530).

`Nat.iterate`, `Function.Iterate.rec`, and `Function.Semiconj.iterate_right`
cover a fixed endofunction, invariant propagation, and exact commuting maps
through iteration. They are useful comparisons, but source prefixes and demand
requests use a different update at each step. A fixed-endofunction encoding
would carry the index as additional state and then require projection lemmas.
An indexed recursor can avoid that cost. Semiconjugacy also expresses exact
function equality; it does not replace the completion relation, which permits
many compatible futures.
[Mathlib source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Function/Iterate.lean).

Mathlib's `Relation.ReflTransGen` supplies nondeterministic finite reachability
and closure lemmas. This experiment already chooses its action sequence and
has a canonical executable state at each index. Replacing that representation
with reachability would require reconstructing determinism and indexed
execution. Reachability becomes a candidate when independent implementations
need a nondeterministic simulation contract.
[Mathlib source](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Relation.lean).

## Felix correspondence and #8

The inspected Felix checkout has HEAD
`6f36d28097db7ea5f5df3263db3e8be08f74e490`, the revision in
[SOURCES.md](../SOURCES.md). Its comma arrow consists of two maps and a
commutation proof. `CategoryH` separates map data from congruence, identity
preservation, and composition preservation. Those completed constructions are
the relevant correspondence: repeatedly composing preserving transitions
preserves their interpretation.
[Comma arrows](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Construct/Comma/Type.agda),
[CategoryH](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda).

`conaled` already supplies relational composition, its exact witness
presentation, and lawful implementation/semantic projections. It also separates
raw category maps from map laws. An indexed execution helper should use these
existing contracts; it would extend their convenience for finite executions,
not fill a demonstrated absence of Felix-style composition.
[Relations](../../SquareKit/Relations.lean),
[relational category and projections](../../SquareKit/RelationalCategory.lean),
[category maps](../../SquareKit/CategoryMap.lean),
[ADR 0002](../adr/0002-relations-and-synchronization.md).

Felix also has a `Traced` interface, but its `trace` eliminates feedback state
from a morphism `a × s → b × s` using a `WF` witness. The function instance
requires a witness of a fixed state/output pair for each input. This is a
completed raw operation and witness interpretation, not a theorem of fair
processing or eventual request delivery. Sharing the word trace does not make
it the counterpart of the FRP event-history execution.
[Traced interface](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L160-L169),
[function instance](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Instances/Function/Raw.agda#L33-L37).

No missing Felix capability required by these callers was identified. The
appropriate connection to #8 is this bounded negative result and the existing
composition correspondence. Feedback, broader preservation constructions, and
full Felix coverage remain separate work. A finite indexed-execution helper
would not establish parity for them.

## Criteria for later extraction

A useful extraction should recover both source-prefix and request execution,
retain their existing checked examples, and remove repeated invariant proofs.
Its relation-preservation operation should compose with existing relational
squares and preserve path-specific honesty assumptions. Its refinement closure
should reuse Mathlib. A general scheduler, cancellation protocol, or feedback
interface needs further concrete callers before extraction.

Statement review must check that the index is the state before its action,
that a response remains an event of one transition, and that absorbing `done`
prevents later emissions. Invariant preservation must impose no fairness
premise. Source availability, source honesty, source progress, and consumer
processing fairness must remain independent assumptions in the existing
progress theorems. These distinctions are already exercised by the
[trace cases](../../Examples/FRPTrace.lean) and
[demand cases](../../Examples/FRPDemand.lean).

## Implemented reuse and statement review

| Public result | Previous caller work | Current caller work |
|---|---|---|
| `Trace.prefix_refines` | An interval induction chaining `process_refines` with reflexivity and transitivity | `Nat.rel_of_forall_rel_succ_of_le` plus the existing one-step proof; two relation instances expose the already proved laws |
| `Demand.done_persists` | An interval induction showing `done` remains absorbing | `monotone_nat_of_le_succ` on the proposition that the request is done, plus the existing `next_done` law |
| `Trace.count_mono` | Mathlib monotonicity from the successor inequality | Unchanged; it already uses the same shared result |

The two new instances require exactly `Refines.refl` and `Refines.trans`.
They impose no partial order on stored source states and no antisymmetry claim.
`prefix_refines` retains its original theorem statement and assumptions. The
completion predicate in `done_persists` is ordered by implication, so monotonicity
means that being done at an earlier step entails being done later. Its original
statement, including arbitrary action sequences, is unchanged. None of these
results requires validity, honesty, availability, or fairness.

No executable definition changed. The retained trace examples still exercise
prefix refinement through observation persistence and interleaving agreement;
the demand examples still exercise completion persistence through at-most-once
delivery, including repeated processing and known-empty output. These checked
uses preserve the original meaning while consuming the Mathlib proof results.
The new public interface consists only of the two relation instances. A custom
runner, simulation record, and generic pending-work framework were not added.

Validation commands:

```sh
direnv exec . lake build Examples.FRPDemand
direnv exec . ./check.sh
```

The targeted build passed, including the unchanged trace and demand examples.
The fresh source check passed all 103 modules, and the exhaustive axiom audit
passed with only `propext`, `Classical.choice`, and `Quot.sound`. The new proofs
build without warnings; existing module-system migration warnings remain.
Local documentation links and whitespace checks passed. Proof infrastructure
is unchanged; audit regression tests are not needed for this refactor.
