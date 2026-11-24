# Combining independently supplied state operations

[#519](https://github.com/VladimirMarko/conaled/issues/519) compares three checked
routes on [one frozen contract](state-operation-comparison/contract.md): direct
conjugation, a small native tuple-operation helper, and Mathlib first-order
signature transport. Each recovers the same independently supplied concatenation
on `List Nat × PUnit`. The selected state is `[4]`; concatenation's unit is `[]`;
the independent result constant is 17. None is silently identified with another.

The implementation uses
[OperationTransport](../../Applications/ModelCombination/OperationTransport.lean),
[SignatureTransport](../../Applications/ModelCombination/SignatureTransport.lean),
and the [initial checked client](../../Examples/StateOperationCombination.lean).
It retains #437's native `Combination`, its stronger arbitrary-carrier rejection
contracts, and its Boolean, ordered-list and independent-constant clients.

## Shared contract and observations

The native prefix action and observer remain independently supplied. The binary
operation and its associativity and two unit laws are supplied on the pair
carrier. All three routes construct an operation on native list state through
the explicit `listPair` equivalence. Their full operation recovery equations and
checked presentation equalities retain argument order and every state value.
The selected concatenation `[8,9]` with `[4]` gives `[8,9,4]`, and the combined
observer returns 3. Observation by length remains noninjective; recovery of the
state operation uses the supplied equivalence rather than inversion of length.

The native helper's binary operation agrees exactly with Mathlib's `Equiv.mul`.
Its associativity proof reuses `Equiv.semigroup`; its unit proofs use cancellation.
The tuple helper admits an arbitrary argument index type, without requiring a
signature. The signature route uses `Equiv.inducedStructure` and
`inducedStructureEquiv`. `realize_transport` reuses `HomClass.realize_term`, and
`equation_transport` derives preservation of all supplied open equations. Binary
associativity and both unit equations are checked specializations of that result.
This route introduces no new syntax, signature category or model framework.

`common_iff` requires exactly the agreement equation needed to identify an actual
shared operation. Native append satisfies it; projection onto the first argument
does not. Prefixing fails to distribute over both arguments of concatenation.
The universal rejection quantifies over an arbitrary joint carrier with exact
action and binary recovery and proves the same obstruction. Carrier equivalence
does not supply extra mixed laws. The mathematical rejection and the retained
[encoding failures](state-operation-comparison/attempts.md) are separate evidence.

## Changed arity after interface freeze

The initial routes passed before their [source hashes](state-operation-comparison/frozen-interfaces.sha256)
were recorded and [unary reversal was selected](state-operation-comparison/extension.md).
Those three frozen source files were not edited for the extension.
[UnaryOperationTransport](../../Applications/ModelCombination/UnaryOperationTransport.lean)
adds native unary extraction and a disjoint unary signature symbol. The independently
supplied reversal operation is defined on the pair carrier and its involution law
is checked there. All three routes recover reversal; native and signature routes
prove the involution law. The extended signature also recovers the original binary
operation unchanged.

| Route | Initial work | Reused for the unary extension | Remaining caller work |
|---|---|---|---|
| Direct | Define conjugation; prove recovery, associativity and both unit laws by cancellation | Equivalence cancellation and existing native operation laws | Define unary conjugation and prove recovery/involution locally |
| Small helper | Tuple transport and full recovery; native binary extraction; reuse Mathlib algebraic transfer | The same tuple definition and recovery theorem at Unit arity | Add unary extraction and a generic involution lemma; supply the concrete operation and its law |
| Signature | Give binary/nullary symbols and their structure; derive term and equation transport; state side laws as terms | The same term/equation transport for a disjoint unary extension | Give the new symbol interpretation and involution term; simplify its concrete semantics |

This is proof-reuse evidence from one author, not an independent author trial or
a productivity measurement. The signature route reuses equation transport across
arities; the native helper keeps ordinary operations directly callable. Both
require the same independently proved side laws. The direct route remains short
and inspectable for this bounded example. These results support retaining the
small helpers and the comparison; they do not justify compulsory signature
adoption or a general model-amalgamation programme.

## Native FIFO consumer

[StateOperationFIFO](../../Examples/StateOperationFIFO.lean) supplies tail separately
on the pair carrier. Its native `Ops` use transported concatenation and singleton
states for enqueue, transported tail for deletion, and native head observation.
`fifo_eq_native` proves equality with the existing list implementation, and
`all_runs` recovers every existing command run. The interleaved sequence enqueue 8,
enqueue 9, delete, enqueue 4 yields `[9,4]` and head `some 9` from the empty state.
This is a checked result by reduction, not a measured execution or cost bound.

`relational_client` reuses `symmetric_correct` and `Simulation.client_empty` under
their original hypotheses. A second generic specialization retains `client_eq`
for arbitrary relations. Invertible recovery is stronger than this relational
contract, which is neither replaced nor required to supply inverse state maps.
The consumer demonstrates a usable native interface; no FIFO migration is made.

## Statement review and limits

The supplied laws concern the independently defined pair operations. The generic
constructors derive the transported operations and their laws, with no desired
combined law as a premise. The checked inputs inhabit the hypotheses. Explicit
point/unit and result/observation inequalities guard against accidental sharing.
The universal negative case ranges over alternative joint carriers, not only the
canonical formulas. Existing universal singleton and invariance rejections remain
checked through their original public contract.

The helpers allow different source and target universes and arbitrary tuple-index
universes; the concrete client selects ordinary Type. All operations use supplied
inverse data and computable definitions. No existence-only equivalence is chosen,
no classical search is introduced, and no modeled or measured cost result is
claimed. The signature language has total operations on one sort; dependent
sorts, partiality, automatic overlap discovery, extra mixed equations and sheaf
amalgamation are outside this comparison. A larger mixed-operation client belongs
under #288/#235 when selected, and does not follow automatically from this delivery.
