# Classical control and selected finite search

The implementation for [#380](https://github.com/VladimirMarko/conaled/issues/380)
formalizes the bounded construction in the
[paper report](classical-control-selected-search.md). The public checked entrypoint
is [Examples/ClassicalControl.lean](../../Examples/ClassicalControl.lean).
The implementation remains experimental: its source and target syntax are specific
to this comparison, and no existing consumer or compiler is migrated.

## Contracts and entrypoints

| Contract | Checked implementation |
|---|---|
| Independent raw certificate meaning and decoder | `First`; `first_indices`, `none_indices`, `decode_correct`, `first_unique` in [Certificate.lean](../../Applications/ClassicalControl/Certificate.lean) |
| Pure logical interpretation for any predecessor-closed pole | `Source.adequacy`, `Source.continuation`, `Source.peirce` in [Adequacy.lean](../../Applications/ClassicalControl/Adequacy.lean) |
| Constructed weak delivery pole, properness and restricted coherence | `Source.Pgood`, `good_nonempty`, `invalid_terminal`, `restricted_coherence` in [Machine.lean](../../Applications/ClassicalControl/Machine.lean) |
| Finite search, full ordered-prefix invariant and direct-recursion equality | `certified_boundary`, `search_runs_direct`, `search_delivery_eq`, `search_normalizes` in [Search.lean](../../Applications/ClassicalControl/Search.lean) |
| Open mixed substitution and both directions of step simulation | `Representation.subst`, `forward`, `backward`, `observations` in [Frames.lean](../../Applications/ClassicalControl/Frames.lean) |
| Changed last-result policy | `last_terminates`, `changed_policy_runs`, `changed_policy_good` in [LastPolicy.lean](../../Applications/ClassicalControl/LastPolicy.lean) |

Names in the table are under `ClassicalControl`; the search and last-policy
results are under `Source`. The decoder checks a raw record's position, numeral,
evenness witness and ordered oddness witnesses. `First` uses an exact list-prefix
equation. Its index consequences recover every condition in the report; the
`None` equation certifies the entire input. Neither predicate mentions a pole,
machine execution or the direct search function. `first_eq_direct` proves that
a valid record determines the direct result, and `first_unique` derives uniqueness.

`Pgood` uses the weaker `Weak` predicate on terminal deliveries for `[1,2,4]`.
Its definition makes no search-program assumption. `search_good` proves actual
membership from a finite execution. The accepted later-even record still fails
`First`; the last-policy program reaches that record and also belongs to the pole.
The invalid terminal and universal-pole examples distinguish predecessor closure
from an output discipline. `no_closed_bottom` uses adequacy and the separate
output-free invariant for the four typing rules.

## Representation and substitution

[SourceSyntax.lean](../../Applications/ClassicalControl/SourceSyntax.lean) and
[TargetSyntax.lean](../../Applications/ClassicalControl/TargetSyntax.lean) have
separate mutually inductive term/stack carriers. Both use de Bruijn variables
`Fin n`, so a process term has type `Term 0`. A saved stack contains only closed
terms, including the closed results of any stored callback function. Its binder
operations therefore leave saved constants unchanged.

A source callback cell stores an actual function `Value → Source.Term 0`.
`Source.callback` constructs the permitted closures. `IsCallback` requires
pointwise equality with a member of that family before the callback reduction
rule applies. The ambient stack datatype can hold a different function, but
there is no callback step for it without that admission proof. Target `next`
frames store a continuation term, list, index, oddness witnesses and tail;
`Target.dispatch` interprets those fields.

`StackRel.callback` carries the pointwise function equation and relates the
captured term and tail separately. It does not identify a source function with
a target constructor. The relation has no last-policy clause. `forward` and
`backward` cover each allowed related step, including restoring a whole saved
stack and discarding the current tail. `observations` transfers a delivery in
both directions with the complete raw value unchanged.

`Representation.subst` is quantified over open mixed terms and arbitrary related
substitutions into any target context size. Its lambda case lifts substitutions;
its `walk` and `test` cases recurse into the continuation argument. Saved stacks
are closed constants. The checked `initializer_substitution` and
`open_test_substitution` cases exercise both scanner constructors with a free
continuation variable. This retains the domain repair made during the report's
review, rather than restricting substitution to pure proof syntax.

## Statement review and checked cases

The intended `[1,2,4]` result is `(position 1, numeral 2, half 1, odds [0])`.
`multiple_witnesses` obtains its execution through `search_runs_direct` and its
certificate through `direct_first`. Target cases use `observations` through
`frame_search_complete`: all-odd `[1,3,5]` returns `None [0,1,2]`, empty input
returns `None []`, and `[0,2]` selects position zero. Decoder examples preserve
these complete records and reject the later-even record and internal `Odd`.

The boundary theorem starts at any exact decomposition into an odd prefix and
remaining suffix. Its saved continuation and current stack are both the output
stack for that entire input. Induction on the suffix constructs a delivery;
`scan_first` preserves every prefix witness. `Step.deterministic` and
`search_delivery_eq` exclude another delivered value, while `search_normalizes`
proves accessibility of all successors of the initial search state. The result
is stronger than existence of one terminating run and says nothing about
normalization of arbitrary lambda/control terms.

The logical statements quantify over arbitrary atom falsity sets and poles.
The Peirce theorem imposes no inhabitance hypothesis on its second formula.
Adequacy permits runtime terms in the closing substitution but its derivation
has only variable, abstraction, application and control rules. The pure class
excludes literal saved continuations and every scanner, return and last-policy
instruction. The clean runtime invariant permits continuations created during
reduction, yet excludes output stacks and output instructions. This distinction
is required by the coherence proof.

The decoder, search and representation results use no realizability hypothesis.
Conversely, logical adequacy supplies no arithmetic extraction theorem.
`no_prefix_for_later_even` rules out every prefix certificate at position two
of `[1,2,4]`; failure is not limited to the particular empty witness list.
`pending_suffix` and `discard_suffix` retain the list, index, witness list and
stack tail involved in continuation reinstatement.

## Source and limits

The source remains Krivine's
[*Realizability algebras: a program to well order R*, arXiv:1005.2395v4](https://arxiv.org/pdf/1005.2395v4),
§1, pp. 3–4 and 7–8. The retrieved PDF checksum matches the report:
`84677db217259cdc1a2a84049511fb04ae08b875e235030785060bf4a7940796`.
The borrowing is application/capture/reinstatement, predecessor closure,
orthogonality, and the implication/Peirce argument. Primitive lambda binders,
finite search, raw certificates, the delivery pole and the closure/frame
comparison belong to this bounded construction. The implementation does not
import the paper's quantifiers, combinator translation or arithmetic extraction.

Direct recursion and control search have the same complete selected observation.
The control route additionally exposes a classical instruction and a checked
change of continuation representation. This comparison establishes neither a
performance improvement nor reduced author effort. Host functions are confined
to the specified callback family; there is no arbitrary callback compiler.
The step relation treats arithmetic and list operations as primitives; these
proofs make no wall-clock or allocation claim.

The independent report remains the record of the paper construction and finite
fixture evaluation. The Lean declarations now supply universal proofs for the
contracts listed above. Candidate build, exhaustive audit and independent review
evidence are owned by the enclosing implementation loop. #107 remains paused;
#108's held-out theorem remains unselected. Any extension of the proof-like class
or arithmetic extraction contract needs a separate coherence/adequacy argument,
coordinated through #235.
