# Admissible semantic type extension with retained cursors

Issue [#262](https://github.com/VladimirMarko/conaled/issues/262) asks whether an
existing compatibility proof can survive a new type interpretation. The checked
case adds a dependent cursor carrier to the operation-only FIFO language. Its
meaning is a list with a selected position in `Fin (length + 1)`. Admission
relates the implementation's measure to list length; local rules preserve both
queue contents and the chosen position. The existing public FIFO client theorem
is reused under its original simulation premise. This is a bounded semantic
type extension in Lean's host language, not an extension of the fixed STLC AST.

Implementation: [CursorExtension](../../Applications/Sequences/CursorExtension.lean)
and [checked clients](../../Examples/SemanticTypeExtension.lean). Inspection base:
`497daa15afc2a38a0640eccfcc5e96100709aa74`. No existing client proof or interface
was changed.

## Primary-source check

The [DRFCaml paper](https://plv.mpi-sws.org/drfcaml/paper.pdf), Definition 5.1,
presents only three core conditions; its formalization has ten. Theorem 5.1
establishes rule compatibility. Theorems 5.2 and 5.3 separately connect syntactic
typing to semantic typing and operational data-race freedom. Section 6 permits
new semantic types satisfying the core conditions, with separately proved
compatibility for new rules. It does not grant arbitrary casts compatibility.

The [official deposited artifact](https://zenodo.org/records/13933463) is version
v1, published 2024-10-15, DOI `10.5281/zenodo.13933463`. A fresh download of
[`ocaml-modes.zip`](https://zenodo.org/records/13933463/files/ocaml-modes.zip)
on 2026-11-05 matched the publisher's MD5
`fb9913677c24df548cfb223cf08ceb1d` and SHA256
`a9153d95edf94c187a124fa9759bd8a391f71a8a6ae841651fc7469d47c4a81d`.
The archive records no Git commit. This deposited version and checksum identify
the inspected revision; no Git revision or Rocq rebuild is claimed.

The following inventory rechecks the detailed
[earlier issue inspection](https://github.com/VladimirMarko/conaled/issues/262#issuecomment-6525320517)
against those downloaded primary files. Paths and line numbers refer to that
archive. `README.md:219–258` records changes from the paper: world growth uses
mutable inclusion and inclusion of the union of mutable/read-only worlds;
shared modality changed or removed some numbered conditions; a duplicability
condition is derived. Paper condition numbers cannot be identified mechanically
with artifact fields.

`src/unary/logrel.v:455–515` supplies a nonexpansive carrier before the ten
`sem_type` fields. The carrier is indexed by two worlds, local context, mode
and value. The surrounding interface also requires decidable/countable context
data, context-token operations and the Iris logical-relation state.

| Artifact field | Required behavior |
|---|---|
| `sem_type_global_context` | Global values permit arbitrary local-context replacement. |
| `sem_type_local_context` | Interpretation survives local-context enlargement. |
| `sem_type_uncontended` | Transport under mutable-world and combined-world inclusion; no Uncontended premise. |
| `sem_type_contended` | Portable, Contended values allow arbitrary replacement of both worlds. |
| `sem_type_mode_weaken` | Mode weakening uses a mutable-world interpretation and an Iris update producing an enlarged mutable world. |
| `sem_type_persistent` | Many, Aliased values are persistent. |
| `sem_type_shared` | The stated Global/Many/Aliased/Portable value transfers its mutable world to the shared read-only world. |
| `sem_type_uncontended_portable_filter_p` | Portable values survive filtering both worlds. |
| `sem_type_local_portable_contended_weaken` | Portable, Contended values admit context replacement when the filtered old context is included. |
| `sem_type_borrow` | Many values permit the specified persistent or fresh-borrow alternative; returning resources restores the original interpretation under later. |

The borrow clause retains freshness, no duplicate entries, non-stack addresses,
invariant ownership and half-views, and token return. It is not a copying axiom
for arbitrary values.

The selected old compatibility lemma is `sem_typed_pair`,
`src/unary/ftlr/ftlr_pair.v:15–49`. Its type quantifies over arbitrary carriers
A and B with full `sem_type` instances, not a closed type syntax. It assumes
semantic typing of each operand and a semantic context join. Its final value
reconstruction uses local-context and world monotonicity.
`ftlr_context.v:206–254` derives the two environment weakenings using those
fields. `interp_env_tctx_join`, starting at line 480, calls
`sem_type_many_copy` at line 532. That helper in `ftlr_persistence.v:25–42`
uses mode weakening and world monotonicity; persistence is supplied through the
registered instance at lines 16–19. These inspected paths expose four fields:
local-context growth, world growth, mode weakening and persistence. The public
theorem still requests all ten. This is a source-path inventory, not a
machine-checked minimal-dependency result for the automation or the Iris stack.

For Capsule, `src/examples/capsule/capsule_def.v:38–39` defines `Ptr_interp`
using an existential world containing the payload at `legacy_m` and persistent
capsule-name ownership. `Ptr_interp_sem_type:216–222` constructs all ten fields
for this carrier from a full payload `sem_type` instance. Its automated proof
does not expose a minimal subset of payload laws. Capsule state and logical
relation state are additional model-specific assumptions.
`capsule_both.v:13–63` separately proves the pairing API, with function-pointer
invariant ownership and admissible payloads. The proof checks calls through
invariants, unions existential worlds, transports both payloads using world
monotonicity and combines capsule-name ownership. `capsule_def.v:10–15` models
`ObjectMagic` as a designated identity function. Correspondence to actual OCaml
execution remains a separate obligation.

The reusable pattern is admission of a semantic carrier followed by rule
compatibility and reuse of old universally quantified proofs. Worlds, mode
orders, updates, borrowing resources and Capsule tokens belong to that memory
model. None is installed as a new axiom in the local denotational experiment.

## Local interface audit and chosen boundary

| Existing public interface | Quantification and limitation for this case |
|---|---|
| `FirstOrderNaturality.naturality`, `STLCNaturality.naturality` | Arbitrary object models, maps and local preservation packages; their syntax induction still ranges over the fixed source type grammar. They do not automatically introduce this dependent cursor family. |
| `STLCRelations.Encoding`, `compile_preserves` | Arbitrary base relation and locally correct primitives; higher types are generated by the existing unit/product/sum/arrow grammar. Replacing one base representation or adding a primitive, as in #259, would not establish this new dependent type's contract. |
| `AbstractFIFO.Simulation`, `Simulation.client_eq`, `Examples.AbstractFIFO.ordinary_correct` | Arbitrary state types and relation, with empty/snoc/tail/head compatibility. They do not enumerate a type grammar. These are the selected reusable old proofs. |
| `DependentSquares.Ty`, `Ext`, `TyRep` | Split Type-indexed families and explicit dependent comparison. This can express the cursor's family, but does not itself supply the FIFO operation compatibility or a general syntax adapter. |
| `DependentJudgments.Sigma.Stable` | Formation and constructor substitution laws over a structural model; dependent elimination comparisons follow from its capability. A host Fin family is not automatically an admitted source type or an interpretation in every such model. |

The new constructor is `Cursor Q size`, with fields `value : Q` and
`position : Fin (size value + 1)`. Its semantic interpretation is
`Cursor (List α) List.length`. The semantic queue and clipping operations are
specified independently using ordinary lists, their length and `min`. Runtime
queues use the existing symmetric two-list representation; their measure is
the sum of the two physical segment lengths. It is proved equal to the
independent length whenever the original representation relation holds.

This adds observable data: positions zero and two over the same `[1,2,3]` list
are distinguished by `same_queue_distinct_position`. Thus it is not merely a
renamed representation of the old queue type. End positions are allowed,
including the sole zero position over an empty queue. Position data is retained;
no assertion of equality between distinct selected indices is justified by
proof irrelevance. Bounds are ordinary propositions in Lean, while positions
are Fin values.

`Admissible rel size` requires measure/length agreement on related queues.
This is sufficient admission for the selected Fin interpretation, not a
minimality theorem for every possible interpretation. Erased head preservation
alone would not require it; that weaker property cannot validate the new type.
`Related` retains both the original queue relation and equality of selected
indices. `select_related` admits any chosen valid position, transporting its
Fin family with the admission equality. `selected_transport` recovers equality
of the actual transported Fin value. It does not replace it with an arbitrary
inhabitant, a mere existential or the old head observation.

The new `resize` rule clips a selected index to the new queue length.
`resize_related` derives its compatibility from admission and compatibility of
the underlying queue operation. `simulation` installs that rule for snoc and
tail. `forget_simulation` projects the richer semantic state to the old list
state. `extension` composes these two simulations using the existing public
`Simulation.comp`; the composite relation retains an intermediate semantic
cursor. `old_client` calls `Simulation.client_eq`. The concrete
`retained_ordinary` calls the already public `Examples.AbstractFIFO.ordinary_correct`
and recovers `some 2` with its original assumptions supplied, not replaced.

The stronger `run_retains` applies the old `Simulation.run_preserves` at the
richer type. The worked word deletes then enqueues 4, taking `[1,2,3]` at position
2 to `[2,3,4]` at position 2. `retained_selected` checks the dependent output
transport. Deleting all elements clips position 2 to zero; repeated deletion
of empty input remains defined. Both distinct physical layouts are inhabited
and related to the same selected semantic cursor.

## Interactions and rejected candidates

The completed [#278 interaction experiment](constructor-observer-composition.md)
shows why checking old/new pieces separately is insufficient. This case uses
its explicit-interaction discipline, without duplicating the vector experiment
or assuming its theorem supplies FIFO laws.

| Rule | Old queue observation | New selected-position observation |
|---|---|---|
| Select q i | Original queue's head | The chosen i, after dependent family transport |
| Empty | Old empty/head law | Zero |
| Snoc x | Original snoc compatibility | Minimum of old position and new length |
| Tail | Original tail compatibility | Minimum of old position and new length |

The `resize_related` proof checks the cross cell between old queue updates and
the new position observer. No arbitrary extension-order commutation is claimed.

`front_size_inadmissible` refutes using only the front segment's length: the
existing related state `([1],[3,2])` denotes `[1,2,3]`, so admission would require
1 = 3. This is a checked failure of the actual admission predicate, not a tactic
failure. `reset_not_identity` refutes a proposed operation which resets the
position to zero while retaining the semantic identity operation. `reset_old_view` checks that it keeps the
queue contents, but it loses the selected position 2. Neither counterexample
changes the relation, independent denotation or requested observation to pass.
A reset operation could instead be given reset semantics, but that is a different
contract and is not the rejected identity extension.

## Same-task author-work comparison

| Obligation | Direct route | Reusable route |
|---|---|---|
| New type meaning and admission | Cursor family, physical measure and its length proof | Identical |
| New rule compatibility | `select_related`, `resize_related` | Identical |
| Entire word retains selected witness | `direct_run` reproves the list induction and command cases | `run_retains` applies existing `Simulation.run_preserves` after packaging local fields |
| Worked word, initial cursor and expected result | `direct_cursor`, `direct_head` | `retained_cursor`, `retained_head` |
| Existing ordinary client's theorem | Could replay its word calculation; no such proof reuse is needed by the direct comparison | `retained_ordinary` invokes the unchanged public theorem through `extension` |
| Dependent transport | Explicit `Fin.cast` along measure equality | Same cast; `selected_transport` consumes the retained relation |

This is one implementer's checked comparison, not independent author timing or
productivity evidence. The reusable route needs a Simulation package and a
forgetful relation in addition to the new family and rule proofs. It avoids a
new word induction and rewriting the old client's proof. The direct proof is
short for this small syntax; no claim of universal effort reduction follows.
Development diagnostics included underconstrained `congrArg` functions in the
forgetful package, explicit initial cursor inference for the empty case, and
an unavailable arithmetic tactic replaced by simplification. These were host
elaboration/tooling issues; the two incompatibility theorems are mathematical
failures. The semantic observations were not weakened during those repairs.

## Scope, adequacy and remaining owners

The demonstrated contract is semantic relation preservation, old head equality
and exact transported selected-position retention. It implies no syntactic
conservativity or reflection, normalization, canonicity, inference completeness,
operational memory safety, data-race freedom or resource bound. No universal
AST, lattice, new axiom or global proof-irrelevance policy was introduced.

Operational conclusions would need an execution semantics for cursor queues,
a simulation connecting execution to these independent list/Fin meanings,
representation invariant preservation under the actual memory discipline,
and separate failure/divergence, interference and cost contracts where relevant.
Total Lean functions and finite examples do not supply those adapters.

The shared-interface mismatch is bounded: `Simulation` admits this richer
carrier directly, while the fixed STLC type grammar and its `Val`/encoding
recursion cannot name both old queues and dependent cursor positions as a new
type constructor. [#235](https://github.com/VladimirMarko/conaled/issues/235)
owns whether to develop a typed family/signature adapter preserving formation,
substitution and selected Fin transport for this concrete client. No retrofit
is selected here; the old ordinary and syntax APIs remain usable.
[#36](https://github.com/VladimirMarko/conaled/issues/36) and
[#200](https://github.com/VladimirMarko/conaled/issues/200) coordinate any wider
language/metatheory consequences.

[#267](https://github.com/VladimirMarko/conaled/issues/267)'s observation work
and completed #278 retain their distinction between forgetting observations
and validating new cross interactions. [#288](https://github.com/VladimirMarko/conaled/issues/288)
owns compositional theory extension; [#291](https://github.com/VladimirMarko/conaled/issues/291)
owns all-model expansion and witness descent. This single admitted carrier is
not an expansion theorem for every model and has no new dependency on #291,
#257 or inactive #260. The decision is to retain the bounded admission/reuse
example and its failures, without adopting a universal extension interface.
