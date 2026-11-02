# Exact priority-queue observations and compatible merge

This is the bounded FDSA-XH01 source draft for common priority-queue laws.
It is **uncompiled and unaccepted**. Chapter 1 remains the active prerequisite;
neither this note nor the accompanying examples closes Chapter 14 or any later
chapter. Frozen requirements, original base, statement assessments, validation
outcomes and independent review history are retained in the checkpoint's
`fdsa-control` directory. The original base is
`07e480f6ec9958d4975bb90151005b84f2907614`.

## Sources and reconstruction boundary

The source is Tobias Nipkow's Chapter 14, printed pages 179–182 / PDF pages
185–188, in the July 27, 2026 edition of
[Functional Data Structures and Algorithms: A Proof Assistant Approach](https://fdsa-book.net/functional_data_structures_algorithms.pdf).
The complete PDF SHA-256 is
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`;
the retained Chapter 14 extraction has SHA-256
`b566830b6c95d218e3fe8095914a336a35d45e0f51df8203588c02b36589fe3a`.
The manuscript is not reproduced in this repository.

The companion contracts and heap interpretations were read at Isabelle revision
`f86f290225eebcc52c1ae7dba2e098f405f51c21`:

| Primary source | SHA-256 |
|---|---|
| [Priority_Queue_Specs.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Priority_Queue_Specs.thy) | `c8ef42fadf9964735af07a9d0c6a5ec1c6a89ffe5ae2bce04865e003eda7d09a` |
| [Heaps.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Heaps.thy) | `662b2bc74840ad46a54e95ed5b62b7117806b9e0cf1407a7d70968e4d2dc95fe` |
| [Tree_Multiset.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Library/Tree_Multiset.thy) | `90524399a3894d8646c21377429a096345a0ddede243d966f8dd141853228508` |

This support revision postdates the PDF. It is not asserted to be the
manuscript's generation revision. The adapted contract mathematics is
attributed to these Isabelle sources; their applicable BSD-3-Clause copyright,
conditions and disclaimer are retained below. The exact retained notice has
SHA-256 `44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
Existing dependencies retain their own licenses and notices.

The book's Figure 14.1 contains **seven** base laws, C14-003–009. The companion
adds an `is_empty` operation and its reflection law, giving eight base laws.
Figure 14.2 adds two merge laws. The additional companion law is recorded
separately; it is not a missing eighth line in the printed figure.

## Operations, occurrences and priorities

The implementation uses the existing `Search.PriorityInterface.Operations`,
`ExactLaws`, `ExactQueue`, `exactLeftist` and `exactList`. Their definitions,
all existing queue implementations, and existing search/Huffman consumers
remain unchanged. The two new supporting modules are
`Applications/Search/PriorityMultiset.lean` and
`Applications/Search/PriorityMerge.lean`.

Ordinary views take only `Operations`: `insertOne ops e q` inserts the
singleton list; `peekEntry?` projects the entry from the actual optional
removal; `peekPriority?` projects its priority; `deleteMin` returns that same
removal's residual, or the input on failure; `isEmpty` observes failure as a
Boolean. No law, model, validity predicate, or default payload is supplied to
these executable operations.

For a selected exact queue Q, `ExactQueue.entryMultiset Q q` is the multiset
of the actual `Q.entries q`. `priorityMultiset` maps its entries through
`Prod.snd`. Full entries retain every payload/priority occurrence; projecting
priorities retains every repeated priority. Finite observations do not require
either element type to be finite, enumerable, decidable for equality, or
inhabited.

The existing `add_exact` and `remove_none` hold on **all raw states**.
Consequently, multiset insertion and emptiness reflection are unconditional
on validity. In contrast, a successful removal's minimum and residual-validity
conclusions retain the actual `Q.Valid q` premise from `remove_spec`.
An existing `ExactQueue` therefore supplies the source's weaker valid-state
laws. The converse does not follow merely from the book's contract.

If a valid q actually removes to `some (e,r)`, the proof follows that same
computed result. It establishes r's validity, e's membership and least
priority, and the occurrence decompositions

```text
entryMultiset Q q = e ::ₘ entryMultiset Q r
priorityMultiset Q q = e.2 ::ₘ priorityMultiset Q r.
```

The cardinality falls by exactly one. These equations do not use decidable
equality on payloads and do not replace multiset deletion with set deletion.
Nonempty observation alone guarantees an actual successful removal, because
the failure law applies to raw states; validity is subsequently used for the
semantic conclusions about that result.

## Common source obligations

The table records the actual existing contract consumed by each new
observation or ordinary view. The implementation's supporting theorem names
are recorded with its statement assessment. Every row retains the indicated
domain rather than introducing a total minimum on an empty element type.

| Obligation | New/reused declarations and mathematical connection |
|---|---|
| C14-001: carrier, empty, insert, minimum, deletion, model and validity | Existing `Operations`/`ExactQueue`; new `Operations.insertOne`, `peekPriority?`, `deleteMin`, and `ExactQueue.priorityMultiset`. Operations, observation and evidence remain separate. |
| C14-002: finite-support minimum | `ExactQueue.remove_spec_multiset` and `peekPriority?_eq_min`, with the private `removed_priority_eq_min` bridge to `Finset.min'` of nonempty support under a linear order. |
| C14-003: empty observation | `ExactQueue.priorityMultiset_empty`, through `entryMultiset_empty` and the existing `empty_entries`. |
| C14-004: valid empty | Existing `ExactQueue.empty_valid`. |
| C14-005: singleton insertion observation | `ExactQueue.priorityMultiset_insertOne_add`, through unconditional `add_exact`; the source's valid-state specialization follows. |
| C14-006: insertion preserves validity | `ExactQueue.insertOne_valid`, through `add_valid`; input validity is retained. |
| C14-007: deletion subtracts one minimum occurrence | `ExactQueue.priorityMultiset_deleteMin_sub_min`, using actual `remove_spec_multiset`, `priorityMultiset_remove_sub` and `Operations.views_of_some`; valid nonempty input. |
| C14-008: deletion preserves validity | `ExactQueue.deleteMin_valid` with actual `remove_spec` residual validity; its stronger valid-input result supplies the source's nonempty specialization. |
| C14-009: observed minimum is the support minimum | `ExactQueue.peekPriority?_eq_min`, through actual selected-priority membership/leastness and linear-order antisymmetry; valid nonempty input. |
| C14-010: merge adds observations | `ExactQueue.entryMultiset_merge` and `priorityMultiset_merge`, through `MergeLaws.entries_perm`; both inputs valid, no disjointness premise. |
| C14-011: merge preserves validity | The separate `MergeLaws.valid` field, with `leftistMergeLaws` and `appendMergeLaws` supplying actual witnesses; both inputs valid. |
| C14-012: companion empty reflection | `ExactQueue.isEmpty_eq_true_iff`, through `remove_none_iff_priorityMultiset` and the original unconditional `remove_none`. The result is a Boolean-to-Prop reflection. |
| C14-013: payload/priority separation | Arbitrary payloads and ordered priorities in the existing interface; the source specialization takes payload `Unit`. |

`PriorityModelExamples.SourceUnit` explicitly exposes these specializations
for arbitrary `σ`, `[LinearOrder σ]`, and `Q : ExactQueue Unit σ` with an
independent carrier universe. Its seven declarations are `empty_content`,
`empty_valid`, `insert_content`, `insert_valid`, `delete_content`,
`delete_valid`, and `get_minimum`. The separate `isEmpty_reflection` is the
companion's eighth law. Each applies the existing stronger generic result to
the actual source operation, retaining the source validity/nonempty domain.

In the source specialization, the returned priority equals the finite-support
minimum of the input multiset, and the actual deletion view has observation
equal to the original multiset minus one occurrence of that same value.
Priority equality decisions needed for finite support or subtraction remain
local to this boundary. They are absent from the central general agreement
theorem and do not impose equality decisions or an order on payloads.

The semantic `deleteMin` view explicitly returns its input on failure. This
gives a convenient stronger valid-empty behavior, while the seven source
laws leave empty deletion unconstrained. The separate `Heaps.Heap` companion
interpretation assumes preservation even for empty heaps, which is stronger
than the abstract nonempty deletion law. Those statements remain distinct.

## Atomic removal agreement and realizability

`ExactQueue.popObs Q q` observes the **actual** optional removal into
`Option (π × Multiset π)`: its selected priority and residual priority
multiset are observed together. The public argument order is

```text
ExactQueue.popObs_eq Q R hantisymm q r hq hr hobs.
```

Q and R may have independent payload types and carrier universes. Their
priority type and selected `LE` relation agree. The assumptions are validity
of the two actual inputs, equality of their initial priority multisets, and
explicit antisymmetry of that relation. No transitivity, totality, linear-order
package, equality decision or shared payload type is required.

In the empty branch, both actual removals fail by the existing exact failure
law. In the nonempty branch, each removed priority belongs to the common
input multiset and is below the other. Antisymmetry makes these priorities
equal. Cancelling this same occurrence from their two multiset decompositions
makes their residual observations equal. This cancellation does not compare
payloads. In particular, the theorem leaves tied payload selection, full-entry
residuals, raw residual states, tree shape and work unconstrained.

The finite-entry realizability result uses actual insertion into empty: choose
a list representative of a finite entry multiset and apply `Q.add` to
`Q.empty`. Empty validity, insertion validity and exact insertion prove the
claimed representative. It is an existence theorem, not an inverse or a
uniqueness statement for the observation.

Priority-only realizability takes an explicit payload value and inserts that
payload with each priority occurrence. `Unit` supplies this witness for the
source specialization. If the payload type is `Empty`, every entry list is
empty, so a nonempty priority multiset cannot be represented. Empty observation
is still represented by `Q.empty`; neither payload nor priority inhabitance
is added to the interface. A queue carrier itself is inhabited by its empty
operation.

## Compatible merge and a real sequential client

`MergeLaws entries Valid merge` is a proposition about a supplied operation
on one existing carrier. It contains exactly two fields: `entries_perm` and
`valid`. Its own type imposes no priority order. There is no new carrier,
operations field, or queue hierarchy in this evidence record.

`leftistMergeLaws` connects the existing `combineQ` to its actual entry and
validity theorems. `appendMergeLaws` uses ordinary list append, identity entry
observation and `True` validity; its evidence is order-free. The latter can
be consumed with the existing `exactList` operations when their executable
comparison assumptions are supplied.

Both full-entry and priority observations of merge are sums. Cardinalities
add, and valid-state observational commutativity, associativity and left/right
empty identities follow. Intermediate merges' validity is carried explicitly
when applying the laws again. None of these equations asserts equality of
raw representations or tied-payload removal choices. Overlap is allowed, and
self-merge doubles every occurrence. This semantic duplication does not grant
permission to spend an amortized potential twice.

The ordinary client is exactly

```text
mergeInsertRemove ops merge e q r =
  ops.remove (ops.add [e] (merge q r)).
```

Its definition sees no observation or law bundle. `mergeInsertRemove_exists`
uses raw exact insertion/failure reflection to establish an actual successful
result even before validity is supplied. `mergeInsertRemove_spec` uses the
selected exact queue and merge evidence to prove validity of the actual merged
and inserted states. Singleton insertion makes the observation nonempty, so
the actual final removal succeeds. The same result has a valid residual,
entry/priority decompositions (hence selected-entry membership), least priority,
and final cardinality equal to the sum of the two original cardinalities.
That cardinality equality follows from inserting and then deleting one
occurrence; it does not say that the deleted entry was the inserted entry.

## Direct root access and costs

The new `Search.LeftistQueue.peekQ?` directly matches the existing raw tree:
empty returns `none`, and a node returns its root payload/priority pair. Its
definition has no order premise. Agreement with `(deleteQ q).map Prod.fst`
retains just the executable comparison assumptions of `deleteQ` and holds
for raw trees. Structural `nullQ` reflection is also a raw observation fact.

The semantic `Operations.peekEntry?` computes through removal. In particular,
leftist deletion merges the children, and `exactList` removal sorts its list.
Projecting away the residual does not establish a constant-time operation.
A direct-root implementation can have the same value with a different cost
model. This unit proves no runtime or amortized bound.

The later source leftist analysis assigns zero helper costs to `mht` and
`node` under its selective tariff. Those conventions differ from the positive
local-access charges in the separately drafted cached-tree support. Neither
tariff transfers through a value theorem. Future chapter proofs must connect
each actual implementation to its own counted-operation recurrence.

## Connected examples and consequential boundaries

`Examples.PriorityModels` supplies public-theorem consumers alongside
independently determined closed observations. Its complete frozen families are:

| Case | Expected observation or boundary |
|---|---|
| Duplicate priorities `[1,1,3]` | Actual removal yields priority 1 and residual multiset `[1,3]`; cardinality 3 becomes 2 and one 1 remains. The source minimum/subtraction results are used. |
| Merge `[1,3]` with `[1,2]`, insert 2, remove | Merged cardinality 4, inserted cardinality 5, removed priority 1, residual multiset `[1,2,2,3]` of cardinality 4. The ordinary shared client and every actual intermediate validity result are used. |
| Existing exact list versus leftist realization | The actual client outputs agree after atomic priority/residual observation. List insertion order and raw tree shape remain their own. |
| Overlap, self-merge and empty identities | The two inputs may both contain 1; self-merging `[1,3]` gives two copies each. The cases consume observational algebra and valid intermediate states. |
| Independent payload universe | A `Unit` leftist queue and `ULift.{1} Unit` list queue realize `[1,1,3]`; the central theorem gives the same atomic removal observation. |
| Equal priorities, different Boolean payloads | Reversing a merge of two singleton roots changes the actual chosen payload and full-entry residual. Both priority observations are `some (1,{1})`. |
| Indiscrete Boolean priority relation | With `a ≤ b` defined locally as `True`, both selected priorities are least but reversing the merge can select different Boolean priorities. Antisymmetry is necessary for the equality conclusion. |
| Empty payloads/priorities, empty and singleton queues | Optional behavior remains meaningful without invented default values. An operation bundle cannot have an empty carrier because it has an empty operation. |
| Finite realizability | Actual insertion realizes a duplicate entry multiset; priority realization uses an explicit payload. Empty payloads cannot realize the singleton Nat priority multiset. |
| Fixed keyed insertion | For the existing fixed key/operations/entry/validity choice, insertion can collapse two same-key entries to one. Keyed coverage and the length bound hold, but exact insertion fails for that observation. |
| Three malformed leftist states | Wrong cached rank may preserve root minimum; wrong heap order may return a nonminimum; a correct minimum may leave an invalid residual. Raw content/reflection facts survive without importing valid-state removal guarantees. |

The malformed-state families also include actual insertion into an invalid
cached tree: its content is still exact by the raw insertion law, while its
validity is not obtained. The fixed keyed witness concerns the selected
existing operations and observation, not an impossibility theorem about all
keyed queue implementations.

The duplicate connections are `duplicates_certificate`, `duplicates_minimum`
and `duplicates_source_subtraction`. `input_cardinalities` connects both count
observations to the independently calculated A/B entry lists, while
`entry_stage_cardinalities` uses the public merge/add count laws and actual
client certificate for full-entry counts 4, 5 and 4. `main_client_certificate`,
`list_client_stages`, `client_input_agreement` and `main_pop` connect the same
actual sequential clients to the shared priority/residual result.

`Indiscrete.different_popObs` retains the precise missing-antisymmetry boundary.
`fixed_keyed_not_exact` fixes all operations, entries and validity in the
replacement counterexample. The private `raw_remove_entries` derives malformed
trees' content directly from the actual child merge; `corrupt_minimum`,
`wrong_order_not_minimum` and `corrupt_below_minimum` keep the three distinct
semantic failures separate. Their deletion-view cases inspect actual residuals
without applying valid-removal laws to an invalid input.

Every new statement must be read back for its actual quantifiers, universes,
chosen observation, validity assumptions and Option branches. General laws and
closed examples remain source-level evidence until matching compilation,
full candidate validation and independent Standards/Spec reviews succeed.

## Later reuse and mandatory work remaining

The source leftist, binomial, skew and pairing implementations expose merge
contracts to which this observation layer can later be connected. Their actual
structural/cache invariants, selected-tree agreements and merge algorithms
remain to be proved against their source carriers. The pinned Braun source
provides the base queue contract and does not supply a merge interpretation.
The optional merge evidence is not imposed on that source.

These later contract connections were read in
[Leftist_Heap.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Leftist_Heap.thy),
[Binomial_Heap.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Binomial_Heap.thy),
and the dated AFP sources
[Priority_Queue_Braun](https://isa-afp.org/release/afp-Priority_Queue_Braun-2026-10-26.tar.gz),
[Skew_Heap](https://isa-afp.org/release/afp-Skew_Heap-2026-10-26.tar.gz), and
[Pairing_Heap](https://isa-afp.org/release/afp-Pairing_Heap-2026-10-26.tar.gz).
Their exact file/archive identities are retained in the checkpoint's source
preflight. These later support versions also postdate the manuscript.

Existing Huffman code already uses exact occurrences and two actual sequential
removals. Its `Good` predicate combines queue validity with the independent
`Cached` invariant relating stored priorities to semantic tree weights.
Priority leastness alone does not imply least tree weight. That implementation
is supporting context; this unit adds no Huffman algorithm, dependency or
tie-specific output-tree equality theorem. Chapter 26 retains its source
cached-tree/list correspondence, coding, optimality and runtime obligations.

All C14-014–040 remain queued and mandatory: the sorted-list exercise with
constant-time minimum/removal, the actual plain-node naive merge and its
termination/content/invariant proofs, ordinary heap interpretation, heap
enumeration with its quadratic work claim, and inorder-preserving heap
construction/existence/distinct-label uniqueness with its duplicate boundary.
The existing exact list sorts during removal and does not solve Exercise 14.1.
Rank-aware leftist `combineQ` can exchange children and is not the printed
plain-node naive merge.

Every later concrete heap algorithm, representation invariant, source
operation correspondence, recurrence, resource/amortized-history premise and
exercise stays under its original chapter obligation. This reusable shared
unit neither activates those chapters nor changes the initial Chapter 2
integration prefix. Its own acceptance additionally requires accepted repaired
Chapter 1, matching immutable-candidate full validation and exhaustive axiom
audit, both independent full-scope review axes, and immediate verification of
that same candidate's record.

## Retained Isabelle notice

The following notice accompanies the adapted companion-contract mathematics.
It does not assign a new license to unrelated project code.

```text
ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2026,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

* Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
```
