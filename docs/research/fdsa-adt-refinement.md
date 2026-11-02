# Shared Set/Map contracts and refinement

This unit reconstructs the common model-oriented contracts and interface
translations in Chapter 6 of *Functional Data Structures and Algorithms:
A Proof Assistant Approach*. It uses conaled's existing relational squares
for composition. The source modules form a shared draft; acceptance, matching
compiler/audit results and independent reviews are recorded in the external
local control history. A declaration or mapping here is not an acceptance claim.

## Sources and exact correspondence

The manuscript is the [official July 27, 2026 PDF](https://fdsa-book.net/functional_data_structures_algorithms.pdf),
SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The relevant material is Chapter 6 by Tobias Nipkow, printed pp.77–83:
the general schema and Set interface on pp.77–79, Map on pp.80–81,
composition of ordered-map refinements on pp.82–83, and both directions of
Exercise 6.2 on p.83. Printed p.84 is blank.

The inspected Isabelle companion revision is
[`f86f290225eebcc52c1ae7dba2e098f405f51c21`](https://github.com/isabelle-prover/mirror-isabelle/tree/f86f290225eebcc52c1ae7dba2e098f405f51c21).
This is a pinned source correspondence, not a claim that this revision built
the pinned manuscript. The original contracts and related refinement laws
have these identities:

| Primary source | SHA-256 |
| --- | --- |
| [Set_Specs.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Set_Specs.thy) | `601f6ff60e58de9d0c608b3b40ddf9105f9eb9fbeb7caabfeb9efc038d0d99d0` |
| [Map_Specs.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Map_Specs.thy) | `54e97e50dc6e44d4d5533b92a109b50e781520c99bd0c50637b42470493b3e5d` |
| [List_Ins_Del.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/List_Ins_Del.thy) | `988921eb88b03519ec3dd365ec90e5fdcead0736065e188e99fc47f7bf206af3` |
| [AList_Upd_Del.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/AList_Upd_Del.thy) | `42f603405ff3fec058ba284c76183924139c42711ec66edaf623bd5b0a921f9a` |
| [Sorted_Less.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/f86f290225eebcc52c1ae7dba2e098f405f51c21/src/HOL/Data_Structures/Sorted_Less.thy) | `971199401fc20cd378ad3ca9c22c314bba146e44b5730dcc718a2b0f6f6a52d5` |

The shared implementations reuse the pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`, including
[`Function.eq_update_iff`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Function/Basic.lean),
[`Relator.LiftFun`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Logic/Relator.lean)
and the actual
[`AList`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Data/List/AList.lean)
operations and lookup laws. The local source/API/case preflights retain the
complete source reading, exact requirements and independent expected examples.
The Isabelle notice is retained below and beside the adapted Map contract.

## Operations, laws and observations

The modules follow the existing `Applications.Sequences.AbstractFIFO` pattern:
operations are passed to an ordinary client, while proposition-valued evidence
establishes their behavior. No generic ADT syntax, interpreter, replacement
state carrier or second refinement hierarchy is introduced.

| Module | Public role |
| --- | --- |
| `SquareKit.ValidGraphs` | `validGraph`, `liftFun_iff`, `comp_iff` connect an invariant and decoder to existing relations. |
| `Applications.Collections.Set` | `Collections.Sets.Ops`, its exact seven-law `Laws`, schema connections and an ordinary three-operation client. |
| `Applications.Collections.Map` | `Collections.Maps.Ops`, exact six-law `Laws`, function-update correspondence, lookup schema and an ordinary client. |
| `Applications.Collections.Modify` | Four-law modified interface, both translations and the two different round-trip conclusions. |
| `Applications.Collections.AList` | Thin `alistOps`/`alist_laws` realization using the actual standard finite association list. |

For sets, the decoder and invariant are separate arguments to `Laws`.
The operations are empty, insert, delete and Boolean membership. The seven
fields assert empty observation and validity unconditionally; on valid input,
insertion observes union with a singleton, deletion observes singleton
subtraction, each mutation preserves validity, and membership reflects the
decoded set. The mathematical model is `Set α`, with no finite-support,
decidability, ordering or default-element requirement in the generic contract.

Lean distinguishes Bool from Prop. `isin_preserves` uses the output decoder
`fun b : Bool => b = true`, with trivial output validity. Its equation into
Prop follows from the membership iff by propositional extensionality. This
supplies no executable decision procedure for membership in every arbitrary set.

For maps, lookup is both an operation and the decoder into `α → Option β`.
The six fields consist of empty observation/validity and the semantic/validity
pair for each mutation. A semantic field groups the selected-key equation and
all unaffected-key equations. The generic Ops/Laws therefore need no key
decision. Under a supplied decision, `Function.eq_update_iff` recovers exactly
the source's function-update equation. The actual AList and function-valued
realizations supply their own key decisions.

`Maps.lookup_preserves` needs no Laws hypothesis: observing the decoder at a
key is reflexive. Its ordinary Option output has trivial validity. There is
no seventh independent Map axiom. Value types need neither an order, equality
decision nor an inhabitant. In particular, `Option Empty` remains meaningful.

## The shared relation bridges

The unbundled predicate is

```text
validGraph I decode c a := I c ∧ decode c = a.
```

For arbitrary independently typed concrete/model inputs and outputs,
`liftFun_iff` identifies relation preservation with the conjunction of output
validity and the decoder equation, only on valid input. Set insertion,
deletion and membership and Map update, deletion and lookup consume this
bridge; initialization supplies the unconditional valid-graph pair.

`comp_iff` gives the exact existential composite:

```text
(∃ a, (I c ∧ decode c = a) ∧ (J a ∧ decode' a = b))
  ↔ (I c ∧ J (decode c)) ∧ decode' (decode c) = b.
```

The intermediate validity predicate is part of the composite invariant.
Removing it needs a separate implication. Neither bridge requires decoder
injectivity, surjectivity or a common universe for all types.

Existing `Relational.existentialSquare` maps an actual middle witness and
requires pointwise agreement of its two middle operation maps on every middle
state. Its `compRel` has the same existential body as Mathlib's `Relation.Comp`.
`Relational.transportRelations` uses `comp_iff` to expose the combined
valid-graph predicate while retaining both actual operation arrows. Equality
of observations is not equality of those middle maps. Agreement only on valid
states needs an appropriate valid-subtype route or its own correctly qualified
proof; it cannot fill the existing helper's stronger premise.

The old bundled records retain their common-universe interface. The concrete
composition examples lie in Type 0, while the new domain contracts and bridge
theorems retain independent key/value/state/model universes. This is a thin
specialization of existing preservation machinery, with no global retrofit or
claim about arbitrary Lean-program parametricity.

## Ordinary clients and concrete expectations

The Set client inserts a, inserts b and deletes a. Its exact final model is
`((decode s ∪ {a}) ∪ {b}) \ {a}` on every valid initial s. Its query at a is
false, its query at a distinct b is true, and unrelated queries are unchanged.
Both insertion validity facts are obtained at the actual successive states
before the deletion and final membership law are used.

The Map client updates a with x, updates b with y and deletes a. Its final
lookup is the corresponding nested function update. The query at a is none;
the query at b is some y when b differs from a, and none when they coincide.
All other queries retain their initial values. `client_intermediate_valid`
retains the two update states and the final state. The observation-agreement
theorems compare lawful implementations from corresponding valid inputs,
including implementations whose state types have different universes.

`Examples.SetMapContracts` realizes the contracts by ordinary function-valued
models and by pairs with a natural hidden counter. The paired invariant is
Even counter; every mutation increments it by two. This is representation
history, with no execution-cost meaning. The two-key clients have these
independently calculated observations:

| Stage | Set at keys (0,1) | Map at keys (0,1) | Counter |
| --- | --- | --- | ---: |
| Empty | (false,false) | (none,none) | 0 |
| First insertion/update | (true,false) | (some false,none) | 2 |
| Second insertion/update | (true,true) | (some false,some true) | 4 |
| Delete key 0 | (false,true) | (none,some true) | 6 |

The generic law theorems provide the observed values; separate reductions
calculate private counters. Equal-key clients, deletion of an already absent
key, and two valid states with equal observations but different counters
expose the limits of representation equality. Empty key/value cases retain
their actual domains: deletion can still change hidden state with Empty
values, while an Empty state carrier cannot provide an Ops.empty field.

The actual AList adapter has intrinsic unique-key evidence and external
validity True. Its main entries are [] then [(0,false)], then
[(1,true),(0,false)], then [(1,true)], where each displayed pair abbreviates
the standard Sigma entry. A Nat-key case starts with [(2,true)] and ends
with [(1,true),(2,true)]; the public unaffected-key law preserves lookup 2
through every step. Fin 2 alone has no key untouched by all three mutations,
so it cannot replace this latter nonvacuous case.

AList insertion prepends and erases an old binding. It supplies a useful
distinct realization, while the source's ascending ordered-list recurrence
remains a separate algorithm. Finite ALists need not represent every abstract
partial function: constant some false on Nat has every key present and cannot
be represented by a finite key list. Neither finite support nor surjectivity
is imposed on the generic model.

## Actual composition and argument roles

`Examples.ADTRefinement` wraps the even-counter Map in a Bool tag. Its first
decoder forgets the tag, with intrinsic predicate tag=true; the second decoder
forgets the counter, with Even counter. The implementation and specification
of the middle stage use the identical paired update or deletion function.
The resulting predicate is `tag=true ∧ Even counter`.

`taggedUpdateSquare` and `taggedDeleteSquare` actually use
`existentialSquare` followed by `transportRelations`. The nullary
`taggedEmptySquare` composes the two initializations through terminal relations.
The six `tagged_laws` are obtained from these composed squares, including
their output validity, and exercise the same generic Map client. Independently,
`sampleQuerySquare` horizontally composes initialization, all three actual
mutations and the ordinary lookup endpoint. `tagged_queries_from_composition`
obtains the expected (none,some true) query pair from that actual composite.
The intermediate states retain true tags and counters 0,2,4,6.

The true-tag/odd-counter and false-tag/even-counter states establish that the
two predicates are independent. They are not misrepresented as observation
failures of the particular +2 implementation. Separate Bool squares isolate
the general failures: one has matching constant-true middle arrows but needs
middle validity, while the other has fully valid equality relations but
mismatched not/identity middle arrows.

The two product examples use an even Nat state decoded by n/2. An ordinary
Nat parameter k=3 and state n=4 yield n+2*k=10, observed as 5=2+3. The ordinary
parameter is neither required even nor decoded. Addition of represented
states 4 and 6 yields 10, observed as 5=2+3; dropping either input validity
allows an odd output. These cases consume the actual `Relational.product`
relations and `liftFun_iff`, without a type-equality test guessing argument
roles or a new n-argument syntax.

## Modify translations and their different round trips

`Collections.Maps.Modify` retains empty/lookup and replaces update/delete
with `modify a f`, for unrestricted `f : Option β → Option β`. Its four laws
retain the two empty facts, whole mutation semantics and output validity.
`toMap` uses constant-some and constant-none callbacks. `Laws.toMap` derives
all six Map laws. `ofMap` matches the actual expression `f (lookup m a)` and
chooses deletion or update; `ofMap_laws` proves both branches from the original
conditional mutation laws.

`toMap_ofMap` recovers the whole original operations record by reduction,
without laws or valid-input assumptions. The reverse `roundTrip_lookup`
proves equality of all lookup results on valid input; `roundTrip_valid`
preserves validity of the reconstructed result. It supplies no concrete-state
equality. These are pure value/interface facts, not callback-sharing or
one-traversal cost claims.

`Examples.MapModify` applies the derived modified law to a nonempty
even-counter map: constant some false, identity, Option.map Bool.not and
constant none give counters 2,4,6,8, preserve the second key, and produce
some false, some false, some true, none at the modified key. The raw first
round trip is also exercised at an invalid odd-counter input, without using
a law on that invalid input. An actual AList specialization consumes the same
derived contract.

The opposite-round-trip counterexample uses a separate lawful modified
implementation with validity True. It adds one to its hidden counter when
`f none = none` and two otherwise. Identity at a present false binding leaves
the full map unchanged and returns counter one. Its reconstructed operation
invokes the constant-some-false callback and returns counter two. The public
round-trip theorem supplies full observation equality; the counter projection
proves unequal states. Imposing Even here would make that implementation
unlawful, so it remains separate from the even-counter examples.

## Statement assessment and remaining book obligations

The source assessment checks exact quantifiers, independent universes, each
validity precondition, all changed/unaffected key clauses, and the difference
between decoded equality and raw state equality. The examples provide usable
initialized and nonempty instances, actual sequential validity, matching
middle operations, both distinct missing-premise failures, and the Empty and
absence boundaries. Future compiler/axiom results and both final review axes
must match the complete immutable source candidate; source readback alone
does not establish elaboration or warning behavior.

This is shared support for C06-001–019, C06-034/036–043, composition principles
used in C05 and C06-066–067, and Exercise 6.2's C06-068–074. Rows are covered
only to their actual statements. The concrete BST and interval-list
instantiations of generic clients remain required. C06-035's full set/partial-
Boolean-map embedding is not discharged merely by distinguishing none and
some false; its general round trips and normalization remain queued.

The literal ordered-list update/deletion/map_of algorithms, tree lookup/update/
delete/split-min, ordered refinements with their extra J and strict key sorting,
all interval-list Exercise 6.1 algorithms and linear work, Set2 operations,
balanced structures, heap multiplicities/nonempty-operation premises, direct
Chapter 5 Exercise 5.3 proof and every other chapter obligation remain required.
The source's targets-minus-cutters interval difference and p.82 split-min
cross-reference correction remain in their original inventory. This unit
does not activate or complete any later chapter.

## Isabelle notice

The pinned Isabelle COPYRIGHT notice has SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
Trailing whitespace is normalized below for ordinary diff checks.

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
