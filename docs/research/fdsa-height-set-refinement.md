# Cached height-balanced trees as the Set ADT

This increment addresses FDSA Chapter 9 obligations **C09-037** and **C09-059**.
It connects the actual cached local-update algorithms to the existing
`Search.AbstractSet.Refinement` interface. The canonical obligation owner is
`docs/history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter09-obligations.md`.
The algorithmic dependency is the preceding generic height-balanced update
increment, including its ordinary AVL specialization and complete-annotation
preservation proofs.

## Source correspondence

FDSA Figure 5.1, printed page 65, gives the inorder commuting equations for empty,
insertion and deletion, together with a Boolean membership observation. Figure
6.1, printed page 78, separates the four executable Set operations from the
abstraction function and invariant used in their specification. Exercise 9.4,
continued on printed page 112, asks for the analogous correctness results with
an arbitrary fixed integer tolerance at least one.

Those three pages of the available official book PDF were individually inspected
for this increment. The complete preparation paper also records its author's
reading of these pages and the actual shared Lean APIs. The canonical ledger
identifies the companion interpretation as `AVL_Set.S`; no fresh reading of that
Isabelle theory is claimed. The Lean construction below follows the available
book specification and the existing local algorithms directly.

The shared refinement record is a proposition with seven fields. It does not
package a replacement implementation. `HeightBalance.deleteOps` contains exactly
the existing empty tree, `HeightBalance.insert ann d`,
`HeightBalance.delete ann d`, and `Search.OrderedMap.containsKey`. Its four field
equations are definitional. The insertion and predecessor-deletion algorithms
therefore remain the local rebalancing programs established by the preceding
increment. Membership remains the comparison path through the original annotated
tree. Computing an inorder list is part of the mathematical view, not the query
program.

## Three distinct representation conditions

For an annotation algebra `ann`, tolerance `d` and state `t`, the view and complete
validity are

```text
view t       = Trees.inorder (Cached.erase t)
SetValid t   = HeightBalance.ValidD ann d t
               ∧ OrderedList.Strict (view t).
```

`ValidD` already combines recursive correctness of the **entire** cached
annotation with the actual height-balance predicate. Its first coordinate is not
merely an equation for a projected height. The separate strict-order condition
provides key uniqueness and licenses the comparison-path membership theorem.
The structural Set observer is `Trees.setTree (Cached.erase t)`; it is defined
independently of the query program.

The raw operations need only decidable strict comparison on the payload. They
exist for every natural tolerance, including zero. `SetValid` itself needs only
the strict-order relation, and the empty state is valid for every natural
tolerance. The Boolean theorem `member_inorder` uses a linear order and strict
inorder alone: it has no cache, balance or positive-tolerance premise.

The full refinement and the inherited Set laws additionally require `1 ≤ d`.
This hypothesis is consumed by auxiliary invariant preservation under insertion
and deletion. It is not needed to define the programs or to establish their
ordered-list commuting equations. Element and annotation universes remain
independent; neither annotation equality nor annotation ordering is required.
The supplied algebra provides its own empty annotation, so no inhabited payload
or fabricated payload witness is introduced.

## The seven fields and their proof owners

`HeightBalance.inorderRefinement ann d hd` targets the existing
`Search.OrderedList.ops`, with the erased inorder view, auxiliary invariant
`ValidD ann d`, and target invariant `OrderedList.Strict`.

| Refinement field | Public fact used | Essential premise |
| --- | --- | --- |
| `empty` | Empty tree erases to the empty inorder list | None |
| `auxiliary_empty` | `validD_nil` | None |
| `insert` | `HeightBalance.inorder_insert` | Strict initial inorder |
| `auxiliary_insert` | The invariant component of `validD_insert` | Complete initial `ValidD`, positive tolerance |
| `delete` | `HeightBalance.inorder_delete` | Strict initial inorder |
| `auxiliary_delete` | The invariant component of `validD_delete` | Complete initial `ValidD`, positive tolerance |
| `member` | `member_inorder`, from the actual ordered-map query theorem | Strict initial inorder |

The interface supplies auxiliary and target validity to each nonempty-state
field, but the commuting and query proofs deliberately use only the premises
they need. No eventual source Set law is assumed in constructing the record.
Target closure follows from the actual commuting equations and existing
ordered-list laws through `Refinement.laws`.

`HeightBalance.setLaws` then changes only the observer. The equivalence
`Trees.mem_inorder_iff_mem_setTree` transports ordered-list membership to the
independent structural Set observer through `DeleteLaws.congr_observe`. Thus
empty, insertion, membership, deletion and all validity-preservation fields are
inherited together. No recursive implementation or Set-law induction is repeated
in this adapter.

The ordinary module uses the height annotation and tolerance one. Its operations
agree with the public `Trees.AVL.insert` and `Trees.AVL.delete` aliases, and its
full validity is `AVL.Valid` conjoined with strict erased inorder. The existing
`validD_one_iff` transports the auxiliary predicate. This keeps the generic and
ordinary algorithms, their complete validity and their operational refinement
connected without duplicating recursion.

## Histories, prefixes and representation agreement

The existing interface already provides execution for arbitrary lists of mixed
insertion/deletion updates. `Refinement.execute` identifies the observed final
list with actual ordered-list execution; `Refinement.member_execute` identifies
every final Boolean query answer. The derived `DeleteLaws` supplies final
validity, independent structural Set execution and every-prefix validity.
`prefix_valid` takes an arbitrary natural prefix length, including lengths beyond
the word; no length side condition is added.

The generic module adds two useful comparisons. `inorder_execute_eq` applies the
same abstract word to two valid states with equal initial erased inorders, using
possibly different positive tolerances and different annotation algebras and
universes. Each execution commutes with the same target-list execution, so their
final inorders agree. `member_execute_eq` transports the same argument through
the actual query programs. These conclusions do not identify concrete shapes or
annotations, and they do not assert injectivity of the inorder view, annotation
commutativity or physical sharing.

The clients also consume the exact positive-integer tolerance bridge: an integer
`D ≥ 1` is represented by `D.toNat`, whose coercion back to an integer is the
original `D`. A negative integer truncated to zero is not covered by that
positive-domain theorem. An empty-carrier instance uses `PEmpty` and a supplied
annotation, obtaining its empty-state and refinement facts without producing a
payload or query value.

## Distinguishing consumers

`Examples.HeightSetRefinement` connects the public refinement, law and history
contracts to the following independently worked outcomes. It reuses prior
height-update fixtures where they already express the required mathematical
distinction.

| Group | Outcome and premise distinguished |
| --- | --- |
| S01 | The word insert 3, insert 1, insert 2, insert 2, delete 9, delete 1 has observed prefixes `[]`, `[3]`, `[1,3]`, `[1,2,3]`, `[1,2,3]`, `[1,2,3]`, `[2,3]`. The actual interface supplies prefix validity and final query agreement. |
| S02 | Tolerances one and two produce different valid trees with the same list history. Tolerance three permits the descending four-node chain, while tolerance two rotates it. Public cross-representation agreement does not imply equal concrete states. |
| S03 | The correctly cached, balanced tree rooted at 5 with left child 9 contains 9 structurally, but its query for 9 follows the wrong search path. Cache/balance validity cannot supply strict ordering. |
| S04 | A singleton with stored height 99 can have strict inorder and answer its payload query correctly while failing full cache validity. A correctly cached three-node chain can have strict inorder and satisfy tolerance two while failing ordinary AVL balance. |
| S05 | A balanced duplicate-key tree has nonstrict inorder `[1,1]`. Actual predecessor deletion of 1 leaves one occurrence, whereas abstract Set removal is empty. Strict uniqueness is essential for the Set contract. |
| S06 | A zero-tolerance valid singleton may become unbalanced after insertion even though cache and list observations are correct. Positivity belongs to auxiliary update preservation. The positive-integer bridge does not validate negative truncation. |
| S07 | Inserting and deleting 7 around the existing tree rooted at 4 preserves height 3 while changing maximum `6 ↔ 7` and words `[2,4,5,6] ↔ [2,4,5,6,7]`. Full Set validity includes the complete changed annotation, not only the unchanged height coordinate. |
| S08 | The empty-carrier construction preserves independent annotation universes and the absence of an inhabitedness requirement. |

The positive cases use proved hypotheses to consume the new contracts. Closed
concrete equalities provide the distinguishing observations; they do not replace
the symbolic refinement/history proofs. The negative cases identify the exact
premise whose removal would make a stronger claim false.

## Qualification boundary and remaining work

This Set refinement adds no measured operational execution, elapsed-time claim,
benchmark or new extraction run. The exact event cost of ordinary tolerance-one
specialization remains a separate obligation, even though its pure algorithms
are aliases. Generic callback costs are not assumed constant: a complete word
annotation can perform nonconstant list concatenation.

The operation-cost obligations C09-039–041, the cost portion of C09-060, later
construction and balance-factor Set row C09-090 remain open. C09-061 now has its
[ordinary repository proof owner](fdsa-height-bound.md). The complete
[operation-cost preparation](fdsa-height-updates.md#unqualified-preparation-for-measured-operation-costs)
retains the prospective tariff, recurrences, assumptions and counterexamples;
those cost claims remain unqualified. Whole-library verification, receiving quality/divergence reviews and
completion of the three-book programme retain their separate gates.

Actual validation, declaration-origin/type inspection, independent reviews and
coverage qualification belong to the exact-candidate checkpoint records. A
development compilation or this correspondence note alone does not discharge
those gates.
