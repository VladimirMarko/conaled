# Local #1014 — VFA Priqueue: requirements and reuse plan

**Planning only, 2026-11-02. Implementation is blocked until #1013 Trie is accepted.**
The chapter sequence remains Redblack → Trie → Priqueue → Binom. Earlier
Selection, Perm, Multiset/BagPerm, ADT, and Extract APIs are mathematical reuse
dependencies; they do not bypass the immediate chapter gate. This file
implements or compiles nothing, accepts no chapter, and changes no tracker,
source inventory, candidate, dependency, configuration, cache, or GitHub state.
Names and packaging remain subject to the actually accepted predecessor APIs.

## 1. Source, scope, and inspected baseline

- Complete inspected source: VFA 2.1, release cover `2026-08-24 10:11`,
  [Priqueue](https://softwarefoundations.cis.upenn.edu/vfa-2.1/Priqueue.html),
  `reference/vfa/vfa/Priqueue.v`: **273 lines, 9,029 bytes**, SHA-256
  `e4dc740bf2c3f338dedae3e6544a8d94d58fd80f810472610122b9ccc4866b9d`.
  Its footer is `2026-08-24 09:43`.
- `../source/Priqueue.inventory.json` has **43 records, two exercises,
  two module records, and zero inventoried pedagogical commands**. There are
  18 interface requirements, 11 definitions, six admitted declarations, and
  eight source-proved declarations. The interface requirements comprise
  seven parameters and eleven law obligations. Both exercises are standard;
  neither is optional or advanced. There are no Abort/Fail declarations or
  grading stubs. The commented premature module ending at line 121 and the
  inner `admit` at line 160 still need explicit treatment.
- The official versioned archive is
  <https://softwarefoundations.cis.upenn.edu/vfa-2.1/vfa.tgz>, SHA-256
  `f03296c763d78aa5bc18a545d848d398292575e5c8af4b5aa94dc25709e169b8`.
  Preserve MIT attribution and follow `../source/SOURCE-RECOVERY.md`.
  Downloaded research copies stay outside deliverables under ADR 0001.
- Inspected checkout: `3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`;
  Lean 4.35.0, revision `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
  Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`;
  Batteries `66e469188fe07963e5cf666c7d4433f45b8131c5`.
  This is an inspected candidate, not an accepted Priqueue baseline.
- Read AGENTS, architectural/domain guidance, GLOSSARY, ADRs 0001/0010,
  implementation/example-driven-development and review/build/audit guidance,
  `../REQUIREMENTS.md`, the entire chapter and inventory, the Selection plan
  and actual source statements, and `PRIORITY-QUEUE-REUSE.md`,
  `RESOURCE-AND-EXECUTION-OBLIGATIONS.md`, and relevant computational-assumption
  notes. Actual pinned priority, order-dual, permutation, multiset, extremum,
  and resource provider types were inspected. No compiler or import-closure
  validation was run. Section 10 records the exact identities.

The required result is the chapter's mergeable **maximum** queue interface
with proved laws, its actual unsorted-list realization, the maximum-selector
proofs, and qualified operation-count bounds. A priority search queue that
deduplicates keys, or a list queue that sorts before deletion, does not supply
the same implementation and cannot discharge its recurrence/cost obligations.

## 2. Architecture and concrete reuse route

Place the small source-list realization and source relation adapters beside
the existing `Applications/Search/PriorityInterface.lean` and
`ExactPriority.lean` family. A source-specific law file is warranted if it
keeps the upcoming Binom consumer from importing the list implementation.
Final names are provisional. Cross-domain/connected examples belong in
`Examples`; use ordinary functions and separate mathematical laws rather
than a new container hierarchy, comparator class, or source-module emulator.

Present the source signature using an ordinary carrier Q and separate
operations `empty`, `insert`, `deleteMax`, and `merge`, together with separate
predicates `Valid : Q → Prop` and `Abs : Q → List Nat → Prop`. A small
Prop-valued bundle of the eleven exact source laws is appropriate. Its
fields are conditional proofs, not new axioms. Do not hide validity or the
abstraction relation inside an operation, and do not duplicate the existing
general occurrence-queue interface merely to rename minimum to maximum.

The source relation contract remains necessary: it permits an arbitrary
list-valued abstraction relation whose witnesses agree up to permutation,
whereas `ExactQueue` uses one concrete observation function. Preserve that
relation and prove the adapter to the existing interface. The concrete list
instance has `Valid := True`, `observe := id`, and identity Abs. Native merge
is ordinary append and receives separate validity/occurrence laws because
the existing queue `Operations` has no merge field.

### Exact source selection through the accepted Selection chapter

Reuse the accepted generic source minimum selector with reversed key order,
not an unrelated argmax or sorting routine. Under `OrderDual`, its test
`i ≤ h` becomes the source test `h ≤ i`. For a generic key-projection version,
use `OrderDual.toDual` as the key projection without preprocessing the list.
If the accepted selector instead takes an order directly on its carrier,
provide a small explicit order-relabelling adapter and prove its equations.
No traversal or list-map cost may be silently added to an executed operation
claimed to have the source recurrence. List maps used solely to express a
proof transport are distinct from runtime preprocessing.

The exact two branches and remainder order in section 3 are the acceptance
criterion. Once that bridge is proved, reuse accepted Selection permutation,
selected-value bound, remainder bound, and measured comparison facts under
the dual order. Definitions/permutation/length do not need order laws; the
maximum proofs need a lawful total preorder. The source Nat specialization
and its executable `h ≤ i` decision remain explicit. No payload equality
decision, antisymmetry on arbitrary records, or stability assumption is
needed for the generic selector.

The current source comment mentions `Selection.select_smallest_aux`, but the
pinned Selection chapter's actual corresponding declaration is
`select_fst_leq` at 201–203: a selected minimum is ≤ the initial candidate,
without a bound-on-remainder premise. Its dual is stronger than this chapter's
`select_biggest_aux`. Reuse that stronger result and retain the exact source
wrapper with its additional hypothesis; do not invent the stale lemma name.

### Existing exact-occurrence interface

Instantiate `Search.PriorityInterface.ExactQueue Unit (OrderDual Nat)`.
Encode each source key k as `((), OrderDual.toDual k)` and decode the
priority with `OrderDual.ofDual`. Unit avoids inventing a payload/priority
consistency invariant. For the concrete source-list carrier:

- `entries p` is the mapped list of encoded keys, an observation, not stored
  state or a preprocessing step executed by insert/delete.
- `empty` is the source empty list.
- Batch `add xs p` right-folds source insert using the decoded priority of
  each entry. A singleton batch is exactly source insertion.
- `remove` maps the source `deleteMax p` result `(k,q)` to the encoded entry
  paired with the unchanged residual source list q.
- `Valid := True` is justified because every list satisfies the source
  representation invariant.

Prove all ExactLaws through the source theorems. The source removal bound
covers the residual list; permutation plus reflexivity extends it to every
original entry, which is the actual `ExactLaws.remove_spec` conclusion.
Minimum in the dual order is maximum in Nat. Keep native source merge and
its entry-permutation theorem as a separate operation/lemma; do not simulate
merge by decoding entries and reinserting them.

The validity boundary matters for subsequent realizations. Existing
`ExactLaws.add_exact` and `remove_none` quantify over every carrier state;
source laws guard their claims by Valid. They agree for the all-valid list
instance. An arbitrary source implementation cannot be adapted on its raw
carrier without more proof. Restrict to `{q // Valid q}` and lift unchanged
operations using closure proofs, then supply a concrete observation witness
`Abs q (observe q)` and transport other witnesses with abs_perm. That is the
planned seam for Binom, not a claim that its malformed raw states satisfy
unconditional occurrence laws. This chapter does not implement Binom.

Exact occurrence removal must be proved for each subsequent algorithm; it
does not follow from a total-preorder extremum bound alone. If one helper
finds a key and another performs removal, prove which occurrence each chooses
and their literal agreement. A chosen-occurrence/scan-provenance theorem may
establish this under a lawful total preorder. Antisymmetry or injective
decoding can supply other equality arguments, but must not be imposed when
actual provenance already suffices. The Binom consumer owns its scan/removal
correspondence; this shared adapter adds no such order assumption. Priqueue's
selector directly returns the actual occurrence that it removes.

| Actually inspected provider | Reuse and precise limitation |
| --- | --- |
| `OrderDual`, `toDual`, `ofDual`, `toDual_le_toDual`; Mathlib `Order/OrderDual.lean` | Explicit reversal: `toDual a ≤ toDual b ↔ b ≤ a`, with dual decisions and inverse coercions. Avoid deprecated `LinearOrder.swap`, arithmetic negation on Nat, or a maximum-bound subtraction trick. |
| Mathlib `Order/Defs/LinearOrder.lean` | A LinearOrder supplies a sufficient realization, but the actual interfaces are weaker: `ExactLaws` and `ExactQueue` require only `[LE π]`; `exactList` and `exactLeftist` require `[LE π] [DecidableLE π] [Std.IsLinearPreorder π]`; `ExactQueue.keyed` additionally requires `Std.Refl (fun a b : π => a ≤ b)`. None of these boundaries requires antisymmetry. A comparison algorithm still needs its actual executable branch adapter. |
| Accepted Selection selector, permutation, `select_fst_leq`, `select_smallest`, length and measured-count results | Reuse only after the exact source max recurrence is identified under the dual order. Earlier #1006 planning is evidence of intended coverage, not an already accepted implementation. |
| `Search.PriorityInterface.Operations` and `ExactLaws`/`ExactQueue` | Carrier, empty, batch add, and remove; exact insertion multiplicities and minimum deletion. There is no native merge field. All-raw add_exact/remove_none are stronger in scope than the source's guarded laws. |
| `ExactQueue.keyed` and weaker `PriorityInterface.Laws` | Exact occurrence preservation implies the weaker keyed contract. The converse fails: keyed replacement may lose repeated occurrences. Do not use add_covers/add_length as the source insertion specification. |
| `exactList`, `listRemove`, `listRemove_spec` | Existing list implementation appends batches and sorts by priority at deletion. Its dual is a lawful maximum observation comparator, not the source cons/linear-select implementation or its residual list order. |
| `PrioritySearchQueue.takeMin`, `takeMin_perm`, `takeMin_le` | Tail-first minimum selection with exact occurrence and original-list bound proofs. It recursively selects the tail before comparing the initial candidate; VFA compares first and carries a candidate down. Duality alone does not identify these remainders or recurrences. |
| `PrioritySearchQueue.insert`, `equal_priority_replaces` | Concrete same-key replacement illustrates why this keyed queue is not a multiplicity-preserving source realization. |
| `LeftistQueue.combineQ_entries`, `combineQ_valid`, `insertQ_entries`, `deleteQ_spec`, `addListQ_entries`; `exactLeftist` | Existing exact occurrence and native meld proofs, plus valid residual and one-element size loss. They support a common observational client if useful; they do not implement source list append/select or inherit its costs. |
| `Huffman.Priority.delete_size`, `two_deletions`, `huffman_correct` | Existing consumers demonstrate the value of the exact-occurrence contract. Huffman's minimum-weight arithmetic is not a maximum-queue client merely by changing an order name. No Huffman or graph proof is required to cover Priqueue's opening list of applications. |
| `List.Perm.mem_iff`, `length_eq`, `map`, `count_eq`; pinned Lean `Init/Data/List/Perm.lean` | Membership, residual length, encoded-entry permutation, and exact multiplicities follow from the actual source permutation. Permutation/count direction needs only the relevant BEq for counts; the converse `perm_iff_count` uses LawfulBEq. Nat has the lawful equality realization. |
| `List.count_cons`, `count_cons_self`, `count_cons_of_ne`; pinned Lean `Init/Data/List/Count.lean` | A cons adds exactly one occurrence. Do not weaken deletion to set membership or merely a maximum bound. |
| `Multiset.coe_eq_coe`, `coe_card`; Mathlib `Multiset/Defs.lean` | List permutation is exactly finite-multiset equality; card is list length. This quotient observation is separate from the source list identity relation. |
| `Multiset.coe_count`, `count_cons`, `ext`; `Multiset/Count.lean` | Relate list counts to finite-multiset multiplicities. Count-based generic statements require the actual equality assumptions. |
| `Multiset.coe_add`, `count_add`, `card_add`, `erase_cons_head`, `cons_erase`; `Multiset/AddSub.lean` | Merge adds multiplicities; deletion removes one copy. Multiset addition, not max-multiplicity union or Finset union, is the source merge observation. These are semantic observations, not replacement executables. |
| `List.argmax_mem`, `argmax_eq_none`, `le_of_mem_argmax`, `maximum_eq_coe_iff`, `Perm.maximum_eq`; `List/MinMax.lean` | Independent extremum observations. `argmax` returns an Option; `maximum` is in WithBot. Neither returns the source reconstructed remainder. Use maximality plus occurrence proofs to connect them if a client needs that observation. |
| `Resources.Measured`, `bind_erases`, `erasureSquare`, `reweight_bound` | Instrument actual branches and prove erasure before counts. Measured supports independent universes; erasureSquare's current same-universe package need not constrain every generic theorem. |
| `Resources.TreeFlattening.appendWithCost_exact` | Actual recursive append returns `(p++q, p.length)` for arbitrary lists, charging copied cons cells in the first input. Reuse this generic helper; the surrounding leaf-tree traversal is unrelated. |
| `Resources.isBigO_of_nat_bound` | Turns a proved eventual Nat bound into real-cast IsBigO. It supplies no selector recurrence, unit-comparison assumption, or tight lower bound. |

## 3. Exact source algorithms and abstraction

These are mathematical requirements for later definitions, not an
implementation in this planning file. Source keys are Nat, including zero.

```text
selectMax i [] = (i, [])
selectMax i (h :: t) =
  if h ≤ i then let (j,r) = selectMax i t; (j, h :: r)
           else let (j,r) = selectMax h t; (j, i :: r)

empty = []
insert k p = k :: p
deleteMax [] = none
deleteMax (i :: p) = some (selectMax i p)
merge p q = p ++ q
Valid p = True
Abs p al ↔ p = al.
```

Source `i >=? h` is the Boolean decision of `h ≤ i`; it is non-strict and
keeps the current candidate on ties. Each branch reuses the same recursive
tail and prepends the displaced/nonselected value on unwind. It does not
sort the residual list, call erase on a separately found maximum, or compute
the tail's maximum before deciding which candidate to pass down.

For example, the source returns `selectMax 2 [1,3] = (3,[1,2])`. The dual of
the inspected tail-first takeMin returns `(3,[2,1])`. Source deletion on
`[3,1,2]` returns `some (3,[1,2])`, while dual exactList's sort-at-deletion
returns a residual list ordered `[2,1]`. Their multisets agree, but those are
different raw results. They therefore cannot establish the source recurrence
by observational agreement alone.

The source Abs' has only the constructor `Abs_intro p : Abs' p p`, and Abs
is an alias of it. Reuse equality with explicit introduction/elimination and
the proved iff above instead of creating another general relation datatype.
Do not redefine the concrete relation as permutation. For example,
`[1,2].Perm [2,1]` holds but source `Abs [1,2] [2,1]` does not. The interface
allows several permutation-equivalent abstraction witnesses; it does not
require every permutation to be a witness.

## 4. Exact source laws and specification assessment

Preserve every source quantifier and validity premise. In this table
`upper k xs` means `∀ x ∈ xs, x ≤ k`, explicitly equivalent to source
`Forall (ge k) xs`; `~` denotes List.Perm.

| Required law | Exact obligation |
| --- | --- |
| can_relate | `∀ p, Valid p → ∃ al, Abs p al`. |
| abs_perm | `∀ p al bl, Valid p → Abs p al → Abs p bl → al ~ bl`. |
| empty_priq | `Valid empty`. |
| empty_relate | `Abs empty []`, with no additional premise. |
| insert_priq | `∀ k p, Valid p → Valid (insert k p)`. |
| insert_relate | `∀ p al k, Valid p → Abs p al → Abs (insert k p) (k::al)`. The conclusion is literal relation to that cons list, not just existence of a permuted representative. |
| delete_max_None_relate | `∀ p, Valid p → (Abs p [] ↔ deleteMax p = none)`. Preserve both directions and the validity guard. |
| delete_max_Some_priq | `∀ p q k, Valid p → deleteMax p = some (k,q) → Valid q`. |
| delete_max_Some_relate | `∀ p q k pl ql, Valid p → Abs p pl → deleteMax p = some (k,q) → Abs q ql → pl ~ k::ql ∧ upper k ql`. The bound is on the residual abstraction; input/output permutation direction is as written. |
| merge_priq | `∀ p q, Valid p → Valid q → Valid (merge p q)`. |
| merge_relate | `∀ p q pl ql al, Valid p → Valid q → Abs p pl → Abs q ql → Abs (merge p q) al → al ~ pl++ql`. It quantifies over any actual result witness. It does not require literal `Abs (merge p q) (pl++ql)` for every abstract implementation. |

Prove the source list instance from identity Abs and True validity. The three
selector results supply the nontrivial deletion proof:

```text
let (j,r) = selectMax i l; (i::l) ~ (j::r)
upper j bl → selectMax i al = (j,bl) → i ≤ j
selectMax i al = (j,bl) → upper j bl.
```

The middle statement retains the source's additional upper-bound premise,
even when supplied by a stronger accepted dual theorem. Derive remainder
length and selected-element membership from permutation. Preserve actual
occurrences, so an equal maximum may remain after one successful deletion.

The source at 103–106 explicitly asks whether the specification is adequate.
Answer this through proved consequences and checked boundaries:

1. Valid states have abstraction witnesses; abs_perm gives a well-defined
   finite multiset despite possible list-order variation. Empty validity
   ensures the interface is inhabited nonvacuously.
2. For a valid source state with `Abs p pl`, None means pl is empty, by the
   iff and abs_perm. Conversely an empty abstraction forces None. For the
   concrete list this is exactly `deleteMax p=none ↔ p=[]`; for a general
   representation it does not imply `p=empty` as raw state equality.
3. A successful deletion produces a valid residual. can_relate then supplies
   a residual witness, so the relation law is not vacuous merely because its
   last premise is Abs q ql. Permutation gives `k ∈ pl` and
   `ql.length+1=pl.length`; the residual bound and reflexivity give
   `∀ x∈pl, x≤k`. The result is an occurring maximum, not a fabricated upper
   bound that discards data.
4. For every a, removal gives
   `count a pl = count a ql + (if a=k then 1 else 0)`. Exactly one maximum
   occurrence is removed. Inserting a repeated key increases multiplicity;
   merge adds both lists' multiplicities, even when keys overlap.
5. merge_priq plus can_relate supplies an output witness; merge_relate
   determines its multiset. Its statement does not assume permutation closure
   of Abs. The stronger literal append relation holds in this concrete list
   instance and must not be silently promoted to an interface axiom.
6. The source contract imposes no stability/tie identity on generalized
   payloads, structural equality between implementations, efficient
   observation function, physical sharing, allocation policy, or operation
   cost. Invalid raw states are outside its laws. Each such extra property
   needs an actual theorem/model if used by a consumer.

Use the accepted Multiset/BagPerm observation to connect these results to
finite-multiset addition and one-copy erasure. The concrete Abs relation
remains identity. A finite set or membership equivalence cannot replace the
multiset observation: `[7,7]` and `[7]` have the same members but different
queue behavior after deletion.

## 5. Complete 43-record map

Every exact lexical source ID occurs once below. Targets denote obligations
for the implementation phase, not declarations supplied by this document.

| Source record | Intended Lean obligation / reuse |
| --- | --- |
| `Priqueue.PRIQUEUE.priqueue@67` | Ordinary carrier parameter Q, separate from operations and law proofs. |
| `Priqueue.PRIQUEUE.key@68` | Exact source key specialization Nat; generic selector/order reuse retains it. |
| `Priqueue.PRIQUEUE.empty@70` | Empty operation parameter of Q. |
| `Priqueue.PRIQUEUE.insert@71` | Single-occurrence insertion `Nat → Q → Q`, not keyed replacement. |
| `Priqueue.PRIQUEUE.delete_max@72` | Total Option-valued maximum removal returning both key and residual state. |
| `Priqueue.PRIQUEUE.merge@73` | Native binary merge operation, kept separately from the existing non-meld queue Operations. |
| `Priqueue.PRIQUEUE.priq@75` | Separate validity predicate on raw states. |
| `Priqueue.PRIQUEUE.Abs@76` | Separate relation to lists of Nat keys; do not replace arbitrary source Abs by equality or automatically permutation-saturate it. |
| `Priqueue.PRIQUEUE.can_relate@77` | Proved law field: every valid state has an abstraction witness. |
| `Priqueue.PRIQUEUE.abs_perm@78` | Proved law field: witnesses for the same valid state agree up to permutation. |
| `Priqueue.PRIQUEUE.empty_priq@80` | Proved valid-empty field. |
| `Priqueue.PRIQUEUE.empty_relate@81` | Proved empty-list abstraction field, without a validity premise. |
| `Priqueue.PRIQUEUE.insert_priq@82` | Proved insertion-closure field. |
| `Priqueue.PRIQUEUE.insert_relate@83` | Exact relation to k::al for every valid input witness. |
| `Priqueue.PRIQUEUE.delete_max_None_relate@85` | Both directions of empty-abstraction iff None on valid states. |
| `Priqueue.PRIQUEUE.delete_max_Some_priq@87` | Successful removal preserves validity. |
| `Priqueue.PRIQUEUE.delete_max_Some_relate@89` | Input-to-output cons permutation plus maximum bound on every residual abstract key, with all source premises. |
| `Priqueue.PRIQUEUE.merge_priq@95` | Merge preserves validity from both valid inputs. |
| `Priqueue.PRIQUEUE.merge_relate@96` | Every actual merge abstraction is a permutation of the two input abstractions appended, preserving all repetitions. |
| `Priqueue.List_Priqueue.select@129` | Exact comparison-first maximum selector and remainder reconstruction; prove reuse of accepted Selection under reversed order. |
| `Priqueue.List_Priqueue.select_perm@139` | Let-bound selector result satisfies `(i::l).Perm (j::r)` independently of order laws. |
| `Priqueue.List_Priqueue.select_biggest_aux@147` | Source upper-bound-premise wrapper concluding i≤j from the selected result; adapt actual `select_fst_leq`, not the stale source comment name. |
| `Priqueue.List_Priqueue.select_biggest@155` | Every element of the selected remainder is ≤ the selected key. Remove the inner admit as well as the terminal Admitted. |
| `Priqueue.List_Priqueue.key@170` | Concrete Nat specialization agrees with the source signature. |
| `Priqueue.List_Priqueue.priqueue@172` | Exact carrier List Nat, not a sorted list, heap, set, or finite map. |
| `Priqueue.List_Priqueue.empty@174` | Empty list operation. |
| `Priqueue.List_Priqueue.insert@175` | Cons insertion preserving every occurrence and exact list order. |
| `Priqueue.List_Priqueue.delete_max@176` | None on []; on i::p return Some of the exact select result. |
| `Priqueue.List_Priqueue.merge@181` | Append p++q in the given operand order. |
| `Priqueue.List_Priqueue.priq@192` | True on every list, justified by the total list representation and unconditional list closure proofs. |
| `Priqueue.List_Priqueue.Abs'@196` | Identity relation with the source reflexive constructor and equality characterization. |
| `Priqueue.List_Priqueue.Abs@199` | Alias/adaptor to the same identity relation; no added permutation closure. |
| `Priqueue.List_Priqueue.can_relate@204` | Witness p itself for every list p. |
| `Priqueue.List_Priqueue.abs_perm@214` | Identity witnesses are equal, hence permuted; this proves the required weaker interface property. |
| `Priqueue.List_Priqueue.empty_priq@224` | True validity of []. |
| `Priqueue.List_Priqueue.empty_relate@227` | [] relates to [] by the actual identity abstraction. |
| `Priqueue.List_Priqueue.insert_priq@230` | Validity of cons, retaining the source wrapper's input premise. |
| `Priqueue.List_Priqueue.insert_relate@233` | From p=al obtain k::p=k::al; exact source witness order. |
| `Priqueue.List_Priqueue.delete_max_Some_priq@237` | Residual list validity for a successful deletion, without using a hidden nonempty invariant. |
| `Priqueue.List_Priqueue.delete_max_None_relate@243` | Identity abstraction to [] iff the actual delete result is None; check nonempty selector pairs produce Some. |
| `Priqueue.List_Priqueue.delete_max_Some_relate@249` | Substitute both identity abstractions and use selector permutation/maximum bounds; retain occurrences and returned residual. |
| `Priqueue.List_Priqueue.merge_priq@258` | True validity of append; this source-proved declaration lies inside the second exercise and still maps to an actual field proof. |
| `Priqueue.List_Priqueue.merge_relate@262` | Actual merge result witness equals p++q; after identity substitutions its required permutation is reflexive. |

## 6. Exercises, module commands, and prose coverage

| Exercise | Exact required work |
| --- | --- |
| `select_perm_and_friends`, 137–165, standard, 3 stars | All three selector theorems, with exact remainder recurrence, maximum orientation, source aux wrapper, and removal of both the inner admit and all terminal admissions. Reuse dual Selection proofs through an actual operation bridge. |
| `simple_priq_proofs`, 241–269, standard, 2 stars | None iff empty abstraction, successful deletion's occurrence/maximum law, merge validity, and merge abstraction. The already source-proved merge_priq still participates in the completed instance. |

There are no optional/advanced exercises to omit and no inventoried
Check/Print/Compute/Extraction commands. The lexical inventory does not
subsume these actual module/command and prose obligations:

| Source span / command | Disposition |
| --- | --- |
| 3–24, queue operations and applications | Preserve the four-operation mergeable queue API. Highest priority means maximum Nat in this chapter; earliest-event and Dijkstra/Huffman use cases need an appropriate priority order rather than the same unmodified numeric maximum. The application list does not require implementing simulations, convex hull, Dijkstra, or an additional heap-sort chapter. |
| 26–49, implementation/performance comparison | Establish actual list empty/insert/delete/merge costs in section 7. The described heap/BST N log N merge is a repeated-removal/insertion strategy, not a lower bound on every native meld algorithm. A BST dictionary with same-key replacement needs multiplicities/tags before it can implement this occurrence queue. |
| 53–62, natural-number comparison discussion | Retain the Nat source specialization and state the unit-comparison abstraction. Source unary-Nat discussion is not a native Lean Nat runtime bound. Efficient-key reuse comes through accepted Extract comparison realizations with their actual laws and range assumptions. |
| `From VFA Require Import Perm` at 64 | Use accepted permutation/Forall/reflection APIs and pinned Lean providers; no new permutation relation or Coq tactic framework. |
| `Module Type PRIQUEUE` at 66; `End PRIQUEUE` at 101 | Complete the source parameter/law interface with all eleven conditional proof fields and exact Nat key type. A signature's source Axioms become proved laws for every supplied realization. |
| 103–106, specification assessment | Provide the nonvacuity, exact-one-occurrence, genuine maximum, multiplicity-preserving merge, and validity/abstraction boundary arguments in section 4. |
| `Module List_Priqueue <: PRIQUEUE` at 111; `End List_Priqueue` at 271 | Construct a complete law-bearing realization using the actual operations and relation. Module syntax/naming may become namespaces/structures; the full checked interface obligation remains. |
| 113–121, premature module-ending experiment | Preserve the lesson that omitted implementation fields cannot establish the signature. The End at 121 is commented, not an actual Fail record. Use a guarded expected missing-field example if appropriate during implementation, or explain completeness using the actual fully constructed law bundle; leave no broken file/admitted placeholder in the build. No exact Rocq diagnostic text is required. |
| 126–164, selector/proof adaptation and bdestruct | Show the min/max duality through the exact executable equations, use ordinary Boolean/decidable reflection and induction, and explain the stale auxiliary-lemma reference. An inner admit is a proof gap even if a later source theorem calls it solved. |
| 188–199, trivial representation/abstraction | True validity is mathematically appropriate for this implementation. Identity Abs remains stronger than multiset observation and is not silently weakened to permutation. |
| 209–219, freedom of abstraction order | Interface witnesses may differ in order but must agree in multiplicity. This does not require the concrete identity relation, or every possible implementation relation, to accept every permutation. |
| 224–269, operation characterizations | Every supplied concrete theorem instantiates its exact source interface field. Preserve Some/None branches, both validity assumptions for merge, and all abstraction witnesses. |

## 7. Resource obligations and cost model

The source explicitly sets aside the time per comparison. First prove counts
in that unit-comparison model, then state how a non-unit comparison cost
changes the bound. Reuse the accepted measured Selection recurrence under
the exact dual operation adapter, or instrument the unchanged source
recursion if its accepted public API lacks the required observation. Prove
erasure to the actual select/delete operations; do not attach a desired
length formula to an arbitrary equivalent maximum-finding program.

Let n be the length of the input list to selectMax after its separate initial
candidate; let N be the full queue length. These are distinct sizes.

| Operation / observation | Exact recurrence and consequence |
| --- | --- |
| Selector comparisons | Empty tail costs 0. Either nonempty branch costs 1 plus the recursive tail count. Exactly n comparisons, regardless of input order or ties. No early stop occurs when a maximum is already known. |
| Selector invocations | Empty tail costs 1; either branch costs 1 plus its recursive count. Exactly n+1 calls, including the terminal call. |
| Selector list constructions | Empty tail constructs no residual cons; either branch constructs one cons after recursion. Exactly n residual cons constructions in this syntactic model, separately from pair/call costs. |
| Empty / insertion | Empty returns []; insert constructs one cons without traversal or comparison. Use a specified constant entry/constructor charge; do not claim a particular runtime allocation count from a value equation. |
| Delete comparisons | On [] cost 0; on i::p, use the selector's p.length comparisons. Hence exactly `N-1` with Nat subtraction, including N=0 and N=1. |
| Delete call/traversal work | With one delete entry charge plus each invoked selector call, [] costs 1 and a nonempty queue costs 1+N. Thus N+1 in both cases. Pair/Option construction contributes only separately specified constant overhead. |
| Delete residual size / constructions | Successful deletion has residual length N−1, established from permutation, and the selector model reconstructs that many cons cells. Empty deletion returns None and constructs no residual list. |
| Merge append copies | Reuse `appendWithCost_exact p q = (p++q, p.length)`. It traverses/copies the first input, not the second. If terminal calls are charged too, the corresponding count is p.length+1. |
| Merge comparisons | Zero; append does not compare keys or eliminate duplicates. |

Combine these counters with explicit primitive weights to obtain constant
empty/insert bounds, a linear delete bound, and a bound in the first merge
input's length. Merge is therefore O(length p+length q+1), but it is not
Theta of total size for every operand split: `merge [] q` performs no copied
cons work regardless of q's size. Conversely, length-p growth supplies the
relevant worst-case linear family. Raw merge order affects this cost even
though its multiset result commutes.

Use `Resources.isBigO_of_nat_bound` only after stating the size-indexed
natural cost and proved inequality. For delete, an explicit N+1 traversal
count and the N−1 comparison count also show the endpoint cases that an
unqualified linear slogan can hide. Value equality to an existing sorted-
deletion or heap queue gives no count equality.

For non-unit comparisons, charge the actual sequence of candidate/head
comparisons. A uniform bound C on each such comparison yields at most C*n
comparison work for select. An unbounded Nat/Int bit-cost account needs key
magnitudes/bit lengths as parameters. The earlier lockstep unary ≤ model
has a cost involving the smaller operand, not just their difference; use
the accepted model/bridge if giving that refinement. Do not infer this model
from native Lean Nat or reuse the introductory Nat.ltb wording as an exact
description of this selector's non-strict Boolean test.

List cons reconstruction and append copies are explicit mathematical
observations. They are not proofs of pointer sharing, physical allocation,
garbage collection, peak live space, or constant stack behavior. No
wall-clock benchmark is requested in Priqueue. Provide meaningful checked
executions for its operations/counts, and expose the accepted source API and
comparison realization to the later Binom measurement task. That task owns
its actual bounded random comparisons, repetitions, timing, and saved results;
this chapter neither preclaims those measurements nor creates a new harness.

## 8. Connected cases and statement review

Cases must use the public operations/contract and independently expected
values or observations. They are implementation obligations, not executions
performed by this plan.

| Case | Purpose |
| --- | --- |
| Empty versus zero | `deleteMax [] = none` and `deleteMax [0] = some (0,[])`. Zero is a valid key, not an emptiness sentinel. |
| Both branches and tie | Select with current candidate larger, smaller, and equal to the next head; the true branch is h≤i and retains i on equality. Connect each result to permutation and the upper bound. |
| Exact remainder | `selectMax 2 [1,3]=(3,[1,2])` and deletion of `[3,1,2]` leaves `[1,2]`. These distinguish the source from tail-first and sort-at-delete implementations. |
| Repeated maxima | Deleting `[2,7,7,4]` returns `some (7,[2,7,4])`; a second successful deletion still returns 7, leaving `[2,4]`. Count/length and the public source law establish exactly one removed copy each time. |
| Duplicate-rich merge | Merge `[7,2,7]` with `[7,0]` returns the exact append with three occurrences of 7. Deletion returns 7 and leaves two occurrences; use the merge and deletion laws together, not membership checks alone. |
| Identity Abs boundary | `[1,2]` and `[2,1]` are permuted but fail the concrete identity relation. They nevertheless determine equal finite-multiset observations. |
| Structural versus observed merge | `merge [1,1] [2]` and the swapped merge differ as lists but are permutations. Their append-copy counts are 2 and 1 respectively. |
| Genuine maximum | From a concrete nonempty deletion and its law, prove returned membership in the original list, residual upper bound, all-original upper bound, and one-element size loss. An arbitrary upper bound without occurrence would fail this client. |
| Dual exact-queue client | Encode the source list into Unit/dual entries. A real build/merge/remove client consumes ExactLaws' original-entry minimum bound and decodes it back to maximum Nat while retaining duplicate counts. It uses source merge separately, since Operations has no meld. |
| Comparator-independent permutation | Exercise generic selector permutation/length without assuming a lawful order; maximum statements separately consume the actual total-preorder/reflection facts. Do not prove a maximum claim for arbitrary comparisons. |
| Cost endpoints | Select an empty tail: zero comparisons/one invocation. Delete empty and singleton: zero comparisons but distinct Option results. A four-element nonempty queue has three comparisons; merging empty on the left has zero append copies. |
| Abstraction witness scope | The concrete complete law bundle has Valid=True and a witness for every state. Generic contract clients retain validity and use residual/output witness existence rather than assuming all raw states or all permuted lists are related. |

A generic key-projection selector may also exhibit different payload orders
among equal-priority residual entries; neither the source Nat contract nor
ExactQueue asserts payload stability. Do not generalize equal maximum keys
into equality of residual list shape across implementations. A common
occurrence observation is the appropriate comparison.

Independent statement review must inspect the actual elaborated types:
source max versus existing min, the two selection branches, input-to-output
permutation orientation, the redundant-but-retained aux hypothesis, None
iff empty abstraction, successful residual validity/witnesses, merge's
universal output-witness premise, identity versus permutation Abs, and the
all-raw versus validity-guarded interface scope. Audit both inner and final
admissions; building a field record with assumed laws is not a realization.

## 9. Implementation order and acceptance gate

After #1013 is accepted:

1. Capture its accepted baseline and inspect the actual accepted Selection,
   Perm, multiplicity, ADT, and Extract APIs. Confirm a small placement beside
   the priority interfaces and exact source-law/observation boundaries.
2. Establish the max-selector recurrence bridge through reversed order and
   reuse the accepted proofs/counts where their exact hypotheses fit. Preserve
   list reconstruction and ties; introduce no alternate selecting algorithm
   merely because its extremum observation is the same.
3. Define the four source list operations and identity abstraction/True
   invariant; supply all eleven source law fields and both exercise groups.
   Connect a build/merge/delete client to the exact occurrence specification.
4. Establish the Unit/OrderDual ExactQueue adapter and separate native merge
   observation law. Keep raw validity gaps explicit for future Binom; do not
   require that future implementation to expose unconditional raw laws.
5. Integrate measured source selection/delete and generic append counts,
   prove erasure and the independent recurrences, and document the qualified
   resource claims. Verify the meaningful boundary/duplicate/remainder cases.
6. Map all 43 records, both exercises, both module records, and all substantive
   prose/command dispositions to actual declarations and evidence. No source
   signature axiom or admission may survive as a new project assumption.
7. Run required focused checks and exact-candidate full Nix/direnv validation,
   audit regression/managed proof audit, both independent review axes, and
   final verification immediately before acceptance. Follow the existing
   implementation workflow and integration-root/example requirements; this
   planning task starts none of those compiler or review-loop actions.
8. Root records local chapter acceptance and immediately creates/exposes/
   uploads the recovery checkpoint with local tracking, source mappings,
   proofs, reviews, checks, and exact Git identities. Only then may Binom
   implementation begin. The future measurement exercise remains separately
   tracked and cannot be credited from this source plan.

Remaining work is explicit: accepted-API reconciliation, exact dual selector
and cost adapters, the proved relational source contract/list realization,
the existing exact-queue/merge observation bridges, connected cases, and
the integrated proof/build/review gate. None was implemented or compiled in
this preparation. Redblack's already reviewed plan remains frozen unchanged.

## 10. Exact inspected identities

Workspace-relative paths identify inspected bytes, not accepted Lean results.
`Lean/` paths are relative to the pinned toolchain source root
`/root/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean` and are recovered
from the stated Lean release/commit, not copied into the project. The prior
chapter specifications are planning references; actual accepted public API
identities must be captured when this chapter begins.

| File | SHA-256 |
| --- | --- |
| `reference/vfa/vfa/Priqueue.v` | `e4dc740bf2c3f338dedae3e6544a8d94d58fd80f810472610122b9ccc4866b9d` |
| `reference/vfa/vfa/Selection.v` | `ff343099ae0fd551648a8fa2bf0adfe32bf5fb158389cee211ff8d1b32c28e11` |
| `work-state/source/Priqueue.inventory.json` | `ed1d31505ff5a96128f3cfe6ed8fe7e033ce95d058b76196abbecfd3931168fb` |
| `work-state/source/PRIORITY-QUEUE-REUSE.md` | `1dc0ab40596354df759ca43ca0764809af9d60f222552b60ecdb05ced8ed5595` |
| `work-state/source/RESOURCE-AND-EXECUTION-OBLIGATIONS.md` | `5d26488e0127a072c61c3db0323deececfd428023d71cf51b4db6b4055e5e03f` |
| `work-state/source/COMPUTATIONAL-ASSUMPTIONS.md` | `eb4e8eb1cc4d04f6fe536e87622c4943d6af160b555e7ae4266979484f3eca30` |
| `work-state/specs/1006-Selection.md` | `ebc4d57d34ff0a6abe26a208702ff14c8ff391de65b7ca5908ed9d960362c3f3` |
| `work-state/specs/1011-Extract.md` | `eccc61e739b5a3ccc0e496ad13828a93b76ec925f3bd80047b799c833a9846ff` |
| `work-state/specs/1013-Trie.md` | `ff3874effda4d56e22a84d16b685e723c72dc210d70a1aec0d38799b7ceaa56e` |
| `conaled/Applications/Search/PriorityInterface.lean` | `8c1b6d6a08c8d0be52efe211affa7032d02b52e383e8bbdd4a4af82b22ee18a6` |
| `conaled/Applications/Search/ExactPriority.lean` | `f2965206add281267f898b3c7e46261a5f4b8f87a43c83e97463bd296633c879` |
| `conaled/Applications/Search/PrioritySearchQueue.lean` | `e1fce1ccb69db8f9b384584367f9a967fd9efb111a08a67554d82f230538c59f` |
| `conaled/Applications/Search/LeftistQueue.lean` | `14a0d1130e04e2576dea2abb452823b5504cdbac9dbc1010f15a2f327c6bc378` |
| `conaled/Applications/Huffman/Priority.lean` | `c06cfbe28f488d5aed5ddc2cc2f8002244eb22818c875b3f752dfccc393048e1` |
| `conaled/Applications/Resources/Measured.lean` | `b5f76c8dfdb3cc9dd28a356bebd12787b3a7add61abba1022d474604a6979667` |
| `conaled/Applications/Resources/Growth.lean` | `5e252788c2365d3f9140288a1d51f2ef38270798419af40df8505590a7d20dcc` |
| `conaled/Applications/Resources/TreeFlattening/Core.lean` | `e9d7610efc7120ca846412f8b951c0c59a6cdfd840af0432222fba95cfed9ce2` |
| `conaled/.lake/packages/mathlib/Mathlib/Order/OrderDual.lean` | `fe55a7686c08d14e66788072bd69b9551c319b311ea3979f4c166d67808a122d` |
| `conaled/.lake/packages/mathlib/Mathlib/Order/Defs/LinearOrder.lean` | `80b40cffbc66b648612bd1195941e30e52d8309701d280a23dc2fc48047a9209` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Multiset/Defs.lean` | `09b5004aedbde97d9fc6f3ad40510eb2d120c7485088c30cf2e2f72e81d72334` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Multiset/Count.lean` | `79d856913f87026ffc066d5aa0a73164f83cdaa5a17773af824b6d4e1368cce0` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/Multiset/AddSub.lean` | `1fd0c73c2dc4c3a2ff08e32939490e1b710e283c83cbaf73166eddc07a0f9f1e` |
| `conaled/.lake/packages/mathlib/Mathlib/Data/List/MinMax.lean` | `7f83e6fb67ff2def7aa99d6a81a06eda1707ef003c437013c54a1b6bae2ea496` |
| `Lean/Init/Data/List/Perm.lean` | `d91620e1c9767119095b48601266b8c5267ed4ab0afb7fe31a4780209b9751fb` |
| `Lean/Init/Data/List/Count.lean` | `4cf663e7844728b7762b9421fedfe044d33ff3a89ccc7e6f4bfd213c6ab336b6` |
| `conaled/AGENTS.md` | `5d017d009307c72a7616d7afe0bee9fb5a7105fe2f6f4e1da3fdccf070d4b4fe` |
| `work-state/REQUIREMENTS.md` | `85fbb013efa28c2aa1827dfaaab9cca5c3498f1da51b446972aa67dd690a7f84` |

Read-only reconciliation confirmed all 43 source IDs exactly once and in
source order, both exercise names/ranges, both module declarations/endings,
the zero-command inventory with its prose/comment exceptions, and all 27
source/provider digests. Redblack's frozen digest was independently unchanged.
This bookkeeping check is not mathematical or chapter completion.
