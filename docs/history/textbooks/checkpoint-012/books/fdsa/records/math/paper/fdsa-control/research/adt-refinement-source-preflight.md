# Model-oriented Set/Map refinement: bounded source preflight

Prepared 2026-11-02. **Source preparation only.** This proposes no frozen scope,
implementation, final review, acceptance, or chapter activation. Chapter 1 remains
the sequential prerequisite; root's session 83124 is the sole compiler/checker
for candidate `07e480f`. All existing inventories and requirements remain intact.
The parallel `adt-refinement-api-preflight.md` owns exact existing Lean API and
reuse assessment; the present note owns the source meanings and mathematical
boundaries of a possible small shared contract/composition unit.

## 1. Inspected source and identity

Read the complete saved Chapter 6 text, including the end of Exercise 6.2 on
printed p.83. Printed p.84 is blank; no continuation of that exercise was omitted.
Read `Set_Specs.thy` and `Map_Specs.thy` in full, the relevant Chapter 5 text and
inventory rows, and the imported list definitions/laws needed to distinguish
strict ordered refinement from a weaker content observation. No new source
search or download was needed.

| Source | Exact location / retained identity |
|---|---|
| FDSA, July 27, 2026 PDF | Chapter 6 by Tobias Nipkow, printed pp.77–83 (physical PDF pp.83–89); Chapter 5 §§5.1, 5.3–5.4, printed pp.60,63–67. `book-source/functional_data_structures_algorithms.pdf`, SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`; official URL <https://fdsa-book.net/functional_data_structures_algorithms.pdf>. |
| `book-source/chapter06.txt` | Page-delimited reading text: interface/model/schema lines 9–93; interval exercise 97–125; maps and Figure 6.2 at 126–162; ordered map refinement 163–222; complete Exercise 6.2 at 223–231. |
| Isabelle companion pin | `f86f290225eebcc52c1ae7dba2e098f405f51c21`; source URL prefix `https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`. This is the inspected mirror revision, not an assertion that it generated the July PDF. |
| `src/HOL/Data_Structures/Set_Specs.thy` | SHA-256 `601f6ff60e58de9d0c608b3b40ddf9105f9eb9fbeb7caabfeb9efc038d0d99d0`; basic locale lines 11–27; ordered refinement 31–76; binary-operation extension 81–93. |
| `src/HOL/Data_Structures/Map_Specs.thy` | SHA-256 `54e97e50dc6e44d4d5533b92a109b50e781520c99bd0c50637b42470493b3e5d`; basic locale 11–25; ordered refinement 30–73. |
| `List_Ins_Del.thy` / `Sorted_Less.thy` | Same source directory/pin. SHA-256 respectively `988921eb88b03519ec3dd365ec90e5fdcead0736065e188e99fc47f7bf206af3` and `971199401fc20cd378ad3ca9c22c314bba146e44b5730dcc718a2b0f6f6a52d5`. The latter's lines 11–14 define the imported sorting predicate using strict `<`. |
| `AList_Upd_Del.thy` / `Tree_Map.thy` | Same directory/pin. SHA-256 respectively `42f603405ff3fec058ba284c76183924139c42711ec66edaf623bd5b0a921f9a` and `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43`. Full pair labels carry semantic values; the tree interpretation uses `Map_by_Ordered` with extra invariant `True` at lines 45–57. |

The recorded theory digests come from the preserved Chapter 5/6 provenance.
Isabelle's pinned BSD-3-Clause `COPYRIGHT` digest is
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
Source inventory mappings are C06-001–019 for the general schema/Set laws,
C06-034–043 for Map, C06-066–067 for ordered composition, and C06-068–074
for the modified interface; Chapter 5 contributes C05-014–016,025,028,037–041.
The repository's AGENTS, architectural/domain guidance, glossary and relevant
relational/composition ADRs were read. Planning does not begin a new review loop.

## 2. Exact contracts

Let `S` be the concrete set carrier, `α` its element type, `decode : S → Set α`
its observation, and `I : S → Prop` its validity predicate. Operations are
`empty : S`, `insert/delete : α → S → S`, and `isin : S → α → Bool`.
Neither `decode` nor `I` is an operational argument that callers must execute.
Figure 6.1, p.78, has exactly these **seven** mathematical laws:

| Source law | Lean-oriented mathematical meaning |
|---|---|
| `set_empty` | `decode empty = ∅`. |
| `set_isin` | `I s → (isin s x = true ↔ x ∈ decode s)`. |
| `set_insert` | `I s → decode (insert x s) = decode s ∪ {x}`. |
| `set_delete` | `I s → decode (delete x s) = decode s \ {x}`. |
| `invar_empty` | `I empty`. |
| `invar_insert` | `I s → I (insert x s)`. |
| `invar_delete` | `I s → I (delete x s)`. |

The two empty laws are unconditional. There is no uniqueness/canonical-form
law, no finite-support premise, and no linear-order requirement on the generic
element type. Chapter 5 p.60 explicitly reserves linear order for its concrete
BST realizations. `Set2` adds union/intersection/difference and six laws, each
with **both** input validity assumptions; these are not additional lines of
Figure 6.1 or a reason to omit a second represented input from the generic schema.

For maps, take carrier `M`, key type `α`, value type `β`, operations
`empty : M`, `update : α → β → M → M`, `delete : α → M → M`, and
`lookup : M → α → Option β`. The model is the unrestricted function type
`α → Option β`. Unlike the set decoder, **lookup is both the abstraction and
an interface operation**. Figure 6.2, p.81, has exactly **six** laws:

| Source law | Mathematical meaning, writing `f[a := v]` for a point update |
|---|---|
| `map_empty` | `lookup empty = (fun _ => none)`. |
| `map_update` | `I m → lookup (update a b m) = (lookup m)[a := some b]`. |
| `map_delete` | `I m → lookup (delete a m) = (lookup m)[a := none]`. |
| `invar_empty` | `I empty`. |
| `invar_update` | `I m → I (update a b m)`. |
| `invar_delete` | `I m → I (delete a m)`. |

The function equalities constrain the changed key **and every other key**.
The equivalent pointwise update law says the lookup at `a` is `some b` and
all lookups at keys different from `a` agree with the old map; deletion says
`none` at `a` and the same unchanged-key clause. Such a pointwise contract
can avoid a public decidable-equality assumption. If `Function.update` is used
as the model operation, its equality decision can be supplied in a local
classical specification or a concrete realization. No order on keys, order on
values, decidable value equality or default value belongs in the general laws.
Lookup's own simulation clause is reflexive, and its output invariant is
trivial, so neither supplies a seventh independent Map axiom (pp.81,83).

### Bool, Prop, Option and finite representations

In Isabelle/HOL, Boolean terms also express propositions. Lean distinguishes
`Bool` and `Prop`; `isin s x` cannot simply be equated to the proposition
`x ∈ decode s`. Reflection as above retains the executable Boolean observation
and arbitrary `Set α` as the abstract model. A supplied reflection law gives a
membership decision for a **valid represented** set; it does not supply a
global executable decision for every arbitrary set. An abstract characteristic
function uses a supplied decidable predicate or classical noncomputability.
An invariant likewise needs no executable checker unless one is separately exposed.

The p.80 view of sets as Boolean-valued maps needs an explicit interpretation
when followed by the partial-map carrier. For example, encode membership by
`some true` and nonmembership by `none`. Decoding by the `some true` test
recovers the set; the opposite round trip recovers a partial Boolean map only
under the normalization that forbids `some false`. `none`, `some false` and
`some true` are three distinct lookup results. In particular, deleting a stored
false value is an observable change. A domain-of-definition interpretation of
partial maps is another observation, not an equality of those three results.

`Option β` permits the Lean case `β = Empty`: every lookup then returns none,
delete/modify remain meaningful, and update has no value argument that can be
supplied. This is a harmless Lean generality extension of the specification;
it is not a claim that HOL admits empty types. With `α = Empty`, observations
are the unique empty-domain function. The carrier of an actual Set/Map
realization is inhabited by its `empty` field; no global `Inhabited β` follows
or is needed. Empty cases alone do not test the nontrivial update/query laws.

Finite lists and trees may realize only finite sets/supports. The model types
still contain arbitrary sets and arbitrary partial functions. On natural keys,
the map constantly returning `some false` has infinite support and cannot be
the lookup of a finite-support representation. No law requires surjectivity
onto it. Conversely, the abstract contract does not require every valid state
to have finite support: only a concrete finite representation or a finite
update history from empty supplies that fact. Neither observation equality nor
the validity laws imply injectivity of decode or equality of concrete states.

## 3. Generic schema and exact composition boundary

On pp.78–79 the book supplies an abstraction `d : T → A` and validity `I`.
For each operation, valid represented inputs imply both output validity and
simulation of the matching model operation. Ordinary arguments and outputs
use identity observation and the predicate `True`. Nullary operations have
an empty, hence true, precondition. Represented argument **roles** must be
explicit: an ordinary parameter whose Lean type happens to be `T` does not
thereby become a represented state.

For the functional representation relation

```text
R t a := I t ∧ d t = a,
```

the conjunction of output validity and the commuting observation equation is
exactly relation preservation, with equality relations on ordinary parameters.
Existing relational squares/products can express this schema; a new universal
signature language is not needed merely to state these contracts. Bool-to-Prop
membership reflection is an explicit observation boundary, not a malformed
equality between different types.

For a second functional representation `e : A → B` with validity `J`, relational
composition retains an actual middle witness. Its functional special case is

```text
(∃ a, (I t ∧ d t = a) ∧ (J a ∧ e a = b))
  ↔ I t ∧ J (d t) ∧ e (d t) = b.
```

Thus the composite decoder is `e ∘ d`, with validity
`I t ∧ J (d t)`, unless a separately proved implication makes the second
conjunct redundant. Every operation must use the same middle operation, or
an explicit agreement law on the valid intermediate arguments. Its output
validity is needed again at the next operation; it cannot be discarded after
proving one observation equation. For several represented inputs, retain all
their intermediate validity assumptions. This is both the source's generic
schema and the reason the ordered-list proofs compose.

The companion API inspection confirms that the existing `existentialSquare`
helper asks for agreement of its two middle maps on every middle state. The
source's literal shared list operation meets that premise directly. A merely
valid-state agreement must instead be packaged on valid subtypes or otherwise
proved sufficient by a separate adapter; it is not the existing helper's
unqualified premise. This source-level distinction should survive the chosen API.

A small independent negative case makes the missing premise visible. Let
`T=A=B=Bool`, both decoders be identity, source validity be `True`, middle
validity be `u=true`, source and middle operations both return true, and the
final abstract operation be identity. The first route preserves its relation
on all inputs; the second preserves its relation on its valid input true.
Their composite agrees with identity only on that middle-valid domain. At
false, incorrectly retaining source validity alone would assert `true=false`.
The counterexample concerns a dropped input premise, not a failure of proper
relational composition.

For concrete client composition, validity is also a sequential obligation.
A Map client that updates `a`, updates `b`, then deletes `a` must establish
`I m₁`, `I m₂`, `I m₃` in order before applying the next law. For `a≠b`, its
final observations at those two keys are `(none, some newValueAtB)`;
for `a=b`, both are none. Agreement for a specified interface-only client
follows from these laws. The same claim for an arbitrary Lean function does
not follow merely from its polymorphic type or the presence of an operations
record: it requires an actual client proof or an existing applicable language
preservation theorem.

## 4. Ordered refinements retain two invariants

Chapter 5 pp.64–67 uses strict inorder lists. Its Figure 5.1 specifies empty
inorder, insertion/deletion refinement to `ins_list`/`del_list`, and membership
reflection. `List_Ins_Del` then supplies content laws and preservation of strict
sorting. Insertion's set-content law is unconditional; deletion's source law
requires strict sorting. Deleting once from `[1,1]` leaves a 1, so deleting one
occurrence is not set subtraction on arbitrary duplicate lists.

`Set_by_Ordered` generalizes the unbalanced presentation by an extra predicate
`J t`. Its premises are `J t ∧ StrictSorted (inorder t)`; it separately assumes
`J empty` and preservation of J. The resulting Set decoder is
`List.set ∘ inorder`, and its invariant is **exactly that conjunction**.
Strict-sortedness preservation follows from the operation refinement plus the
list-level preservation law; it does not prove a balancing/cache predicate J.
The actual later source specializations include `RBT_Set.thy:278–281` with
`J=rbt` and `AVL_Set.thy:211–214` with `J=avl`. These are concrete consumers of
the same semantic route, with distinct balancing obligations.

`Map_by_Ordered` is analogous, using full semantic pair inorder and
`sorted1 ps := StrictSorted (ps.map Prod.fst)`. Its resulting invariant is
`J t ∧ sorted1 (inorder t)` (`Map_Specs.thy:52–53`). The lookup law must be
applied to the **updated/deleted state** when composing the map observation.
This requires both preservation of J and the newly established key-sortedness;
the pinned proof explicitly uses those facts at lines 60–66. The unbalanced
tree instance chooses J=True, but later refinements need not.

Values have no order here. A lexicographically increasing list
`[(1,10),(1,20)]` can still repeat a key; deleting its first binding leaves
lookup 1 equal to `some 20` rather than none. Map inorder keeps the value
component, unlike the annotation-erasing traversal for cached tree labels.
The existing inventory's p.82 split-min cross-reference correction remains:
use the full-pair `Tree_Set.split_min`, not the interval-cache operation of
§5.6.4. None of these concrete list/tree algorithms or their proof lemmas is
implemented by the proposed shared contracts alone.

## 5. Exercise 6.2: both translations and their round trips

The replacement interface retains empty/lookup and uses
`modify : α → (Option β → Option β) → M → M`. Besides the two empty laws,
its two mutation clauses, under `I m`, are

```text
lookup (modify a f m) = (lookup m)[a := f (lookup m a)]
I (modify a f m).
```

The source imposes no condition `f none = none`. The function can create an
absent binding, overwrite a present value, delete it, or preserve its observation.

**From modify to update/delete**, define
`update a b m := modify a (fun _ => some b) m` and
`delete a m := modify a (fun _ => none) m`. Substitute these functions in the
two modify laws, retaining empty/lookup, to derive all six original Map laws.
This proof must work from the interface laws, without inspecting a representation.

**From update/delete to modify**, compute `v := f (lookup m a)` and return
`delete a m` if v is none or `update a b m` if v is some b. The case split
uses no default β. The None and Some branches supply their respective mutation
equation and invariant preservation; pointwise lookup at a and all other keys
establishes the required whole-function equation. The definition evaluates
the displayed `f (lookup m a)` once as a source expression; no machine-cost,
sharing, effectful callback or runtime theorem is implied by this pure definition.

The two round trips have different strengths:

| Starting interface and translations | Valid conclusion |
|---|---|
| Original update/delete → case-based modify → constant-function update/delete | The resulting update and delete reduce pointwise to the original operations, even on raw invalid states. Empty/lookup are retained. This equality follows from these particular definitions, not from observational completeness of the Map laws. |
| Arbitrary lawful modify → constant-function update/delete → case-based modify | For each valid input, original and reconstructed modify preserve validity and have equal lookup functions. Concrete results need not be equal. |

For a nonvacuous counterexample to a stronger second round trip, use keys
`Fin 2`, values Bool, and representation `(map, counter)`, with lookup the
first projection and invariant True. Let modify perform the specified point
update and increment the hidden counter by one when `f none = none`, otherwise
by two. This is a lawful modified interface. Start with key 0 mapped to
`some false`, key 1 mapped to `some true`, and counter zero. Original modify
at key 0 with `f=id` leaves the map unchanged and counter one. The reconstructed
operation selects its derived update branch, hence invokes original modify
with the constant `some false` function and produces counter two. Both lookup
functions are the original map. The counter is representation metadata, not a
claim about execution cost. The simpler original-interface example where every
update/delete increments a counter also shows that deleting an absent key need
not return the same concrete state.

## 6. Small useful scope and connected cases

A shared unit is mathematically warranted by the already repeated source use:
thin operation/law contracts for Set and Map; the invariant-conditioned
functional-relation bridge and its composition through existing machinery;
the two modify translations with appropriately stated round trips; and a small
specified interface-only client whose observation theorem consumes those laws.
Keep decoder/invariant separate from operations, retain independent key/value/
representation types, and use the same Map lookup as its decoder. The API note
assesses the existing operations/simulation pattern and relation composition;
this source note does not prescribe an extra parallel hierarchy.

Meaningful examples can be bounded model realizations rather than unfinished
chapter algorithms:

- A two-key set model and a paired realization carrying an even natural history
  counter: start at counter zero, increment by two on insert/delete, decode by
  forgetting the counter, and require evenness as the nontrivial invariant.
  Insert 0, insert 1, delete 0 gives membership `(false,true)` and counter six.
  A state with an odd counter is genuinely outside this realization's validity.
- A two-key Option-Bool map model and a paired/history realization of the same
  observation. Update key 0 to false, update key 1 to true, delete key 0; the
  queries are `(none,some true)`. Include the equal-key variant and a missing-key
  deletion so unaffected-key and absence clauses are exercised.
- A concrete two-stage version adds a Boolean tag to the paired model/counter
  state. Its first decoder forgets the tag; its second forgets the counter.
  Empty uses a true tag and counter zero. Mutations preserve the tag and
  increment the counter by two. The intrinsic first predicate is `tag=true`,
  the middle predicate is even counter, and
  composite validity is their conjunction. A true-tag/odd-counter state shows
  why the second predicate is not implied by the first. Apply the composition
  theorem to the actual operations and the same nonempty client; the Bool
  negative example above separately refutes omitting middle validity. A bare
  pair of unrelated law certificates is not an agreement example.
- Exercise modify insertion from none, overwrite, deletion and identity, with
  the history-sensitive round-trip counterexample above. These connect to the
  derived interface laws instead of proving only isolated table arithmetic.
- Retain Empty keys/values as generality boundaries and `none ≠ some false`
  as the partial-Boolean-map boundary. The nonempty two-key cases carry the
  substantive update/composition evidence; empty cases do not replace them.

The shared validity/simulation pattern also applies to heap models, but the
Set/Map operations are not heap specifications. `Priority_Queue_Specs.thy`
uses multisets, retains repeated occurrences, restricts minimum/deletion laws
to nonempty queues, and requires both inputs valid for merge. Nonemptiness is
an operation-specific premise, not a permanent invariant that would exclude
the lawful empty queue. Existing exact queue contracts and carriers must
retain those meanings. A Set decoder that
forgets multiplicity cannot discharge a heap insertion/deletion obligation.
No new heap algorithm or queue hierarchy is proposed here.

Outside this proposed unit are all concrete BST/balanced-tree/map/heap
algorithms, ordered-list operation implementations and their source-specific
proofs, interval-list Exercise 6.1 operations/early exits/linear work, balancing
and cache proofs, and the direct recursive proof explicitly required by
Exercise 5.3. The paired model cases are evidence for the shared contract,
not substitutes for the eventual BST and interval-list chapter realizations.
All original obligations remain mandatory and queued. These boundaries do not
require a particular new trace syntax, compiler, history framework, auxiliary
statistic, or cost observation beyond the actual source obligations.

Only this report was written. No compiler, Lean/Lake, project checker or project
hash helper, Git/ref mutation, cache modification, remote write, gate operation,
acceptance loop or chapter activation was performed.
