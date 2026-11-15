# Ordered-tree search: independent case preflight

Recorded 2026-11-02 for FDSA-XS01. **Bounded mathematical preparation only.**
No API, implementation scope or source worktree is frozen or released by this
report. The retained tree components remain uncompiled and unaccepted.

Root reported that Chapter 1 attempt 3 was launched once at 22:08:37 UTC on
`07e480f6ec9958d4975bb90151005b84f2907614`; it is the sole authorized
compiler/checker. Both earlier outcomes remain unknown. This report neither
observed a terminal outcome nor performed validation. Earlier status passages
in the source report and ticket describe their recorded recovery times.

## 1. Recommendation and operation identity

The independent cases support a small shared binary selected-path query that
returns an optional **actual stored entry**. Membership and semantic map lookup
can observe that one result. A single measured executor with the ordinary Nat
invocation observation is sufficient for the calculations below; visited nodes
can be derived with a proved terminal-miss correction. This agrees with the
current coordinator/API direction, but fixes neither names nor representation.
There is no mathematical reason here to add another carrier, comparison-law
record, state-machine framework, duplicate scalar recursion or probability API.

Before calculating cases, the source and API authors supplied these boundaries:
empty returns none; LT selects the left child; EQ returns the stored node entry;
GT selects the right child. The source comparator compares **query to key**,
first with `<`, then `=`, otherwise GT. Its ordinary specialization has linear
keys. The raw operation may instead receive `route : α → Ordering`, and its
key-correctness laws must then require the actual local `Ordering.Compares`
contract. The source report confirms the repeated binary clients and the
absence of a generated `T_isin` or `T_lookup` in the inspected query theories.

Below, `F(route,t)`, `E(route,t)` and `V(route,t)` are mathematical notation for
that same prospective selected-path execution and its observations, **not
already existing Lean declarations**. They must refer to the actual returned
entry and selected child, not an inorder scan or a path traversed twice whose
returned value happens to agree. All exact case expectations were derived from
these equations before any search implementation existed.

## 2. Inputs and recoverable identities

All paths are relative to `/workspace/scratch/845aa1048b05` unless otherwise
specified. Byte and line counts below identify entire files; a count is not a
claim that every unrelated declaration in a file was read. The source report,
interim note and current ticket were read in full. Relevant retained definitions,
fixture statements and primary query equations were read directly; unrelated
chapter inventories were not treated as substitutes for those definitions.

### Control and prior case material

| File under `fdsa-control/` | Bytes / lines | SHA-256 |
|---|---:|---|
| `tickets/FDSA-XS01.md` | 3305 / 55 | `2177027f80ba29c652cb4e543c366d260be7b051f4cc784bbb48b670713983d9` |
| `research/ordered-search-source-preflight.md` | 29001 / 410 | `71fe9b69807db736c0d6319995a61bf72b1b5ff508c085d128de96c07b589c21` |
| `research/ordered-search-interim-notes.md` | 4003 / 65 | `57e893c4bb0e23e61b715220aae49deaa4d1b0c468e07b8e0c783508339831a1` |
| `research/tree-order-case-preflight.md` | 12227 / 210 | `e5c680ecdd0430f71e96f7149ebc64bdd4d834f7b0272129f0976bac4c537ffe` |
| `reviews/tree-order-requirements.md` | 19009 / 327 | `309bd487fbe1a49ddd1348af0e517327ebf22614b9e5adcf92d1254a9aeca7a1` |

The ticket identity is the resumed 55-line snapshot, including its resumption
paragraph. Earlier task messages and coordination with the API author are
proposals, not a frozen API file. This report does not claim to have read the
API author's complete stopped report.

### Retained tree candidate

Exact source is retained commit
`66eae34815a177c6b4bf5120e05202ebb8876c91`. It was read using `git show`
under the pinned Nix environment, without restoring its removed worktree.

| Blob path at that commit | Bytes / lines | SHA-256 |
|---|---:|---|
| `Applications/Trees/Observations.lean` | 4119 / 107 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| `Applications/Trees/Ordered.lean` | 5817 / 126 | `26549e623acdce3ac29e3fdd30858eb068c1bf7cd5f223468bbcbb30ecffbe66` |
| `Applications/Trees/Rotations.lean` | 7436 / 181 | `d9a9aef015fbe2c3ffcc638ea8b963784adaec4d88d9b500b5a5f148264407b3` |
| `Applications/Trees/OrderedRotations.lean` | 1814 / 43 | `c610556b727e7ddd35187c9302649948a203c0d0076e8bf3758fcfc95da50c89` |
| `Examples/OrderedTrees.lean` | 17154 / 386 | `e7715af3106bfa32983d424abc87ee75c70c8e362bb6d9e27de3ee7a253793d1` |

### Existing resource and pinned library interfaces

The base checkout is `conaled-ch01-cost-models` at the coordinator's pinned
`07e480f6ec9958d4975bb90151005b84f2907614`. Pinned Mathlib revision is
`56a005855ea17e0b0958f73ec801ae140b0a1679`, with Lean 4.35.0 revision
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. No tool/version change was made.

| File relative to that checkout | Bytes / lines | SHA-256 |
|---|---:|---|
| `Applications/Resources/Measured.lean` | 2906 / 71 | `feb5f2f3096b327d8cf636343f33fcc7be08d1324f3dc7ff6f168bf68a203f46` |
| `Applications/Resources/CallCount.lean` | 2447 / 58 | `5bb2d9e1e43dde11fdcee3c492c44662351c72e9a27af385b79de53e8e76b2a8` |
| `.lake/packages/mathlib/Mathlib/Data/Tree/Get.lean` | 2536 / 72 | `773d67e99f76e26c96e2d718d88203396fdacba3506d2e42476823440e5aa4bd` |
| `.lake/packages/mathlib/Mathlib/Data/Ordering/Basic.lean` | 1589 / 56 | `8add9a4a99dd00271f4f50a73171d5a0f4af31e971c73a807da90a93e0aac89a` |
| `.lake/packages/mathlib/Mathlib/Order/Compare.lean` | 7916 / 209 | `2a1b09abbc7d20f75a832fc47d1b6014f606938ad1b3db8c9e2bf545fdaca0d4` |

### Direct primary-source passages and governing context

| Local `book-source/` file | Bytes / lines | SHA-256 |
|---|---:|---|
| `Cmp.thy` | 682 / 24 | `5539b207634456f4c359dc12cabf720018cbc62c2c67b6d99ad0b7e5ac5993e6` |
| `Tree_Set.thy` | 3801 / 119 | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` |
| `Tree_Map.thy` | 2028 / 58 | `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43` |
| `Tree23_Set.thy` | 16114 / 381 | `ae1317555ff4e8223d2e047098c62a954f09b8e45e8fd1b1d6522ecdbc888c31` |
| `chapter05.txt` | 32466 / 605 | `b00475b2893cf76a66a5c164a63ee99e065772fffa7ae56054359b278c5c4b1e` |

The companion revision is
`f86f290225eebcc52c1ae7dba2e098f405f51c21`, under
`src/HOL/Data_Structures/` in the Isabelle mirror. The pinned July 27, 2026
book PDF has SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
The complete source preflight records the PDF, license, annotation theories,
later chapter passages and their identities. Those later-source claims below
are attributed to that report; this case task did not repeat its source survey
or download anything. The retained companion revision is not asserted to have
generated that PDF. The full applicable Isabelle copyright notice and project
provenance rules remain requirements for any later source adaptation.

Previously read governing files in the pinned base remain applicable, with the
user's local-ticket/durability-checkpoint exception. Their identities are:

| Policy/context file | SHA-256 |
|---|---|
| `AGENTS.md` | `5d017d009307c72a7616d7afe0bee9fb5a7105fe2f6f4e1da3fdccf070d4b4fe` |
| `docs/agents/architectural-quality.md` | `609c81cd22803888cfc8dafcfb6097f958e8e7c749df16b5156cd179b87835e6` |
| `docs/agents/domain.md` | `2f27fd2dec160969245bceba26cf65a0bc45fd2be24f065f84c766e5e5537a7d` |
| `README.md`, including development-environment guidance | `85d09c317be36c015927e948a379cdc7a11c2a8ec8ad6268cbd61708d5e11216` |
| `GLOSSARY.md` | `de34dcd63191a11fa6c96d37c4c9457a77d8127ceb4156f6f8f44d3dbe3e88e6` |

These are ordinary byte identities, not project verification hashes or evidence
that any Lean source compiled.

## 3. General expected laws and their exact premises

### 3.1 Raw selected-path equations

Use Mathlib's actual carrier `BinaryTree α`, whose node constructor has order
`.node entry left right`. Keep label and key types in independent universes.
The raw operation requires no order, equality decision or inhabitance on α.

| Reached case | F | E: search invocations | V: nonempty visits / three-way route calls |
|---|---|---:|---:|
| `.nil` | `none` | 1 | 0 |
| `.node a l r`, `route a = .eq` | `some a` | 1 | 1 |
| Same node, `route a = .lt` | `F(route,l)` | `1 + E(route,l)` | `1 + V(route,l)` |
| Same node, `route a = .gt` | `F(route,r)` | `1 + E(route,r)` | `1 + V(route,r)` |

Only the selected child is executed, and a hit executes neither child. These
are reconstructed charges: one for each invocation of this search, including
an empty call, with comparator internals, key projection and nonrecursive
observation wrappers uncharged. They are not recovered generated timing facts.

Let `δ(route,t)` be 1 when the actual returned option is none and 0 otherwise.
Induction over the reached branch gives the unconditional exact relation

`E(route,t) = V(route,t) + δ(route,t)`.

On a hit, E=V. On a miss, E=V+1. A root hit therefore refutes a copied merge-like
universal E=V+1 law. If V is represented as `E - δ` in Nat, its branch equations
and the absence of problematic truncation still need proof from the actual
executor; defining a subtraction alone does not establish the visit meaning.

All raw trees and routes satisfy `1 ≤ E`, `V ≤ t.height`, and
`E ≤ t.height + 1`. A successful result additionally gives `1 ≤ V` and
`E ≤ t.height`. A hit at node depth d, with root depth zero, has E=V=d+1;
a miss after m nonempty nodes has V=m and E=m+1. No depth datatype is needed
for the prospective implementation merely to use this explanatory count.

Raw success has a useful law independent of any ordering assumption:

`F(route,t) = some a  ⇒  a ∈ Trees.inorder t ∧ route a = .eq`.

It states that the exact returned label was reached. It does not say its key
matches a query. Every malformed-tree case below must still satisfy this law
and the raw bounds.

### 3.2 Calibration, strict key order and stored-entry semantics

For `key : α → κ` and `q : κ`, retain `[Preorder κ]` and the local premise

`∀ a ∈ Trees.inorder t, (route a).Compares q (key a)`.

`Ordering.Compares` means `<`, equality and reverse `<` for its three outcomes.
The actual pinned `Compares.eq_lt`, `.eq_eq`, `.eq_gt` and `.inj` laws expose
these implications under a Preorder. `cmp_compares` supplies the ordinary
LinearOrder specialization. No comparator law is required on labels outside
the input tree.

Calibration plus raw returned-entry membership is enough for **soundness**:
a returned a has `key a = q`, even on a malformed tree. Calibration alone is
not enough for completeness, because the selected branch can skip a matching
entry placed on the wrong side. Add the actual retained invariant

`Trees.Ordered (fun a b => key a < key b) t`.

Then the expected full-entry specification is

`F(route,t) = some a  ↔  a ∈ Trees.inorder t ∧ key a = q`.

Consequently presence is equivalent to occurrence of a matching key, and none
is equivalent to absence of every matching key. This is an equality-key query
law, not a payload comparison or global injectivity assumption. Strict ordering
supplies key uniqueness on this particular tree through
`Trees.ordered_key_nodup`; existing
`OrderedTreeExamples.key_injective_on_labels` already connects that theorem to
`List.inj_on_of_nodup_map` with actual membership premises.

The first-inorder-entry observation can use
`List.find? (fun a => route a == .eq) (Trees.inorder t)`. Under these premises
it equals F and needs no equality decision on κ or α. A separate first-key
association lookup, if chosen as an adapter, must retain whatever local lawful
BEq/DecidableEq interface it actually uses. The source linear-key `map_of`
observation is legitimate; silently assuming a payload equality/order is not.

The strict invariant and the local comparison law have different jobs. The
counterexamples in Section 5 distinguish them; neither should be discharged
by a count calculation or by the other premise.

### 3.3 Route-compatible label transport

For arbitrary `f : α → β` and routes r and s, the input-local hypothesis

`∀ a ∈ Trees.inorder t, s (f a) = r a`

should transport the same execution as follows:

- `F(s,t.map f) = (F(r,t)).map f`;
- `E(s,t.map f) = E(r,t)` and `V(s,t.map f) = V(r,t)`.

This requires no BST, cache validity, global injectivity, payload equality or
payload order. The count equalities follow from identical reached branches;
`Trees.inorder_map` or `Trees.height_map` alone does not prove them. The existing
`Trees.ordered_map_key_iff` can separately transport strict validity when f
preserves the key. This is an equation relating runs on two representations,
not permission to charge an actual full-tree conversion as zero.

## 4. Compact connected positive cases

### 4.1 Empty and uninhabited labels

For an arbitrary label type and route, the empty tree returns none with
`(V,E)=(0,1)`. This directly tests the base equation and the +1 in the all-input
height bound, since empty height is zero. No default label is available or
needed.

For `BinaryTree Empty`, no node can exist. More usefully for a nonvacuous map
query, take labels `Nat × Empty`, key `Prod.fst`, and query 0. Every such tree
is empty, so the stored-entry result and projected `Option Empty` payload are
none with `(V,E)=(0,1)`. This tests uninhabited semantic values while the query
itself exists. Quantifying only over a query of type Empty would hide the
boundary behind a vacuous premise.

Existing `OrderedTreeExamples.empty_payload` and its cited tree-empty case
already demonstrate that these carriers do not require Inhabited. The new
query expectation should connect to the actual empty equation, not introduce
a default, an exception or `getOrElse` to obtain a result.

### 4.2 The existing printed six-label BST

Reuse `OrderedTreeExamples.printedTree` in retained `Examples/OrderedTrees.lean`
lines 63–85. It is root6, left subtree root3 with leaves2/5, and right subtree
root9 with left leaf8. Its height is 3; `printed_inorder` gives
`[2,3,5,6,8,9]`; `printed_ordered` and `printed_keys_nodup` supply the actual
strict-order and uniqueness connections.

Use the lawful Nat query-to-entry comparator. Direct evaluation gives:

| Query | Reached keys and outcomes | Stored-entry result | V | E |
|---:|---|---|---:|---:|
| 6 | `6:EQ` | `some 6` | 1 | 1 |
| 3 | `6:LT, 3:EQ` | `some 3` | 2 | 2 |
| 9 | `6:GT, 9:EQ` | `some 9` | 2 | 2 |
| 8 | `6:GT, 9:LT, 8:EQ` | `some 8` | 3 | 3 |
| 4 | `6:LT, 3:GT, 5:LT, empty` | `none` | 3 | 4 |

These five related queries cover root/left/right/deep hit and a deep miss.
For example, query8 has V=1+(1+1)=3 and E=1+(1+1)=3; query4 has
V=1+(1+(1+0))=3 and E=1+(1+(1+1))=4. The hit and miss attain the respective
height and height-plus-one bounds. Public correctness should connect the
actual returned entries/absence to `printed_inorder`, not merely assert a
standalone numerical table.

The existing `printed_left`, `printedAfter_inorder` and `printedAfter_ordered`
also give a useful boundary using this same fixture: after its legal left
rotation, query6 still returns 6 but follows `9:LT,6:EQ`, so E=V=2 instead of
1. Valid inorder-preserving rotations preserve this lookup value; they need
not preserve an individual query's path length or cost. This is a consequence
of the concrete run, not an additional balancing theorem.

### 4.3 Semantic payload, membership and label transport

Reuse the exact existing fixture

`OrderedTreeExamples.taggedTree = three (0,false) (1,true) (2,false)`.

For this map example, regard its Bool component as **semantic payload**. The
existing `taggedTree_inorder` and `taggedTree_ordered` supply full-record inorder
and strict `Prod.fst` ordering. Query0 takes LT then EQ, returns the actual
entry `some (0,false)`, and has E=V=2. Projecting the payload gives `some false`;
observing presence gives true. Query3 takes GT then GT then empty and returns
none, with V=2 and E=3. Thus presence is different from the Boolean value
stored, and a default false would lose information.

For an actual measured result m, the existing public
`Resources.CallCount.primitive_rule` can connect both observers to that result:
`bind m (fun o => pure (o.map Prod.snd))` has the projected value and m's
unchanged E; the same applies to `Option.isSome`. This consumes m.1 and does
not run a second search. The projection is uncharged under the declared model,
not under a claim that arbitrary functions have zero runtime.

The existing `discardTag (k,b) = (k,())`, `discardTag_not_injective`,
`discardTag_preserves_key` and `discarded_ordered_iff` give a concrete route
transport client with no global injectivity. Query0 on the mapped tree returns
`some (0,())` with E=V=2; query3 remains none with V=2/E=3. This mapping changes
the semantic Bool payload to Unit; it preserves keys, routing and the mapped
stored-entry result, not the original Bool value.

For the actual annotated-map source boundary, use the same general transport
with `f = Prod.fst : ((κ × β) × γ) → κ × β`. The key is the inner first
component and the semantic value the inner second component. This erases only
the outer annotation, preserving arbitrary β, including false or Empty. It
requires no color, cached-height or balance validity. It does not confuse the
outer annotation with the semantic payload or charge whole-tree erasure as a
free executable preprocessing pass.

## 5. Missing-premise counterexamples

### 5.1 Unique keys do not ensure correct pruning

Take the raw tree with root `(2,"root")`, left singleton `(5,"left")`, and
empty right child. Its inorder keys are `[5,2]`, so they are duplicate-free,
but the left-to-root strict bound is false. For query5, a lawful comparator
chooses GT at 2 and reaches the empty right child:

`F = none, V = 1, E = 2`.

The matching full entry is nevertheless in the inorder list, and first-key
association lookup returns `some "left"`. This refutes completeness and
inorder-lookup agreement without orderedness, even with unique keys. It does
not refute raw returned-entry soundness or any raw height bound.

### 5.2 Duplicate full records and inorder-preserving rotations

Reuse `OrderedTreeExamples.sameKeyRecords`, whose root is `(1,10)` and right
singleton `(1,20)`. Existing `sameKeyRecords_inorder`, `sameKeyRecords_distinct`,
`sameKeyRecords_lex_ordered` and `sameKeyRecords_not_key_ordered` distinguish
full-record order/distinctness from semantic-key order.

The exact `Trees.rotateLeft?_node_node` equation gives a root `(1,20)` with
left singleton `(1,10)`. By `Trees.inorder_of_rotateLeft?`, both trees have
inorder `[(1,10),(1,20)]`. For a lawful key query1:

| Tree | Returned stored entry | Payload | V | E |
|---|---|---:|---:|---:|
| Existing `sameKeyRecords` | `some (1,10)` | 10 | 1 | 1 |
| Its left rotation | `some (1,20)` | 20 | 1 | 1 |

First-inorder association lookup returns 10 in both cases. Thus an
unconditional inorder-extensional **stored-entry/payload** search theorem is
false. Full records are distinct; their keys are not. Both key lists are weakly
sorted, which also fails to supply the missing uniqueness. Boolean key
membership happens to be true in both runs, so this example must not be
misreported as a membership counterexample. The separate malformed-tree case
provides that completeness boundary.

### 5.3 Strict BST validity does not calibrate a dishonest route

On the valid three-key tree with root2 and leaves1/3, ask for key9 but supply
`route := fun _ => .eq`. The raw result is `some 2`, with E=V=1. It really is
a stored entry, but its key is not 9. Tree validity cannot discharge the missing
local `Ordering.Compares` premise.

There is also a concrete API reason for retaining that premise under Preorder:
Mathlib `cmpUsing` tests `q<k`, then `k<q`, else EQ, whereas the book tests
`q<k`, then `q=k`, else GT. For incomparable distinct elements of a partial
order, Mathlib can report EQ without key equality. The value programs agree
under the stated LinearOrder laws; no new partial-order fixture or instance
is needed in the compact implementation cases merely to repeat this hazard.

## 6. Height tightness and precisely scoped averages

### 6.1 Retain a deepest-present-key witness

The book p.59 search-height statement needs more than an upper bound or an
absent Nat-key example. The following is the independently justified general
expectation for a nonempty strict tree:

Given `key : α → κ`, `[Preorder κ]`, a nonempty t satisfying the strict keyed
`Trees.Ordered` invariant, and a query family `route : κ → α → Ordering`
calibrated on the actual stored queries and entries,

`∀ a ∈ inorder t, ∀ b ∈ inorder t, (route (key a) b).Compares (key a) (key b)`,

there exists `a ∈ inorder t` for which

`F(route (key a),t) = some a` and `V(route (key a),t) = E(route (key a),t) = t.height`.

This premise only requires the family at queries that are actually stored.
Linear-order `cmp` gives the source specialization. A deepest label exists
because the tree is finite and nonempty. Inductively choose a child attaining
the maximum height; if both children are empty, choose the root. Strict bounds
and calibration force the query for the chosen label through that child, adding
one to its reached count. Strict key uniqueness rules out an earlier equal-key
stop. This argument needs no absent key, default payload, global key
injectivity, depth framework, or maximum over an empty query domain.

The printedTree query8 is a concrete nonempty witness with E=V=height=3.
If a first shared scope omits the general witness, **C5's p.59 worst-height
claim remains explicitly incomplete and mandatory**. An upper-bound-only
result must not be labeled full coverage of that claim.

### 6.2 Raw height bounds do not supply logarithmic work

For a strict increasing Nat right chain containing keys1 through n, n≥1, the
last present key n takes E=V=n=height. The absent query n+1 takes V=n and E=n+1.
The root key1 takes E=V=1 for every n. These are direct recurrence patterns,
not new complexity theorems inferred from a few samples.

They explain both limitations: strict BST validity alone permits linear
height, and even a future balanced worst-case bound does not make every
successful query take Θ(log n). Balanced chapters must establish their actual
shape invariants, height-size inequalities and node-count/abstract-cardinality
bridge before composing with the search bound. At n=0 the invocation count is
1, so an all-size bound with zero right-hand side at empty size is false.

### 6.3 The preserved finite present-key average

For the printed p.67 comparison, the retained interpretation is the uniform
choice among the three **present** keys3,6,9. Use existing `three 3 6 9` for
the balanced tree and the literal increasing right chain3→6→9.

| Query | Balanced V=E | Chain V=E |
|---:|---:|---:|
| 3 | 2 | 1 |
| 6 | 1 | 2 |
| 9 | 2 | 3 |
| Sum | 5 | 6 |

The arithmetic means are 5/3 and 2. The actual selected-path outputs are
respectively `some 3`, `some 6`, `some 9`; all queries succeed, so the E/V
hit relation is the connection allowing either observation. This does not
prescribe a uniform distribution on an infinite type, an absent-key distribution,
a general expected-search framework or a nonuniform-query theorem. If included,
it must refer to the actual three runs, not only the constants 5 and 6.

## 7. Literal primitive tests and existing public connections

### Primitive tests stay separate

For the book's literal comparator, every visited node executes one `<` test;
EQ/GT additionally execute one equality test. On the five printedTree queries
6,3,9,8,4, the respective unit-test totals are **2,3,4,5,4**. For example,
query8 has GT/LT/EQ, hence 2+1+2=5 tests despite only three route calls.

If Q counts reached non-LT results, this separate declared total is V+Q,
with `<` count V and equality count Q; consequently V≤V+Q≤2V. It is not the
main E charge and must not be called the number of route invocations. No
primitive-test definition is required merely to state this boundary. Mathlib's
second test is reverse `<`, so equal returned Ordering values alone supply no
primitive-tariff or real comparison-cost equality. An expensive arbitrary
route is not made constant-time by the raw E/V bounds.

### Connections worth consuming, without a declaration quota

| Existing public surface | Meaningful prospective connection | Retained limit |
|---|---|---|
| `Trees.inorder_node`, `inorder_map`, `inorder_length`, `height_map` | Stored-entry membership, transport and shape/count observations | An inorder or ordinary fold evaluation is not the selected query path |
| `Trees.ordered_node`, `ordered_key_iff_pairwise`, `ordered_key_nodup` | Prune the opposite subtree and identify the unique full entry matching q | Full-record lexicographic order or weak key sorting alone is insufficient |
| `Ordering.Compares` and `.eq_lt/.eq_eq/.eq_gt`; `cmp_compares` | Actual input-local route law and source LinearOrder specialization | Preorder alone does not make generic cmp lawful |
| `Trees.ordered_map_key_iff` with `discardTag_preserves_key` | Preserve keyed validity independently of raw result/path transport | No global injectivity or semantic-payload preservation from erasing Bool |
| `Resources.Measured`, `CallCount.tick`, `tick_value`, `tick_cost` | One actual invocation-count executor with unchanged returned entry | No generated source time theorem or Lean runtime claim |
| `CallCount.primitive_rule` | Payload/isSome observations of the actual measured result | No second search or uncharged expensive conversion |
| `rotateLeft?_node_node`, `inorder_of_rotateLeft?`, existing ordered rotation facts | Valid lookup-value invariance and the duplicate-key counterexample | Neither raw arbitrary-tree lookup nor individual path cost is inorder-extensional |

The exact pinned path interfaces also remain relevant:

- `BinaryTree.indexOf (lt : α → α → Prop) [DecidableRel lt] (x : α)`
  has result type `BinaryTree α → Option PosNum`; its branch decision is
  `cmpUsing lt x a`.
- `BinaryTree.get : PosNum → BinaryTree α → Option α` follows
  `PosNum.one`, `.bit0` and `.bit1` to a stored label.

A homogeneous value bridge can equate F with indexOf followed by get when its
route is exactly that cmpUsing. A heterogeneous key bridge can instead obtain
an index from `t.map key` and get the full entry from the original t. These
are proposed value equations supported by the literal matching recurrences;
`Get.lean` itself provides no correctness or cost theorem. Mapping all labels
and/or following the position is additional work. Defining a costful search
through either construction cannot inherit a one-pass E/V equation merely
from value agreement. Likewise, fabricating a full query record to satisfy
indexOf's homogeneous type would impose an unjustified payload inhabitance.

No suitable existing general BST ADT query interface was identified in this
bounded base-graph read. The API author confirmed that
`Search.HeuristicCore.lookup` is a specialized list-store operation, not this
tree query. No XA01/ADT import is forced. The actual semantic targets are the
query clauses of the source Set/Map refinements: Tree_Set membership in inorder
and Tree_Map lookup against its first-binding observation. Proving those
clauses does not construct or verify the full ADT, its updates or invariant
preservation. The source report owns the exact later-client and obligation map.

## 8. Scope decision, independent calculation record and stop boundary

The compact evidence is connected: one printed tree covers every branch and
the hit/miss height boundary; one existing keyed Bool fixture covers full-entry,
false-payload, membership and label transport; the existing duplicate fixture
and its rotation isolate uniqueness; one malformed unique-key tree isolates
pruning; a dishonest route isolates calibration. Empty/uninhabited types and
the source's finite present-key comparison cover their distinct domains.
There is no request here for an extra example per helper declaration.

The general laws and tables were derived directly from the literal recurrence.
A bounded in-memory Python calculation corroborated the displayed printedTree,
rotation, tagged, malformed, duplicate and three-present-key numbers. It wrote
no artifact and did not evaluate any Lean implementation. That arithmetic
corroboration, source reading and ordinary SHA-256 identities are not compiler
or theorem-validation evidence.

The smallest useful shared addition therefore consists of the actual binary
selected-path execution, stored-entry and calibrated keyed specifications,
route-compatible transport, and exact invocation/visit interpretation with
raw height bounds. The nonempty deepest-present witness is either included
explicitly or remains a named mandatory C5 obligation. No choice here authorizes
source implementation; root still must reconcile the complete stopped reports,
freeze a bounded scope, record ownership and save its pre-code checkpoint.

Remaining source boundaries are substantive. Chapter 7's Node3 may make two
three-way comparisons per visited node and needs its own recurrence/count;
interval-overlap queries and Chapter 10's reconstructing split are different
operations. All insertion/deletion, cache/balance invariants, rotations' local
reconstruction work, logarithmic guarantees, full Set/Map implementations and
remaining whole-book obligations stay mandatory. No chapter was activated,
accepted or declared covered by this preflight.

Only this report was written. No Lean source, compiler/checker, project hash
helper, Git ref/worktree, project cache, remote operation or final-review loop
was used or changed by this task. Read-only Git blob retrieval under pinned
Nix and ordinary report identity calculation are the permitted exceptions to
source/tool inactivity. After the complete report readback and ordinary
size/line/SHA handoff, all writes stop so root can capture these exact bytes.
