# Ordinary leftmost extraction: bounded source preflight

Status: **source preparation only, 2026-11-02**. No scope is frozen and no new
implementation, chapter activation or acceptance is authorized by this note.
Chapter 1 attempt 3 remains the coordinator's sole validation; this task ran no
compiler, checker, project hash helper, cache or Git operation. All original
chapter inventories, corrections, requirements and pending proofs are unchanged.
Read with `../REQUEST.md`, `../DECISIONS.md`, the Chapters 5–10 inventories and
the separate `tree-leftmost-api-preflight.md` when its author stops that report.

## 1. Decision supported by the sources

A small **ordinary binary-tree extractor of the first inorder entry and its
actual residual tree** has a concrete repeated use. Chapter 6 does not merely
resemble Chapter 5: `Tree_Map.thy` imports `Tree_Set` and calls the very same
polymorphic `Tree_Set.split_min` on full `(key,value)` labels. This warrants
considering a bounded shared operation over the existing `BinaryTree`, subject
to the separate API/case assessment. It does not warrant a general balanced-tree
extraction framework, a new tree carrier, a complete deletion implementation,
or a new ADT hierarchy.

The strongest useful common fact is the exact **head-and-tail inorder equation
on arbitrary labels**, together with the literal rebuilding recurrence. Leastness
is a consequence of strict key ordering, not part of the raw operation. The
extractor preserves the remaining tree structure by rebuilding only the left
ancestors and returning the removed node's original right child. Rebuilding a
new tree from the same tail list is not the same source implementation.

Later variants share some mathematics and leftmost descent, but their actual
returned trees, domains, helper work and invariants differ. AVL's printed
extractor even goes in the opposite direction. These distinctions are detailed
below and remain original chapter obligations.

## 2. Exact primary sources, provenance and reading scope

The retained official manuscript is the **July 27, 2026** FDSA PDF:
<https://fdsa-book.net/functional_data_structures_algorithms.pdf>,
1,742,029 bytes, SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
All page numbers below are printed pages. Local `book-source/chapterNN.txt`
files are research extractions of this PDF; their printed-page markers and
line references locate the inspected passages, not a new source edition.

The Isabelle mirror is pinned to
`f86f290225eebcc52c1ae7dba2e098f405f51c21`. It postdates the manuscript and is
not asserted to be its generating revision. Source URLs are the following
prefix followed by the path in the table:

`https://raw.githubusercontent.com/isabelle-prover/mirror-isabelle/f86f290225eebcc52c1ae7dba2e098f405f51c21/`

| Pinned source path | SHA-256 | Bounded material used |
| --- | --- | --- |
| `src/HOL/Data_Structures/Tree_Set.thy` | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` | Entire 119-line source; ordinary extractor, both deletion algorithms, exact inorder refinement. |
| `src/HOL/Data_Structures/Tree_Map.thy` | `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43` | Entire 58-line source; actual import and full-pair successor use. |
| `src/HOL/Library/Tree.thy` | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` | Retained carrier/height/inorder context from Chapters 4–5; no claim of rereading the entire theory in this pass. |
| `src/HOL/Data_Structures/Tree2.thy` | `c63da5dc95f98c1c6d1eac889e9c798f3a53ef5b21658791dc914b34b5ea904e` | Lines 7–28, 36–40: outer-annotation erasure, erased inorder and BST. |
| `src/HOL/Data_Structures/Interval_Tree.thy` | `0a70bfdd8ff8d86055e20319e7bb918550067d2e3f738a42517c8c2bc640def2` | Lines 70–81, 119–172: smart reconstruction, extraction/list law and independent cache validity. |
| `src/HOL/Data_Structures/Tree23_Set.thy` | `ae1317555ff4e8223d2e047098c62a954f09b8e45e8fd1b1d6522ecdbc888c31` | Lines 78–143, 190–202, 342–358: tagged extraction, partial helper domains and completeness premises. |
| `src/HOL/Data_Structures/RBT_Set2.thy` | `512db7d1698b5c9ce3447ea30a7b493f957655cafeb2e9d5c6437b9f59e14560` | Entire 152-line source; replacement extractor, old-color tests, raw inorder law and invariant contract. |
| `src/HOL/Data_Structures/RBT_Set.thy` | `542519dc50a4ca03735f68f36bf6bf666f941a33502b028cf2f939b3119d80c8` | Lines 72–90, 242–271: balancing/join observations and their separate invariant hypotheses. |
| `src/HOL/Data_Structures/RBT_Map.thy` | `18aad043c03697c6bd0fb3ad18387dd9030727dceaceee26abb7d5a108ca43ba` | Lines 5–35, 53–59: supplied map implementation uses joining, not replacement. |
| `src/HOL/Data_Structures/AVL_Set_Code.thy` | `423ea6e7e5d415a9d279ca24c48ce45b2d1bd60f591fae50a00ffa6e852cb2e3` | Entire 107-line source; rightmost extraction and raw inorder laws. |
| `src/HOL/Data_Structures/AVL_Set.thy` | `282cf829b7efc3421428cbe7ee3e590492d45ed0b8c7b80eff1ae3c57630f3b9` | Lines 134–145: actual AVL and height-change premises. |
| `src/HOL/Data_Structures/AVL_Bal_Set.thy` | `f347f9d6f788e1a057e82c4e5fd0a274cfb95593d1a0fc6094e00ceef83bdcae` | Lines 69–87, 133–155: old/new height-change tests and stronger inorder-domain premise. |
| `src/HOL/Data_Structures/Set2_Join.thy` | `15edbd8a0b1b00633a15d9d1ccffb92d60ca9b313ba3b2f3bf4313af79f57d1b` | Lines 10–78: exact supplied-join assumptions, extractor and join2 contracts. |
| `src/HOL/Library/Time_Functions.thy` | `29a91b7ff9a9939bfed168dfc28407bb3b8e07ff2783d9e9bea0cdc387312d01` | Lines 12–19: generated zero pair-projection costs; timing-convention context. |

All listed local file identities were checked by ordinary byte hashing. This
is provenance checking, not an Isabelle build or a Lean validation claim.
Ordinary query/deletion theories credit Tobias Nipkow; `Interval_Tree` credits
Bohua Zhan with modifications by Tobias Nipkow; `AVL_Set_Code` credits Tobias
Nipkow and Daniel Stüwe and notes its AFP AVL basis. The Isabelle BSD notice is
`book-source/ISABELLE-COPYRIGHT`, 1,673 bytes, SHA-256
`44176a9195f0d6110302ca58c302437b2d6685049d4b8a7c1117121883d4b64d`.
Any source-derived implementation/documentation must retain that complete
notice. Manuscript research copies remain excluded from deliverables.

There is also a **distinct, already retained generated timing source** for
Chapter 10: Marco Haucke's AFP *Work Bounds for Strongly Joinable Balanced
Binary Search Trees*, dated September 24, 2026, via
<https://isa-afp.org/release/afp-Joinable_BST_Work_Bounds-2026-10-26.tar.gz>.
The 52,075-byte archive has SHA-256
`5bf4d3bfc7f9106748163e8c7d4940d7756bcfe5a7ae197ce98dc520fb0b4911`;
its `StronglyJoinable.thy` research copy has SHA-256
`da113a8cbdadeb27b7c6689b9e9b929dfb654870484238d4a29e515868b7185f`.
Its BSD-3-Clause provenance and license hash
`9ac784670a1624c9b0f83f61c2c68163985cfd50f5c2fbe9699623311a5ce4bd`
are already retained in `chapter10-obligations.md`. Only the locale and
extraction-cost passages specified below were revisited; no paper-wide or
AFP-wide scope is added.

## 3. Literal ordinary operation and its empty domain

Book p.61 (`chapter05.txt:82–98`) and `Tree_Set.thy:35–45` give the same
operation. Write E for empty and N(l,a,r) for the source constructor; Lean's
existing constructor orders arguments as `BinaryTree.node a l r`.

On a **nonempty** tree:

- If the left child is E, return `(a,r)` immediately.
- Otherwise compute `(m,l') = split_min l`, then return
  `(m,N(l',a,r))` using that actual returned left subtree.

There is no call to `split_min E` at the bottom of a valid descent. The code
inspects the left-child shape before deciding to recurse. There is no key
comparison, sortedness test, inorder construction, subtree minimum scan or
right-subtree traversal in this extractor. Testing whether a tree is empty
can be a constructor match; it does not require equality on labels.

The source's type is polymorphic `'a tree -> 'a * 'a tree`, with no ordering
class. Only a node equation is supplied. Isabelle/HOL leaves the E case
unspecified; it is not a useful equation saying that E returns a default
label or a particular residual tree. There are no values of type
`Empty × BinaryTree Empty` in Lean, so a global default cannot be imported
from HOL's nonempty-type setting.

A source-faithful total Lean adaptation can return
`Option (α × BinaryTree α)`, with none on E, or use an explicit nonempty
input domain. Option fits the existing project partial-operation convention.
Whichever form is chosen, the actual nonempty equations and successful
recursive calls need correspondence proofs. For Option, failure iff E and
success on every nonempty raw tree are useful complete-domain laws. This is
not an extra ordering invariant. The proposal leaves names and implementation
choices unfrozen; this report does not define a Lean operation.

The source callers already establish the domain: ordinary set and map deletion
first test whether the right child is E. The EQ branch returns the left child
when it is; otherwise it extracts a successor from the nonempty right child.
The recursive extractor branch similarly knows its left child is nonempty.
A future caller must carry these facts through the actual returned pair or
Option; successful extraction is not permission to replace the residual tree
by an unrelated tree with the same set.

## 4. Shared value claims and the necessary premises

These are the smallest useful mathematical targets suggested by the actual
source. They are proposed proof targets, not new frozen requirements or
implemented/accepted theorems.

| Claim | Exact domain and reason |
| --- | --- |
| `m :: inorder t' = inorder t` after successful extraction | Arbitrary labels and raw trees. Source `split_minD`, `Tree_Set.thy:76–79`, assumes only the result equation and `t != E`. It is stronger than a set equation and retains order and repeated occurrences. |
| Returned m belongs to the input; input labels are `{m} union labels(t')` | Follows from the exact list equation without ordering or decidable label equality. The residual may still contain m. |
| `t'.numNodes + 1 = t.numNodes` | Follows from the exact list equation and existing inorder-length law; counts one occurrence, including duplicate labels. It is not a raw set-cardinality decrement. |
| `height t' <= height t` | Structural induction on the actual ordinary recurrence, no BST premise. This is the helper needed for the replacement-deletion part of the p.62 height claim, C05-013. The whole deletion proof remains separate. |
| The residual remains strictly key ordered and every residual key is greater than `key m` | Add `Trees.Ordered (fun a b => key a < key b) t` and a key Preorder. Existing ordered-inorder/Pairwise facts plus the head equation supply this consequence. No order on full payload records, global key injectivity, comparator, or key-equality decision is needed. |
| `key m` is a least input key; the residual has exactly the original keys minus `key m` | Same strict key premise. Leastness uses the extracted key's membership and the strict tail bound; absence from the residual uses irreflexivity. For full-pair map labels, keep the returned semantic value as well. |
| Exact transport through an arbitrary label map f | The ordinary recurrence suggests mapping the actual output by `(m,t') -> (f m,t'.map f)`. Independent label universes, no injectivity/order/decidable equality. This is a structural value law; it does not make preprocessing by `t.map f` free or preserve an arbitrary cache invariant. |

The scalar set specialization uses `key = id`; the map specialization uses
`key = Prod.fst`, preserving arbitrary values in an independent universe.
Strict key ordering implies uniqueness within this tree, not global injectivity
of the key function. Extraction itself does not need the local comparison
calibration introduced for query search because it makes no comparisons.

Raw orderedness preservation for a still weaker arbitrary relation may also
be provable by direct structural reasoning, but it is not needed to justify a
new general preservation framework or to enlarge this proposed first scope.
The existing strict-key/inorder interface already serves the source clients.

### Exact Chapter 6 reuse and retained source erratum

`Tree_Map.thy:5–8` imports `Tree_Set`; lines 23–28 call its polymorphic
`split_min` on full semantic pairs. Lines 41–43 use that same `split_minD`
for the map deletion's list refinement. No annotation is discarded and no
successor value is recomputed.

Book p.82, `chapter06.txt:181–192`, points to **§5.6.4**. That is the retained
wrong cross-reference: §5.6.4 is interval-tree smart rebuilding, whose second
field is an endpoint cache. The actual generic dependency is **§5.2, p.61**.
This is recorded already in C06-047 and the Chapter 6 defect section; no prior
inventory is changed here. Treating the pair's second field as an annotation
would destroy map values and is not a harmless notation adjustment.

For example, deleting key 1 from an ordinary tree with root `(1,true)` and
right child `(2,false)` must replace the root by the complete `(2,false)`
entry. Reusing the old true value, returning only 2, or substituting a default
value would fail the original map deletion contract. This example is an
independent expected client calculation, not a new implementation in this note.

## 5. Later consumers: same idea does not identify the executable operation

| Later source and original obligations | Actual difference and retained proof domain |
| --- | --- |
| Interval trees, pp.73–74; C05-074, C05-076–079; `Interval_Tree.thy:119–172` | Extract logical interval a from `(a,cache)`; use the smart constructor `node l' a r`, recomputing the changed ancestor's maximum cache. The erased head-inorder identity needs no cache/BST premise. Cache preservation separately needs valid input caches and nonemptiness, but no BST premise. Ordinary extraction on full pairs would leave stale ancestor caches. |
| 2–3 trees, p.89 Figure 7.2 and p.91; C07-037/042/048/049 and C07-054; `Tree23_Set.thy:110–143,190–194,342–354` | Distinct Node2/Node3 carrier and underflow-tagged residual. Bottom Node2 returns Uf E; bottom Node3 retains its second key in an Eqd Node2. Higher nodes use node21/node31. Nonempty **completeness** is needed even for the source head-inorder law and for safe helper calls, not only for logarithmic height. |
| Red-black replacement, pp.99–100; C08-047–051 and C08-071/072; `RBT_Set2.thy:13–28,40–48,63–70` | Descend left but rebuild by `baldL l' a r` iff the **old left child** is Black, otherwise R. Raw erased inorder survives without search/color/black-height invariants. Lemma 8.1 separately needs nonempty input, invc and invh, and distinguishes old root Red from Black. |
| Red-black maps, p.102; C08-086; `chapter08.txt:249–257`, `RBT_Map.thy:25–35` | The book asserts that both deletion methods adapt to maps by comparing keys and preserving full entries. The supplied map file chooses joining; it is not evidence that the replacement-map variant is already implemented there. Both original alternatives remain covered by their own obligations. |
| Cached AVL, pp.109–110; C09-030–033 and C09-039/040; `AVL_Set_Code.thy:57–70,96–105`, `AVL_Set.thy:134–139` | The printed algorithm extracts the **rightmost maximum of the left child**. It returns `(residual,entry)`, recursively descends right and rebuilds with balL. Its raw list law is `inorder residual ++ [entry] = inorder input`, with nonemptiness but no AVL/BST premise. AVL and the height drop of at most one require the actual AVL invariant. A leftmost implementation is not this recurrence. |
| Balance-factor AVL, p.115; C09-084–086; `AVL_Bal_Set.thy:72–87,133–155` | Rebuild with balL only when `incr r' r`, using **new,old** in that order; otherwise retain the old balance tag. Unlike the cached-height family, its inspected source inorder theorem additionally assumes avl. That valid-domain difference must not be erased by a shared theorem name. |
| Join-based helpers, pp.119/122; C10-014–021; `Set2_Join.thy:22–78` | The leftmost recursion calls the supplied `join l' a r` on its actual recursive residual. It separately proves set conservation, BST preservation/strict minimum and the supplied invariant. Join may rebalance recursively; plain node rebuilding is not a substitute. |

For red-black Lemma 8.1, the exact structural conclusion is: invh remains;
if the old root is Red, black height is unchanged and invc remains; if the old
root is Black, black height decreases by one and only invc2 is promised.
It does not assume a black root or BST ordering. Final public deletion's
painting and its BST/set laws remain distinct obligations.

For 2–3 trees, source `split_min E` is unspecified and some malformed nonempty
trees also reach partial helper cases. A one-sided empty-child test is justified
by completeness, which forces the other children at that node to be empty as
well (`Tree23_Set.thy:116–117`). Thus the ordinary extractor's raw
"success iff nonempty" law cannot be copied to that family without a new,
explicit totalization and valid-domain correspondence.

### Join-based raw sets are not ordinary raw inorder

The five source join/invariant assumptions are precisely at
`Set2_Join.thy:22–29` and book Figure 10.2, p.119. The unconditional value
assumption is **set union**, not full inorder, multiplicity or node count.
Consequently the source's nonempty extraction conclusion is
`m in set(input)` and `set(input) = {m} union set(residual)` (lines 40–46).
BST ordering gives strict minimality and no duplicate m (48–54); the separate
supplied invariant gives residual validity (56–62).

An arbitrary join satisfying only those original contracts may change shape
and raw occurrence/order observations. Do not import ordinary `split_minD`
or a raw one-node decrement into this locale for free. Under strict BST
premises, sorted unique key observations permit stronger consequences, but
that requires a proved bridge. The supplementary StronglyJoinable locale
explicitly adds `join_size` under valid children (`StronglyJoinable.thy:31–39,
50–70`); its `split_min_sum` at 606–615 then proves a one-node decrement under
inv. This extra hypothesis confirms the distinction rather than eliminating it.

Even when a later constructor preserves erased inorder, that proves an
observation law, not equality with the ordinary residual tree. Balancing,
cache repair, underflow flags and costs remain separate actual operations.

## 6. Timing: literal descent, declared extension and other rebuilders

### What is and is not supplied

Book §1.5, pp.6–8 (`chapter01.txt:188–244`), counts selected nonprimitive
function calls, charges a recursive defining equation one, treats constructors
and designated primitives as zero, and removes entry charges for nonrecursive
helpers under its inlining convention. Appendix B p.347 says zero time
functions have already been simplified away. `Time_Functions.thy:12–19`
confirms the zero fst/snd projections in the pinned source.

A scoped read/search found **no** `time_fun`, `T_split_min` or `T_split_max`
declaration in Tree_Set, Tree_Map, Interval_Tree, Tree23_Set, RBT_Set2, RBT_Set,
RBT_Map, AVL_Set_Code, AVL_Set, AVL_Bal_Set or Set2_Join. Appendix B contains
no split_min/split_max entry. Therefore a measured ordinary extractor would
reconstruct the literal recurrence under explicit charges; it would not quote
an already generated timing theorem. This does not waive any original
complexity claim or the balanced variants' helper work.

### Ordinary nonempty self-call observation

Let d(t) be the number of nonempty nodes on the left spine: d(E)=0 and
`d(N(l,a,r)) = 1 + d(l)`. This is explanatory notation, not a required new
public statistic. Under one charge per invocation of the actual ordinary
extractor, with constructors/shape tests/pair/Option observations uncharged,
its nonempty cost E obeys:

- `E(N(E,a,r)) = 1`, for every right subtree r;
- if l is nonempty, `E(N(l,a,r)) = E(l) + 1`.

Thus `E(t)=d(t)` on nonempty inputs, independently of label order. Every such
invocation visits one node, and there is **no reached empty recursive call**.
A total Option realization may declare `(none,1)` on E by charging its new
empty entry; that is an explicit Lean extension, not source behavior on the
unspecified input. With that convention the useful raw bounds are:

- on nonempty t, `1 <= E(t) <= height t`;
- on every t, `1 <= E(t)` and `E(t) <= height t + 1`;
- successful extraction's returned height is at most input height, separately
  from the number of invocations.

An implementation that recursively calls the left child **even when it is
empty**, then interprets none as "use this root", can have the same value but
one extra charged call on every nonempty input. `TreeSearch.run` with an
always-left route likewise reaches nil and does not return a residual tree.
Neither is an unchanged recurrence/cost realization of the guarded extractor.

The count is not uniformly proportional to the height of each individual
nonempty tree. A right chain can have arbitrary height and extraction cost 1;
a left chain of n nonempty nodes has cost n. Both can be strict BSTs with the
same inorder [0,...,n-1]. These give useful sharpness and value-versus-cost
boundaries without asserting a lower bound for every shape. A logarithmic
bound needs the later representation's actual height guarantee.

There are d(t)-1 ancestor `Node` rebuilds in the ordinary successful recursion.
That is a separate constructor-use observation; it is not a claim about
physical allocation or retained memory. The source self-call tariff charges
those constructors zero. No runtime, compiler sharing or stack theorem is
implied by returning an existing right subtree or by naming a recursive result.

### Actual later helper work

For a variant that follows the same left descent but runs a rebuilder on each
returned residual, counting only extractor entries can still give d(t).
It omits those actual rebuilding computations. Under a separately declared
model their total is `d(t) + sum(rebuilder costs)` over the d(t)-1 rebuilt
ancestors. If each reached rebuilder cost is at most K in that model, the
total is at most `d(t) + K*(d(t)-1) <= (K+1)*d(t)`. This conditional arithmetic
does not establish the bound K for a source helper, and it does not require
introducing a generic callback executor now.

In particular, source nonrecursive/inlined helpers and XT01's separately
charged positive cache-access model are not interchangeable. Interval cache
recomputation and RBT/AVL local balancers need their actual operations and
named tariffs; the arbitrary Chapter 10 join can itself recurse and needs its
own work bound. A value/inorder erasure theorem transfers none of these counts.

The retained AFP `StronglyJoinable.thy` is a specific counterexample to an
unqualified assertion that no generated extractor timing exists anywhere:
line 699 generates **its join-based** `T_split_min`. Lines 619–621 define
`W_split_min` on a nonempty node as 1 at the base, otherwise
`1 + W_split_min l + W_join l' a r`, using the actual returned l'. The bridge
at 706–710 bounds generated time by `(1+k0+k1)*W_split_min` under inv and
nonemptiness, within the full StronglyJoinable locale. That locale assumes
rank/balance laws, nonnegative constants, and a supplied T_join/rank-difference
bound; its text explicitly requires a concrete instantiation to connect
T_join to actual join timing. This is not a timing theorem for the ordinary
Node constructor, and it does not settle C10-117 or the later set algorithms.

## 7. Original obligation mapping and minimal future steps

| Existing original rows | What an ordinary shared extractor could support; what remains |
| --- | --- |
| C05-006/007 | Literal ordinary nonempty extraction and full-entry head-inorder/minimum consequences, with the stated hypothesis separation. |
| C05-008, extraction part of C05-013, deletion clauses of C05-014/015/028/041 | Actual successor result and height helper. The entire delete recursion, both valid-input semantics and invariant preservation, and the refinement composition remain mandatory. |
| C05-021 | May reuse an actual operation, but the exercise still needs its direct recursive BST/set proof route. An inorder-only proof is not its full solution. |
| C06-047; helper use in C06-048/063/066 | Exact full-pair reuse and corrected reference. Key-directed deletion/list refinement, lookup/update laws and the complete six-law tree Map realization remain queued. |
| C05-076/078 | A later smart-rebuilding specialization can reuse the observation pattern after correspondence. This ordinary unit does not implement interval extraction or prove its cache preservation. |
| C07-037/042/048/049/054; C08-047–051/071/072/086; C09-030–033/039/040/084–086 | Later domain, representation, balancing and work obligations remain unchanged, including the opposite-direction AVL algorithms and map alternatives. |
| C10-014–021 and C10-098 onward | Supplied-join algorithms need their own contracts and actual work, with all additional rank/size premises retained. No automatic raw inorder or total-cost transfer. |

The smallest useful next scope, if the coordinator chooses to freeze one, is
an ordinary full-entry Option/domain extraction over existing BinaryTree,
its exact raw recurrence/head-inorder/failure laws, the source-needed residual
height/size consequences, a key-ordered minimum consequence, and genuine set
and semantic-pair clients. Exact arbitrary-label mapping is a natural shared
transport law. A single actual measured realization and its declared
invocation equations would be useful if resource work is selected; no duplicate
pure executor or arbitrary generic rebuild framework is needed just to serve
Chapters 5 and 6. API authoring/readiness and independent cases still determine
that final choice; this report does not allocate files or freeze names.

A bounded local search found no matching extractor in the inspected existing
Mathlib `Data/Tree/{Basic,Get}` interfaces or retained conaled tree modules.
Mathlib supplies the carrier, map, canonical size/height and `height_le_numNodes`;
retained `Trees.inorder`, `inorder_length`, `inorder_map` and
`ordered_key_iff_pairwise` provide the needed observations. The retained
`Resources.TreeSearch` returns a found entry and count, not the rebuilt
remainder. Priority-list deletion operates on a different representation and
selects by priority, not inorder position. This is a scoped reuse observation,
not a claim of absence from every dependency; the complementary API report
owns the exact final reuse assessment. Inherited tree drafts remain unaccepted.

## 8. Independent boundary cases worth connecting later

These are direct mathematical calculations from the literal recurrence, not
an enumeration run, executed Lean tests or new frozen example requirements.
They are intentionally small enough to distinguish actual behavior.

| Input or client | Expected observation and purpose |
| --- | --- |
| E, including `BinaryTree Empty` | Option none; if the total entry tariff is selected, cost 1. No payload/default or nonempty witness exists. |
| N(E,a,E), arbitrary a | Return `(a,E)`, cost 1. No order/decidable equality on a is required. |
| N(E,a,r), arbitrary large r | Return the exact r without traversing it, cost 1. Prevents a full-tree scan or a spurious height lower bound. |
| Root 4, left node 2 with right singleton 3, right singleton 6 | Inorder [2,3,4,6]; return 2 and root 4 with left singleton 3/right singleton 6, cost 2. Checks the removed node's right-child splice and actual ancestor rebuilding. |
| Root 2, left singleton 5, right singleton 1 | First inorder entry is 5, even though numeric least is 1. Raw list law holds; the missing strict-order premise cannot be hidden. |
| Root 1 with left singleton 1 | Remove one occurrence; residual still contains 1. Raw node decrement is 1, but the represented set does not become empty. |
| Root `(1,true)`, right singleton `(2,false)` | The actual replacement-deletion body must use extracted `(2,false)`, not the old payload or an annotation-erased key. |
| A constant label map | Exact mapped extraction/count can survive while strict semantic-key order does not. Keep raw transport separate from ordered conclusions. |
| Height-tagged root `(2,2)` with left singleton `(1,1)` | Ordinary full-pair extraction retains root tag 2 although its new structural height is 1. Erased inorder is correct; cache validity is false. Smart rebuilding is a separate client. |
| Strict left chain 2→1→0 versus strict right chain 0→1→2 | Same inorder [0,1,2] and height 3; extracted first key 0 in both, but invocation counts 3 and 1. Returned residual trees also have different shapes. |

The Empty semantic-map case can use a key type Nat and value type Empty:
every `BinaryTree (Nat × Empty)` is E, so extraction returns none without
hiding behind an impossible query type. Extraction has no query argument in
the first place; its successful result must still retain arbitrary values.

## 9. Scope and status handoff

The source evidence supports considering the ordinary primitive because of
literal cross-chapter reuse, while rejecting automatic identification with
all later balanced variants. The existing p.82 cross-reference erratum is
retained explicitly. No new false printed theorem was discovered in this
bounded read. The principal hazards are conflating first inorder with minimum,
set removal with one-occurrence removal, semantic pair payload with annotation,
nonempty with balanced-family validity, and equal observations with equal work.

All original insert/delete/join/union and direct-proof exercise obligations,
interval-cache/search/sweep algorithms, balanced carriers and helper branches,
logarithmic bounds and Chapter 10 work analysis remain mandatory. No acceptance
claim follows from this report, a source-only draft or a durability checkpoint.
No prior report, requirement, ticket, source file, branch or validation state
was changed by this task. Only this preparation report was written; the parent
coordinates any later scope, implementation, review, checkpoint or upload.
